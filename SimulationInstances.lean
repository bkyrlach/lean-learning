/-
  Simulation Instances: Traffic Light, Elevator & Parallel SFC

  Instantiates the general Simulation framework (from Simulations.lean) for
  the traffic light, elevator, and parallel SFC examples. Each example yields:
  1. A forward simulation (inductive semantics → SFC engine)
  2. A backward simulation (SFC engine → inductive semantics)
  3. A full bisimulation pairing both directions

  The parallel SFC (AND-divergence/convergence) requires this framework because
  its configurations have multiple active steps ({S2, S3}), which cannot be
  expressed with SFCBisimulation's single-step `toId : S → StepId`.

  Design: State types are packaged as products (State × Valuation) to fit
  the binary step relation required by LTS. Init/final are set to False
  (both systems are cyclic), making those diagrams vacuously true. The step
  diagram is the substance — it reuses the existing forward/backward proofs.
-/
import Simulations
import TrafficLightEquiv
import ElevatorEquiv

open TLState ElevState

-- ============================================================================
-- Traffic Light: Simulation Instances
-- ============================================================================

section TrafficLightSimulation

-- Inductive operational semantics as an LTS over (TLState × Valuation)
local instance tlIndLTS : LTS (TLState × Valuation) where
  init := fun _ => False
  final := fun _ => False
  step := fun ⟨s, v⟩ ⟨s', v'⟩ => TLStep s (v "timer") s' ∧ v' = v

-- SFC engine as an LTS over Config (traffic light specific)
local instance tlSfcLTS : LTS Config where
  init := fun _ => False
  final := fun _ => False
  step := fun cfg cfg' => SFCStep Examples.trafficLightSFC cfg cfg'

-- Full bisimulation with shared match relation
def tlBisimulation :
    Bisimulation (TLState × Valuation) Config Unit emptyRel emptyRel_wf where
  match_states := fun _ ⟨s, v⟩ cfg => cfg = toConfig s v
  init_diagram := fun _ h => h.elim
  init_diagram_backward := fun _ h => h.elim
  final_diagram_forward := fun _ _ _ _ h => h
  final_diagram_backward := fun _ _ _ _ h => h
  step_forward := by
    intro _ ⟨s, v⟩ cfg hmatch ⟨s', v'⟩ hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨htl, rfl⟩ := hstep
    exact ⟨(), Or.inr ⟨toConfig s' v', StepPlus.single _ _ (tl_to_sfc s s' v' htl), rfl⟩⟩
  step_backward := by
    intro _ ⟨s, v⟩ cfg hmatch cfg' hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨s', hact, hval, htl⟩ := sfc_to_tl s v cfg' hstep
    refine ⟨(), Or.inr ⟨⟨s', v⟩, StepPlus.single _ _ ⟨htl, rfl⟩, ?_⟩⟩
    cases cfg'; simp_all [toConfig]

end TrafficLightSimulation

-- ============================================================================
-- Elevator: Simulation Instances
-- ============================================================================

section ElevatorSimulation

-- Inductive operational semantics as an LTS over (ElevState × Valuation)
local instance elevIndLTS : LTS (ElevState × Valuation) where
  init := fun _ => False
  final := fun _ => False
  step := fun ⟨s, v⟩ ⟨s', v'⟩ => ElevStep s v s' ∧ v' = v

-- SFC engine as an LTS over Config (elevator specific)
local instance elevSfcLTS : LTS Config where
  init := fun _ => False
  final := fun _ => False
  step := fun cfg cfg' => SFCStep elevatorSFC cfg cfg'

-- Full bisimulation with shared match relation
def elevBisimulation :
    Bisimulation (ElevState × Valuation) Config Unit emptyRel emptyRel_wf where
  match_states := fun _ ⟨s, v⟩ cfg => cfg = toElevConfig s v
  init_diagram := fun _ h => h.elim
  init_diagram_backward := fun _ h => h.elim
  final_diagram_forward := fun _ _ _ _ h => h
  final_diagram_backward := fun _ _ _ _ h => h
  step_forward := by
    intro _ ⟨s, v⟩ cfg hmatch ⟨s', v'⟩ hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨hel, rfl⟩ := hstep
    exact ⟨(), Or.inr ⟨toElevConfig s' v', StepPlus.single _ _ (elev_to_sfc s s' v' hel), rfl⟩⟩
  step_backward := by
    intro _ ⟨s, v⟩ cfg hmatch cfg' hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨s', hact, hval, hel⟩ := sfc_to_elev s v cfg' hstep
    refine ⟨(), Or.inr ⟨⟨s', v⟩, StepPlus.single _ _ ⟨hel, rfl⟩, ?_⟩⟩
    cases cfg'; simp_all [toElevConfig]

end ElevatorSimulation

-- ============================================================================
-- Parallel SFC: Simulation Instances
--
-- AND-divergence/convergence: S1 → {S2, S3} → S4
-- This requires the general Simulation framework because the intermediate
-- configuration {S2, S3} has multiple active steps — SFCBisimulation's
-- `toId : S → StepId` cannot represent this.
--
-- SFC Diagram:
--          [S2]
--         /    \
--  [S1] --      -- [S4]
--         \    /
--          [S3]
-- ============================================================================

-- Inductive state type representing reachable configurations
inductive ParState where
  | Initial  -- active = ["S1"]
  | Forked   -- active = ["S2", "S3"]
  | Joined   -- active = ["S4"]
deriving DecidableEq, Repr

open ParState

-- Map to active step lists (not single IDs — the whole point)
def ParState.toActive : ParState → ActiveSteps
  | Initial => ["S1"]
  | Forked  => ["S2", "S3"]
  | Joined  => ["S4"]

def toParConfig (s : ParState) (v : Valuation) : Config :=
  { active := s.toActive, valuation := v }

--     true
--   ─────────────── (Fork)
--   {S1} → {S2, S3}
--
--     true
--   ─────────────── (Join)
--   {S2, S3} → {S4}
inductive ParStep : ParState → ParState → Prop where
  | fork : ParStep Initial Forked
  | join : ParStep Forked Joined

-- Properties

theorem parStep_deterministic : ∀ s s1 s2,
    ParStep s s1 → ParStep s s2 → s1 = s2 := by
  intro s s1 s2 H1 H2
  cases H1 <;> cases H2 <;> rfl

-- Forward: ParStep → SFCStep

theorem par_to_sfc (s s' : ParState) (v : Valuation) :
    ParStep s s' →
    SFCStep Examples.parallelSFC (toParConfig s v) (toParConfig s' v) := by
  intro H
  cases H with
  | fork =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S2", "S3"], guard := .True })
    · simp [Examples.parallelSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toParConfig, ParState.toActive]
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toParConfig, ParState.toActive]
    · rfl
  | join =>
    apply SFCStep.fireTransition
      (t := { sources := ["S2", "S3"], targets := ["S4"], guard := .True })
    · simp [Examples.parallelSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toParConfig, ParState.toActive]
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toParConfig, ParState.toActive]
    · rfl

-- Backward: SFCStep → ParStep

theorem sfc_to_par (s : ParState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.parallelSFC (toParConfig s v) cfg' →
    ∃ s', cfg'.active = s'.toActive ∧ cfg'.valuation = v ∧ ParStep s s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen _ Hact Hval
    simp [Examples.parallelSFC] at Hin
    rcases Hin with rfl | rfl
    · -- Fork transition: sources = ["S1"], targets = ["S2", "S3"]
      cases s with
      | Initial =>
        refine ⟨Forked, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toParConfig, ParState.toActive] at Hact
          exact Hact
        · simp [toParConfig] at Hval; exact Hval
        · exact ParStep.fork
      | Forked =>
        simp [Transition.enabled, allActive, isActive, toParConfig, ParState.toActive] at Hen
      | Joined =>
        simp [Transition.enabled, allActive, isActive, toParConfig, ParState.toActive] at Hen
    · -- Join transition: sources = ["S2", "S3"], targets = ["S4"]
      cases s with
      | Initial =>
        simp [Transition.enabled, allActive, isActive, toParConfig, ParState.toActive] at Hen
      | Forked =>
        refine ⟨Joined, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toParConfig, ParState.toActive] at Hact
          exact Hact
        · simp [toParConfig] at Hval; exact Hval
        · exact ParStep.join
      | Joined =>
        simp [Transition.enabled, allActive, isActive, toParConfig, ParState.toActive] at Hen

section ParallelSimulation

-- Inductive semantics as LTS: guards are always True so step doesn't depend on valuation
local instance parIndLTS : LTS (ParState × Valuation) where
  init := fun _ => False
  final := fun _ => False
  step := fun ⟨s, v⟩ ⟨s', v'⟩ => ParStep s s' ∧ v' = v

-- SFC engine as LTS (parallel SFC specific)
local instance parSfcLTS : LTS Config where
  init := fun _ => False
  final := fun _ => False
  step := fun cfg cfg' => SFCStep Examples.parallelSFC cfg cfg'

-- Full bisimulation with shared match relation
def parBisimulation :
    Bisimulation (ParState × Valuation) Config Unit emptyRel emptyRel_wf where
  match_states := fun _ ⟨s, v⟩ cfg => cfg = toParConfig s v
  init_diagram := fun _ h => h.elim
  init_diagram_backward := fun _ h => h.elim
  final_diagram_forward := fun _ _ _ _ h => h
  final_diagram_backward := fun _ _ _ _ h => h
  step_forward := by
    intro _ ⟨s, v⟩ cfg hmatch ⟨s', v'⟩ hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨hpar, rfl⟩ := hstep
    exact ⟨(), Or.inr ⟨toParConfig s' v', StepPlus.single _ _ (par_to_sfc s s' v' hpar), rfl⟩⟩
  step_backward := by
    intro _ ⟨s, v⟩ cfg hmatch cfg' hstep
    simp only at hmatch hstep
    subst hmatch
    obtain ⟨s', hact, hval, hpar⟩ := sfc_to_par s v cfg' hstep
    refine ⟨(), Or.inr ⟨⟨s', v⟩, StepPlus.single _ _ ⟨hpar, rfl⟩, ?_⟩⟩
    cases cfg'; simp_all [toParConfig]

end ParallelSimulation
