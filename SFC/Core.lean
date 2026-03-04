/-
  Sequential Function Charts (SFC) Formal Semantics
  Based on IEC 61131-3 standard for PLC programming

  SFCs model discrete event control systems with:
  - Steps: Named states in the control flow
  - Transitions: Guarded edges between steps
  - Parallel branching (AND): Fork/join for concurrent execution
  - Alternative branching (OR): Priority-based selection
-/

-- ============================================================================
-- Core Types
-- ============================================================================

-- Step identifiers
abbrev StepId := String

-- Variables for guards
abbrev Var := String

-- Valuation maps variables to natural numbers
abbrev Valuation := Var -> Nat

-- Empty valuation (all variables default to 0)
def emptyValuation : Valuation := fun _ => 0

-- Update a valuation with a new binding
def Valuation.update (v : Valuation) (x : Var) (n : Nat) : Valuation :=
  fun y => if y = x then n else v y

notation:max v "[" x " |-> " n "]" => Valuation.update v x n

-- ============================================================================
-- Guard Expressions (Boolean conditions for transitions)
-- ============================================================================

inductive Guard where
  | True : Guard                          -- Always true
  | False : Guard                         -- Always false
  | Var : Var -> Guard                    -- Variable (nonzero = true)
  | Not : Guard -> Guard                  -- Negation
  | And : Guard -> Guard -> Guard         -- Conjunction
  | Or : Guard -> Guard -> Guard          -- Disjunction
  | Lt : Var -> Nat -> Guard              -- x < n
  | Le : Var -> Nat -> Guard              -- x <= n
  | Gt : Var -> Nat -> Guard              -- x > n
  | Ge : Var -> Nat -> Guard              -- x >= n
  | Eq : Var -> Nat -> Guard              -- x == n
deriving Repr, DecidableEq

namespace Guard

-- Evaluate a guard expression
def eval (g : Guard) (v : Valuation) : Bool :=
  match g with
  | True => true
  | False => false
  | Var x => v x != 0
  | Not g => !g.eval v
  | And g1 g2 => g1.eval v && g2.eval v
  | Or g1 g2 => g1.eval v || g2.eval v
  | Lt x n => v x < n
  | Le x n => v x <= n
  | Gt x n => v x > n
  | Ge x n => v x >= n
  | Eq x n => v x == n

end Guard

-- ============================================================================
-- SFC Structure
-- ============================================================================

-- A step in the SFC
structure Step where
  id : StepId
  isInitial : Bool := false
deriving Repr, DecidableEq

-- A transition connects source steps to target steps with a guard
-- - sources.length > 1 indicates AND-convergence (synchronization)
-- - targets.length > 1 indicates AND-divergence (fork)
-- - Multiple transitions with same source but different guards = OR-branching
structure Transition where
  sources : List StepId
  targets : List StepId
  guard : Guard
  priority : Nat := 0    -- Lower = higher priority (for OR-branch resolution)
deriving Repr, DecidableEq

-- An SFC is a collection of steps and transitions
structure SFC where
  steps : List Step
  transitions : List Transition
deriving Repr, DecidableEq

-- ============================================================================
-- Configuration (Runtime State)
-- ============================================================================

-- Set of currently active step IDs
abbrev ActiveSteps := List StepId

-- Configuration: active steps + variable valuation
structure Config where
  active : ActiveSteps
  valuation : Valuation

-- ============================================================================
-- Helper Functions
-- ============================================================================

-- Check if a step ID is in the active set
def isActive (s : StepId) (active : ActiveSteps) : Bool :=
  active.contains s

-- Check if all source steps are active
def allActive (sources : List StepId) (active : ActiveSteps) : Bool :=
  sources.all (isActive · active)

-- Remove steps from active set
def deactivate (active : ActiveSteps) (steps : List StepId) : ActiveSteps :=
  active.filter (fun s => !steps.contains s)

-- Add steps to active set (avoiding duplicates)
def activate (active : ActiveSteps) (steps : List StepId) : ActiveSteps :=
  active ++ steps.filter (fun s => !active.contains s)

-- Fire a transition: deactivate sources, activate targets
def fireTransition (active : ActiveSteps) (t : Transition) : ActiveSteps :=
  activate (deactivate active t.sources) t.targets

-- Check if a transition is enabled
def Transition.enabled (t : Transition) (cfg : Config) : Bool :=
  allActive t.sources cfg.active && t.guard.eval cfg.valuation

-- Get all enabled transitions
def SFC.enabledTransitions (sfc : SFC) (cfg : Config) : List Transition :=
  sfc.transitions.filter (·.enabled cfg)

-- Get the initial configuration for an SFC
def SFC.initialConfig (sfc : SFC) (v : Valuation) : Config :=
  let initSteps := sfc.steps.filter (·.isInitial) |>.map (·.id)
  { active := initSteps, valuation := v }

-- ============================================================================
-- Well-Formedness
-- ============================================================================

-- Well-formed SFC predicate
def SFC.WellFormed (sfc : SFC) : Prop :=
  -- At least one initial step
  (sfc.steps.filter (·.isInitial)).length >= 1 ∧
  -- All transition sources reference existing steps
  (∀ t ∈ sfc.transitions, ∀ s ∈ t.sources, ∃ step ∈ sfc.steps, step.id = s) ∧
  -- All transition targets reference existing steps
  (∀ t ∈ sfc.transitions, ∀ s ∈ t.targets, ∃ step ∈ sfc.steps, step.id = s) ∧
  -- No empty transitions
  (∀ t ∈ sfc.transitions, t.sources.length > 0 ∧ t.targets.length > 0)

-- ============================================================================
-- Small-Step Semantics
-- ============================================================================

-- Small-step: fire one enabled transition
-- Priority ensures determinism for OR-branches (same sources, different guards)
inductive SFCStep (sfc : SFC) : Config -> Config -> Prop where
  | fireTransition : ∀ cfg t cfg',
      -- Transition is in the SFC
      t ∈ sfc.transitions →
      -- Transition is enabled (sources active, guard true)
      t.enabled cfg = true →
      -- This transition has highest priority among enabled transitions with same sources
      (∀ t' ∈ sfc.transitions,
        t'.sources = t.sources →
        t'.enabled cfg = true →
        t.priority ≤ t'.priority) →
      -- New configuration: fire the transition
      cfg'.active = fireTransition cfg.active t →
      cfg'.valuation = cfg.valuation →
      SFCStep sfc cfg cfg'

-- Reflexive transitive closure of small-step
inductive SFCStepStar (sfc : SFC) : Config -> Config -> Prop where
  | refl : ∀ cfg, SFCStepStar sfc cfg cfg
  | step : ∀ cfg1 cfg2 cfg3,
      SFCStep sfc cfg1 cfg2 →
      SFCStepStar sfc cfg2 cfg3 →
      SFCStepStar sfc cfg1 cfg3

-- Notation for small-step
infix:50 " =[" => fun cfg sfc => SFCStep sfc cfg
notation:50 cfg1 " =[" sfc "]=>" cfg2 => SFCStep sfc cfg1 cfg2
notation:50 cfg1 " =[" sfc "]*=>" cfg2 => SFCStepStar sfc cfg1 cfg2

-- ============================================================================
-- Big-Step Semantics
-- ============================================================================

-- A configuration is stable if no transitions are enabled
def Config.stable (sfc : SFC) (cfg : Config) : Prop :=
  ∀ t ∈ sfc.transitions, t.enabled cfg = false

-- Decidable stability check
def Config.isStable (sfc : SFC) (cfg : Config) : Bool :=
  sfc.transitions.all (fun t => !t.enabled cfg)

-- Big-step: run until stable (no enabled transitions)
inductive SFCEval (sfc : SFC) : Config -> Config -> Prop where
  | done : ∀ cfg,
      cfg.stable sfc →
      SFCEval sfc cfg cfg
  | step : ∀ cfg1 cfg2 cfg3,
      SFCStep sfc cfg1 cfg2 →
      SFCEval sfc cfg2 cfg3 →
      SFCEval sfc cfg1 cfg3

-- Notation for big-step
notation:10 cfg1 " ⟹[" sfc "]" cfg2 => SFCEval sfc cfg1 cfg2

-- ============================================================================
-- Example SFCs
-- ============================================================================

namespace Examples

-- Example 1: Simple Sequential SFC
-- [S1*] --[x > 0]--> [S2] --[true]--> [S3]
def sequentialSFC : SFC := {
  steps := [
    { id := "S1", isInitial := true },
    { id := "S2" },
    { id := "S3" }
  ],
  transitions := [
    { sources := ["S1"], targets := ["S2"], guard := .Gt "x" 0 },
    { sources := ["S2"], targets := ["S3"], guard := .True }
  ]
}

-- Example 2: Parallel Branching (AND-divergence and AND-convergence)
--         [S2]
--        /    \
-- [S1] --      -- [S4]
--        \    /
--         [S3]
def parallelSFC : SFC := {
  steps := [
    { id := "S1", isInitial := true },
    { id := "S2" },
    { id := "S3" },
    { id := "S4" }
  ],
  transitions := [
    -- AND-divergence: S1 -> {S2, S3}
    { sources := ["S1"], targets := ["S2", "S3"], guard := .True },
    -- AND-convergence: {S2, S3} -> S4
    { sources := ["S2", "S3"], targets := ["S4"], guard := .True }
  ]
}

-- Example 3: Alternative Branching (OR-selection with priority)
--        --[x > 5]--> [S2]
--       /
-- [S1] -
--       \
--        --[true]--> [S3]  (lower priority fallback)
def alternativeSFC : SFC := {
  steps := [
    { id := "S1", isInitial := true },
    { id := "S2" },
    { id := "S3" }
  ],
  transitions := [
    -- High priority: x > 5 goes to S2
    { sources := ["S1"], targets := ["S2"], guard := .Gt "x" 5, priority := 0 },
    -- Low priority fallback: goes to S3
    { sources := ["S1"], targets := ["S3"], guard := .True, priority := 1 }
  ]
}

-- Example 4: Loop (cycle back to same step)
-- [S1*] --[x < 10]--> [S1]  (self-loop, lower priority)
--       --[x >= 10]--> [S2] (exit, higher priority)
def loopSFC : SFC := {
  steps := [
    { id := "S1", isInitial := true },
    { id := "S2" }
  ],
  transitions := [
    -- Exit condition (higher priority)
    { sources := ["S1"], targets := ["S2"], guard := .Ge "x" 10, priority := 0 },
    -- Continue looping (lower priority)
    { sources := ["S1"], targets := ["S1"], guard := .Lt "x" 10, priority := 1 }
  ]
}

-- Example 5: Traffic Light Controller
-- [Red*] --[timer >= 30]--> [Green] --[timer >= 25]--> [Yellow] --[timer >= 5]--> [Red]
def trafficLightSFC : SFC := {
  steps := [
    { id := "Red", isInitial := true },
    { id := "Green" },
    { id := "Yellow" }
  ],
  transitions := [
    { sources := ["Red"], targets := ["Green"], guard := .Ge "timer" 30 },
    { sources := ["Green"], targets := ["Yellow"], guard := .Ge "timer" 25 },
    { sources := ["Yellow"], targets := ["Red"], guard := .Ge "timer" 5 }
  ]
}

end Examples

-- ============================================================================
-- Basic Theorems
-- ============================================================================

-- Transitivity of SFCStepStar
theorem sfcStepStar_trans (sfc : SFC) :
    ∀ cfg1 cfg2 cfg3,
    SFCStepStar sfc cfg1 cfg2 →
    SFCStepStar sfc cfg2 cfg3 →
    SFCStepStar sfc cfg1 cfg3 := by
  intro cfg1 cfg2 cfg3 H12 H23
  induction H12 with
  | refl => exact H23
  | step c1 c2 _ Hstep _ ih => exact SFCStepStar.step c1 c2 cfg3 Hstep (ih H23)

-- Small-step determinism (with priority)
-- Note: Full determinism requires showing that priority ordering yields a unique transition
-- when multiple transitions have the same sources. This is left as sorry for now.
theorem sfcStep_deterministic (sfc : SFC) :
    ∀ cfg cfg1 cfg2,
    SFCStep sfc cfg cfg1 →
    SFCStep sfc cfg cfg2 →
    cfg1 = cfg2 := by
  intro cfg cfg1 cfg2 H1 H2
  cases H1 with
  | fireTransition t1 Hin1 Hen1 Hpri1 Hact1 Hval1 =>
    cases H2 with
    | fireTransition t2 Hin2 Hen2 Hpri2 Hact2 Hval2 =>
      -- Need to show t1 = t2 (or at least they produce the same result)
      -- This requires showing that priority ordering gives a unique choice
      -- when sources match
      sorry

-- Big-step implies small-step star to stable
theorem sfcEval_implies_stepStar (sfc : SFC) :
    ∀ cfg cfg',
    SFCEval sfc cfg cfg' →
    SFCStepStar sfc cfg cfg' ∧ cfg'.stable sfc := by
  intro cfg cfg' Heval
  induction Heval with
  | done c Hstable =>
    constructor
    · exact SFCStepStar.refl c
    · exact Hstable
  | step c1 c2 c3 Hstep _ ih =>
    obtain ⟨Hstar, Hstable⟩ := ih
    constructor
    · exact SFCStepStar.step c1 c2 c3 Hstep Hstar
    · exact Hstable

-- Small-step star to stable implies big-step
theorem sfcStepStar_stable_implies_eval (sfc : SFC) :
    ∀ cfg cfg',
    SFCStepStar sfc cfg cfg' →
    cfg'.stable sfc →
    SFCEval sfc cfg cfg' := by
  intro cfg cfg' Hstar Hstable
  induction Hstar with
  | refl c => exact SFCEval.done c Hstable
  | step c1 c2 c3 Hstep _ ih =>
    exact SFCEval.step c1 c2 c3 Hstep (ih Hstable)

-- Big-step determinism (follows from small-step determinism)
theorem sfcEval_deterministic (sfc : SFC) :
    ∀ cfg cfg1 cfg2,
    SFCEval sfc cfg cfg1 →
    SFCEval sfc cfg cfg2 →
    cfg1 = cfg2 := by
  intro cfg cfg1 cfg2 H1 H2
  -- Follows from small-step determinism
  sorry

-- ============================================================================
-- Bisimulation Structure
-- ============================================================================

-- A bisimulation between an inductive small-step semantics (over state type S)
-- and an SFC. Bundles the forward and backward simulation proofs.
structure SFCBisimulation (S : Type) where
  sfc : SFC
  toId : S → StepId
  step : S → Valuation → S → Prop
  forward : ∀ s s' v, step s v s' →
    SFCStep sfc ⟨[toId s], v⟩ ⟨[toId s'], v⟩
  backward : ∀ s v cfg',
    SFCStep sfc ⟨[toId s], v⟩ cfg' →
    ∃ s', cfg'.active = [toId s'] ∧ cfg'.valuation = v ∧ step s v s'

namespace SFCBisimulation

def toConfig (b : SFCBisimulation S) (s : S) (v : Valuation) : Config :=
  ⟨[b.toId s], v⟩

-- Shape preservation: SFC steps preserve the single-active-step invariant
theorem preserves_shape (b : SFCBisimulation S)
    (s : S) (v : Valuation) (cfg' : Config) :
    SFCStep b.sfc (b.toConfig s v) cfg' →
    ∃ s', cfg' = b.toConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := b.backward s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toConfig]⟩

-- If the inductive step relation is deterministic, the SFC restriction is too
theorem deterministic (b : SFCBisimulation S)
    (hdet : ∀ s v s1 s2, b.step s v s1 → b.step s v s2 → s1 = s2)
    (s : S) (v : Valuation) (cfg1 cfg2 : Config) :
    SFCStep b.sfc (b.toConfig s v) cfg1 →
    SFCStep b.sfc (b.toConfig s v) cfg2 →
    cfg1 = cfg2 := by
  intro H1 H2
  obtain ⟨s1, Hact1, Hval1, Hstep1⟩ := b.backward s v cfg1 H1
  obtain ⟨s2, Hact2, Hval2, Hstep2⟩ := b.backward s v cfg2 H2
  have := hdet s v s1 s2 Hstep1 Hstep2
  subst this
  cases cfg1; cases cfg2; simp_all [toConfig]

end SFCBisimulation

-- ============================================================================
-- Execution Proofs for Examples
-- ============================================================================

namespace Examples

-- Helper: the first transition in sequentialSFC
def seqT1 : Transition := { sources := ["S1"], targets := ["S2"], guard := .Gt "x" 0 }

-- Prove sequential SFC takes one step from initial config with x > 0
theorem sequential_step (v : Valuation) (Hx : v "x" > 0) :
    SFCStep sequentialSFC
      (sequentialSFC.initialConfig v)
      { active := ["S2"], valuation := v } := by
  apply SFCStep.fireTransition (t := seqT1)
  · -- t ∈ sfc.transitions
    simp [sequentialSFC, seqT1]
  · -- t.enabled cfg = true
    simp [Transition.enabled, allActive, isActive, SFC.initialConfig,
          sequentialSFC, Guard.eval, seqT1]
    omega
  · -- priority condition
    intro t' Hin Hsrc Hen
    simp [sequentialSFC, seqT1] at Hin Hsrc
    cases Hin with
    | inl h => simp [h, seqT1]
    | inr h => simp [h] at Hsrc
  · -- cfg'.active = fireTransition ...
    simp [fireTransition, activate, deactivate, SFC.initialConfig,
          sequentialSFC, seqT1]
  · -- cfg'.valuation = cfg.valuation
    rfl

-- Helper: the first transition in parallelSFC
def parT1 : Transition := { sources := ["S1"], targets := ["S2", "S3"], guard := .True }

-- Prove parallel SFC fork: S1 -> {S2, S3}
theorem parallel_fork :
    SFCStep parallelSFC
      (parallelSFC.initialConfig emptyValuation)
      { active := ["S2", "S3"], valuation := emptyValuation } := by
  apply SFCStep.fireTransition (t := parT1)
  · simp [parallelSFC, parT1]
  · simp [Transition.enabled, allActive, isActive, SFC.initialConfig,
          parallelSFC, Guard.eval, parT1]
  · intro t' Hin Hsrc Hen
    simp [parallelSFC, parT1] at Hin Hsrc
    cases Hin with
    | inl h => simp [h, parT1]
    | inr h => simp [h] at Hsrc
  · simp [fireTransition, activate, deactivate, SFC.initialConfig, parallelSFC, parT1]
  · rfl

-- Prove parallel SFC join: {S2, S3} -> S4
def parT2 : Transition := { sources := ["S2", "S3"], targets := ["S4"], guard := .True }

theorem parallel_join :
    SFCStep parallelSFC
      { active := ["S2", "S3"], valuation := emptyValuation }
      { active := ["S4"], valuation := emptyValuation } := by
  apply SFCStep.fireTransition (t := parT2)
  · simp [parallelSFC, parT2]
  · simp [Transition.enabled, allActive, isActive, Guard.eval, parT2]
  · intro t' Hin Hsrc Hen
    simp [parallelSFC, parT2] at Hin Hsrc
    cases Hin with
    | inl h => simp [h] at Hsrc
    | inr h => simp [h, parT2]
  · simp [fireTransition, activate, deactivate, parT2]
  · rfl

-- Prove alternative SFC with x > 5 goes to S2
def altT1 : Transition := { sources := ["S1"], targets := ["S2"], guard := .Gt "x" 5, priority := 0 }

theorem alternative_high_priority (v : Valuation) (Hx : v "x" > 5) :
    SFCStep alternativeSFC
      (alternativeSFC.initialConfig v)
      { active := ["S2"], valuation := v } := by
  apply SFCStep.fireTransition (t := altT1)
  · simp [alternativeSFC, altT1]
  · simp [Transition.enabled, allActive, isActive, SFC.initialConfig,
          alternativeSFC, Guard.eval, altT1]
    omega
  · intro t' Hin Hsrc Hen
    simp [alternativeSFC, altT1] at Hin Hsrc
    cases Hin with
    | inl h => simp [h, altT1]
    | inr h => simp [h, altT1]
  · simp [fireTransition, activate, deactivate, SFC.initialConfig,
          alternativeSFC, altT1]
  · rfl

-- ============================================================================
-- Interesting Theorems: Complete Execution Traces
-- ============================================================================

-- Prove that S4 is a stable state in parallelSFC (no transitions can fire)
theorem parallel_s4_stable :
    Config.stable parallelSFC { active := ["S4"], valuation := emptyValuation } := by
  intro t Ht
  simp [parallelSFC] at Ht
  cases Ht with
  | inl h =>
    -- First transition: sources = ["S1"]
    simp [h, Transition.enabled, allActive, isActive]
  | inr h =>
    -- Second transition: sources = ["S2", "S3"]
    simp [h, Transition.enabled, allActive, isActive]

-- Complete execution of parallel SFC: S1 -> {S2, S3} -> S4 (big-step)
theorem parallel_full_execution :
    SFCEval parallelSFC
      (parallelSFC.initialConfig emptyValuation)
      { active := ["S4"], valuation := emptyValuation } := by
  -- First step: S1 -> {S2, S3}
  apply SFCEval.step
  · exact parallel_fork
  -- Second step: {S2, S3} -> S4
  apply SFCEval.step
  · exact parallel_join
  -- Now stable
  apply SFCEval.done
  exact parallel_s4_stable

-- Prove the parallel SFC reaches S4 via small-step star
theorem parallel_reaches_s4 :
    SFCStepStar parallelSFC
      (parallelSFC.initialConfig emptyValuation)
      { active := ["S4"], valuation := emptyValuation } := by
  -- Use the equivalence theorem
  have h := sfcEval_implies_stepStar parallelSFC _ _ parallel_full_execution
  exact h.1

-- Sequential SFC: S3 is stable
theorem sequential_s3_stable :
    Config.stable sequentialSFC { active := ["S3"], valuation := emptyValuation } := by
  intro t Ht
  simp [sequentialSFC] at Ht
  cases Ht with
  | inl h => simp [h, Transition.enabled, allActive, isActive]
  | inr h => simp [h, Transition.enabled, allActive, isActive]

-- Sequential SFC second step: S2 -> S3
def seqT2 : Transition := { sources := ["S2"], targets := ["S3"], guard := .True }

theorem sequential_step2 :
    SFCStep sequentialSFC
      { active := ["S2"], valuation := emptyValuation }
      { active := ["S3"], valuation := emptyValuation } := by
  apply SFCStep.fireTransition (t := seqT2)
  · simp [sequentialSFC, seqT2]
  · simp [Transition.enabled, allActive, isActive, Guard.eval, seqT2]
  · intro t' Hin Hsrc Hen
    simp [sequentialSFC, seqT2] at Hin Hsrc
    cases Hin with
    | inl h => simp [h] at Hsrc
    | inr h => simp [h, seqT2]
  · simp [fireTransition, activate, deactivate, seqT2]
  · rfl

-- Complete execution of sequential SFC with x > 0: S1 -> S2 -> S3
theorem sequential_full_execution (v : Valuation) (Hx : v "x" > 0) :
    SFCEval sequentialSFC
      (sequentialSFC.initialConfig v)
      { active := ["S3"], valuation := v } := by
  -- First step: S1 -> S2
  apply SFCEval.step (cfg2 := { active := ["S2"], valuation := v })
  · exact sequential_step v Hx
  -- Second step: S2 -> S3
  apply SFCEval.step (cfg2 := { active := ["S3"], valuation := v })
  · apply SFCStep.fireTransition (t := seqT2)
    · simp [sequentialSFC, seqT2]
    · simp [Transition.enabled, allActive, isActive, Guard.eval, seqT2]
    · intro t' Hin Hsrc Hen
      simp [sequentialSFC, seqT2] at Hin Hsrc
      cases Hin with
      | inl h => simp [h] at Hsrc
      | inr h => simp [h, seqT2]
    · simp [fireTransition, activate, deactivate, seqT2]
    · rfl
  -- Now stable
  apply SFCEval.done
  intro t Ht
  simp [sequentialSFC] at Ht
  cases Ht with
  | inl h => simp [h, Transition.enabled, allActive, isActive]
  | inr h => simp [h, Transition.enabled, allActive, isActive]

-- Alternative SFC: both S2 and S3 are stable (terminal states)
theorem alternative_s2_stable :
    Config.stable alternativeSFC { active := ["S2"], valuation := emptyValuation } := by
  intro t Ht
  simp [alternativeSFC] at Ht
  rcases Ht with h | h <;> simp [h, Transition.enabled, allActive, isActive]

theorem alternative_s3_stable :
    Config.stable alternativeSFC { active := ["S3"], valuation := emptyValuation } := by
  intro t Ht
  simp [alternativeSFC] at Ht
  rcases Ht with h | h <;> simp [h, Transition.enabled, allActive, isActive]

-- Key property: In alternative SFC, high priority wins
-- When x > 5, we go to S2 (not S3) even though S3's guard is also true
theorem alternative_priority_matters (v : Valuation) (Hx : v "x" > 5) :
    SFCEval alternativeSFC
      (alternativeSFC.initialConfig v)
      { active := ["S2"], valuation := v } := by
  apply SFCEval.step
  · exact alternative_high_priority v Hx
  apply SFCEval.done
  intro t Ht
  simp [alternativeSFC] at Ht
  rcases Ht with h | h <;> simp [h, Transition.enabled, allActive, isActive]

-- Prove that the lower-priority fallback triggers when x <= 5
def altT2 : Transition := { sources := ["S1"], targets := ["S3"], guard := .True, priority := 1 }

theorem alternative_low_priority (v : Valuation) (Hx : v "x" ≤ 5) :
    SFCStep alternativeSFC
      (alternativeSFC.initialConfig v)
      { active := ["S3"], valuation := v } := by
  apply SFCStep.fireTransition (t := altT2)
  · simp [alternativeSFC, altT2]
  · simp [Transition.enabled, allActive, isActive, SFC.initialConfig,
          alternativeSFC, Guard.eval, altT2]
  · intro t' Hin Hsrc Hen
    simp [alternativeSFC, altT2] at Hin Hsrc Hen
    cases Hin with
    | inl h =>
      -- t' is the high-priority transition with guard x > 5
      -- But it's not enabled because x <= 5
      simp [h, Transition.enabled, allActive, isActive, SFC.initialConfig,
            Guard.eval] at Hen
      omega
    | inr h => simp [h, altT2]
  · simp [fireTransition, activate, deactivate, SFC.initialConfig,
          alternativeSFC, altT2]
  · rfl

-- Complete proof: Alternative SFC is deterministic based on condition
-- x > 5 => S2, x <= 5 => S3
theorem alternative_complete (v : Valuation) :
    (v "x" > 5 → SFCEval alternativeSFC (alternativeSFC.initialConfig v) { active := ["S2"], valuation := v }) ∧
    (v "x" ≤ 5 → SFCEval alternativeSFC (alternativeSFC.initialConfig v) { active := ["S3"], valuation := v }) := by
  constructor
  · intro Hx
    exact alternative_priority_matters v Hx
  · intro Hx
    apply SFCEval.step
    · exact alternative_low_priority v Hx
    apply SFCEval.done
    intro t Ht
    simp [alternativeSFC] at Ht
    rcases Ht with h | h <;> simp [h, Transition.enabled, allActive, isActive]

end Examples
