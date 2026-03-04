/-
  Traffic Light: Inductive Operational Semantics ↔ SFC Bisimulation

  Two equivalent formulations of a traffic light controller:
  1. Inductive small-step semantics: typed states, one inference rule per transition
  2. Sequential Function Chart: data-driven transition graph with string-keyed states

  The bisimulation proves these describe the same system:
  - Every inductive step has a corresponding SFC step (forward)
  - Every SFC step from a valid config has a corresponding inductive step (backward)

  SFC Diagram:
  ┌─────────────────────────────────────────────────┐
  │                                                 │
  │   ╔═══════╗    timer ≥ 30    ╔═══════╗         │
  │   ║ Red * ║────────────────▶║ Green ║         │
  │   ╚═══════╝                  ╚═══════╝         │
  │       ▲                          │              │
  │       │                          │ timer ≥ 25   │
  │       │                          ▼              │
  │       │    timer ≥ 5     ╔════════╗            │
  │       └─────────────────║ Yellow ║            │
  │                          ╚════════╝            │
  │                                                 │
  │   * = initial step                              │
  │   All transitions have priority 0 (no OR-branch)│
  └─────────────────────────────────────────────────┘
-/
import SFC.Core

-- ============================================================================
-- Inductive Small-Step Semantics for Traffic Light
-- ============================================================================

-- States as a proper inductive type (not strings)
inductive TLState where
  | Red | Green | Yellow
deriving DecidableEq, Repr

open TLState

-- Map typed state to SFC step identifier
def TLState.toId : TLState → StepId
  | Red => "Red"
  | Green => "Green"
  | Yellow => "Yellow"

-- Each constructor is one inference rule of the operational semantics:
--
--     timer ≥ 30
--   ─────────────────── (RedToGreen)
--   (Red, timer) → (Green, timer)
--
--     timer ≥ 25
--   ─────────────────────── (GreenToYellow)
--   (Green, timer) → (Yellow, timer)
--
--     timer ≥ 5
--   ─────────────────────── (YellowToRed)
--   (Yellow, timer) → (Red, timer)
--
inductive TLStep : TLState → Nat → TLState → Prop where
  | redToGreen    : ∀ t, t ≥ 30 → TLStep Red t Green
  | greenToYellow : ∀ t, t ≥ 25 → TLStep Green t Yellow
  | yellowToRed   : ∀ t, t ≥ 5  → TLStep Yellow t Red

-- Reflexive transitive closure
inductive TLStepStar : TLState → Nat → TLState → Prop where
  | refl : ∀ s t, TLStepStar s t s
  | step : ∀ s1 t s2 s3,
      TLStep s1 t s2 → TLStepStar s2 t s3 → TLStepStar s1 t s3

-- ============================================================================
-- Properties of the Inductive Semantics
-- ============================================================================

-- Determinism: at most one successor from any (state, timer) pair
theorem tlStep_deterministic : ∀ s t s1 s2,
    TLStep s t s1 → TLStep s t s2 → s1 = s2 := by
  intro s t s1 s2 H1 H2
  cases H1 <;> cases H2 <;> rfl

-- Progress: every state has a timer threshold above which it can step
theorem tlStep_progress : ∀ s,
    ∃ threshold, ∀ t, t ≥ threshold → ∃ s', TLStep s t s' := by
  intro s
  cases s with
  | Red => exact ⟨30, fun t ht => ⟨Green, TLStep.redToGreen t ht⟩⟩
  | Green => exact ⟨25, fun t ht => ⟨Yellow, TLStep.greenToYellow t ht⟩⟩
  | Yellow => exact ⟨5, fun t ht => ⟨Red, TLStep.yellowToRed t ht⟩⟩

-- A full cycle: Red → Green → Yellow → Red (at timer = 30)
theorem tlStep_full_cycle : TLStepStar Red 30 Red := by
  apply TLStepStar.step _ _ Green
  · exact TLStep.redToGreen 30 (by omega)
  apply TLStepStar.step _ _ Yellow
  · exact TLStep.greenToYellow 30 (by omega)
  apply TLStepStar.step _ _ Red
  · exact TLStep.yellowToRed 30 (by omega)
  exact TLStepStar.refl _ _

-- ============================================================================
-- Configuration Correspondence
-- ============================================================================

-- Convert (TLState, Valuation) to SFC Config
def toConfig (s : TLState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- ============================================================================
-- Forward Direction: TLStep → SFCStep
-- Every step in the inductive semantics has a corresponding SFC step
-- ============================================================================

theorem tl_to_sfc (s s' : TLState) (v : Valuation) :
    TLStep s (v "timer") s' →
    SFCStep Examples.trafficLightSFC (toConfig s v) (toConfig s' v) := by
  intro H
  cases H with
  | redToGreen t Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["Red"], targets := ["Green"], guard := .Ge "timer" 30 })
    · -- t ∈ transitions
      simp [Examples.trafficLightSFC]
    · -- t.enabled cfg = true
      simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId]
      omega
    · -- priority (all transitions have priority 0, so 0 ≤ _ trivially)
      intro _ _ _ _; simp
    · -- cfg'.active = fireTransition ...
      simp [fireTransition, activate, deactivate, toConfig, TLState.toId]
    · -- cfg'.valuation preserved
      rfl
  | greenToYellow t Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["Green"], targets := ["Yellow"], guard := .Ge "timer" 25 })
    · simp [Examples.trafficLightSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toConfig, TLState.toId]
    · rfl
  | yellowToRed t Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["Yellow"], targets := ["Red"], guard := .Ge "timer" 5 })
    · simp [Examples.trafficLightSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toConfig, TLState.toId]
    · rfl

-- ============================================================================
-- Backward Direction: SFCStep → TLStep
-- Every SFC step from a valid traffic light config corresponds to an inductive step
-- ============================================================================

theorem sfc_to_tl (s : TLState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.trafficLightSFC (toConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ TLStep s (v "timer") s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen _ Hact Hval
    -- Enumerate which transition t is
    simp [Examples.trafficLightSFC] at Hin
    rcases Hin with rfl | rfl | rfl
    · -- t = Red → Green transition
      cases s with
      | Red =>
        refine ⟨Green, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toConfig, TLState.toId] at Hact
          exact Hact
        · simp [toConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId] at Hen
          exact TLStep.redToGreen _ (by omega)
      | Green =>
        -- sources = ["Red"] but active = ["Green"] → contradiction
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
      | Yellow =>
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
    · -- t = Green → Yellow transition
      cases s with
      | Red =>
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
      | Green =>
        refine ⟨Yellow, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toConfig, TLState.toId] at Hact
          exact Hact
        · simp [toConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId] at Hen
          exact TLStep.greenToYellow _ (by omega)
      | Yellow =>
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
    · -- t = Yellow → Red transition
      cases s with
      | Red =>
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
      | Green =>
        simp [Transition.enabled, allActive, isActive, toConfig, TLState.toId] at Hen
      | Yellow =>
        refine ⟨Red, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toConfig, TLState.toId] at Hact
          exact Hact
        · simp [toConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval, toConfig, TLState.toId] at Hen
          exact TLStep.yellowToRed _ (by omega)

-- ============================================================================
-- Lift to Multi-Step: TLStepStar → SFCStepStar
-- ============================================================================

theorem tl_to_sfc_star (s s' : TLState) (v : Valuation) :
    TLStepStar s (v "timer") s' →
    SFCStepStar Examples.trafficLightSFC (toConfig s v) (toConfig s' v) := by
  intro H
  generalize ht : v "timer" = k at H
  induction H with
  | refl _ _ => exact SFCStepStar.refl _
  | step s1 _ s2 s3 Hstep _ ih =>
    subst ht
    exact SFCStepStar.step _ _ _ (tl_to_sfc s1 s2 v Hstep) (ih rfl)

-- ============================================================================
-- Lift Backward: SFCStepStar from valid config stays valid
-- ============================================================================

-- SFC steps preserve the "single active step" shape
theorem sfc_step_preserves_shape (s : TLState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.trafficLightSFC (toConfig s v) cfg' →
    ∃ s', cfg' = toConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := sfc_to_tl s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toConfig]⟩

-- ============================================================================
-- Bisimulation Instance
-- ============================================================================

def trafficLightBisim : SFCBisimulation TLState where
  sfc := Examples.trafficLightSFC
  toId := TLState.toId
  step := fun s v s' => TLStep s (v "timer") s'
  forward := tl_to_sfc
  backward := sfc_to_tl
