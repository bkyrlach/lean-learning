/-
  Elevator Controller: Inductive Operational Semantics ↔ SFC Bisimulation

  A simplified elevator controller with OR-branching (priority-based):
  - When idle, the elevator prioritizes departing (request ≥ 1, priority 0)
    over staying idle (fallback, priority 1)
  - This exercises the SFC priority mechanism not used by the traffic light

  SFC Diagram:
  ┌──────────────────────────────────────────────────────────┐
  │                                                          │
  │          ┌──────────┐                                    │
  │          │ [True]   │                                    │
  │          │ priority 1 (fallback self-loop)               │
  │          ▼          │                                    │
  │      ╔════════╗─────┘                                    │
  │ ┌───▶║ Idle * ║                                          │
  │ │    ╚════════╝                                          │
  │ │        │                                               │
  │ │        │ [request ≥ 1] priority 0                      │
  │ │        ▼                                               │
  │ │    ╔══════════╗    [timer ≥ 3]    ╔═════════╗         │
  │ │    ║ GoingUp  ║─────────────────▶║ Arrived ║         │
  │ │    ╚══════════╝                   ╚═════════╝         │
  │ │                                       │                │
  │ │                                       │ [timer ≥ 2]    │
  │ │                                       ▼                │
  │ │    [timer ≥ 3]                 ╔═══════════╗          │
  │ └────────────────────────────────║ GoingDown ║          │
  │                                  ╚═══════════╝          │
  │                                                          │
  │   * = initial step                                       │
  │   OR-branch at Idle: priority 0 wins over priority 1    │
  │   when request ≥ 1, otherwise fallback self-loop fires  │
  └──────────────────────────────────────────────────────────┘
-/
import SFC

-- ============================================================================
-- Inductive Small-Step Semantics for Elevator
-- ============================================================================

inductive ElevState where
  | Idle | GoingUp | Arrived | GoingDown
deriving DecidableEq, Repr

open ElevState

def ElevState.toId : ElevState → StepId
  | Idle => "Idle"
  | GoingUp => "GoingUp"
  | Arrived => "Arrived"
  | GoingDown => "GoingDown"

-- Inference rules:
--
--     request ≥ 1
--   ─────────────────── (Depart)
--   (Idle, v) → (GoingUp, v)
--
--     request < 1
--   ─────────────────── (StayIdle)
--   (Idle, v) → (Idle, v)
--
--     timer ≥ 3
--   ─────────────────── (Arrive)
--   (GoingUp, v) → (Arrived, v)
--
--     timer ≥ 2
--   ─────────────────── (DoorClose)
--   (Arrived, v) → (GoingDown, v)
--
--     timer ≥ 3
--   ─────────────────── (ReturnHome)
--   (GoingDown, v) → (Idle, v)
--
inductive ElevStep : ElevState → Valuation → ElevState → Prop where
  | depart     : ∀ v, v "request" ≥ 1 → ElevStep Idle v GoingUp
  | stayIdle   : ∀ v, v "request" < 1 → ElevStep Idle v Idle
  | arrive     : ∀ v, v "timer" ≥ 3   → ElevStep GoingUp v Arrived
  | doorClose  : ∀ v, v "timer" ≥ 2   → ElevStep Arrived v GoingDown
  | returnHome : ∀ v, v "timer" ≥ 3   → ElevStep GoingDown v Idle

inductive ElevStepStar : ElevState → Valuation → ElevState → Prop where
  | refl : ∀ s v, ElevStepStar s v s
  | step : ∀ s1 v s2 s3,
      ElevStep s1 v s2 → ElevStepStar s2 v s3 → ElevStepStar s1 v s3

-- ============================================================================
-- Properties of the Inductive Semantics
-- ============================================================================

theorem elevStep_deterministic : ∀ s v s1 s2,
    ElevStep s v s1 → ElevStep s v s2 → s1 = s2 := by
  intro s v s1 s2 H1 H2
  cases H1 <;> cases H2 <;> first | rfl | omega

theorem elevStep_progress : ∀ s, ∃ (P : Valuation → Prop),
    ∀ v, P v → ∃ s', ElevStep s v s' := by
  intro s
  cases s with
  | Idle => exact ⟨fun _ => True, fun v _ => by
      by_cases h : v "request" ≥ 1
      · exact ⟨GoingUp, ElevStep.depart v h⟩
      · exact ⟨Idle, ElevStep.stayIdle v (by omega)⟩⟩
  | GoingUp => exact ⟨fun v => v "timer" ≥ 3, fun v h => ⟨_, ElevStep.arrive v h⟩⟩
  | Arrived => exact ⟨fun v => v "timer" ≥ 2, fun v h => ⟨_, ElevStep.doorClose v h⟩⟩
  | GoingDown => exact ⟨fun v => v "timer" ≥ 3, fun v h => ⟨_, ElevStep.returnHome v h⟩⟩

-- Idle always has a successor (total): depart or stayIdle covers all cases
theorem elevStep_idle_total : ∀ v, ∃ s', ElevStep Idle v s' := by
  intro v
  by_cases h : v "request" ≥ 1
  · exact ⟨GoingUp, ElevStep.depart v h⟩
  · exact ⟨Idle, ElevStep.stayIdle v (by omega)⟩

-- ============================================================================
-- SFC Definition
-- ============================================================================

def elevatorSFC : SFC := {
  steps := [
    { id := "Idle", isInitial := true },
    { id := "GoingUp" },
    { id := "Arrived" },
    { id := "GoingDown" }
  ],
  transitions := [
    -- OR-branch: depart has higher priority than stayIdle
    { sources := ["Idle"], targets := ["GoingUp"],
      guard := .Ge "request" 1, priority := 0 },
    { sources := ["Idle"], targets := ["Idle"],
      guard := .True, priority := 1 },
    -- Sequential transitions
    { sources := ["GoingUp"], targets := ["Arrived"],
      guard := .Ge "timer" 3 },
    { sources := ["Arrived"], targets := ["GoingDown"],
      guard := .Ge "timer" 2 },
    { sources := ["GoingDown"], targets := ["Idle"],
      guard := .Ge "timer" 3 }
  ]
}

-- ============================================================================
-- Configuration Correspondence
-- ============================================================================

def toElevConfig (s : ElevState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- ============================================================================
-- Forward Direction: ElevStep → SFCStep
-- ============================================================================

theorem elev_to_sfc (s s' : ElevState) (v : Valuation) :
    ElevStep s v s' →
    SFCStep elevatorSFC (toElevConfig s v) (toElevConfig s' v) := by
  intro H
  cases H with
  | depart v Hreq =>
    apply SFCStep.fireTransition
      (t := { sources := ["Idle"], targets := ["GoingUp"],
              guard := .Ge "request" 1, priority := 0 })
    · simp [elevatorSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toElevConfig, ElevState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId]
    · rfl
  | stayIdle v Hreq =>
    apply SFCStep.fireTransition
      (t := { sources := ["Idle"], targets := ["Idle"],
              guard := .True, priority := 1 })
    · simp [elevatorSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toElevConfig, ElevState.toId]
    · -- Priority: must show depart transition (priority 0) is NOT enabled
      intro t' Hin Hsrc Hen
      simp [elevatorSFC] at Hin
      rcases Hin with rfl | rfl | rfl | rfl | rfl
      · -- depart transition: sources match, but guard is false (request < 1)
        simp [Transition.enabled, allActive, isActive, Guard.eval,
              toElevConfig, ElevState.toId] at Hen
        omega
      · simp  -- self (same transition)
      · simp at Hsrc  -- sources don't match
      · simp at Hsrc
      · simp at Hsrc
    · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId]
    · rfl
  | arrive v Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["GoingUp"], targets := ["Arrived"],
              guard := .Ge "timer" 3 })
    · simp [elevatorSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toElevConfig, ElevState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId]
    · rfl
  | doorClose v Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["Arrived"], targets := ["GoingDown"],
              guard := .Ge "timer" 2 })
    · simp [elevatorSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toElevConfig, ElevState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId]
    · rfl
  | returnHome v Ht =>
    apply SFCStep.fireTransition
      (t := { sources := ["GoingDown"], targets := ["Idle"],
              guard := .Ge "timer" 3 })
    · simp [elevatorSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toElevConfig, ElevState.toId]
      omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId]
    · rfl

-- ============================================================================
-- Backward Direction: SFCStep → ElevStep
-- ============================================================================

theorem sfc_to_elev (s : ElevState) (v : Valuation) (cfg' : Config) :
    SFCStep elevatorSFC (toElevConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ ElevStep s v s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen Hpri Hact Hval
    simp [elevatorSFC] at Hin
    rcases Hin with rfl | rfl | rfl | rfl | rfl
    · -- Depart transition: Idle → GoingUp (request ≥ 1)
      cases s with
      | Idle =>
        refine ⟨GoingUp, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId] at Hact
          exact Hact
        · simp [toElevConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toElevConfig, ElevState.toId] at Hen
          exact ElevStep.depart v (by omega)
      | GoingUp =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | Arrived =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingDown =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
    · -- StayIdle transition: Idle → Idle (priority 1, fallback)
      cases s with
      | Idle =>
        refine ⟨Idle, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId] at Hact
          exact Hact
        · simp [toElevConfig] at Hval; exact Hval
        · -- Key: derive request < 1 from priority constraint
          -- Hpri says: for all enabled transitions with same sources, our priority (1) ≤ theirs
          -- The depart transition has priority 0 and same sources ["Idle"]
          -- If depart were enabled, we'd need 1 ≤ 0 (false)
          -- So depart must be disabled → its guard (request ≥ 1) is false → request < 1
          have Hnotdepart := Hpri
            { sources := ["Idle"], targets := ["GoingUp"],
              guard := .Ge "request" 1, priority := 0 }
            (by simp [elevatorSFC])
            (by simp)
          simp [Transition.enabled, allActive, isActive, Guard.eval,
                toElevConfig, ElevState.toId] at Hnotdepart
          exact ElevStep.stayIdle v (by omega)
      | GoingUp =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | Arrived =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingDown =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
    · -- Arrive transition: GoingUp → Arrived
      cases s with
      | GoingUp =>
        refine ⟨Arrived, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId] at Hact
          exact Hact
        · simp [toElevConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toElevConfig, ElevState.toId] at Hen
          exact ElevStep.arrive v (by omega)
      | Idle =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | Arrived =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingDown =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
    · -- DoorClose transition: Arrived → GoingDown
      cases s with
      | Arrived =>
        refine ⟨GoingDown, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId] at Hact
          exact Hact
        · simp [toElevConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toElevConfig, ElevState.toId] at Hen
          exact ElevStep.doorClose v (by omega)
      | Idle =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingUp =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingDown =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
    · -- ReturnHome transition: GoingDown → Idle
      cases s with
      | GoingDown =>
        refine ⟨Idle, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toElevConfig, ElevState.toId] at Hact
          exact Hact
        · simp [toElevConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toElevConfig, ElevState.toId] at Hen
          exact ElevStep.returnHome v (by omega)
      | Idle =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | GoingUp =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen
      | Arrived =>
        simp [Transition.enabled, allActive, isActive, toElevConfig, ElevState.toId] at Hen

-- ============================================================================
-- Lift to Multi-Step: ElevStepStar → SFCStepStar
-- ============================================================================

theorem elev_to_sfc_star (s s' : ElevState) (v : Valuation) :
    ElevStepStar s v s' →
    SFCStepStar elevatorSFC (toElevConfig s v) (toElevConfig s' v) := by
  intro H
  generalize hv : v = v' at H
  induction H with
  | refl _ _ => exact SFCStepStar.refl _
  | step s1 _ s2 s3 Hstep _ ih =>
    subst hv
    exact SFCStepStar.step _ _ _ (elev_to_sfc s1 s2 v Hstep) (ih rfl)

-- ============================================================================
-- Shape Preservation
-- ============================================================================

theorem sfc_elev_preserves_shape (s : ElevState) (v : Valuation) (cfg' : Config) :
    SFCStep elevatorSFC (toElevConfig s v) cfg' →
    ∃ s', cfg' = toElevConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := sfc_to_elev s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toElevConfig]⟩

-- ============================================================================
-- Complete Execution Traces
-- ============================================================================

-- Full cycle: Idle → GoingUp → Arrived → GoingDown → Idle
-- (with request ≥ 1 and timer ≥ 3)
theorem elevStep_full_cycle (v : Valuation)
    (Hreq : v "request" ≥ 1) (Ht : v "timer" ≥ 3) :
    ElevStepStar Idle v Idle := by
  apply ElevStepStar.step _ _ GoingUp
  · exact ElevStep.depart v Hreq
  apply ElevStepStar.step _ _ Arrived
  · exact ElevStep.arrive v Ht
  apply ElevStepStar.step _ _ GoingDown
  · exact ElevStep.doorClose v (by omega)
  apply ElevStepStar.step _ _ Idle
  · exact ElevStep.returnHome v Ht
  exact ElevStepStar.refl _ _

-- Premium path through SFC matches
theorem elevSFC_full_cycle (v : Valuation)
    (Hreq : v "request" ≥ 1) (Ht : v "timer" ≥ 3) :
    SFCStepStar elevatorSFC (toElevConfig Idle v) (toElevConfig Idle v) := by
  exact elev_to_sfc_star Idle Idle v (elevStep_full_cycle v Hreq Ht)

-- ============================================================================
-- OR-Branching Resolution: The Key Property
-- ============================================================================

-- When a request exists, the elevator departs (priority 0 wins)
theorem elev_departs_on_request (v : Valuation) (Hreq : v "request" ≥ 1) :
    ElevStep Idle v GoingUp :=
  ElevStep.depart v Hreq

-- When no request, the elevator stays idle (fallback, priority 1)
theorem elev_stays_when_no_request (v : Valuation) (Hreq : v "request" < 1) :
    ElevStep Idle v Idle :=
  ElevStep.stayIdle v Hreq

-- The OR-branching is complete: one of the two always fires from Idle
theorem elev_idle_complete (v : Valuation) :
    (v "request" ≥ 1 ∧ ElevStep Idle v GoingUp) ∨
    (v "request" < 1 ∧ ElevStep Idle v Idle) := by
  by_cases h : v "request" ≥ 1
  · left; exact ⟨h, ElevStep.depart v h⟩
  · right; exact ⟨by omega, ElevStep.stayIdle v (by omega)⟩

-- The SFC agrees: from Idle, the SFC also resolves the OR-branch identically
theorem sfc_idle_matches_elev (v : Valuation) (cfg' : Config) :
    SFCStep elevatorSFC (toElevConfig Idle v) cfg' →
    (v "request" ≥ 1 ∧ cfg'.active = [ElevState.toId GoingUp] ∧ cfg'.valuation = v) ∨
    (v "request" < 1 ∧ cfg'.active = [ElevState.toId Idle] ∧ cfg'.valuation = v) := by
  intro H
  obtain ⟨s', Hact, Hval, Hstep⟩ := sfc_to_elev Idle v cfg' H
  cases Hstep with
  | depart _ Hreq =>
    left; exact ⟨Hreq, Hact, Hval⟩
  | stayIdle _ Hreq =>
    right; exact ⟨Hreq, Hact, Hval⟩

-- ============================================================================
-- Bisimulation Instance
-- ============================================================================

def elevatorBisim : SFCBisimulation ElevState where
  sfc := elevatorSFC
  toId := ElevState.toId
  step := ElevStep
  forward := elev_to_sfc
  backward := sfc_to_elev
