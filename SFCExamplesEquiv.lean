/-
  SFC Examples: Inductive Operational Semantics ↔ SFC Bisimulation

  Bisimulations for the simple examples from SFC.lean:
  1. Sequential SFC: S1 → S2 → S3
  2. Alternative SFC: S1 → S2 (priority) or S1 → S3 (fallback)
  3. Loop SFC: S1 → S1 (loop) or S1 → S2 (exit)
-/
import SFC

-- ============================================================================
-- 1. Sequential SFC: S1 --[x > 0]--> S2 --[true]--> S3
-- ============================================================================

namespace Sequential

inductive SeqState where
  | S1 | S2 | S3
deriving DecidableEq, Repr

open SeqState

def SeqState.toId : SeqState → StepId
  | S1 => "S1"
  | S2 => "S2"
  | S3 => "S3"

--     x > 0
--   ─────────── (Step1)
--   S1 → S2
--
--     true
--   ─────────── (Step2)
--   S2 → S3
inductive SeqStep : SeqState → Valuation → SeqState → Prop where
  | step1 : ∀ v, v "x" > 0 → SeqStep S1 v S2
  | step2 : ∀ v, SeqStep S2 v S3

inductive SeqStepStar : SeqState → Valuation → SeqState → Prop where
  | refl : ∀ s v, SeqStepStar s v s
  | step : ∀ s1 v s2 s3,
      SeqStep s1 v s2 → SeqStepStar s2 v s3 → SeqStepStar s1 v s3

-- Properties

theorem seqStep_deterministic : ∀ s v s1 s2,
    SeqStep s v s1 → SeqStep s v s2 → s1 = s2 := by
  intro s v s1 s2 H1 H2
  cases H1 <;> cases H2 <;> rfl

-- Configuration correspondence

def toSeqConfig (s : SeqState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- Forward: SeqStep → SFCStep

theorem seq_to_sfc (s s' : SeqState) (v : Valuation) :
    SeqStep s v s' →
    SFCStep Examples.sequentialSFC (toSeqConfig s v) (toSeqConfig s' v) := by
  intro H
  cases H with
  | step1 v Hx =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S2"], guard := .Gt "x" 0 })
    · simp [Examples.sequentialSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toSeqConfig, SeqState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toSeqConfig, SeqState.toId]
    · rfl
  | step2 v =>
    apply SFCStep.fireTransition
      (t := { sources := ["S2"], targets := ["S3"], guard := .True })
    · simp [Examples.sequentialSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toSeqConfig, SeqState.toId]
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toSeqConfig, SeqState.toId]
    · rfl

-- Backward: SFCStep → SeqStep

theorem sfc_to_seq (s : SeqState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.sequentialSFC (toSeqConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ SeqStep s v s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen _ Hact Hval
    simp [Examples.sequentialSFC] at Hin
    rcases Hin with rfl | rfl
    · -- S1 → S2 transition
      cases s with
      | S1 =>
        refine ⟨S2, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toSeqConfig, SeqState.toId] at Hact
          exact Hact
        · simp [toSeqConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toSeqConfig, SeqState.toId] at Hen
          exact SeqStep.step1 v (by omega)
      | S2 =>
        simp [Transition.enabled, allActive, isActive, toSeqConfig, SeqState.toId] at Hen
      | S3 =>
        simp [Transition.enabled, allActive, isActive, toSeqConfig, SeqState.toId] at Hen
    · -- S2 → S3 transition
      cases s with
      | S1 =>
        simp [Transition.enabled, allActive, isActive, toSeqConfig, SeqState.toId] at Hen
      | S2 =>
        refine ⟨S3, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toSeqConfig, SeqState.toId] at Hact
          exact Hact
        · simp [toSeqConfig] at Hval; exact Hval
        · exact SeqStep.step2 v
      | S3 =>
        simp [Transition.enabled, allActive, isActive, toSeqConfig, SeqState.toId] at Hen

-- Multi-step lift

theorem seq_to_sfc_star (s s' : SeqState) (v : Valuation) :
    SeqStepStar s v s' →
    SFCStepStar Examples.sequentialSFC (toSeqConfig s v) (toSeqConfig s' v) := by
  intro H
  generalize hv : v = v' at H
  induction H with
  | refl _ _ => exact SFCStepStar.refl _
  | step s1 _ s2 s3 Hstep _ ih =>
    subst hv
    exact SFCStepStar.step _ _ _ (seq_to_sfc s1 s2 v Hstep) (ih rfl)

-- Shape preservation

theorem sfc_seq_preserves_shape (s : SeqState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.sequentialSFC (toSeqConfig s v) cfg' →
    ∃ s', cfg' = toSeqConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := sfc_to_seq s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toSeqConfig]⟩

-- Full execution: S1 → S2 → S3

theorem seqStep_full (v : Valuation) (Hx : v "x" > 0) :
    SeqStepStar S1 v S3 := by
  apply SeqStepStar.step _ _ S2
  · exact SeqStep.step1 v Hx
  apply SeqStepStar.step _ _ S3
  · exact SeqStep.step2 v
  exact SeqStepStar.refl _ _

-- Bisimulation instance

def sequentialBisim : SFCBisimulation SeqState where
  sfc := Examples.sequentialSFC
  toId := SeqState.toId
  step := SeqStep
  forward := seq_to_sfc
  backward := sfc_to_seq

end Sequential

-- ============================================================================
-- 2. Alternative SFC: S1 --[x > 5]--> S2 (priority 0)
--                     S1 --[true]--> S3  (priority 1, fallback)
-- ============================================================================

namespace Alternative

inductive AltState where
  | S1 | S2 | S3
deriving DecidableEq, Repr

open AltState

def AltState.toId : AltState → StepId
  | S1 => "S1"
  | S2 => "S2"
  | S3 => "S3"

--     x > 5
--   ─────────── (GoS2)
--   S1 → S2
--
--     x ≤ 5
--   ─────────── (GoS3)
--   S1 → S3
inductive AltStep : AltState → Valuation → AltState → Prop where
  | goS2 : ∀ v, v "x" > 5 → AltStep S1 v S2
  | goS3 : ∀ v, v "x" ≤ 5 → AltStep S1 v S3

inductive AltStepStar : AltState → Valuation → AltState → Prop where
  | refl : ∀ s v, AltStepStar s v s
  | step : ∀ s1 v s2 s3,
      AltStep s1 v s2 → AltStepStar s2 v s3 → AltStepStar s1 v s3

-- Properties

theorem altStep_deterministic : ∀ s v s1 s2,
    AltStep s v s1 → AltStep s v s2 → s1 = s2 := by
  intro s v s1 s2 H1 H2
  cases H1 <;> cases H2 <;> first | rfl | omega

theorem altStep_total_from_s1 : ∀ v, ∃ s', AltStep S1 v s' := by
  intro v
  by_cases h : v "x" > 5
  · exact ⟨S2, AltStep.goS2 v h⟩
  · exact ⟨S3, AltStep.goS3 v (by omega)⟩

-- Configuration correspondence

def toAltConfig (s : AltState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- Forward: AltStep → SFCStep

theorem alt_to_sfc (s s' : AltState) (v : Valuation) :
    AltStep s v s' →
    SFCStep Examples.alternativeSFC (toAltConfig s v) (toAltConfig s' v) := by
  intro H
  cases H with
  | goS2 v Hx =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S2"],
              guard := .Gt "x" 5, priority := 0 })
    · simp [Examples.alternativeSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toAltConfig, AltState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toAltConfig, AltState.toId]
    · rfl
  | goS3 v Hx =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S3"],
              guard := .True, priority := 1 })
    · simp [Examples.alternativeSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toAltConfig, AltState.toId]
    · -- Priority: depart (priority 0) is NOT enabled because x ≤ 5
      intro t' Hin Hsrc Hen
      simp [Examples.alternativeSFC] at Hin
      rcases Hin with rfl | rfl
      · simp [Transition.enabled, allActive, isActive, Guard.eval,
              toAltConfig, AltState.toId] at Hen; omega
      · simp
    · simp [fireTransition, activate, deactivate, toAltConfig, AltState.toId]
    · rfl

-- Backward: SFCStep → AltStep

theorem sfc_to_alt (s : AltState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.alternativeSFC (toAltConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ AltStep s v s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen Hpri Hact Hval
    simp [Examples.alternativeSFC] at Hin
    rcases Hin with rfl | rfl
    · -- S1 → S2 (x > 5)
      cases s with
      | S1 =>
        refine ⟨S2, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toAltConfig, AltState.toId] at Hact
          exact Hact
        · simp [toAltConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toAltConfig, AltState.toId] at Hen
          exact AltStep.goS2 v (by omega)
      | S2 =>
        simp [Transition.enabled, allActive, isActive, toAltConfig, AltState.toId] at Hen
      | S3 =>
        simp [Transition.enabled, allActive, isActive, toAltConfig, AltState.toId] at Hen
    · -- S1 → S3 (fallback, priority 1)
      cases s with
      | S1 =>
        refine ⟨S3, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toAltConfig, AltState.toId] at Hact
          exact Hact
        · simp [toAltConfig] at Hval; exact Hval
        · -- Derive x ≤ 5 from priority constraint
          have Hnothi := Hpri
            { sources := ["S1"], targets := ["S2"],
              guard := .Gt "x" 5, priority := 0 }
            (by simp [Examples.alternativeSFC])
            (by simp)
          simp [Transition.enabled, allActive, isActive, Guard.eval,
                toAltConfig, AltState.toId] at Hnothi
          exact AltStep.goS3 v (by omega)
      | S2 =>
        simp [Transition.enabled, allActive, isActive, toAltConfig, AltState.toId] at Hen
      | S3 =>
        simp [Transition.enabled, allActive, isActive, toAltConfig, AltState.toId] at Hen

-- Multi-step lift

theorem alt_to_sfc_star (s s' : AltState) (v : Valuation) :
    AltStepStar s v s' →
    SFCStepStar Examples.alternativeSFC (toAltConfig s v) (toAltConfig s' v) := by
  intro H
  generalize hv : v = v' at H
  induction H with
  | refl _ _ => exact SFCStepStar.refl _
  | step s1 _ s2 s3 Hstep _ ih =>
    subst hv
    exact SFCStepStar.step _ _ _ (alt_to_sfc s1 s2 v Hstep) (ih rfl)

-- Shape preservation

theorem sfc_alt_preserves_shape (s : AltState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.alternativeSFC (toAltConfig s v) cfg' →
    ∃ s', cfg' = toAltConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := sfc_to_alt s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toAltConfig]⟩

-- Bisimulation instance

def alternativeBisim : SFCBisimulation AltState where
  sfc := Examples.alternativeSFC
  toId := AltState.toId
  step := AltStep
  forward := alt_to_sfc
  backward := sfc_to_alt

end Alternative

-- ============================================================================
-- 3. Loop SFC: S1 --[x ≥ 10]--> S2 (exit, priority 0)
--              S1 --[x < 10]--> S1  (loop, priority 1)
-- ============================================================================

namespace Loop

inductive LoopState where
  | S1 | S2
deriving DecidableEq, Repr

open LoopState

def LoopState.toId : LoopState → StepId
  | S1 => "S1"
  | S2 => "S2"

--     x ≥ 10
--   ─────────── (Exit)
--   S1 → S2
--
--     x < 10
--   ─────────── (Loop)
--   S1 → S1
inductive LoopStep : LoopState → Valuation → LoopState → Prop where
  | exit : ∀ v, v "x" ≥ 10 → LoopStep S1 v S2
  | loop : ∀ v, v "x" < 10 → LoopStep S1 v S1

inductive LoopStepStar : LoopState → Valuation → LoopState → Prop where
  | refl : ∀ s v, LoopStepStar s v s
  | step : ∀ s1 v s2 s3,
      LoopStep s1 v s2 → LoopStepStar s2 v s3 → LoopStepStar s1 v s3

-- Properties

theorem loopStep_deterministic : ∀ s v s1 s2,
    LoopStep s v s1 → LoopStep s v s2 → s1 = s2 := by
  intro s v s1 s2 H1 H2
  cases H1 <;> cases H2 <;> first | rfl | omega

theorem loopStep_total_from_s1 : ∀ v, ∃ s', LoopStep S1 v s' := by
  intro v
  by_cases h : v "x" ≥ 10
  · exact ⟨S2, LoopStep.exit v h⟩
  · exact ⟨S1, LoopStep.loop v (by omega)⟩

-- Configuration correspondence

def toLoopConfig (s : LoopState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- Forward: LoopStep → SFCStep

theorem loop_to_sfc (s s' : LoopState) (v : Valuation) :
    LoopStep s v s' →
    SFCStep Examples.loopSFC (toLoopConfig s v) (toLoopConfig s' v) := by
  intro H
  cases H with
  | exit v Hx =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S2"],
              guard := .Ge "x" 10, priority := 0 })
    · simp [Examples.loopSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toLoopConfig, LoopState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toLoopConfig, LoopState.toId]
    · rfl
  | loop v Hx =>
    apply SFCStep.fireTransition
      (t := { sources := ["S1"], targets := ["S1"],
              guard := .Lt "x" 10, priority := 1 })
    · simp [Examples.loopSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toLoopConfig, LoopState.toId]; omega
    · -- Priority: exit (priority 0) is NOT enabled because x < 10
      intro t' Hin Hsrc Hen
      simp [Examples.loopSFC] at Hin
      rcases Hin with rfl | rfl
      · simp [Transition.enabled, allActive, isActive, Guard.eval,
              toLoopConfig, LoopState.toId] at Hen; omega
      · simp
    · simp [fireTransition, activate, deactivate, toLoopConfig, LoopState.toId]
    · rfl

-- Backward: SFCStep → LoopStep

theorem sfc_to_loop (s : LoopState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.loopSFC (toLoopConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ LoopStep s v s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen Hpri Hact Hval
    simp [Examples.loopSFC] at Hin
    rcases Hin with rfl | rfl
    · -- S1 → S2 (exit, x ≥ 10)
      cases s with
      | S1 =>
        refine ⟨S2, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toLoopConfig, LoopState.toId] at Hact
          exact Hact
        · simp [toLoopConfig] at Hval; exact Hval
        · simp [Transition.enabled, allActive, isActive, Guard.eval,
                toLoopConfig, LoopState.toId] at Hen
          exact LoopStep.exit v (by omega)
      | S2 =>
        simp [Transition.enabled, allActive, isActive, toLoopConfig, LoopState.toId] at Hen
    · -- S1 → S1 (loop, x < 10)
      cases s with
      | S1 =>
        refine ⟨S1, ?_, ?_, ?_⟩
        · simp [fireTransition, activate, deactivate, toLoopConfig, LoopState.toId] at Hact
          exact Hact
        · simp [toLoopConfig] at Hval; exact Hval
        · -- Derive x < 10 from priority constraint
          have Hnotexit := Hpri
            { sources := ["S1"], targets := ["S2"],
              guard := .Ge "x" 10, priority := 0 }
            (by simp [Examples.loopSFC])
            (by simp)
          simp [Transition.enabled, allActive, isActive, Guard.eval,
                toLoopConfig, LoopState.toId] at Hnotexit
          exact LoopStep.loop v (by omega)
      | S2 =>
        simp [Transition.enabled, allActive, isActive, toLoopConfig, LoopState.toId] at Hen

-- Multi-step lift

theorem loop_to_sfc_star (s s' : LoopState) (v : Valuation) :
    LoopStepStar s v s' →
    SFCStepStar Examples.loopSFC (toLoopConfig s v) (toLoopConfig s' v) := by
  intro H
  generalize hv : v = v' at H
  induction H with
  | refl _ _ => exact SFCStepStar.refl _
  | step s1 _ s2 s3 Hstep _ ih =>
    subst hv
    exact SFCStepStar.step _ _ _ (loop_to_sfc s1 s2 v Hstep) (ih rfl)

-- Shape preservation

theorem sfc_loop_preserves_shape (s : LoopState) (v : Valuation) (cfg' : Config) :
    SFCStep Examples.loopSFC (toLoopConfig s v) cfg' →
    ∃ s', cfg' = toLoopConfig s' v := by
  intro H
  obtain ⟨s', Hact, Hval, _⟩ := sfc_to_loop s v cfg' H
  exact ⟨s', by cases cfg'; simp_all [toLoopConfig]⟩

-- Bisimulation instance

def loopBisim : SFCBisimulation LoopState where
  sfc := Examples.loopSFC
  toId := LoopState.toId
  step := LoopStep
  forward := loop_to_sfc
  backward := sfc_to_loop

end Loop
