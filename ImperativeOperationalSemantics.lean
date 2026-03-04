/-
  Imperative Operational Semantics
  Translated from FRAP Chapter 8: OperationalSemantics.v
  https://github.com/achlipala/frap/blob/master/OperationalSemantics.v
-/

-- Variables are represented as strings
abbrev Var := String

-- Arithmetic expressions
inductive Arith where
  | Const : Nat -> Arith
  | Var : Var -> Arith
  | Plus : Arith -> Arith -> Arith
  | Minus : Arith -> Arith -> Arith
  | Times : Arith -> Arith -> Arith
deriving Repr, DecidableEq

open Arith

-- Valuation maps variables to natural numbers
abbrev Valuation := Var -> Nat

-- Empty valuation (all variables default to 0)
def emptyValuation : Valuation := fun _ => 0

-- Update a valuation with a new binding
def Valuation.update (v : Valuation) (x : Var) (n : Nat) : Valuation :=
  fun y => if y = x then n else v y

notation:max v "[" x " |-> " n "]" => Valuation.update v x n

-- Interpret arithmetic expressions
def interp (e : Arith) (v : Valuation) : Nat :=
  match e with
  | Const n => n
  | Arith.Var x => v x
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v

-- ============================================================================
-- Simple Module: Sequential Imperative Language
-- ============================================================================

namespace Simple

-- Commands
inductive Cmd where
  | Skip : Cmd
  | Assign : Var -> Arith -> Cmd
  | Seq : Cmd -> Cmd -> Cmd
  | If : Arith -> Cmd -> Cmd -> Cmd
  | While : Arith -> Cmd -> Cmd
deriving Repr, DecidableEq

open Cmd

-- Notation for commands
infixr:60 ";;" => Cmd.Seq

-- ============================================================================
-- Big-Step Semantics (Natural Semantics)
-- ============================================================================

inductive Eval : Valuation -> Cmd -> Valuation -> Prop where
  | EvalSkip : forall v, Eval v Skip v
  | EvalAssign : forall v x e,
      Eval v (Assign x e) (v[x |-> interp e v])
  | EvalSeq : forall v c1 v1 c2 v2,
      Eval v c1 v1 ->
      Eval v1 c2 v2 ->
      Eval v (Seq c1 c2) v2
  | EvalIfTrue : forall v e thenC elseC v',
      interp e v ≠ 0 ->
      Eval v thenC v' ->
      Eval v (If e thenC elseC) v'
  | EvalIfFalse : forall v e thenC elseC v',
      interp e v = 0 ->
      Eval v elseC v' ->
      Eval v (If e thenC elseC) v'
  | EvalWhileTrue : forall v e body v' v'',
      interp e v ≠ 0 ->
      Eval v body v' ->
      Eval v' (While e body) v'' ->
      Eval v (While e body) v''
  | EvalWhileFalse : forall v e body,
      interp e v = 0 ->
      Eval v (While e body) v

-- ============================================================================
-- Small-Step Semantics (Structural Operational Semantics)
-- ============================================================================

inductive Step : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | StepAssign : forall v x e,
      Step (v, Assign x e) (v[x |-> interp e v], Skip)
  | StepSeq1 : forall v c1 c2 v' c1',
      Step (v, c1) (v', c1') ->
      Step (v, Seq c1 c2) (v', Seq c1' c2)
  | StepSeq2 : forall v c2,
      Step (v, Seq Skip c2) (v, c2)
  | StepIfTrue : forall v e thenC elseC,
      interp e v ≠ 0 ->
      Step (v, If e thenC elseC) (v, thenC)
  | StepIfFalse : forall v e thenC elseC,
      interp e v = 0 ->
      Step (v, If e thenC elseC) (v, elseC)
  | StepWhileTrue : forall v e body,
      interp e v ≠ 0 ->
      Step (v, While e body) (v, Seq body (While e body))
  | StepWhileFalse : forall v e body,
      interp e v = 0 ->
      Step (v, While e body) (v, Skip)

-- Reflexive transitive closure of step
inductive StepStar : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | refl : forall s, StepStar s s
  | step : forall s1 s2 s3, Step s1 s2 -> StepStar s2 s3 -> StepStar s1 s3

-- ============================================================================
-- Determinism of Step
-- ============================================================================

theorem step_deterministic : forall s out1 out2,
    Step s out1 -> Step s out2 -> out1 = out2 := by
  intro s out1 out2 H1 H2
  induction H1 generalizing out2 with
  | StepAssign v x e =>
    cases H2
    rfl
  | StepSeq1 v c1 c2 v' c1' Hstep ih =>
    cases H2 with
    | StepSeq1 _ _ _ v'' c1'' Hstep' =>
      have heq := ih (v'', c1'') Hstep'
      injection heq with hv hc
      subst hv hc
      rfl
    | StepSeq2 => cases Hstep
  | StepSeq2 v c2 =>
    cases H2 with
    | StepSeq1 _ _ _ _ _ Hstep => cases Hstep
    | StepSeq2 => rfl
  | StepIfTrue v e thenC elseC Hne =>
    cases H2 with
    | StepIfTrue => rfl
    | StepIfFalse _ _ _ _ Heq => exact absurd Heq Hne
  | StepIfFalse v e thenC elseC Heq =>
    cases H2 with
    | StepIfTrue _ _ _ _ Hne => exact absurd Heq Hne
    | StepIfFalse => rfl
  | StepWhileTrue v e body Hne =>
    cases H2 with
    | StepWhileTrue => rfl
    | StepWhileFalse _ _ _ Heq => exact absurd Heq Hne
  | StepWhileFalse v e body Heq =>
    cases H2 with
    | StepWhileTrue _ _ _ Hne => exact absurd Heq Hne
    | StepWhileFalse => rfl

-- ============================================================================
-- Determinism of Eval (Big-Step)
-- ============================================================================

theorem eval_deterministic : forall v c v1 v2,
    Eval v c v1 -> Eval v c v2 -> v1 = v2 := by
  intro v c v1 v2 H1 H2
  induction H1 generalizing v2 with
  | EvalSkip v =>
    cases H2
    rfl
  | EvalAssign v x e =>
    cases H2
    rfl
  | EvalSeq v c1 v1 c2 v2 _ _ ih1 ih2 =>
    cases H2 with
    | EvalSeq _ _ v1' _ _ Hc1 Hc2 =>
      have heq := ih1 v1' Hc1
      subst heq
      exact ih2 _ Hc2
  | EvalIfTrue v e thenC elseC v' Hne _ ih =>
    cases H2 with
    | EvalIfTrue _ _ _ _ _ _ Hthen => exact ih _ Hthen
    | EvalIfFalse _ _ _ _ _ Heq => exact absurd Heq Hne
  | EvalIfFalse v e thenC elseC v' Heq _ ih =>
    cases H2 with
    | EvalIfTrue _ _ _ _ _ Hne => exact absurd Heq Hne
    | EvalIfFalse _ _ _ _ _ _ Helse => exact ih _ Helse
  | EvalWhileTrue v e body v' v'' Hne _ _ ih1 ih2 =>
    cases H2 with
    | EvalWhileTrue _ _ _ v1' _ _ Hbody Hwhile =>
      have heq := ih1 v1' Hbody
      subst heq
      exact ih2 _ Hwhile
    | EvalWhileFalse _ _ _ Heq => exact absurd Heq Hne
  | EvalWhileFalse v e body Heq =>
    cases H2 with
    | EvalWhileTrue _ _ _ _ _ Hne => exact absurd Heq Hne
    | EvalWhileFalse => rfl

-- ============================================================================
-- Contextual Semantics
-- ============================================================================

-- Evaluation contexts
inductive Context where
  | Hole : Context
  | CSeq : Context -> Cmd -> Context
deriving Repr, DecidableEq

open Context

-- Plugging a command into a context
inductive Plug : Context -> Cmd -> Cmd -> Prop where
  | PlugHole : forall c, Plug Hole c c
  | PlugSeq : forall c C c' c2,
      Plug C c c' ->
      Plug (CSeq C c2) c (Seq c' c2)

-- Primitive reduction steps (no context)
inductive Step0 : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | Step0Assign : forall v x e,
      Step0 (v, Assign x e) (v[x |-> interp e v], Skip)
  | Step0Seq : forall v c2,
      Step0 (v, Seq Skip c2) (v, c2)
  | Step0IfTrue : forall v e thenC elseC,
      interp e v ≠ 0 ->
      Step0 (v, If e thenC elseC) (v, thenC)
  | Step0IfFalse : forall v e thenC elseC,
      interp e v = 0 ->
      Step0 (v, If e thenC elseC) (v, elseC)
  | Step0WhileTrue : forall v e body,
      interp e v ≠ 0 ->
      Step0 (v, While e body) (v, Seq body (While e body))
  | Step0WhileFalse : forall v e body,
      interp e v = 0 ->
      Step0 (v, While e body) (v, Skip)

-- Contextual step: find a redex, reduce it, plug result back
inductive CStep : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | CStep_ : forall C v c v' c' c1 c2,
      Plug C c c1 ->
      Step0 (v, c) (v', c') ->
      Plug C c' c2 ->
      CStep (v, c1) (v', c2)

-- ============================================================================
-- Equivalence: Step <-> CStep
-- ============================================================================

theorem step_cstep : forall v c v' c',
    Step (v, c) (v', c') -> CStep (v, c) (v', c') := by
  intro v c v' c' H
  generalize hvc : (v, c) = vc at H
  generalize hvc' : (v', c') = vc' at H
  induction H generalizing v c v' c' with
  | StepAssign v0 x e =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (Assign x e) (v0[x |-> interp e v0]) Skip
      (Assign x e) Skip (Plug.PlugHole _) (Step0.Step0Assign v0 x e) (Plug.PlugHole _)
  | StepSeq1 v0 c1 c2 v0' c1' Hstep ih =>
    cases hvc; cases hvc'
    have ih' := ih v0 c1 v0' c1' rfl rfl
    cases ih' with
    | CStep_ C _ redex _ redex' _ _ Hplug1 Hstep0 Hplug2 =>
      exact CStep.CStep_ (CSeq C c2) v0 redex v0' redex' (Seq c1 c2) (Seq c1' c2)
        (Plug.PlugSeq _ _ _ _ Hplug1) Hstep0 (Plug.PlugSeq _ _ _ _ Hplug2)
  | StepSeq2 v0 c2 =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (Seq Skip c2) v0 c2 (Seq Skip c2) c2
      (Plug.PlugHole _) (Step0.Step0Seq v0 c2) (Plug.PlugHole _)
  | StepIfTrue v0 e thenC elseC Hne =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (If e thenC elseC) v0 thenC (If e thenC elseC) thenC
      (Plug.PlugHole _) (Step0.Step0IfTrue v0 e thenC elseC Hne) (Plug.PlugHole _)
  | StepIfFalse v0 e thenC elseC Heq =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (If e thenC elseC) v0 elseC (If e thenC elseC) elseC
      (Plug.PlugHole _) (Step0.Step0IfFalse v0 e thenC elseC Heq) (Plug.PlugHole _)
  | StepWhileTrue v0 e body Hne =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (While e body) v0 (Seq body (While e body))
      (While e body) (Seq body (While e body))
      (Plug.PlugHole _) (Step0.Step0WhileTrue v0 e body Hne) (Plug.PlugHole _)
  | StepWhileFalse v0 e body Heq =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (While e body) v0 Skip (While e body) Skip
      (Plug.PlugHole _) (Step0.Step0WhileFalse v0 e body Heq) (Plug.PlugHole _)

theorem plug_function : forall C c c1 c2,
    Plug C c c1 -> Plug C c c2 -> c1 = c2 := by
  intro C c c1 c2 H1 H2
  induction H1 generalizing c2 with
  | PlugHole c => cases H2; rfl
  | PlugSeq cmd C c' tail Hplug ih =>
    cases H2 with
    | PlugSeq _ _ c'' _ Hplug' =>
      have := ih c'' Hplug'
      subst this
      rfl

theorem cstep_step : forall v c v' c',
    CStep (v, c) (v', c') -> Step (v, c) (v', c') := by
  intro v c v' c' H
  obtain ⟨C, _, cmd, _, cmd', _, _, Hplug1, Hstep0, Hplug2⟩ := H
  induction Hplug1 generalizing c' with
  | PlugHole _ =>
    cases Hplug2
    cases Hstep0 with
    | Step0Assign => exact Step.StepAssign _ _ _
    | Step0Seq => exact Step.StepSeq2 _ _
    | Step0IfTrue _ _ _ _ Hne => exact Step.StepIfTrue _ _ _ _ Hne
    | Step0IfFalse _ _ _ _ Heq => exact Step.StepIfFalse _ _ _ _ Heq
    | Step0WhileTrue _ _ _ Hne => exact Step.StepWhileTrue _ _ _ Hne
    | Step0WhileFalse _ _ _ Heq => exact Step.StepWhileFalse _ _ _ Heq
  | PlugSeq cmd C c' tail Hplug ih =>
    cases Hplug2 with
    | PlugSeq _ _ c'' _ Hplug' =>
      exact Step.StepSeq1 _ _ _ _ _ (ih c'' Hstep0 Hplug')

-- ============================================================================
-- Equivalence: Big-Step <-> Small-Step
-- ============================================================================

theorem stepStar_trans : forall s1 s2 s3,
    StepStar s1 s2 -> StepStar s2 s3 -> StepStar s1 s3 := by
  intro s1 s2 s3 H12 H23
  induction H12 with
  | refl => exact H23
  | step s1 s2 _ Hstep _ ih => exact StepStar.step s1 s2 s3 Hstep (ih H23)

theorem stepStar_seq : forall v c1 v' c2,
    StepStar (v, c1) (v', Skip) ->
    StepStar (v, Seq c1 c2) (v', c2) := by
  intro v c1 v' c2 H
  have Hseq : StepStar (v, Seq c1 c2) (v', Seq Skip c2) := by
    generalize Hs : (v, c1) = s at H
    generalize Hs' : (v', Skip) = s' at H
    induction H generalizing v c1 v' with
    | refl =>
      cases Hs
      cases Hs'
      exact StepStar.refl _
    | step s1 s2 s3 Hstep _ ih =>
      cases Hs
      obtain ⟨v'', c1'⟩ := s2
      have Hseq1 : Step (v, Seq c1 c2) (v'', Seq c1' c2) := Step.StepSeq1 _ _ _ _ _ Hstep
      exact StepStar.step _ _ _ Hseq1 (ih v'' c1' v' rfl Hs')
  exact stepStar_trans _ _ _ Hseq (StepStar.step _ _ _ (Step.StepSeq2 _ _) (StepStar.refl _))

-- Big-step implies small-step
theorem big_small : forall v c v',
    Eval v c v' -> StepStar (v, c) (v', Skip) := by
  intro v c v' H
  induction H with
  | EvalSkip v => exact StepStar.refl _
  | EvalAssign v x e =>
    exact StepStar.step _ _ _ (Step.StepAssign _ _ _) (StepStar.refl _)
  | EvalSeq v c1 v1 c2 v2 _ _ ih1 ih2 =>
    exact stepStar_trans _ _ _ (stepStar_seq _ _ _ _ ih1) ih2
  | EvalIfTrue v e thenC elseC v' Hne _ ih =>
    exact StepStar.step _ _ _ (Step.StepIfTrue _ _ _ _ Hne) ih
  | EvalIfFalse v e thenC elseC v' Heq _ ih =>
    exact StepStar.step _ _ _ (Step.StepIfFalse _ _ _ _ Heq) ih
  | EvalWhileTrue v e body v' v'' Hne _ _ ih1 ih2 =>
    have Hunroll : StepStar (v, While e body) (v, Seq body (While e body)) :=
      StepStar.step _ _ _ (Step.StepWhileTrue _ _ _ Hne) (StepStar.refl _)
    exact stepStar_trans _ _ _ Hunroll (stepStar_trans _ _ _ (stepStar_seq _ _ _ _ ih1) ih2)
  | EvalWhileFalse v e body Heq =>
    exact StepStar.step _ _ _ (Step.StepWhileFalse _ _ _ Heq) (StepStar.refl _)

-- Helper: if c1 steps, then Seq c1 c2 steps correspondingly
theorem step_seq_context : forall v c1 v' c1' c2,
    Step (v, c1) (v', c1') ->
    Step (v, Seq c1 c2) (v', Seq c1' c2) := by
  intro v c1 v' c1' c2 H
  exact Step.StepSeq1 _ _ _ _ _ H

-- Single step preserves evaluation (going backwards)
theorem step_eval : forall v c v' c',
    Step (v, c) (v', c') -> forall v'', Eval v' c' v'' -> Eval v c v'' := by
  intro v c v' c' Hstep v'' Heval
  cases Hstep with
  | StepAssign _ x e =>
    cases Heval
    exact Eval.EvalAssign _ _ _
  | StepSeq1 _ c1 c2 _ c1' Hstep' =>
    cases Heval with
    | EvalSeq _ _ v1' _ _ Hc1' Hc2 =>
      exact Eval.EvalSeq _ _ _ _ _ (step_eval _ _ _ _ Hstep' _ Hc1') Hc2
  | StepSeq2 _ c2 =>
    exact Eval.EvalSeq _ _ _ _ _ (Eval.EvalSkip _) Heval
  | StepIfTrue _ e thenC elseC Hne =>
    exact Eval.EvalIfTrue _ _ _ _ _ Hne Heval
  | StepIfFalse _ e thenC elseC Heq =>
    exact Eval.EvalIfFalse _ _ _ _ _ Heq Heval
  | StepWhileTrue _ e body Hne =>
    cases Heval with
    | EvalSeq _ _ v1' _ _ Hbody Hwhile =>
      exact Eval.EvalWhileTrue _ _ _ _ _ Hne Hbody Hwhile
  | StepWhileFalse _ e body Heq =>
    cases Heval
    exact Eval.EvalWhileFalse _ _ _ Heq

-- Small-step implies big-step (helper lemma)
theorem small_big_helper : forall s s',
    StepStar s s' ->
    forall v c v' c' v'', s = (v, c) -> s' = (v', c') -> Eval v' c' v'' -> Eval v c v'' := by
  intro s s' Hstar
  induction Hstar with
  | refl =>
    intro v c v' c' v'' hs hs' Heval
    cases hs; cases hs'
    exact Heval
  | step s1 s2 s3 Hstep Hstar' ih =>
    intro v c v' c' v'' hs hs' Heval
    cases hs
    obtain ⟨v2, c2⟩ := s2
    have ih' := ih v2 c2 v' c' v'' rfl hs' Heval
    exact step_eval _ _ _ _ Hstep _ ih'

-- Small-step implies big-step
theorem small_big : forall v c v',
    StepStar (v, c) (v', Skip) -> Eval v c v' := by
  intro v c v' H
  exact small_big_helper _ _ H _ _ _ _ _ rfl rfl (Eval.EvalSkip _)

end Simple

-- ============================================================================
-- Concurrent Module: Parallel Composition
-- ============================================================================

namespace Concurrent

-- Commands with parallel composition
inductive Cmd where
  | Skip : Cmd
  | Assign : Var -> Arith -> Cmd
  | Seq : Cmd -> Cmd -> Cmd
  | If : Arith -> Cmd -> Cmd -> Cmd
  | While : Arith -> Cmd -> Cmd
  | Parallel : Cmd -> Cmd -> Cmd
deriving Repr, DecidableEq

open Cmd

-- Notation for commands
infixr:60 ";;" => Cmd.Seq
infixr:55 "|||" => Cmd.Parallel

-- ============================================================================
-- Evaluation Contexts for Concurrent Language
-- ============================================================================

inductive Context where
  | Hole : Context
  | CSeq : Context -> Cmd -> Context
  | CPar1 : Context -> Cmd -> Context
  | CPar2 : Cmd -> Context -> Context
deriving Repr, DecidableEq

open Context

-- Plugging a command into a context
inductive Plug : Context -> Cmd -> Cmd -> Prop where
  | PlugHole : forall c, Plug Hole c c
  | PlugSeq : forall c C c' c2,
      Plug C c c' ->
      Plug (CSeq C c2) c (Seq c' c2)
  | PlugPar1 : forall c C c' c2,
      Plug C c c' ->
      Plug (CPar1 C c2) c (Parallel c' c2)
  | PlugPar2 : forall c C c' c1,
      Plug C c c' ->
      Plug (CPar2 c1 C) c (Parallel c1 c')

-- ============================================================================
-- Primitive Reduction Steps
-- ============================================================================

inductive Step0 : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | Step0Assign : forall v x e,
      Step0 (v, Assign x e) (v[x |-> interp e v], Skip)
  | Step0Seq : forall v c2,
      Step0 (v, Seq Skip c2) (v, c2)
  | Step0IfTrue : forall v e thenC elseC,
      interp e v ≠ 0 ->
      Step0 (v, If e thenC elseC) (v, thenC)
  | Step0IfFalse : forall v e thenC elseC,
      interp e v = 0 ->
      Step0 (v, If e thenC elseC) (v, elseC)
  | Step0WhileTrue : forall v e body,
      interp e v ≠ 0 ->
      Step0 (v, While e body) (v, Seq body (While e body))
  | Step0WhileFalse : forall v e body,
      interp e v = 0 ->
      Step0 (v, While e body) (v, Skip)
  | Step0Par : forall v c,
      Step0 (v, Parallel Skip c) (v, c)

-- ============================================================================
-- Contextual Step
-- ============================================================================

inductive CStep : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | CStep_ : forall C v c v' c' c1 c2,
      Plug C c c1 ->
      Step0 (v, c) (v', c') ->
      Plug C c' c2 ->
      CStep (v, c1) (v', c2)

-- ============================================================================
-- Direct Small-Step Semantics
-- ============================================================================

inductive Step : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | StepAssign : forall v x e,
      Step (v, Assign x e) (v[x |-> interp e v], Skip)
  | StepSeq1 : forall v c1 c2 v' c1',
      Step (v, c1) (v', c1') ->
      Step (v, Seq c1 c2) (v', Seq c1' c2)
  | StepSeq2 : forall v c2,
      Step (v, Seq Skip c2) (v, c2)
  | StepIfTrue : forall v e thenC elseC,
      interp e v ≠ 0 ->
      Step (v, If e thenC elseC) (v, thenC)
  | StepIfFalse : forall v e thenC elseC,
      interp e v = 0 ->
      Step (v, If e thenC elseC) (v, elseC)
  | StepWhileTrue : forall v e body,
      interp e v ≠ 0 ->
      Step (v, While e body) (v, Seq body (While e body))
  | StepWhileFalse : forall v e body,
      interp e v = 0 ->
      Step (v, While e body) (v, Skip)
  | StepParSkip1 : forall v c,
      Step (v, Parallel Skip c) (v, c)
  | StepPar1 : forall v c1 c2 v' c1',
      Step (v, c1) (v', c1') ->
      Step (v, Parallel c1 c2) (v', Parallel c1' c2)
  | StepPar2 : forall v c1 c2 v' c2',
      Step (v, c2) (v', c2') ->
      Step (v, Parallel c1 c2) (v', Parallel c1 c2')

-- Reflexive transitive closure
inductive StepStar : Valuation × Cmd -> Valuation × Cmd -> Prop where
  | refl : forall s, StepStar s s
  | step : forall s1 s2 s3, Step s1 s2 -> StepStar s2 s3 -> StepStar s1 s3

-- ============================================================================
-- Equivalence: Step <-> CStep for Concurrent Language
-- ============================================================================

theorem step_cstep : forall v c v' c',
    Step (v, c) (v', c') -> CStep (v, c) (v', c') := by
  intro v c v' c' H
  generalize hvc : (v, c) = vc at H
  generalize hvc' : (v', c') = vc' at H
  induction H generalizing v c v' c' with
  | StepAssign v0 x e =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (Assign x e) (v0[x |-> interp e v0]) Skip
      (Assign x e) Skip (Plug.PlugHole _) (Step0.Step0Assign v0 x e) (Plug.PlugHole _)
  | StepSeq1 v0 c1 c2 v0' c1' Hstep ih =>
    cases hvc; cases hvc'
    have ih' := ih v0 c1 v0' c1' rfl rfl
    cases ih' with
    | CStep_ C _ redex _ redex' _ _ Hplug1 Hstep0 Hplug2 =>
      exact CStep.CStep_ (CSeq C c2) v0 redex v0' redex' (Seq c1 c2) (Seq c1' c2)
        (Plug.PlugSeq _ _ _ _ Hplug1) Hstep0 (Plug.PlugSeq _ _ _ _ Hplug2)
  | StepSeq2 v0 c2 =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (Seq Skip c2) v0 c2 (Seq Skip c2) c2
      (Plug.PlugHole _) (Step0.Step0Seq v0 c2) (Plug.PlugHole _)
  | StepIfTrue v0 e thenC elseC Hne =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (If e thenC elseC) v0 thenC (If e thenC elseC) thenC
      (Plug.PlugHole _) (Step0.Step0IfTrue v0 e thenC elseC Hne) (Plug.PlugHole _)
  | StepIfFalse v0 e thenC elseC Heq =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (If e thenC elseC) v0 elseC (If e thenC elseC) elseC
      (Plug.PlugHole _) (Step0.Step0IfFalse v0 e thenC elseC Heq) (Plug.PlugHole _)
  | StepWhileTrue v0 e body Hne =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (While e body) v0 (Seq body (While e body))
      (While e body) (Seq body (While e body))
      (Plug.PlugHole _) (Step0.Step0WhileTrue v0 e body Hne) (Plug.PlugHole _)
  | StepWhileFalse v0 e body Heq =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (While e body) v0 Skip (While e body) Skip
      (Plug.PlugHole _) (Step0.Step0WhileFalse v0 e body Heq) (Plug.PlugHole _)
  | StepParSkip1 v0 c =>
    cases hvc; cases hvc'
    exact CStep.CStep_ Hole v0 (Parallel Skip c) v0 c (Parallel Skip c) c
      (Plug.PlugHole _) (Step0.Step0Par v0 c) (Plug.PlugHole _)
  | StepPar1 v0 c1 c2 v0' c1' Hstep ih =>
    cases hvc; cases hvc'
    have ih' := ih v0 c1 v0' c1' rfl rfl
    cases ih' with
    | CStep_ C _ redex _ redex' _ _ Hplug1 Hstep0 Hplug2 =>
      exact CStep.CStep_ (CPar1 C c2) v0 redex v0' redex' (Parallel c1 c2) (Parallel c1' c2)
        (Plug.PlugPar1 _ _ _ _ Hplug1) Hstep0 (Plug.PlugPar1 _ _ _ _ Hplug2)
  | StepPar2 v0 c1 c2 v0' c2' Hstep ih =>
    cases hvc; cases hvc'
    have ih' := ih v0 c2 v0' c2' rfl rfl
    cases ih' with
    | CStep_ C _ redex _ redex' _ _ Hplug1 Hstep0 Hplug2 =>
      exact CStep.CStep_ (CPar2 c1 C) v0 redex v0' redex' (Parallel c1 c2) (Parallel c1 c2')
        (Plug.PlugPar2 _ _ _ _ Hplug1) Hstep0 (Plug.PlugPar2 _ _ _ _ Hplug2)

theorem cstep_step : forall v c v' c',
    CStep (v, c) (v', c') -> Step (v, c) (v', c') := by
  intro v c v' c' H
  obtain ⟨C, _, cmd, _, cmd', _, _, Hplug1, Hstep0, Hplug2⟩ := H
  induction Hplug1 generalizing c' with
  | PlugHole _ =>
    cases Hplug2
    cases Hstep0 with
    | Step0Assign => exact Step.StepAssign _ _ _
    | Step0Seq => exact Step.StepSeq2 _ _
    | Step0IfTrue _ _ _ _ Hne => exact Step.StepIfTrue _ _ _ _ Hne
    | Step0IfFalse _ _ _ _ Heq => exact Step.StepIfFalse _ _ _ _ Heq
    | Step0WhileTrue _ _ _ Hne => exact Step.StepWhileTrue _ _ _ Hne
    | Step0WhileFalse _ _ _ Heq => exact Step.StepWhileFalse _ _ _ Heq
    | Step0Par => exact Step.StepParSkip1 _ _
  | PlugSeq cmd C c' tail Hplug ih =>
    cases Hplug2 with
    | PlugSeq _ _ c'' _ Hplug' =>
      exact Step.StepSeq1 _ _ _ _ _ (ih c'' Hstep0 Hplug')
  | PlugPar1 cmd C c' tail Hplug ih =>
    cases Hplug2 with
    | PlugPar1 _ _ c'' _ Hplug' =>
      exact Step.StepPar1 _ _ _ _ _ (ih c'' Hstep0 Hplug')
  | PlugPar2 cmd C c' head Hplug ih =>
    cases Hplug2 with
    | PlugPar2 _ _ c'' _ Hplug' =>
      exact Step.StepPar2 _ _ _ _ _ (ih c'' Hstep0 Hplug')

end Concurrent

-- ============================================================================
-- Examples
-- ============================================================================

section Examples

open Simple
open Cmd

-- Example: x := 1; y := x + 1
def exampleProg1 : Cmd :=
  Assign "x" (Const 1) ;; Assign "y" (Plus (Arith.Var "x") (Const 1))

-- Prove that the example program evaluates correctly
example : Eval emptyValuation exampleProg1 (emptyValuation["x" |-> 1]["y" |-> 2]) := by
  unfold exampleProg1
  apply Eval.EvalSeq
  · apply Eval.EvalAssign
  · simp [interp]
    apply Eval.EvalAssign

-- Example: factorial computation
-- n := 5; result := 1; while n > 0 do (result := result * n; n := n - 1)
-- Note: we use n ≠ 0 as the condition since our language uses ≠ 0 for truth

def factorialProg : Cmd :=
  Assign "n" (Const 5) ;;
  Assign "result" (Const 1) ;;
  While (Arith.Var "n")
    (Assign "result" (Times (Arith.Var "result") (Arith.Var "n")) ;;
     Assign "n" (Minus (Arith.Var "n") (Const 1)))

end Examples
