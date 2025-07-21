inductive exp where
 | C : Nat -> exp
 | Plus : exp -> exp -> exp
open exp

def eval (e1 : exp) : Nat :=
  match e1 with
  | C n => n
  | Plus l r =>
  let lCall := eval l
  let rCall := eval r
  lCall + rCall


#check Nat
#check Type 1
#check Prop

theorem excluded_middle : forall P : Prop, P ∨ ¬ P := sorry

theorem excluded_middle_bool : forall P : Bool, P = true ∨ P = false := by
  intros P
  cases P <;> simp



inductive evalInd : exp -> Nat -> Prop where
| E_C : forall (n: Nat), evalInd (C n) n
| E_Plus : forall l r l_n r_n,
  evalInd l l_n -> evalInd r r_n ->
    evalInd (Plus l r) (l_n + r_n)

open evalInd


example : forall (n : Nat), evalInd (C n) (0 + n) := by
  intros n
  have H: 0 + n = n := by simp
  rw [H]
  apply E_C



/- For small step semantics this sort of reduction is what we want
   to create inductively:

  - A reduction step is finding one plus in an expression over two constants to simplify
  - It will have the form of a relation that is parameterized over two expression
    - Will define/formalize relations later
  - Reduce the exp by picking some numbers to add
  - Only reduce the right hand side of plus when the left hand side is a Constant

  (C 1 + C 2) + C 3 ==> C 3 + C 3
   C 3 + C 3 ==> C 6
 -/

def stepProg (e : exp): exp :=
  match e with
  | C n => C n
  | Plus (C n) (C m) => C (n + m)
  | Plus (C n) e2 =>
    Plus (C n) (stepProg e2)
  | Plus e1 e2 =>
    Plus (stepProg e1) e2


inductive step_value : exp -> Prop where
| vConst : forall n, step_value (C n)


inductive step : exp -> exp -> Prop where

| stepPlusConst : forall n m, step (Plus (C n) (C m)) (C (n + m))

| stepPlusConstLeft: forall e resultExp eValue,
    step e resultExp ->
    step_value eValue ->
    step (Plus eValue e) (Plus eValue resultExp)

| stepPlusLeftStep : forall e1 e2 resultExp,
    step e1 resultExp ->
    step (Plus e1 e2) (Plus resultExp e2)
open step

/- infix:50 " ==> " => step

example : step (Plus (C 0) (C 1)) (C 1) := by
  apply stepPlusConst

example : (Plus (Plus (C 0) (C 1)) (Plus (C 2) (C 3))) ==>
  (Plus (C 1) (Plus (C 2) (C 3)))
 := by
  apply stepPlusLeftStep
  apply stepPlusConst

example : (Plus (C 1) (Plus (C 2) (C 3))) ==>
  (Plus (C 1) (C 5))
 := by sorry


example : ¬ (Plus (Plus (C 1) (C 2)) (Plus (C 2) (C 3))) ==>
  (Plus (Plus (C 1) (C 2)) (C 5))
 := by sorry
 -/

-- Lets formalize some stuff about relations.

-- even
   --- exists n = 2 * m

-- even 6
--  - sub2 : even 4
--  - sub4 : even 2


def relation (X : Type) := X -> X -> Prop
def value (X : Type) := X -> Prop

def deterministic {X : Type} (R : relation X) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2

def progress {X : Type} (R : relation X) (valueP : value X) :=
  forall x: X, exists y, R x y ∨ valueP x

def normal_formal {X : Type} (R : relation X) (x : X) :=
  ¬ exists y, R x y

theorem step_deterministic : deterministic step := by
  unfold deterministic
  intros x y1 y2
  intros H1 H2
  revert y2
  induction H1 with
  | stepPlusConst n m =>
    intros y2
    intros H2
    have y2Plus: y2 = C (n + m) := by
      cases H2 with
      | stepPlusConst n m => simp
      | stepPlusConstLeft e resultExp eValue H3 H4 =>
        cases H3
      | stepPlusLeftStep e1 e2 resultExp a =>
        cases a
    rw [y2Plus]
  | stepPlusConstLeft e resultExp eValue H3 H4 ih =>
    intros y2
    intros H2
    cases H2 with
    | stepPlusConst n m => cases H3
    | stepPlusConstLeft e_ resultExp_ eValue_ H3_ H4_ =>
      simp
      apply ih
      simp [*]
    | stepPlusLeftStep e1 e2 resultExp a =>
        cases H4
        cases a
  | stepPlusLeftStep e1 e2 resultExp a ih =>
    intros y2
    intros H2
    cases H2 with
    | stepPlusConst n m => cases a
    | stepPlusConstLeft e_ resultExp_ eValue_ H3_ H4_ =>
      cases H4_
      cases a
    | stepPlusLeftStep e1_ e2_ resultExp_ a_ =>
      simp
      apply ih
      simp [*]



































def deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2

theorem step_deterministic : deterministic step := by
  unfold deterministic
  intros x y1 y2 H1 H2
  revert y2
  induction H1 <;> intros
  have H2: C
