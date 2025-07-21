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


inductive step : exp -> exp -> Prop where
| stepConst1 : forall n, step (C n) (C n)

| stepPlusConst : forall n m, step (Plus (C n) (C m)) (C (n + m))

| stepPlusConstLeft: forall n e resultExp,
    step e resultExp ->
    step (Plus (C n) e) (Plus (C n) resultExp)

| stepPlusLeftStep : forall e1 e2 resultExp,
    step e1 resultExp ->
    step (Plus e1 e2) (Plus resultExp e2)
open step

infix:50 " ==> " => step

example : (C 0) ==> (C 0) := by apply stepConst1

example : (Plus (C 0) (C 1)) ==> (C 1) := by
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
