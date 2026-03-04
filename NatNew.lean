inductive CBool where
| CTrue : CBool
| CFalse : CBool

open CBool

def CAnd(a b : CBool): CBool :=
  match (a, b) with
  | (CTrue, CTrue) => CTrue
  | _ => CFalse

def COr(a b : CBool): CBool :=
  match (a, b) with
  | (CTrue, _) => CTrue
  | (_, CTrue) => CTrue
  | _ => CFalse

def CNot(a : CBool): CBool :=
  match a with
  | CTrue => CFalse
  | CFalse => CTrue

theorem De_Morgans_Law : forall a b : CBool,
  CNot (CAnd a b) = COr (CNot a) (CNot b) := by
    intros a b
    cases a
    {
      cases b
      rfl
      rfl
    }
    {
      cases b
      rfl
      rfl
    }

inductive CNat where
| CZero : CNat -- 0
| CS : CNat -> CNat

open CNat

def one : CNat := CS CZero
def two : CNat := CS one

def one_is_one : one = one := Eq.refl one

def add (a b : CNat): CNat :=
 match a with
 | CZero => b
 | CS a' => CS (add a' b)

def sub (a b : CNat): CNat :=
 match a with
 | CZero => CZero
 | CS a' =>
  match b with
  | CZero => a
  | CS b' => (sub a' b')

-- This is the form of induction that we use below with some syntactic
-- sugar for a auto generated version of this for each inductive type
/- def nat_ind : forall (P : CNat -> Prop) n,
  P CZero ->
  (forall n' n, P n' -> P n) ->
  P n :=
   -/


theorem add_comm : forall a b: CNat, add a b = add b a := by
  intros a b
  induction a with
  | CZero => simp!
  | CS a' IH =>
    simp!
    rewrite [IH]
