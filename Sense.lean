import Mathlib.Data.Set.Basic
open Set


/-

# even : Nat → Prop

------------------------------------------------------  [even0]
 ⊢ 0 ∈ even


 ⊢ n ∈ even
------------------------------------------------------  [even2]
 ⊢ n + 2 ∈ even

0 ∈ even apply even0

2 ∈ even  apply even2

4 ∈ even  apply even2



-/

-- Operational Semantics
inductive even : Nat -> Prop where
  | even0 : even 0
  | even2 : forall n, even n -> even n.succ.succ

open even

-- Axiomic
axiom evenA : Nat -> Prop
axiom evenA0 : evenA 0
axiom evenA2 : forall n, evenA n -> evenA n.succ.succ
axiom evenA2k : forall n, evenA n -> exists k, n = 2 * k

-- Denotational
def even_without_rules (n : Nat): Prop := exists k, n = 2 * k
def even_without_rules_bool (n : Nat): Prop := n % 2 = 0

def even_extension: Set Nat := {n : Nat | even_without_rules n }















theorem exProof : even_without_rules 2 := by
  apply Exists.intro 1
  apply Eq.refl

theorem exProofRules : even 2 := by
  apply even2
  apply even0

def ext_comparison A B (f g : A -> B): Prop :=
  forall x, f x = g x -> f = g

def even_ext_finite := [0, 2, 4]

-- Is this an intensional definition?
def is_even (n : Nat) := n ∈ even_ext_finite

def f : Nat → Nat := fun n => 0 + n
def g : Nat → Nat := fun n => n

abbrev NatFun := Nat → Nat

def fun_ext1 (f g : NatFun) : Prop := ∀ n, f n = g n → f = g
def fun_ext2 (f g : NatFun) : Prop := ∀ n, f (n + 0) = g (n + 0) → f = g

theorem p_eq : ∀ f g, fun_ext1 f g ↔ fun_ext2 f g := by
  intro f g
  constructor
  · simp [fun_ext1, fun_ext2]
  · simp [fun_ext1, fun_ext2]
