import Untitled

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

inductive BenNat where
  | S : BenNat -> BenNat
  | Z : BenNat
  deriving Repr

def add (a b : BenNat) : BenNat :=
  match a with
  | BenNat.S c => add c (BenNat.S b)
  | BenNat.Z => b

open BenNat

#eval add (S Z) Z

theorem add_zero_left : forall a, add Z a = a := by
  intro a
  unfold add
  eq_refl

theorem add_one_left : forall a, (S a) = add (S Z) a := by
  intro a
  unfold add
  unfold add
  rfl

theorem add_one_succ : forall a b, add (S a) b = S (add a b) := by
  intro a
  induction a with
  | Z =>
    intro b
    unfold add
    apply add_zero_left
  | S x iHA =>
    intro b
    conv =>
      rhs
      unfold add
    rw [<- iHA]
    conv =>
      lhs
      unfold add

theorem add_zero_right : forall a, add a Z = a := by
  intro a
  induction a with
  | Z =>
    rw [add_zero_left]
  | S x iHA =>
    rw [add_one_succ, iHA]
