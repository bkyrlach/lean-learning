inductive BenNat where
  | S : BenNat -> BenNat
  | Z : BenNat
  deriving Repr


/- forall (P: BenNat -> Prop) n,
 (BaseCase: P Z) ->
 ((IH: forall n', P n') -> P (S n')) ->
 P n
 -/
open BenNat

def two: BenNat := S (S Z)

def add (a b : BenNat) : BenNat :=
  match a with
  | BenNat.S aguts =>
     S (add aguts b)
  | BenNat.Z => b


theorem add_zero_left : forall a:BenNat, add Z a = a := by
  intro a
  unfold add
  eq_refl

theorem add_zero_right : forall a, add a Z = a := by
  intro a
  induction a with
  | Z => unfold add; eq_refl
  | S aguts IH =>
    unfold add
    rw [IH]

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

theorem add_assoc
