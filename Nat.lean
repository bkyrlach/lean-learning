inductive BenNat where
  | S : BenNat -> BenNat
  | Z : BenNat
  deriving Repr

open BenNat

theorem foo : forall (P : BenNat -> Prop) n, P Z ->
  (forall n', P n' -> P (S n')) -> P n := by
  intro P
  intro n
  intro Hzero
  intro Hsucc
  match n with
  | Z => exact Hzero
  | S n' =>
    have thing := Hsucc n'
    apply Hsucc
    apply foo
    exact Hzero
    exact Hsucc

def two: BenNat := S (S Z)

def add (a b : BenNat) : BenNat :=
  match a with
  | BenNat.S aguts =>
     S (add aguts b)
  | BenNat.Z => b

#eval add (S Z) Z

theorem add_zero_left : forall a, add Z a = a := by
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

theorem add_zero_right_other : forall a, add a Z = a := by
  intro a
  induction a with
  | Z =>
    rw [add_zero_left]
  | S x iHA =>
    rw [add_one_succ, iHA]


def indRec (n: BenNat) : forall (P : BenNat -> Prop), P Z ->
 (forall n', P n' -> P (S n')) -> P n :=
  match n with
  | Z => fun _ BC _ => BC
  | S nguts =>
    fun P BC IH =>
      let bleh := (indRec nguts P BC IH)
      (IH nguts bleh)
