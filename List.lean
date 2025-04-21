inductive BenNat where
  | S : BenNat -> BenNat
  | Z : BenNat
  deriving Repr


inductive BenList (A: Type u) where
  | Cons : A -> BenList A -> BenList A
  | Nil : BenList A


infixr:67 " :: " => BenList.Cons

open BenList

-- example: BenList Nat := 1::2::Nil


def squareAdd (x : Nat): Nat := (x ^ 2) + 5

example := [1, 2, 3]

/- syntax "[" x, ..., rest "]"

macro
| `([]) => Nil
| [$head, $tail] => Cons head (macro call tail)
 -/
def exList: BenList BenNat := Cons (BenNat.S BenNat.Z) Nil -- 1::Nil


inductive Permutation : Nat -> Type u where
  | NilP : forall n, Permutation n
  | ConsP : forall n, Permutation n


def append {A: Type} (l1 l2: BenList A): BenList A :=
  match l1 with
  | BenList.Nil => l2
  | BenList.Cons a lguts => Cons a (append lguts l2)


def length {A : Type} (l1 : BenList A): Nat :=
  match l1 with
  | BenList.Nil => 0
  | BenList.Cons _ lguts => 1 + (length lguts)

-- For ++ operator overload
instance {α} : Append (BenList α) where
  append := append

notation "|" xs "|" => length xs

-- To make proving theorems with this syntax ok.
@[simp] theorem nil_append (as : BenList α) : Nil ++ as = as := rfl
@[simp] theorem cons_append (a : α) (as bs : BenList α) : (a::as) ++ bs = a::(as ++ bs) := rfl

theorem length_append A : forall (l1 l2: BenList A),
  length (l1 ++ l2) = length l1 + length l2 := by
  intros l1 l2
  induction l1 with
  | Nil => simp!
  | Cons h t ih =>
    simp! [*, Nat.add_assoc]
