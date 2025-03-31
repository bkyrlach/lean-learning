inductive BenNat where
  | S : BenNat -> BenNat
  | Z : BenNat
  deriving Repr


inductive BenList (A: Type) where
  | Cons : A -> BenList A -> BenList A
  | Nil : BenList A


open BenList

def exList: BenList BenNat := Cons (BenNat.S BenNat.Z) Nil -- 1::Nil

def append (A: Type) (l1 l2: BenList A): BenList A :=
  match l1 with
  | BenList.Nil => l2
  | BenList.Cons a lguts => Cons a (append A lguts l2)
