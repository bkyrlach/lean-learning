inductive BenBool where
  | T : BenBool
  | F : BenBool
  deriving Repr

def Band (a b : BenBool) : BenBool :=
  match a with
  | BenBool.T => b
  | BenBool.F => BenBool.F

def Bor (a b : BenBool) : BenBool :=
  match a with
  | BenBool.T => BenBool.T
  | BenBool.F => b

def Bnot (a : BenBool) : BenBool :=
  match a with
  | BenBool.T => BenBool.F
  | BenBool.F => BenBool.T

def Bxor (a b : BenBool) : BenBool :=
  match a with
  | BenBool.F => b
  | BenBool.T => Bnot b

theorem modus_ponens :
  forall (a b : BenBool),
  Bnot (Band a b) = Bor (Bnot a) (Bnot b) := by
    intro a
    intro b
    cases a
    cases b
    rfl
    rfl
    cases b
    rfl
    rfl
