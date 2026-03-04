#print And

set_option pp.proofs true

-- Configure simp with beta reduction (and other reductions)
-- beta: (fun x => e) a → e[x := a]
-- zeta: let x := a in e → e[x := a]
-- iota: match/recursor reduction
-- eta: (fun x => f x) → f

-- Example using simp with explicit beta config:
example : (fun x => x + 1) 5 = 6 := by simp (config := { beta := true })

-- You can also use simp_all or create a custom simp macro:
macro "simp_beta" : tactic => `(tactic| simp (config := { beta := true, zeta := true, iota := true }))

-- Now you can use simp_beta in proofs:
example : (fun x y => x + y) 3 4 = 7 := by simp_beta

open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := by
  unfold add
  exact rfl

theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := by
  rfl

theorem zero_add : ∀ n, add zero n = n := by
  intros n





def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)

axiom cows_are_purple : Prop

structure blah where
  x : Nat
  x_pf : x < 10

#eval (· , ·) 1 2

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => show not (not true) = true from rfl
  | false => show not (not false) = false from rfl

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)



theorem of_decjklide_eq_true [inst : Decidable p] : Eq (decide p) true → p := fun h => by
  apply (match (generalizing := false) inst with
  | isTrue  h₁ => h₁
  | isFalse h₁ => absurd h (ne_true_of_eq_false (decide_eq_false h₁)))

def x: blah := by
  apply (blah.mk 5 (by decide))


#print x
#print x._proof_1
#print of_decide_eq_true



def y: blah := by
  apply (blah.mk 5)
  -- Proving 5 < 10 manually
  -- 5 < 10 means Nat.succ 4 < 10
  apply Nat.succ_lt_succ
  -- Now need to prove 4 < 9
  apply Nat.succ_lt_succ
  -- Now need to prove 3 < 8
  apply Nat.succ_lt_succ
  -- Now need to prove 2 < 7
  apply Nat.succ_lt_succ
  -- Now need to prove 1 < 6
  apply Nat.succ_lt_succ
  -- Now need to prove 0 < 5
  apply Nat.zero_lt_succ
#print y
#print y._proof_1

example : x = y := by
  unfold x y
  unfold x._proof_1 y._proof_1
  simp




-- ============================================================
-- DECIDABLE TYPE CLASS EXAMPLES
-- ============================================================

#print Decidable

-- Decidable is defined as:
-- inductive Decidable (p : Prop) : Type where
--   | isFalse (h : ¬p) : Decidable p
--   | isTrue  (h : p)  : Decidable p

-- It's a type class that witnesses whether a proposition is computably decidable

-- Example 1: Using decide tactic (requires Decidable instance)
example : 5 < 10 := by decide


-- Example 2: Using decide for equality
example : 3 + 2 = 5 := by decide

-- Example 3: Manual use of Decidable instance
def check_lt : Decidable (5 < 10) := inferInstance

#eval match check_lt with
  | Decidable.isTrue _ => "5 is less than 10"
  | Decidable.isFalse _ => "5 is not less than 10"

-- Example 4: Building a Decidable instance manually
def myDecidable : Decidable (2 + 2 = 4) :=
  Decidable.isTrue (by decide)

-- Example 5: Using Decidable with if-then-else (decidable propositions)
def checkNumber (n : Nat) : String :=
  if n < 10 then
    "less than 10"
  else
    "not less than 10"

#eval checkNumber 5  -- "less than 10"
#eval checkNumber 15 -- "not less than 10"

-- Example 6: Extracting proof from Decidable
def proveLessThan : 5 < 10 :=
  match inferInstance (α := Decidable (5 < 10)) with
  | Decidable.isTrue h => h
  | Decidable.isFalse _ => by contradiction

-- Example 7: Custom decidable proposition
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k

-- We can make our own decidable instance (simplified version)
def decideEvenSmall : (n : Nat) → Decidable (n % 2 = 0)
  | _ => inferInstance  -- Nat.decEq provides this

-- Example 8: Using decidability to get computational content
def isLessThan10 (n : Nat) : Bool :=
  if n < 10 then true else false

#eval isLessThan10 5   -- true
#eval isLessThan10 15  -- false

-- Example 9: The `decide` function (not tactic)
-- decide : {p : Prop} → [Decidable p] → Bool
#check @decide

def useDecideFunction : Bool :=
  decide (5 < 10)  -- Evaluates to true

#eval useDecideFunction  -- true

-- Example 10: Decidable for And, Or, Not
example : Decidable (5 < 10 ∧ 3 < 7) := inferInstance
example : Decidable (5 < 3 ∨ 2 < 4) := inferInstance
example : Decidable (¬(10 < 5)) := inferInstance

-- ============================================================

theorem test2 (hp: cows_are_purple) (hp_: cows_are_purple): hp = hp_ :=
  by
    simp

def main : IO Unit := IO.println "Hello"
def asdf: Nat :=
  match 2 with
  | 2 => sorry
  | _ => sorry


variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  simp [*]

  -- have H: x = z := by apply Eq.trans h₁ h₂


/- theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro (by sorry) (by sorry)
 -/


/-   apply And.intro
  case left =>
    exact hp
  case right =>
    apply And.intro
    case left => assumption
    case right => assumption
 -/

def foo (n : Nat): Prop := True

def test (p q : Prop) (hp : p) (hq : q):  p ∧ q := by
  constructor
  exact hp
  exact hq

def applyTest: (foo 3) ∧ (foo 7) :=
  test (foo 3) (foo 7) True.intro True.intro


example (p q : α → Prop) t : t -> (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro t ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩


variable (arg : Int)

def asdf := arg

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, ⟨hpw, hqw⟩⟩
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  unhygienic
  intro
  | ⟨ w, Or.inl l⟩ => sorry
  | ⟨ w, Or.inr r⟩ => sorry



theorem testn (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>


    sorry




  case left => sorry
