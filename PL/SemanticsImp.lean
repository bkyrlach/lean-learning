inductive exp where
 | Const : Nat -> exp
 | Var :  String -> exp
 | Plus : exp -> exp -> exp
 | Times : exp -> exp -> exp
 deriving Repr

namespace exp

-- Notation for expressions
scoped notation:80 "‹" n "›" => exp.Const n
scoped notation:80 "⟨" s "⟩" => exp.Var s
scoped infixl:65 " ⊕ " => exp.Plus
scoped infixl:70 " ⊗ " => exp.Times

end exp

-- State maps variable names to optional values (partial function)
abbrev State := String → Option Nat

abbrev StateNate := List (String × Nat)

-- Interpreter for expressions (returns None if any variable is undefined)
def exp.eval (s : State) (e : exp) : Option Nat :=
  match e with
  | .Const n => some n
  | .Var x => s x
  | .Plus e₁ e₂ => do
      let v₁ ← e₁.eval s
      let v₂ ← e₂.eval s
      pure (v₁ + v₂)
  | .Times e₁ e₂ => do
      let v₁ ← e₁.eval s
      let v₂ ← e₂.eval s
      pure (v₁ * v₂)

section EvalExamples

open exp

-- Empty state (no variables defined)
def emptyState : State := fun _ => none

-- State with x = 5, y = 3
def exampleState : State := fun v =>
    if v == "x" then some 5
    else if v == "y" then some 3
    else none

def exampleStateRev : State := fun v =>
    if v == "y" then some 3
    else if v == "x" then some 5
    else none


theorem leibniz (A : Type) : ∀ (x y : A),
  (∀ P : A → Prop, P x ↔ P y) ↔ x = y := by
  intro x y
  constructor
  · -- Forward: if x and y satisfy all the same properties, then x = y
    intro h
    -- Use P := (· = x), then P x ↔ P y gives us (x = x) ↔ (y = x)
    have := h (· = x)
    simp at this
    exact this.symm
  · -- Backward: if x = y, then they satisfy the same properties
    intro heq P
    rw [heq]


axiom myfunext : forall f1 f2 : A -> B,
  (forall x, f1 x = f2 x) -> f1 = f2


def updateState (key: String) (value: Nat) (env: State): State :=
  fun v => if v == key then pure value else env v


#eval (‹5›).eval emptyState              -- some 5
#eval (‹3› ⊕ ‹4›).eval emptyState        -- some 7
#eval (⟨"x"⟩).eval exampleState          -- some 5
#eval (⟨"x"⟩ ⊕ ⟨"y"⟩).eval exampleState  -- some 8
#eval (⟨"x"⟩ ⊗ ‹2›).eval exampleState    -- some 10
#eval ((‹2› ⊕ ‹3›) ⊗ ⟨"x"⟩).eval exampleState  -- some 25
#eval (⟨"z"⟩).eval exampleState          -- none (undefined variable)
#eval (⟨"x"⟩ ⊕ ⟨"z"⟩).eval exampleState  -- none (z is undefined)

end EvalExamples

inductive stmt where
 -- Assign "v" (Const 2)
 | Skip : stmt
 | Assign : String -> exp -> stmt
 | Seq : stmt -> stmt -> stmt
 | If : exp -> stmt -> stmt -> stmt
 | While : exp -> stmt -> stmt

open exp
open stmt
namespace stmt

def evalStmt (fuel : Nat) (env : State) (stmt : stmt) : Option State := do
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stmt with
    | .Skip => pure env
    | .Assign var e => do
        let res ← e.eval env
        updateState var res env
    | .Seq s1 s2 => do
        let env' ← evalStmt fuel env s1
        evalStmt fuel env' s2
    | If e s1 s2 => do
        let cond ← e.eval env
        evalStmt fuel env (if cond == 0 then s2 else s1)
    | While e s => do
        let cond ← e.eval env
        if cond == 0 then pure env
        else do
          let env' ← evalStmt fuel env s
          evalStmt fuel env' (While e s)


set_option pp.fieldNotation.generalized false

-- Big-step (natural) semantics: (stmt, env) ⇓ env'
-- Relates a statement and initial state to a final state
inductive BigStep : stmt → State → State → Prop where
  | Skip {env} : BigStep .Skip env env

  | Assign {var v env env' e} :
      e.eval env = some v →
      env' = (updateState var v env) ->
      BigStep (.Assign var e) env env'

  | Seq {s1 env env' s2 env''} :
      BigStep s1 env env' →
      BigStep s2 env' env'' →
      BigStep (.Seq s1 s2) env env''

  | IfTrue {s1 env env' e s2} {cond : Nat} :
      e.eval env = some cond →
      cond ≠ 0 →
      BigStep s1 env env' →
      BigStep (.If e s1 s2) env env'

  | IfFalse {s2 env env' e s1} :
      e.eval env = some 0 →
      BigStep s2 env env' →
      BigStep (.If e s1 s2) env env'

  | WhileFalse {e s env} :
      e.eval env = some 0 →
      BigStep (.While e s) env env

  | WhileTrue {s env env' e env''} {cond : Nat} :
      e.eval env = some cond →
      cond ≠ 0 →
      BigStep s env env' →
      BigStep (.While e s) env' env'' →
      BigStep (.While e s) env env''


def emptyState: State := (fun _ => none)

example :
  BigStep (stmt.Assign "x" (exp.Const 1)) emptyState
    (updateState "x" 1 (updateState "x" 2 emptyState)) := by
  apply (BigStep.Assign (v := 1))
  ·
    unfold eval
    apply Eq.refl
  ·
    unfold updateState
    funext
    rename_i v

    by_cases h : (v = "x")
    -- Case: v = "x", both sides pick the first branch (some 1)
    ·
      subst h
      have Hx : "x" == "x" := by simp
      rw [Hx]
      have IfLaw : forall A (a b : A), (if true = true then a else b) = a := by
        intros a b
        simp
      rw [IfLaw]
      rw [IfLaw]







    -- Case: v ≠ "x", so both sides fall through to emptyState v
    · simp [h, emptyState]


/-
  Law1: For any big step evaluation we can add a small step at the begginning and consider the
    big step from what the small step evaluates to and get the same result as starting
    from the initial stmt

forall s s' env env' result_env,
  SmallStep (s, env) (s', env') /\ BigStep s env result_env ->
  BigStep s' env' result_env

Law2: We can apply Law1 any number of times.

H: SmallStep (v, {a = 1}) (Skip, {a = 1, b = 2})

inversion H.
  -
    // StepAssign
    H: SmallStep (Assign "b" (C 2)), {a = 1}) (Skip, {a = 1, b = 2}) |-
  -
  // StepSeq
    H: H: SmallStep (Seq st1 Assign "b" (C 2)), {a = 1}) (Skip, {a = 1, b = 2}) |-
  -
    ...

-/

inductive SmallStep : stmt × State -> stmt × State -> Prop where
  | StepAssign (env  env': State) (v : String) (e: exp) (value: Nat):

    e.eval env = some value ->

    env' = updateState v value env →

    SmallStep (Assign v e, env) (Skip, env')

  | StepSeq  :
    SmallStep (s₁, env) (s₁', env') ->
    SmallStep (Seq s₁ s₂, env) (Seq s₁' s₂, env')

  | StepSeqBaseCase  :

    SmallStep (Seq Skip s, env) (s, env)

  | StepIfTrue :
    e.eval env = some n ->
    n > 0 -> -- True
    SmallStep (If e thenStmt elseStmt, env) (thenStmt, env')

  | StepIfFalse :
    e.eval env = some n ->
    n = 0 ->
    SmallStep (If e thenStmt elseStmt, env) (thenStmt, env')

| StepWhileTrueIdea1 :
    e.eval env = some n ->
    n > 0 ->
    SmallStep (stmt1, env) (s', env') ->
    SmallStep (While e stmt1, env) (While e s', env')

| StepWhileTrueIdea2 :
    e.eval env = some n ->
    n > 0 ->
    SmallStep (While e stmt1, env) (Seq stmt1 (While e stmt1), env)

  | StepWhileFalse :
    e.eval env = some n ->
    n = 0 -> -- False
    SmallStep (While e stmt1, env) (Skip, env)



-- Compute the maximum element of a list (None for empty list)
def listMax : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl Nat.max x)

-- Predicate: elt is the maximum element of list l
def isMax (elt : Nat) (l : List Nat) : Prop :=
  elt ∈ l ∧ ∀ elt' ∈ l, elt' ≤ elt

-- Helper: foldl Nat.max acc l ≥ acc
theorem foldl_max_ge_acc (acc : Nat) (l : List Nat) :
    acc ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc acc ≤ Nat.max acc x := Nat.le_max_left acc x
         _ ≤ xs.foldl Nat.max (Nat.max acc x) := ih _

-- Helper: foldl Nat.max acc l ≥ each element in l
theorem foldl_max_ge_elem (acc : Nat) (l : List Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (Nat.le_max_right acc x) (foldl_max_ge_acc _ _)
    · exact ih _ hx'

-- Helper: foldl Nat.max acc l is either acc or in l
theorem foldl_max_mem_or_eq (acc : Nat) (l : List Nat) :
    l.foldl Nat.max acc = acc ∨ l.foldl Nat.max acc ∈ l := by
  induction l generalizing acc with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (Nat.max acc x) with h | h
    · -- foldl result = max acc x
      rw [h]
      rcases Nat.le_total acc x with hle | hgt
      · right; simp [Nat.max_eq_right hle]
      · left; simp [Nat.max_eq_left hgt]
    · -- foldl result ∈ xs
      right; exact List.mem_cons_of_mem x h

-- Equivalence theorem
theorem listMax_iff_isMax (l : List Nat) (elt : Nat) :
    listMax l = some elt ↔ isMax elt l := by
  cases l with
  | nil =>
    simp only [listMax, isMax, List.not_mem_nil, false_and, iff_false]
    intro h; cases h
  | cons x xs =>
    simp only [listMax, Option.some.injEq, isMax]
    constructor
    · -- Forward: foldl result = elt → isMax elt (x :: xs)
      intro h
      constructor
      · -- elt ∈ x :: xs
        rcases foldl_max_mem_or_eq x xs with heq | hmem
        · rw [← h, heq]; exact List.mem_cons_self
        · rw [← h]; exact List.mem_cons_of_mem x hmem
      · -- ∀ elt' ∈ x :: xs, elt' ≤ elt
        intro elt' helt'
        rw [← h]
        rcases List.mem_cons.mp helt' with rfl | hmem
        · exact foldl_max_ge_acc elt' xs
        · exact foldl_max_ge_elem x xs elt' hmem
    · -- Backward: isMax elt (x :: xs) → foldl result = elt
      intro ⟨hmem, hmax⟩
      apply Nat.le_antisymm
      · -- xs.foldl Nat.max x ≤ elt
        rcases foldl_max_mem_or_eq x xs with heq | hmem'
        · rw [heq]; exact hmax x List.mem_cons_self
        · exact hmax _ (List.mem_cons_of_mem x hmem')
      · -- elt ≤ xs.foldl Nat.max x
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact foldl_max_ge_acc elt xs
        · exact foldl_max_ge_elem x xs elt hmem'

/-
  Set-theoretic characterization of FavoriteNumbers:

  Base = {("Nate", 2), ("Nate", 10)}

  FavoriteNumbers is the smallest set such that:
    Base ⊆ FavoriteNumbers
  ∧ ∀ n, ("Nate", n) ∈ FavoriteNumbers → ("David", n) ∈ FavoriteNumbers

  Equivalently, as a membership predicate:
    (name, n) ∈ FavoriteNumbers ↔
        (name, n) ∈ Base
      ∨ (name = "David" ∧ ("Nate", n) ∈ FavoriteNumbers)
-/


inductive FavoriteNumbers : String -> Nat -> Prop where
  | Likes2 : FavoriteNumbers "Nate" 2

  | Likes10 : FavoriteNumbers "Nate" 10

  -- | LikesFriends : forall n,
  --   FavoriteNumbers "Nate" n ->
  --   FavoriteNumbers "David" n

  -- | LikesBen : forall n m,
  --   FavoriteNumbers "Nate" n ->
  --   n != m ->
  --   FavoriteNumbers "Ben" m

  -- | likesMult : forall n1 n2 name,
  --   FavoriteNumbers name n1 ->
  --   FavoriteNumbers name n2 ->
  --   FavoriteNumbers name (n1 * n2)

-- Strict positivity paradox demonstration
-- This would be rejected by the kernel:
-- But we can bypass with unsafe to see the paradox:
unsafe inductive Liar : Type where
  | mk : (Liar → False) → Liar

unsafe def NoLiar (b : Liar) : Liar -> False :=
  match b with
  | Liar.mk f => f

unsafe def badImpliesFalse : Liar → False := by
  intro a
  cases a with
  | mk f =>
    apply f
    apply Liar.mk f




unsafe def aBad : Liar := Liar.mk badImpliesFalse

-- A "proof" of False from nothing! (unsound due to unsafe)
unsafe def oops : False := badImpliesFalse aBad

-- Assume a halting oracle exists (seems reasonable for termination proofs!)
axiom halts : (Nat → Option Nat) → Nat → Bool
axiom halts_true : ∀ f n, halts f n = true → ∃ v, f n = some v
axiom halts_false : ∀ f n, halts f n = false → f n = none

-- Gödel encoding: functions ↔ natural numbers
axiom encodeHalt : (Nat → Option Nat) → Nat
axiom decodeHalt : Nat → (Nat → Option Nat)
axiom encode_decode_halt : ∀ f, decodeHalt (encodeHalt f) = f

-- Helper function for the termination argument
noncomputable def diagonal (n : Nat) : Option Nat :=
  if halts (decodeHalt n) n then none else some 0

noncomputable def d : Nat := encodeHalt diagonal

-- The "original" interpreter without fuel
-- Termination uses properties of the halting oracle
noncomputable def evalStmtNoFuel (env : State) (s : stmt) : Option State :=
  match s with
  | .Skip => some env
  | .Assign var e => do
      let res ← e.eval env
      updateState var res env
  | .Seq s1 s2 => do
      let env' ← evalStmtNoFuel env s1
      evalStmtNoFuel env' s2
  | .If e s1 s2 => do
      let cond ← e.eval env
      if cond == 0 then evalStmtNoFuel env s2
      else evalStmtNoFuel env s1
  | .While e s => do
      let cond ← e.eval env
      if cond == 0 then some env
      else do
        let env' ← evalStmtNoFuel env s
        evalStmtNoFuel env' (.While e s)
termination_by (env, s)
decreasing_by
  -- Termination proof: case analysis on whether diagonal halts on itself
  all_goals (
    have h1 : decodeHalt d = diagonal := encode_decode_halt diagonal
    cases hd : halts diagonal d with
    | false =>
      have h2 : diagonal d = none := halts_false diagonal d hd
      unfold diagonal at h2
      rw [h1, hd] at h2
      simp at h2
    | true =>
      obtain ⟨v, h2⟩ := halts_true diagonal d hd
      unfold diagonal at h2
      rw [h1, hd] at h2
      simp at h2
  )

-- ═══════════════════════════════════════════════════════════════════════════
-- Hmm, wait... that proof looks suspicious. Let's see what else it proves...
-- ═══════════════════════════════════════════════════════════════════════════

-- The SAME proof proves False!
theorem halting_paradox : False := by
  have h1 : decodeHalt d = diagonal := encode_decode_halt diagonal
  cases hd : halts diagonal d with
  | false =>
    have h2 : diagonal d = none := halts_false diagonal d hd
    unfold diagonal at h2
    rw [h1, hd] at h2
    simp at h2
  | true =>
    obtain ⟨v, h2⟩ := halts_true diagonal d hd
    unfold diagonal at h2
    rw [h1, hd] at h2
    simp at h2

-- Our "reasonable" axioms about the halting oracle are inconsistent!
-- The halting problem is undecidable - no such oracle can exist.

-- Notation for big-step semantics
scoped infix:10 " ⇓ " => BigStep

/-
══════════════════════════════════════════════════════════════════════════════
                        PROOF TREE EXAMPLES
══════════════════════════════════════════════════════════════════════════════

Notation: We write ⟨s, σ⟩ ⇓ σ' to mean "statement s in state σ evaluates to σ'"

─────────────────────────────────────────────────────────────────────────────
Example 1: Simple Assignment
─────────────────────────────────────────────────────────────────────────────

Program: x := 5
Initial state: σ = {}

              ----------------------------------( by refl)
                6 = 6
               -------------------------------- (by computation )
                    ‹5 + 1›.eval {} = some 6
                ─────────────────────────────── (Assign)
                  ⟨x := 5 + 1, {}⟩ ⇓ {x ↦ 6}


─────────────────────────────────────────────────────────────────────────────
Example 2: Sequence of Assignments (Big-Step)
─────────────────────────────────────────────────────────────────────────────

Program: x := 1; y := 2
Initial state: σ = {}

      ‹1›.eval {} = some 1                ‹2›.eval {x↦1} = some 2
    ─────────────────────────(Assign)   ───────────────────────────(Assign)
     ⟨x := 1, {}⟩ ⇓ {x↦1}                ⟨y := 2, {x↦1}⟩ ⇓ {x↦1, y↦2}
    ─────────────────────────────────────────────────────────────────(Seq)
                  ⟨x := 1; y := 2, {}⟩ ⇓ {x↦1, y↦2}


─────────────────────────────────────────────────────────────────────────────
Example 2b: Same Program in Small-Step Semantics
─────────────────────────────────────────────────────────────────────────────

Program: x := 1; y := 2    Initial state: σ = {}

Using →* for reflexive-transitive closure of →

                         ‹1›.eval {} = some 1
                       ───────────────────────(Assign)
                       ⟨x:=1, {}⟩ → ⟨skip, {x↦1}⟩                   ‹2›.eval {x↦1} = some 2
                    ───────────────────────────────(Seq-Step)     ─────────────────────────(Assign)
                    ⟨x:=1; y:=2, {}⟩ → ⟨skip; y:=2, {x↦1}⟩        ⟨y:=2, {x↦1}⟩ → ⟨skip, {x↦1,y↦2}⟩
                    ─────────────────────────────────────────(Seq-Skip)  ────────────────────────────
                              ⟨skip; y:=2, {x↦1}⟩ → ⟨y:=2, {x↦1}⟩              │
                    ───────────────────────────────────────────────────────────────────────(Trans)
                                        ⟨x:=1; y:=2, {}⟩ →* ⟨skip, {x↦1, y↦2}⟩

Step-by-step trace:

x := 1

⟨ x := 1, {} ⟩ ==>> (skip, {x ↦ 1})


  ⟨x:=1; y:=2, {}⟩
       │
       │  ‹1›.eval {} = some 1
       │  ─────────────────────(Assign)         ⟨x:=1, {}⟩ → ⟨skip, {x↦1}⟩
       │  ─────────────────────────────(Seq-Step)
       ↓
  ⟨skip; y:=2, {x↦1}⟩
       │
       │  ─────────────────────(Seq-Skip)
       ↓
  ⟨y:=2, {x↦1}⟩
       │
       │  ‹2›.eval {x↦1} = some 2
       │  ─────────────────────────(Assign)
       ↓
  ⟨skip, {x↦1, y↦2}⟩   ← terminal configuration


{} |- ⟨skip, {x↦1, y↦2}⟩
-----------------------
{} |- ⟨s1, {x↦1, y↦2}⟩




─────────────────────────────────────────────────────────────────────────────
Example 3: If-True Branch
─────────────────────────────────────────────────────────────────────────────

Program: if x then y := 1 else y := 0
State: σ = {x ↦ 5}

                                    ‹1›.eval {x↦5} = some 1
   ⟨"x"⟩.eval {x↦5} = some 5      ─────────────────────────────(Assign)
         5 ≠ 0                       ⟨y := 1, {x↦5}⟩ ⇓ {x↦5, y↦1}
  ──────────────────────────────────────────────────────────────────(IfTrue)
          ⟨if x then y := 1 else y := 0, {x↦5}⟩ ⇓ {x↦5, y↦1}


─────────────────────────────────────────────────────────────────────────────
Example 4: If-False Branch
─────────────────────────────────────────────────────────────────────────────

Program: if x then y := 1 else y := 0
State: σ = {x ↦ 0}

                                    ‹0›.eval {x↦0} = some 0
   ⟨"x"⟩.eval {x↦0} = some 0      ─────────────────────────────(Assign)
                                     ⟨y := 0, {x↦0}⟩ ⇓ {x↦0, y↦0}
  ──────────────────────────────────────────────────────────────────(IfFalse)
          ⟨if x then y := 1 else y := 0, {x↦0}⟩ ⇓ {x↦0, y↦0}


─────────────────────────────────────────────────────────────────────────────
Example 5: While Loop (terminates after 2 iterations)
─────────────────────────────────────────────────────────────────────────────

Program: while x do x := x - 1  (pretend we have subtraction)
State: σ = {x ↦ 2}

The full tree (reading bottom-up, this unrolls the loop):

                                                 ⟨"x"⟩.eval {x↦0} = some 0
                                                ──────────────────────────(WhileFalse)
                        D₁                      ⟨while x do x:=x-1, {x↦0}⟩ ⇓ {x↦0}
   ⟨"x"⟩.eval {x↦1} = some 1   ─────────(Assign)  ────────────────────────────────────
         1 ≠ 0                 ⟨x:=x-1,{x↦1}⟩⇓{x↦0}
   ────────────────────────────────────────────────────────────────────────(WhileTrue)
                         ⟨while x do x:=x-1, {x↦1}⟩ ⇓ {x↦0}
                                     ╲
                                      ╲  (this is D₁ above)
                                       ╲
                                  D₀    ╲           D₁
   ⟨"x"⟩.eval {x↦2} = some 2  ─────────(Assign)  ─────────────────────────
         2 ≠ 0                ⟨x:=x-1,{x↦2}⟩⇓{x↦1}  (from above)
   ────────────────────────────────────────────────────────────────────────(WhileTrue)
                         ⟨while x do x:=x-1, {x↦2}⟩ ⇓ {x↦0}


─────────────────────────────────────────────────────────────────────────────
Example 6: Nested Sequence with Expression
─────────────────────────────────────────────────────────────────────────────

Program: x := 2; y := 3; z := x + y
Initial state: σ = {}

Let σ₁ = {x↦2}, σ₂ = {x↦2, y↦3}, σ₃ = {x↦2, y↦3, z↦5}

                                                (⟨"x"⟩⊕⟨"y"⟩).eval σ₂ = some 5
       ───────────(Assign)    ───────────(Assign)    ─────────────────────(Assign)
       ⟨x:=2,{}⟩⇓σ₁           ⟨y:=3,σ₁⟩⇓σ₂            ⟨z:=x+y, σ₂⟩ ⇓ σ₃
       ─────────────────────────────────(Seq)         ────────────────────
              ⟨x:=2; y:=3, {}⟩ ⇓ σ₂                          │
       ─────────────────────────────────────────────────────────────────(Seq)
                      ⟨x:=2; y:=3; z:=x+y, {}⟩ ⇓ σ₃


─────────────────────────────────────────────────────────────────────────────
Reading Proof Trees
─────────────────────────────────────────────────────────────────────────────

• Premises go ABOVE the line
• Conclusion goes BELOW the line
• Rule name is on the right in parentheses
• To verify: check that premises match the rule's requirements
• Trees compose: conclusions of sub-derivations become premises

The BigStep relation is deterministic: given (s, σ), there is at most one σ'
such that ⟨s, σ⟩ ⇓ σ'. The proof tree is unique (up to the derivation structure).

══════════════════════════════════════════════════════════════════════════════
-/


-- Notation for statements
scoped notation:20 "SKIP " s => stmt.Skip s
scoped notation:30 s " ::= " e => stmt.Assign s e
scoped infixr:25 " ;; " => stmt.Seq
scoped notation:15 "IF " c " THEN " t " ELSE " f " END" => stmt.If c t f
scoped notation:15 "WHILE " c " DO " b " END" => stmt.While c b

end stmt

-- Example programs using the notation
section Examples

open exp stmt

-- x := 5
#check ("x" ::= ‹5›)

-- x := 3 + 4
#check ("x" ::= ‹3› ⊕ ‹4›)

-- x := y * 2
#check ("x" ::= ⟨"y"⟩ ⊗ ‹2›)

-- x := 1; y := 2
#check ("x" ::= ‹1›) ;; ("y" ::= ‹2›)

-- x := 1; y := 2; z := x + y
#check ("x" ::= ‹1›) ;; ("y" ::= ‹2›) ;; ("z" ::= ⟨"x"⟩ ⊕ ⟨"y"⟩)

-- if x then y := 1 else y := 0
#check IF ⟨"x"⟩ THEN ("y" ::= ‹1›) ELSE ("y" ::= ‹0›) END

-- while x do x := x + 1
#check WHILE ⟨"x"⟩ DO ("x" ::= ⟨"x"⟩ ⊕ ‹1›) END

-- Factorial-like program:
-- result := 1; while n do (result := result * n; n := n - 1)
-- (Note: we don't have minus, but this shows the structure)
#check ("result" ::= ‹1›) ;;
       (WHILE ⟨"n"⟩ DO
         (("result" ::= ⟨"result"⟩ ⊗ ⟨"n"⟩) ;;
          ("n" ::= ⟨"n"⟩ ⊕ ‹0›))  -- placeholder since no minus
       END)

end Examples
