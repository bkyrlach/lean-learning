-- Declare a type `Prog` representing programs
axiom Prog : Type

-- Define a predicate `halts` that determines if a program halts
axiom halts : Prog → Prop

-- Assume decidability of the halting predicate for any program
axiom halt_dec : ∀ p : Prog, Decidable (halts p)

-- Assume the existence of a "diagonal" program
axiom diagonal : Prog → Prog

-- Define the behavior of the diagonal program using an axiom
axiom diagonalProg : ∀ p : Prog, halts (diagonal p) ↔ ¬ halts p

theorem Halt_False : ∃ p, halts p -> ¬ halts p := by
