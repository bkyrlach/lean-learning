/-
  GraphAlgebra

  A Lean 4 formalization of a practical graph algebra for query optimization.

  Based on "Toward a Practical Graph Algebra: Tractable Algebraic Foundations
  for Graph Query Optimization" by Ryan Wright (2026).

  The formalization covers:
  - The structural hierarchy: Value → Record → Table → Tree → Graph
  - Relational algebra: σ, π, ⋈, ∪, ∩, \ with algebraic laws
  - Property graphs: labeled directed graphs with node/edge properties
  - Graph algebra operators: σ_N, σ_E, π_G, ∪_G, ∩_G, \G, ⊔, ↑, ↓, TC, ⋈_P
  - Algebraic laws: selection pushdown, commutativity, distributivity,
    monotonicity, pattern decomposition foundations, schema-based pruning
-/
import GraphAlgebra.Basic
import GraphAlgebra.Relation
import GraphAlgebra.Graph
import GraphAlgebra.Operators
import GraphAlgebra.Laws
import GraphAlgebra.Induction
import GraphAlgebra.Lawler
