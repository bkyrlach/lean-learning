/-
  GraphAlgebra.Relation

  Relational algebra formalization — the classical foundation that the
  graph algebra extends. Defines relations (tables), the standard operators
  (σ, π, ⋈, ∪, ∩, \), and their algebraic laws.
-/
import GraphAlgebra.Basic
import Mathlib.Data.List.Basic

namespace GraphAlgebra

/-! ## Relations

A relation is a bag (list) of records. We use `List Record` for simplicity,
treating duplicates as meaningful (bag semantics, matching SQL). -/

@[ext]
structure Relation where
  rows : List Record
  deriving Inhabited

namespace Relation

def empty : Relation := ⟨[]⟩

def size (r : Relation) : Nat := r.rows.length

/-! ## Selection (σ)

Filters rows by a predicate. The fundamental filtering operator. -/

def select (p : Record → Prop) [DecidablePred p] (r : Relation) : Relation :=
  ⟨r.rows.filter p⟩

/-! ## Projection (π)

Retains only specified attributes, discarding others. -/

def project (attrs : Finset AttrName) (r : Relation) : Relation :=
  ⟨r.rows.map (·.project attrs)⟩

/-! ## Union (∪)

Bag union of two relations. -/

def union (r₁ r₂ : Relation) : Relation :=
  ⟨r₁.rows ++ r₂.rows⟩

instance : Union Relation := ⟨union⟩

/-! ## Intersection (∩)

Retains rows present in both relations.
Requires decidable equality on records (which we approximate). -/

def inter (r₁ r₂ : Relation) (mem : Record → Record → Prop) [DecidableRel mem] : Relation :=
  ⟨r₁.rows.filter (fun row => r₂.rows.any (fun row' => decide (mem row row')))⟩

/-! ## Difference (\)

Removes from r₁ all rows present in r₂. -/

def diff (r₁ r₂ : Relation) (mem : Record → Record → Prop) [DecidableRel mem] : Relation :=
  ⟨r₁.rows.filter (fun row => !(r₂.rows.any (fun row' => decide (mem row row'))))⟩

/-! ## Cross Product (×)

Cartesian product of two relations. Foundation for joins. -/

def cross (r₁ r₂ : Relation) (combine : Record → Record → Record) : Relation :=
  ⟨r₁.rows.flatMap (fun row₁ => r₂.rows.map (fun row₂ => combine row₁ row₂))⟩

/-! ## Natural Join (⋈)

Join two relations on a predicate. -/

def join (r₁ r₂ : Relation) (combine : Record → Record → Record)
    (joinPred : Record → Record → Prop) [DecidableRel joinPred] : Relation :=
  ⟨r₁.rows.flatMap (fun row₁ =>
    (r₂.rows.filter (joinPred row₁)).map (combine row₁))⟩

/-! ## Algebraic Laws -/

section Laws

variable {p q : Record → Prop} [DecidablePred p] [DecidablePred q]

/-- Selection commutativity: σ_p(σ_q(R)) = σ_q(σ_p(R)) -/
theorem select_comm (r : Relation) :
    select p (select q r) = select q (select p r) := by
  simp only [select, Relation.mk.injEq]
  simp [List.filter_filter]
  congr 1; ext x; simp [Bool.and_comm]

/-- Conjunctive decomposition: σ_{p∧q}(R) = σ_p(σ_q(R)) -/
theorem select_conj (r : Relation) :
    select (fun x => p x ∧ q x) r = select p (select q r) := by
  simp only [select, Relation.mk.injEq]
  simp [List.filter_filter]

/-- Selection idempotence: σ_p(σ_p(R)) = σ_p(R) -/
theorem select_idem (r : Relation) :
    select p (select p r) = select p r := by
  simp only [select, Relation.mk.injEq]
  simp [List.filter_filter]

/-- Selection distributes over union: σ_p(R₁ ∪ R₂) = σ_p(R₁) ∪ σ_p(R₂) -/
theorem select_union_dist (r₁ r₂ : Relation) :
    select p (r₁ ∪ r₂) = select p r₁ ∪ select p r₂ := by
  simp only [select, Union.union, union, Relation.mk.injEq]
  simp [List.filter_append]

/-- Union is associative. -/
theorem union_assoc (r₁ r₂ r₃ : Relation) :
    (r₁ ∪ r₂) ∪ r₃ = r₁ ∪ (r₂ ∪ r₃) := by
  simp only [Union.union, union, Relation.mk.injEq]
  simp [List.append_assoc]

/-- Empty is a left identity for union. -/
theorem empty_union (r : Relation) :
    empty ∪ r = r := by
  simp only [Union.union, union, empty]
  simp

/-- Empty is a right identity for union. -/
theorem union_empty (r : Relation) :
    r ∪ empty = r := by
  simp only [Union.union, union, empty]
  simp

/-- Selection of empty is empty. -/
theorem select_empty : select p empty = empty := by
  simp only [select, empty, Relation.mk.injEq]
  simp

/-- Projection of empty is empty. -/
theorem project_empty (attrs : Finset AttrName) : project attrs empty = empty := by
  simp only [project, empty, Relation.mk.injEq]
  simp

/-- Projection idempotence: π_A(π_A(R)) = π_A(R) -/
theorem project_idem (attrs : Finset AttrName) (r : Relation) :
    project attrs (project attrs r) = project attrs r := by
  simp only [project, Relation.mk.injEq, List.map_map]
  congr 1
  ext rec
  simp only [Function.comp_apply, Record.project]
  congr 1
  funext k
  simp only [PropMap.restrict]
  split <;> simp_all

end Laws

end Relation

end GraphAlgebra
