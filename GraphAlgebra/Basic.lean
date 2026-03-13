/-
  GraphAlgebra.Basic

  Foundation types for the graph algebra formalization.
  Implements the structural hierarchy from the proposal:
    Value → Record → Table → Tree → Graph

  Based on "Toward a Practical Graph Algebra" by Ryan Wright (2026).
-/
import Mathlib.Data.Finset.Basic

namespace GraphAlgebra

/-! ## Values

Values are the atomic elements of the hierarchy — scalars with no
internal structure that the algebra cares about. -/

inductive Value where
  | nat  : Nat → Value
  | int  : Int → Value
  | str  : String → Value
  | bool : Bool → Value
  deriving DecidableEq, Repr, Inhabited

/-! ## Attribute Names and Property Maps -/

abbrev AttrName := String

/-- A property map assigns optional values to attribute names. -/
def PropMap := AttrName → Option Value

instance : Inhabited PropMap := ⟨fun _ => none⟩

def PropMap.empty : PropMap := fun _ => none

def PropMap.set (m : PropMap) (k : AttrName) (v : Value) : PropMap :=
  fun k' => if k' == k then some v else m k'

def PropMap.get (m : PropMap) (k : AttrName) : Option Value := m k

def PropMap.remove (m : PropMap) (k : AttrName) : PropMap :=
  fun k' => if k' == k then none else m k'

/-- Restrict a property map to a set of attribute names. -/
def PropMap.restrict (m : PropMap) (attrs : Finset AttrName) : PropMap :=
  fun k => if k ∈ attrs then m k else none

/-- Merge two property maps. Left-wins on conflicts. -/
def PropMap.merge (m₁ m₂ : PropMap) : PropMap :=
  fun k => match m₁ k with
    | some v => some v
    | none => m₂ k

/-- Two property maps agree on all keys where both are defined. -/
def PropMap.compatible (m₁ m₂ : PropMap) : Prop :=
  ∀ k, m₁ k ≠ none → m₂ k ≠ none → m₁ k = m₂ k

/-! ## Records

A Record is the composition of finitely many values — the atomic element
of relational algebra. We model it as a property map (named tuple). -/

structure Record where
  props : PropMap
  deriving Inhabited

def Record.get (r : Record) (attr : AttrName) : Option Value :=
  r.props attr

def Record.set (r : Record) (attr : AttrName) (v : Value) : Record :=
  ⟨r.props.set attr v⟩

/-- Project a record onto a subset of attributes. -/
def Record.project (r : Record) (attrs : Finset AttrName) : Record :=
  ⟨r.props.restrict attrs⟩

/-! ## Schema

A schema describes the expected attribute names for a relation. -/

structure Schema where
  attrs : Finset AttrName
  deriving Inhabited

/-! ## Predicates

Predicates over property maps, used in selection operators.
We keep predicates as functions but provide combinators. -/

def Pred (α : Type) := α → Prop

namespace Pred

def true_ : Pred α := fun _ => True
def false_ : Pred α := fun _ => False
def and_ (p q : Pred α) : Pred α := fun x => p x ∧ q x
def or_ (p q : Pred α) : Pred α := fun x => p x ∨ q x
def not_ (p : Pred α) : Pred α := fun x => ¬ p x

/-- A predicate that checks a specific attribute against a value. -/
def attrEq (attr : AttrName) (v : Value) : Pred PropMap :=
  fun m => m attr = some v

end Pred

/-! ## Decidable Predicates

For computational purposes, we often need decidable predicates. -/

structure DecPred (α : Type) where
  pred : α → Prop
  dec  : DecidablePred pred

instance (dp : DecPred α) (x : α) : Decidable (dp.pred x) := dp.dec x

namespace DecPred

def true_ : DecPred α where
  pred := fun _ => True
  dec  := fun _ => isTrue trivial

def and_ (p q : DecPred α) : DecPred α where
  pred := fun x => p.pred x ∧ q.pred x
  dec  := fun x => by
    have := p.dec x
    have := q.dec x
    exact instDecidableAnd

def or_ (p q : DecPred α) : DecPred α where
  pred := fun x => p.pred x ∨ q.pred x
  dec  := fun x => by
    have := p.dec x
    have := q.dec x
    exact instDecidableOr

def not_ (p : DecPred α) : DecPred α where
  pred := fun x => ¬ p.pred x
  dec  := fun x => by
    have := p.dec x
    exact instDecidableNot

/-- The set of attributes that a predicate references.
    This is important for commutativity with projection (C² condition). -/
def attrs (p : DecPred PropMap) : Finset AttrName := sorry -- opaque, user-specified

end DecPred

/-! ## The Structural Hierarchy ("The Kite")

We formalize the five levels as an inductive type representing
the compositional complexity of data structures. -/

inductive DataLevel where
  | value   : DataLevel  -- scalar, no internal structure
  | record  : DataLevel  -- finite composition of values
  | table   : DataLevel  -- flat composition of records (relational)
  | tree    : DataLevel  -- nested composition of records (NF²)
  | graph   : DataLevel  -- composition with sharing and cycles
  deriving DecidableEq, Repr

/-- The structural ordering: each level adds compositional complexity. -/
instance : LE DataLevel where
  le a b := match a, b with
    | .value, _      => True
    | .record, .value => False
    | .record, _     => True
    | .table, .value | .table, .record => False
    | .table, _      => True
    | .tree, .graph | .tree, .tree => True
    | .tree, _       => False
    | .graph, .graph => True
    | .graph, _      => False

instance : LT DataLevel where
  lt a b := a ≤ b ∧ ¬ b ≤ a

end GraphAlgebra
