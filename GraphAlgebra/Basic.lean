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

/-- The finite support of a property map: the set of attribute names with non-none values.
    This requires the user to specify it explicitly since PropMap is a function type. -/
structure SupportedPropMap where
  map : PropMap
  support : Finset AttrName
  support_spec : ∀ k, k ∉ support → map k = none

/-- Restrict a property map to a set of attribute names. -/
def PropMap.restrict (m : PropMap) (attrs : Finset AttrName) : PropMap :=
  fun k => if k ∈ attrs then m k else none

/-- Restricting a supported prop map to its support is the identity. -/
theorem PropMap.restrict_support (sm : SupportedPropMap) :
    sm.map.restrict sm.support = sm.map := by
  funext k
  simp only [PropMap.restrict]
  split
  · rfl
  · exact (sm.support_spec k ‹_›).symm ▸ rfl

/-- Restricting to a superset of the support is also the identity. -/
theorem PropMap.restrict_superset (sm : SupportedPropMap) (attrs : Finset AttrName)
    (h : sm.support ⊆ attrs) :
    sm.map.restrict attrs = sm.map := by
  funext k
  simp only [PropMap.restrict]
  split
  · rfl
  · exact (sm.support_spec k (fun hk => ‹k ∉ attrs› (h hk))).symm ▸ rfl

/-- Restricting to a subset of a superset equals restricting to the subset directly. -/
theorem PropMap.restrict_restrict_subset (m : PropMap) (s t : Finset AttrName) (h : s ⊆ t) :
    (m.restrict t).restrict s = m.restrict s := by
  funext k
  simp only [PropMap.restrict]
  split
  · split
    · rfl
    · exact absurd (h ‹_›) ‹_›
  · rfl

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

end DecPred

/-! ## Property Map Predicates

A decidable predicate over `PropMap` that explicitly tracks which attributes it
references. This enables the C² commutativity condition: `σ_p(π_A(G)) = π_A(σ_p(G))`
whenever `attrs p ⊆ A`. -/

structure PropPred where
  pred : PropMap → Prop
  dec  : DecidablePred pred
  attrs : Finset AttrName
  attrs_spec : ∀ m, pred m ↔ pred (m.restrict attrs)

instance (pp : PropPred) (m : PropMap) : Decidable (pp.pred m) := pp.dec m

/-- Coerce a `PropPred` to a `DecPred PropMap`. -/
def PropPred.toDecPred (pp : PropPred) : DecPred PropMap where
  pred := pp.pred
  dec  := pp.dec

namespace PropPred

def true_ : PropPred where
  pred := fun _ => True
  dec  := fun _ => isTrue trivial
  attrs := ∅
  attrs_spec := fun _ => ⟨fun h => h, fun h => h⟩

def false_ : PropPred where
  pred := fun _ => False
  dec  := fun _ => isFalse (fun h => h)
  attrs := ∅
  attrs_spec := fun _ => ⟨fun h => h, fun h => h⟩

private theorem restrict_union_left (p q : PropPred) (m : PropMap) :
    (m.restrict (p.attrs ∪ q.attrs)).restrict p.attrs = m.restrict p.attrs :=
  PropMap.restrict_restrict_subset m p.attrs (p.attrs ∪ q.attrs) Finset.subset_union_left

private theorem restrict_union_right (p q : PropPred) (m : PropMap) :
    (m.restrict (p.attrs ∪ q.attrs)).restrict q.attrs = m.restrict q.attrs :=
  PropMap.restrict_restrict_subset m q.attrs (p.attrs ∪ q.attrs) Finset.subset_union_right

private theorem lift_attrs_spec (p : PropPred) (s : Finset AttrName) (hs : p.attrs ⊆ s) (m : PropMap) :
    p.pred m ↔ p.pred (m.restrict s) := by
  rw [p.attrs_spec m, p.attrs_spec (m.restrict s), PropMap.restrict_restrict_subset m p.attrs s hs]

def and_ (p q : PropPred) : PropPred where
  pred := fun m => p.pred m ∧ q.pred m
  dec  := fun m => by
    have := p.dec m
    have := q.dec m
    exact instDecidableAnd
  attrs := p.attrs ∪ q.attrs
  attrs_spec := fun m =>
    ⟨fun ⟨hp, hq⟩ => ⟨(lift_attrs_spec p _ Finset.subset_union_left m).mp hp,
                       (lift_attrs_spec q _ Finset.subset_union_right m).mp hq⟩,
     fun ⟨hp, hq⟩ => ⟨(lift_attrs_spec p _ Finset.subset_union_left m).mpr hp,
                       (lift_attrs_spec q _ Finset.subset_union_right m).mpr hq⟩⟩

def or_ (p q : PropPred) : PropPred where
  pred := fun m => p.pred m ∨ q.pred m
  dec  := fun m => by
    have := p.dec m
    have := q.dec m
    exact instDecidableOr
  attrs := p.attrs ∪ q.attrs
  attrs_spec := fun m =>
    ⟨fun h => h.imp (lift_attrs_spec p _ Finset.subset_union_left m).mp
                     (lift_attrs_spec q _ Finset.subset_union_right m).mp,
     fun h => h.imp (lift_attrs_spec p _ Finset.subset_union_left m).mpr
                     (lift_attrs_spec q _ Finset.subset_union_right m).mpr⟩

def not_ (p : PropPred) : PropPred where
  pred := fun m => ¬ p.pred m
  dec  := fun m => by
    have := p.dec m
    exact instDecidableNot
  attrs := p.attrs
  attrs_spec := fun m =>
    ⟨fun hn hp => hn ((p.attrs_spec m).mpr hp),
     fun hn hp => hn ((p.attrs_spec m).mp hp)⟩

/-- A predicate checking a specific attribute against a value. -/
def attrEq (attr : AttrName) (v : Value) : PropPred where
  pred := fun m => m attr = some v
  dec  := fun m => decEq (m attr) (some v)
  attrs := {attr}
  attrs_spec := fun m => by
    simp only [PropMap.restrict, Finset.mem_singleton]
    constructor <;> intro h <;> simp_all

end PropPred

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
