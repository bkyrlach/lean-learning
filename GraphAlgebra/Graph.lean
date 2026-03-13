/-
  GraphAlgebra.Graph

  Labeled property graph definition — the central type of the algebra.
  A graph consists of nodes and labeled directed edges, each carrying properties.

  Key design decisions:
  - Parameterized over vertex type V and edge label type L
  - Uses Finset for finite graphs (required for decidable operations)
  - Edges are directed and labeled: (source, label, target)
  - Both nodes and edges carry property maps
  - Disconnected graphs are allowed (essential for closure)
-/
import GraphAlgebra.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

namespace GraphAlgebra

/-! ## Edge Type -/

/-- A labeled directed edge from source to target with a label. -/
structure Edge (V L : Type) where
  src   : V
  label : L
  tgt   : V
  deriving DecidableEq, Repr, Inhabited

/-! ## Property Graph -/

/-- A labeled property graph.

  This is the fundamental structure of the graph algebra. It allows:
  - Multiple disconnected components (essential for closure)
  - Self-loops and parallel edges
  - Properties on both nodes and edges
  - Labeled, directed edges -/
structure Graph (V L : Type) [DecidableEq V] [DecidableEq L] where
  /-- The set of nodes in the graph. -/
  nodes : Finset V
  /-- The set of labeled directed edges. -/
  edges : Finset (Edge V L)
  /-- Properties associated with each node. -/
  nodeProps : V → PropMap
  /-- Properties associated with each edge. -/
  edgeProps : Edge V L → PropMap
  /-- Every edge's source is a valid node. -/
  edge_src_valid : ∀ e ∈ edges, e.src ∈ nodes
  /-- Every edge's target is a valid node. -/
  edge_tgt_valid : ∀ e ∈ edges, e.tgt ∈ nodes

namespace Graph

variable {V L : Type} [DecidableEq V] [DecidableEq L]

/-! ## Empty Graph -/

/-- The empty graph with no nodes or edges. -/
def empty : Graph V L where
  nodes := ∅
  edges := ∅
  nodeProps := fun _ => PropMap.empty
  edgeProps := fun _ => PropMap.empty
  edge_src_valid := by simp
  edge_tgt_valid := by simp

instance : Inhabited (Graph V L) := ⟨empty⟩

/-! ## Graph Size -/

def nodeCount (G : Graph V L) : Nat := G.nodes.card
def edgeCount (G : Graph V L) : Nat := G.edges.card

/-! ## Subgraph Relation -/

/-- G₁ is a subgraph of G₂ if all nodes and edges of G₁ are in G₂
    and properties are preserved. -/
def IsSubgraph (G₁ G₂ : Graph V L) : Prop :=
  G₁.nodes ⊆ G₂.nodes ∧
  G₁.edges ⊆ G₂.edges ∧
  (∀ v ∈ G₁.nodes, G₁.nodeProps v = G₂.nodeProps v) ∧
  (∀ e ∈ G₁.edges, G₁.edgeProps e = G₂.edgeProps e)

instance : LE (Graph V L) where
  le := IsSubgraph

/-- Subgraph is reflexive. -/
theorem IsSubgraph.refl (G : Graph V L) : IsSubgraph G G :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Subgraph is transitive. -/
theorem IsSubgraph.trans {G₁ G₂ G₃ : Graph V L}
    (h₁₂ : IsSubgraph G₁ G₂) (h₂₃ : IsSubgraph G₂ G₃) : IsSubgraph G₁ G₃ :=
  ⟨Finset.Subset.trans h₁₂.1 h₂₃.1,
   Finset.Subset.trans h₁₂.2.1 h₂₃.2.1,
   fun v hv => (h₁₂.2.2.1 v hv).trans (h₂₃.2.2.1 v (h₁₂.1 hv)),
   fun e he => (h₁₂.2.2.2 e he).trans (h₂₃.2.2.2 e (h₁₂.2.1 he))⟩

/-- Empty graph is a subgraph of everything. -/
theorem empty_isSubgraph (G : Graph V L) : IsSubgraph empty G :=
  ⟨Finset.empty_subset _, Finset.empty_subset _,
   fun _ h => absurd h (Finset.notMem_empty _),
   fun _ h => absurd h (Finset.notMem_empty _)⟩

/-! ## Graph Homomorphism -/

/-- A graph homomorphism maps nodes to nodes preserving edge structure. -/
structure Homomorphism (G₁ G₂ : Graph V L) where
  nodeMap : V → V
  nodeMap_valid : ∀ v ∈ G₁.nodes, nodeMap v ∈ G₂.nodes
  edge_preserved : ∀ e ∈ G₁.edges,
    ⟨nodeMap e.src, e.label, nodeMap e.tgt⟩ ∈ G₂.edges

/-- An injective homomorphism (subgraph isomorphism). -/
structure Embedding (G₁ G₂ : Graph V L) extends Homomorphism G₁ G₂ where
  injective : Function.Injective nodeMap

/-- Graph isomorphism: bijective homomorphism with inverse. -/
structure Isomorphism (G₁ G₂ : Graph V L) where
  forward  : Homomorphism G₁ G₂
  backward : Homomorphism G₂ G₁
  left_inv  : ∀ v ∈ G₁.nodes, backward.nodeMap (forward.nodeMap v) = v
  right_inv : ∀ v ∈ G₂.nodes, forward.nodeMap (backward.nodeMap v) = v

/-- Isomorphism notation (≅). -/
def isIso (G₁ G₂ : Graph V L) : Prop :=
  Nonempty (Isomorphism G₁ G₂)

/-! ## Node Labels and Edge Labels -/

/-- The set of edge labels used in a graph. -/
def edgeLabels (G : Graph V L) : Finset L :=
  G.edges.image (·.label)

/-- Neighbors of a node: nodes reachable by a single edge. -/
def neighbors (G : Graph V L) (v : V) : Finset V :=
  (G.edges.filter (·.src = v)).image (·.tgt)

/-- In-neighbors: nodes with an edge to v. -/
def inNeighbors (G : Graph V L) (v : V) : Finset V :=
  (G.edges.filter (·.tgt = v)).image (·.src)

/-- Out-degree of a node. -/
def outDegree (G : Graph V L) (v : V) : Nat :=
  (G.edges.filter (·.src = v)).card

/-- In-degree of a node. -/
def inDegree (G : Graph V L) (v : V) : Nat :=
  (G.edges.filter (·.tgt = v)).card

/-! ## Adjacency -/

/-- Two nodes are adjacent if there is an edge between them in either direction. -/
def adjacent (G : Graph V L) (u v : V) : Prop :=
  ∃ e ∈ G.edges, (e.src = u ∧ e.tgt = v) ∨ (e.src = v ∧ e.tgt = u)

/-! ## Induced Subgraph -/

/-- The subgraph induced by a set of nodes: keeps all edges between kept nodes. -/
def inducedSubgraph (G : Graph V L) (S : Finset V) (_hS : S ⊆ G.nodes) : Graph V L where
  nodes := S
  edges := G.edges.filter (fun e => e.src ∈ S ∧ e.tgt ∈ S)
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_filter] at he
    exact he.2.1
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_filter] at he
    exact he.2.2

theorem inducedSubgraph_isSubgraph (G : Graph V L) (S : Finset V) (hS : S ⊆ G.nodes) :
    IsSubgraph (G.inducedSubgraph S hS) G :=
  ⟨hS,
   Finset.filter_subset _ _,
   fun _ _ => rfl,
   fun _ _ => rfl⟩

/-! ## Induced Subgraph Containment -/

/-- H is an induced subgraph of G if H.nodes ⊆ G.nodes and H contains exactly
    the edges of G between its nodes (not just a subset). -/
def IsInducedSubgraph (H G : Graph V L) : Prop :=
  H.nodes ⊆ G.nodes ∧
  H.edges = G.edges.filter (fun e => e.src ∈ H.nodes ∧ e.tgt ∈ H.nodes) ∧
  (∀ v ∈ H.nodes, H.nodeProps v = G.nodeProps v) ∧
  (∀ e ∈ H.edges, H.edgeProps e = G.edgeProps e)

/-- An induced subgraph is a subgraph. -/
theorem IsInducedSubgraph.toIsSubgraph {H G : Graph V L}
    (h : IsInducedSubgraph H G) : IsSubgraph H G :=
  ⟨h.1, h.2.1 ▸ Finset.filter_subset _ _, h.2.2.1, h.2.2.2⟩

/-- inducedSubgraph produces an induced subgraph. -/
theorem inducedSubgraph_isInducedSubgraph (G : Graph V L) (S : Finset V)
    (hS : S ⊆ G.nodes) : IsInducedSubgraph (G.inducedSubgraph S hS) G :=
  ⟨hS, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Graph

end GraphAlgebra
