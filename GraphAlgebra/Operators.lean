/-
  GraphAlgebra.Operators

  Graph algebra operators formalized from the proposal:

  Tier 1 (Core):
    - Graph Construction (↑) — lifts relational data to graph form
    - Node Selection (σ_N) — filters nodes by predicate
    - Edge Selection (σ_E) — filters edges by predicate
    - Graph Projection (π_G) — retains specified properties
    - Graph Union (∪_G) — merges two graphs
    - Graph Intersection (∩_G) — retains shared structure
    - Disjoint Union (⊔) — concatenates without merging
    - Connected Component Decomposition (CC)
    - Relational Projection (↓) — drops to relational form

  Tier 2:
    - Graph Difference (\G)

  Tier 3:
    - Transitive Closure (TC)
    - Pattern Matching (⋈_P) — subgraph matching
-/
import GraphAlgebra.Graph
import GraphAlgebra.Relation

namespace GraphAlgebra

variable {V L : Type} [DecidableEq V] [DecidableEq L]

namespace Graph

/-! ## Tier 1: Core Operators -/

/-! ### Node Selection (σ_N)

Keeps nodes satisfying predicate p and all edges between kept nodes.
σ_N(p, G) retains {v ∈ G.nodes | p(nodeProps(v))} and edges with both
endpoints in the kept set. -/

def selectNodes (G : Graph V L) (p : PropMap → Prop) [DecidablePred p] : Graph V L where
  nodes := G.nodes.filter (fun v => p (G.nodeProps v))
  edges := G.edges.filter (fun e =>
    p (G.nodeProps e.src) ∧ p (G.nodeProps e.tgt))
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_filter] at he ⊢
    exact ⟨G.edge_src_valid e he.1, he.2.1⟩
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_filter] at he ⊢
    exact ⟨G.edge_tgt_valid e he.1, he.2.2⟩

/-! ### Edge Selection (σ_E)

Keeps edges satisfying predicate p and their incident nodes. -/

def selectEdges (G : Graph V L) (p : PropMap → Prop) [DecidablePred p] : Graph V L where
  nodes := G.nodes
  edges := G.edges.filter (fun e => p (G.edgeProps e))
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_filter] at he
    exact G.edge_src_valid e he.1
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_filter] at he
    exact G.edge_tgt_valid e he.1

/-! ### Graph Projection (π_G)

Retains only specified properties. Does not change topology. -/

def projectProps (G : Graph V L) (attrs : Finset AttrName) : Graph V L where
  nodes := G.nodes
  edges := G.edges
  nodeProps := fun v => (G.nodeProps v).restrict attrs
  edgeProps := fun e => (G.edgeProps e).restrict attrs
  edge_src_valid := G.edge_src_valid
  edge_tgt_valid := G.edge_tgt_valid

/-! ### Graph Union (∪_G)

Identity-based union: merges two graphs, combining nodes and edges.
This is the simplest variant. Node properties from G₁ take precedence
(left-wins policy). -/

def union (G₁ G₂ : Graph V L) : Graph V L where
  nodes := G₁.nodes ∪ G₂.nodes
  edges := G₁.edges ∪ G₂.edges
  nodeProps := fun v => if v ∈ G₁.nodes then G₁.nodeProps v else G₂.nodeProps v
  edgeProps := fun e => if e ∈ G₁.edges then G₁.edgeProps e else G₂.edgeProps e
  edge_src_valid := by
    intro e he
    simp [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_src_valid e h
    | inr h => right; exact G₂.edge_src_valid e h
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_tgt_valid e h
    | inr h => right; exact G₂.edge_tgt_valid e h

instance : Union (Graph V L) := ⟨union⟩

/-! ### Key-Based Union (∪_K)

Key-based union: merges two graphs where nodes are matched by identity
but properties are combined using a merge strategy rather than left-wins.

This captures the semantics discussed in C⁴–C⁶ of the proposal:
- Identity-based union with left-wins is our `union` above
- Key-based union with explicit merge is `keyUnion` below
- The C-notes describe when algebraic laws hold depending on the merge strategy -/

/-- A merge strategy for combining property maps from two sources. -/
structure MergeStrategy where
  /-- How to merge two property maps for the same key. -/
  mergeProps : PropMap → PropMap → PropMap

/-- Left-wins merge: properties from the first graph take precedence. -/
def MergeStrategy.leftWins : MergeStrategy :=
  ⟨PropMap.merge⟩

/-- Right-wins merge: properties from the second graph take precedence. -/
def MergeStrategy.rightWins : MergeStrategy :=
  ⟨fun m₁ m₂ => PropMap.merge m₂ m₁⟩

/-- Key-based graph union. Same topology as identity-based union (nodes and edges
    are set-unioned) but properties on shared nodes/edges are merged using the
    given strategy rather than left-wins.

    This is the operator whose algebraic properties depend on the merge strategy:
    - C⁴: idempotent iff ms is idempotent
    - C⁵: commutative iff ms is commutative
    - C⁶: congruent iff properties are compatible -/
def keyUnion (G₁ G₂ : Graph V L) (ms : MergeStrategy) : Graph V L where
  nodes := G₁.nodes ∪ G₂.nodes
  edges := G₁.edges ∪ G₂.edges
  nodeProps := fun v =>
    if v ∈ G₁.nodes ∧ v ∈ G₂.nodes then
      ms.mergeProps (G₁.nodeProps v) (G₂.nodeProps v)
    else if v ∈ G₁.nodes then G₁.nodeProps v
    else G₂.nodeProps v
  edgeProps := fun e =>
    if e ∈ G₁.edges ∧ e ∈ G₂.edges then
      ms.mergeProps (G₁.edgeProps e) (G₂.edgeProps e)
    else if e ∈ G₁.edges then G₁.edgeProps e
    else G₂.edgeProps e
  edge_src_valid := by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_src_valid e h
    | inr h => right; exact G₂.edge_src_valid e h
  edge_tgt_valid := by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_tgt_valid e h
    | inr h => right; exact G₂.edge_tgt_valid e h

/-- A merge strategy is commutative when merging order doesn't matter. -/
def MergeStrategy.isCommutative (ms : MergeStrategy) : Prop :=
  ∀ m₁ m₂ : PropMap, ms.mergeProps m₁ m₂ = ms.mergeProps m₂ m₁

/-- A merge strategy is idempotent when merging with self is identity. -/
def MergeStrategy.isIdempotent (ms : MergeStrategy) : Prop :=
  ∀ m : PropMap, ms.mergeProps m m = m

/-- A merge strategy is associative. -/
def MergeStrategy.isAssociative (ms : MergeStrategy) : Prop :=
  ∀ m₁ m₂ m₃ : PropMap, ms.mergeProps (ms.mergeProps m₁ m₂) m₃ =
    ms.mergeProps m₁ (ms.mergeProps m₂ m₃)

/-! ### Graph Intersection (∩_G)

Identity-based intersection: retains nodes and edges present in both graphs. -/

def inter (G₁ G₂ : Graph V L) : Graph V L where
  nodes := G₁.nodes ∩ G₂.nodes
  edges := G₁.edges ∩ G₂.edges
  nodeProps := G₁.nodeProps  -- properties from G₁ (arbitrary choice for shared nodes)
  edgeProps := G₁.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_inter] at he ⊢
    exact ⟨G₁.edge_src_valid e he.1, G₂.edge_src_valid e he.2⟩
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_inter] at he ⊢
    exact ⟨G₁.edge_tgt_valid e he.1, G₂.edge_tgt_valid e he.2⟩

instance : Inter (Graph V L) := ⟨inter⟩

/-! ### Graph Difference (\G)

Removes from G₁ all nodes and edges present in G₂. -/

def diff (G₁ G₂ : Graph V L) : Graph V L where
  nodes := G₁.nodes \ G₂.nodes
  edges := G₁.edges.filter (fun e =>
    e.src ∈ G₁.nodes \ G₂.nodes ∧ e.tgt ∈ G₁.nodes \ G₂.nodes)
  nodeProps := G₁.nodeProps
  edgeProps := G₁.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_filter, Finset.mem_sdiff] at he
    exact Finset.mem_sdiff.mpr he.2.1
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_filter, Finset.mem_sdiff] at he
    exact Finset.mem_sdiff.mpr he.2.2

instance : SDiff (Graph V L) := ⟨diff⟩

/-! ### Disjoint Union (⊔)

Places two graphs side by side without merging. We model this by
tagging nodes with a sum type to ensure disjointness.

For graphs over the same vertex type, this requires embedding into
a sum type. We provide a version that assumes disjoint node sets. -/

/-- Disjoint union assuming node sets are already disjoint. -/
def disjointUnion (G₁ G₂ : Graph V L) (_h_disjoint : Disjoint G₁.nodes G₂.nodes) :
    Graph V L where
  nodes := G₁.nodes ∪ G₂.nodes
  edges := G₁.edges ∪ G₂.edges
  nodeProps := fun v =>
    if v ∈ G₁.nodes then G₁.nodeProps v else G₂.nodeProps v
  edgeProps := fun e =>
    if e ∈ G₁.edges then G₁.edgeProps e else G₂.edgeProps e
  edge_src_valid := by
    intro e he
    simp [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_src_valid e h
    | inr h => right; exact G₂.edge_src_valid e h
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_union] at he ⊢
    cases he with
    | inl h => left; exact G₁.edge_tgt_valid e h
    | inr h => right; exact G₂.edge_tgt_valid e h

/-- Tagged disjoint union using Sum type. Always well-defined. -/
def taggedDisjointUnion (G₁ G₂ : Graph V L) :
    Graph (V ⊕ V) L where
  nodes := G₁.nodes.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
           G₂.nodes.map ⟨Sum.inr, Sum.inr_injective⟩
  edges := G₁.edges.map ⟨fun e => ⟨Sum.inl e.src, e.label, Sum.inl e.tgt⟩,
    by intro a b h; simp [Edge.mk.injEq] at h; cases a; cases b; simp_all⟩ ∪
           G₂.edges.map ⟨fun e => ⟨Sum.inr e.src, e.label, Sum.inr e.tgt⟩,
    by intro a b h; simp [Edge.mk.injEq] at h; cases a; cases b; simp_all⟩
  nodeProps := fun v => match v with
    | Sum.inl v => G₁.nodeProps v
    | Sum.inr v => G₂.nodeProps v
  edgeProps := fun e => match e.src, e.tgt with
    | Sum.inl s, Sum.inl t =>
      G₁.edgeProps ⟨s, e.label, t⟩
    | Sum.inr s, Sum.inr t =>
      G₂.edgeProps ⟨s, e.label, t⟩
    | _, _ => PropMap.empty
  edge_src_valid := by
    intro e he
    simp [Finset.mem_union, Finset.mem_map] at he ⊢
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · left; exact ⟨e'.src, G₁.edge_src_valid e' he', rfl⟩
    · right; exact ⟨e'.src, G₂.edge_src_valid e' he', rfl⟩
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_union, Finset.mem_map] at he ⊢
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · left; exact ⟨e'.tgt, G₁.edge_tgt_valid e' he', rfl⟩
    · right; exact ⟨e'.tgt, G₂.edge_tgt_valid e' he', rfl⟩

/-! ### Connected Component Decomposition (CC)

Computes connected components. We define reachability first,
then decompose. This uses the undirected version (ignoring edge direction). -/

/-- Two nodes are in the same connected component if there is an undirected
    path between them (considering edges in both directions). -/
inductive Connected (G : Graph V L) : V → V → Prop where
  | refl : ∀ v, v ∈ G.nodes → Connected G v v
  | edge : ∀ e, e ∈ G.edges → Connected G e.src e.tgt
  | edge_rev : ∀ e, e ∈ G.edges → Connected G e.tgt e.src
  | trans : Connected G u v → Connected G v w → Connected G u w

/-! ### Graph Construction (↑) — Lift from relational form

Constructs a graph from a node relation and an edge relation.
The node relation provides node IDs and properties.
The edge relation provides (source_id, label, target_id) triples with properties. -/

/-- Construct a graph from explicit node and edge sets with property assignments. -/
def construct
    (nodes : Finset V) (edges : Finset (Edge V L))
    (nodeProps : V → PropMap) (edgeProps : Edge V L → PropMap)
    (h_src : ∀ e ∈ edges, e.src ∈ nodes) (h_tgt : ∀ e ∈ edges, e.tgt ∈ nodes) :
    Graph V L :=
  ⟨nodes, edges, nodeProps, edgeProps, h_src, h_tgt⟩

/-! ### Relational Projection (↓) — Drop to relational form

Extracts the node table and edge table from a graph as relations.
This is the inverse of construction (↑). -/

/-- Extract the node relation from a graph.
    Each node becomes a record with its properties. -/
noncomputable def toNodeRelation (G : Graph V L) (idAttr : AttrName) (toVal : V → Value) :
    Relation :=
  ⟨G.nodes.val.toList.map (fun v =>
    ⟨(G.nodeProps v).set idAttr (toVal v)⟩)⟩

/-- Extract the edge relation from a graph. -/
noncomputable def toEdgeRelation (G : Graph V L)
    (srcAttr tgtAttr labelAttr : AttrName)
    (toNodeVal : V → Value) (toLabelVal : L → Value) : Relation :=
  ⟨G.edges.val.toList.map (fun e =>
    ⟨(G.edgeProps e).set srcAttr (toNodeVal e.src)
      |>.set tgtAttr (toNodeVal e.tgt)
      |>.set labelAttr (toLabelVal e.label)⟩)⟩

/-! ## Tier 3: Path and Reachability -/

/-! ### Transitive Closure (TC)

Computes the transitive closure of edges with a given label.
TC(G, l) adds edges (u, l, v) whenever there is a path from u to v
using only l-labeled edges. -/

/-- Reachability via edges with a specific label. -/
inductive LabelReachable (G : Graph V L) (l : L) : V → V → Prop where
  | single : ∀ e, e ∈ G.edges → e.label = l → LabelReachable G l e.src e.tgt
  | trans  : LabelReachable G l u v → LabelReachable G l v w → LabelReachable G l u w

/-- Reachability via edges satisfying a predicate (generalized TC). -/
inductive PredReachable (G : Graph V L) (p : Edge V L → Prop) : V → V → Prop where
  | single : ∀ e, e ∈ G.edges → p e → PredReachable G p e.src e.tgt
  | trans  : PredReachable G p u v → PredReachable G p v w → PredReachable G p u w

/-! ### Path Projection (ρ_path)

Projects paths from a graph: given a label sequence (regular path query),
returns the set of (source, target) pairs connected by matching paths.

The output is a graph containing the endpoints and the edges along matching paths.
This is the ρ_path operator from the property table. -/

/-- A regular path query (RPQ) over edge labels. -/
inductive RPQ (L : Type) where
  | label : L → RPQ L                   -- single edge label
  | seq   : RPQ L → RPQ L → RPQ L       -- concatenation
  | alt   : RPQ L → RPQ L → RPQ L       -- alternation
  | star  : RPQ L → RPQ L               -- Kleene star
  deriving Inhabited

/-- Path matching: does a path from u to v in G match the RPQ? -/
inductive RPQMatch (G : Graph V L) : RPQ L → V → V → Prop where
  | label : ∀ l e, e ∈ G.edges → e.label = l → RPQMatch G (.label l) e.src e.tgt
  | seq   : RPQMatch G q₁ u v → RPQMatch G q₂ v w → RPQMatch G (.seq q₁ q₂) u w
  | alt_l : RPQMatch G q₁ u v → RPQMatch G (.alt q₁ q₂) u v
  | alt_r : RPQMatch G q₂ u v → RPQMatch G (.alt q₁ q₂) u v
  | star_refl : v ∈ G.nodes → RPQMatch G (.star q) v v
  | star_step : RPQMatch G q u v → RPQMatch G (.star q) v w → RPQMatch G (.star q) u w

/-- Path projection result: nodes that are endpoints of matching paths. -/
def pathProjectNodes (G : Graph V L) (q : RPQ L) : Set V :=
  {v | ∃ u, RPQMatch G q u v ∨ RPQMatch G q v u}

/-- Path projection result: the set of (source, target) pairs connected by matching paths. -/
def pathProjectPairs (G : Graph V L) (q : RPQ L) : Set (V × V) :=
  {p | RPQMatch G q p.1 p.2}

/-! ### Pattern Matching (⋈_P)

Given a data graph G and a pattern graph P, find all occurrences of P in G.
We define this in terms of homomorphisms and subgraph isomorphisms.

The output is a graph: the union of all matched subgraphs.
This preserves closure — the result feeds directly into further graph operations. -/

/-- The set of all homomorphisms from P to G. -/
def homomorphisms (P G : Graph V L) : Set (V → V) :=
  {f | (∀ v ∈ P.nodes, f v ∈ G.nodes) ∧
       (∀ e ∈ P.edges, ⟨f e.src, e.label, f e.tgt⟩ ∈ G.edges)}

/-- The set of all injective homomorphisms (embeddings) from P to G.
    This is the ⋈_P (iso) operator from the property table. -/
def embeddings (P G : Graph V L) : Set (V → V) :=
  {f | f ∈ homomorphisms P G ∧
       (∀ u ∈ P.nodes, ∀ v ∈ P.nodes, f u = f v → u = v)}

/-- Embeddings are a subset of homomorphisms. -/
theorem embeddings_sub_homomorphisms (P G : Graph V L) :
    embeddings P G ⊆ homomorphisms P G :=
  fun _ hf => hf.1

/-- Pattern matching result (injective): nodes matched by some embedding. -/
def isoMatchNodes (G P : Graph V L) : Set V :=
  {v | ∃ f ∈ embeddings P G, ∃ u ∈ P.nodes, f u = v}

/-- Pattern matching result (injective): edges matched by some embedding. -/
def isoMatchEdges (G P : Graph V L) : Set (Edge V L) :=
  {e | ∃ f ∈ embeddings P G, ∃ e' ∈ P.edges,
    e = ⟨f e'.src, e'.label, f e'.tgt⟩}

/-- Non-induced match image: contains only pattern-specified edges mapped through f.
    This is the standard homomorphism image — one "occurrence" of the pattern. -/
def matchImage (G P : Graph V L) (f : V → V)
    (_hf : f ∈ homomorphisms P G) : Graph V L where
  nodes := P.nodes.image f
  edges := P.edges.image (fun e => ⟨f e.src, e.label, f e.tgt⟩)
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp [Finset.mem_image] at he ⊢
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨e'.src, by exact P.edge_src_valid e' he', rfl⟩
  edge_tgt_valid := by
    intro e he
    simp [Finset.mem_image] at he ⊢
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨e'.tgt, by exact P.edge_tgt_valid e' he', rfl⟩

/-- Induced match image: contains ALL edges of G between matched vertices.
    This captures the "induced subgraph" interpretation of pattern matching
    discussed in the proposal feedback. The result includes edges not in the
    pattern but present in G between matched nodes. -/
def matchInducedImage (G P : Graph V L) (f : V → V)
    (_hf : f ∈ homomorphisms P G) : Graph V L where
  nodes := P.nodes.image f
  edges := G.edges.filter (fun e =>
    e.src ∈ P.nodes.image f ∧ e.tgt ∈ P.nodes.image f)
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp only [Finset.mem_filter] at he
    exact he.2.1
  edge_tgt_valid := by
    intro e he
    simp only [Finset.mem_filter] at he
    exact he.2.2

/-- Non-induced match is a subgraph of induced match:
    matchImage ⊆ matchInducedImage (same nodes, fewer edges). -/
theorem matchImage_sub_matchInducedImage (G P : Graph V L) (f : V → V)
    (hf : f ∈ homomorphisms P G) :
    (matchImage G P f hf).edges ⊆ (matchInducedImage G P f hf).edges := by
  intro e he
  simp [matchImage, matchInducedImage, Finset.mem_filter, Finset.mem_image] at he ⊢
  obtain ⟨e', he', rfl⟩ := he
  exact ⟨hf.2 e' he',
    ⟨e'.src, P.edge_src_valid e' he', rfl⟩,
    ⟨e'.tgt, P.edge_tgt_valid e' he', rfl⟩⟩

/-- Pattern matching result (non-induced): union of all match images.
    ⋈_P(G, P) = ⋃ {matchImage(G, P, f) | f ∈ homomorphisms(P, G)}
    This is defined set-theoretically since the union over all homomorphisms
    may not be finitely computable in general. -/
def patternMatchNodes (G P : Graph V L) : Set V :=
  {v | ∃ f ∈ homomorphisms P G, ∃ u ∈ P.nodes, f u = v}

def patternMatchEdges (G P : Graph V L) : Set (Edge V L) :=
  {e | ∃ f ∈ homomorphisms P G, ∃ e' ∈ P.edges,
    e = ⟨f e'.src, e'.label, f e'.tgt⟩}

/-- Pattern matching result (induced): union of all induced match images. -/
def patternMatchInducedEdges (G P : Graph V L) : Set (Edge V L) :=
  {e | e ∈ G.edges ∧ e.src ∈ patternMatchNodes G P ∧ e.tgt ∈ patternMatchNodes G P}

/-- Non-induced pattern match edges are a subset of induced pattern match edges. -/
theorem patternMatchEdges_sub_induced (G P : Graph V L) :
    patternMatchEdges G P ⊆ patternMatchInducedEdges G P := by
  intro e he
  obtain ⟨f, hf, e', he', rfl⟩ := he
  exact ⟨hf.2 e' he',
    ⟨f, hf, e'.src, P.edge_src_valid e' he', rfl⟩,
    ⟨f, hf, e'.tgt, P.edge_tgt_valid e' he', rfl⟩⟩

/-! ### σ_N as Induced Subgraph

Node selection is precisely the induced subgraph on the set of nodes satisfying p. -/

/-- σ_N(p, G) = G[{v | p(nodeProps(v))}] — node selection equals the induced subgraph
    on the vertex set satisfying p. This makes explicit that σ_N produces an
    induced subgraph, as noted in the proposal feedback. -/
theorem selectNodes_eq_inducedSubgraph (G : Graph V L) (p : PropMap → Prop) [DecidablePred p] :
    let S := G.nodes.filter (fun v => p (G.nodeProps v))
    let hS : S ⊆ G.nodes := Finset.filter_subset _ _
    (G.selectNodes p).nodes = (G.inducedSubgraph S hS).nodes ∧
    (G.selectNodes p).edges = (G.inducedSubgraph S hS).edges := by
  constructor
  · simp [selectNodes, inducedSubgraph]
  · ext e
    simp only [selectNodes, inducedSubgraph, Finset.mem_filter]
    constructor
    · intro ⟨he, hp_src, hp_tgt⟩
      exact ⟨he, ⟨G.edge_src_valid e he, hp_src⟩, ⟨G.edge_tgt_valid e he, hp_tgt⟩⟩
    · intro ⟨he, ⟨_, hp_src⟩, ⟨_, hp_tgt⟩⟩
      exact ⟨he, hp_src, hp_tgt⟩

/-- σ_N produces an induced subgraph of G. -/
theorem selectNodes_isInducedSubgraph (G : Graph V L) (p : PropMap → Prop) [DecidablePred p] :
    IsInducedSubgraph (G.selectNodes p) G := by
  have edge_eq : (G.selectNodes p).edges = G.edges.filter fun e =>
      e.src ∈ (G.selectNodes p).nodes ∧ e.tgt ∈ (G.selectNodes p).nodes := by
    ext e
    simp only [selectNodes, Finset.mem_filter]
    constructor
    · intro ⟨he, hp_src, hp_tgt⟩
      exact ⟨he, ⟨G.edge_src_valid e he, hp_src⟩, ⟨G.edge_tgt_valid e he, hp_tgt⟩⟩
    · intro ⟨he, ⟨_, hp_src⟩, ⟨_, hp_tgt⟩⟩
      exact ⟨he, hp_src, hp_tgt⟩
  exact ⟨Finset.filter_subset _ _, edge_eq, fun _ _ => rfl, fun _ _ => rfl⟩

end Graph

end GraphAlgebra
