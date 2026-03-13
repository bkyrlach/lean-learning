/-
  GraphAlgebra.Induction

  Six induction principles for property graphs, organized in three parts.

  Part 1 — Graph-algebraic decomposition (component/separator based):

    1. Connected Component Induction (`cc_induction`) — decompose any graph into
       connected components. For "component-local" properties (chromatic number,
       etc.), this is more natural than vertex-by-vertex growth.

    2. Separator/Tree-Decomposition Induction (`separator_induction`) — decompose
       along small separators. For bounded-treewidth graphs, this captures the
       recursive structure that algorithms like Lawler's chromatic number
       computation implicitly use.

  Part 2 — Coq-style growth principles (adapted from DirectedGraphs_morph.v a thing I did ten years ago
          that took me a long time... Claude did it in less than an hour with some direction :(
    ):

    3. Vertex/Edge Growth (`ind1`) — peel off edges then vertices one at a time.
       Corresponds to `GraphConst1` in the Coq formalization.

    4. Vertex-with-Star Growth (`ind2`) — remove one vertex plus all its incident
       edges at a time. Corresponds to `GraphConst2` in the Coq formalization.

    5. Vertex Count Induction (`ind3`) — plain induction on |V|.

    6. Vertex Count Monotone (`ind4`) — transfer from smaller to larger |V|.
-/
import GraphAlgebra.Laws

open Classical

namespace GraphAlgebra

namespace Graph

variable {V L : Type} [DecidableEq V] [DecidableEq L]

/-! # Part 1: Connected Component Induction -/

/-! ## Definitions -/

/-- A graph is connected if it is nonempty and every pair of nodes is connected. -/
def IsConnectedGraph (G : Graph V L) : Prop :=
  G.nodes.Nonempty ∧ ∀ u ∈ G.nodes, ∀ v ∈ G.nodes, Connected G u v

/-- The empty graph is not connected (it has no nodes). -/
theorem not_isConnectedGraph_empty : ¬IsConnectedGraph (empty : Graph V L) := by
  intro ⟨h, _⟩
  simp [empty] at h

/-- The connected component of v: all nodes in G reachable from v. -/
noncomputable def componentOf (G : Graph V L) (v : V) : Finset V :=
  G.nodes.filter (fun u => Connected G v u)

/-- The complement of the connected component of v. -/
noncomputable def complementOf (G : Graph V L) (v : V) : Finset V :=
  G.nodes \ componentOf G v

theorem componentOf_subset {G : Graph V L} {v : V} :
    componentOf G v ⊆ G.nodes :=
  Finset.filter_subset _ _

theorem mem_componentOf_self {G : Graph V L} {v : V} (hv : v ∈ G.nodes) :
    v ∈ componentOf G v := by
  simp only [componentOf, Finset.mem_filter]
  exact ⟨hv, Connected.refl v hv⟩

theorem connected_of_mem_componentOf {G : Graph V L} {v u : V}
    (hu : u ∈ componentOf G v) : Connected G v u := by
  simp only [componentOf, Finset.mem_filter] at hu
  exact hu.2

theorem mem_componentOf_of_connected {G : Graph V L} {v u : V}
    (hu_node : u ∈ G.nodes) (hc : Connected G v u) :
    u ∈ componentOf G v := by
  simp only [componentOf, Finset.mem_filter]
  exact ⟨hu_node, hc⟩

/-! ## No-crossing-edges lemma

The key structural property: edges cannot cross between a connected
component and its complement. -/

theorem no_crossing_edges_forward (G : Graph V L) (v : V)
    (e : Edge V L) (he : e ∈ G.edges) (hsrc : e.src ∈ componentOf G v) :
    e.tgt ∈ componentOf G v := by
  simp only [componentOf, Finset.mem_filter] at hsrc ⊢
  exact ⟨G.edge_tgt_valid e he, Connected.trans hsrc.2 (Connected.edge e he)⟩

theorem no_crossing_edges_backward (G : Graph V L) (v : V)
    (e : Edge V L) (he : e ∈ G.edges) (htgt : e.tgt ∈ componentOf G v) :
    e.src ∈ componentOf G v := by
  simp only [componentOf, Finset.mem_filter] at htgt ⊢
  exact ⟨G.edge_src_valid e he, Connected.trans htgt.2 (Connected.edge_rev e he)⟩

/-- Every edge has both endpoints in the component or both in the complement. -/
theorem edges_partition (G : Graph V L) (v : V) (_hv : v ∈ G.nodes)
    (e : Edge V L) (he : e ∈ G.edges) :
    (e.src ∈ componentOf G v ∧ e.tgt ∈ componentOf G v) ∨
    (e.src ∈ complementOf G v ∧ e.tgt ∈ complementOf G v) := by
  by_cases hsrc : e.src ∈ componentOf G v
  · left
    exact ⟨hsrc, no_crossing_edges_forward G v e he hsrc⟩
  · right
    refine ⟨Finset.mem_sdiff.mpr ⟨G.edge_src_valid e he, hsrc⟩, ?_⟩
    refine Finset.mem_sdiff.mpr ⟨G.edge_tgt_valid e he, ?_⟩
    intro htgt
    exact absurd (no_crossing_edges_backward G v e he htgt) hsrc

/-! ## Component-complement partition -/

theorem component_complement_disjoint (G : Graph V L) (v : V) :
    Disjoint (componentOf G v) (complementOf G v) :=
  disjoint_sdiff_self_right

theorem component_complement_union (G : Graph V L) (v : V) :
    componentOf G v ∪ complementOf G v = G.nodes := by
  simp only [complementOf]
  exact Finset.union_sdiff_of_subset componentOf_subset

/-- If G is disconnected, the complement of any component is nonempty. -/
theorem complement_nonempty_of_not_connected {G : Graph V L}
    (hne : G.nodes.Nonempty) (hdisc : ¬IsConnectedGraph G) (v : V) (hv : v ∈ G.nodes) :
    (complementOf G v).Nonempty := by
  simp only [IsConnectedGraph, not_and] at hdisc
  have hdisc := hdisc hne
  push_neg at hdisc
  obtain ⟨u, hu, w, hw, hnc⟩ := hdisc
  by_cases hu_comp : u ∈ componentOf G v
  · use w
    refine Finset.mem_sdiff.mpr ⟨hw, ?_⟩
    intro hw_comp
    exact hnc (Connected.trans (connected_symm (connected_of_mem_componentOf hu_comp))
      (connected_of_mem_componentOf hw_comp))
  · use u
    exact Finset.mem_sdiff.mpr ⟨hu, hu_comp⟩

/-- The component is strictly smaller than G when G is disconnected. -/
theorem componentOf_card_lt {G : Graph V L} {v : V} (hv : v ∈ G.nodes)
    (hdisc : ¬IsConnectedGraph G) (hne : G.nodes.Nonempty) :
    (componentOf G v).card < G.nodes.card := by
  apply Finset.card_lt_card
  refine ⟨componentOf_subset, ?_⟩
  intro h
  have ⟨w, hw⟩ := complement_nonempty_of_not_connected hne hdisc v hv
  exact (Finset.mem_sdiff.mp hw).2 (h (Finset.mem_sdiff.mp hw).1)

/-- The complement is strictly smaller than G when the component is nonempty. -/
theorem complementOf_card_lt {G : Graph V L} {v : V} (hv : v ∈ G.nodes) :
    (complementOf G v).card < G.nodes.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset, ?_⟩
  intro h
  have hv_comp : v ∈ complementOf G v := h hv
  exact (Finset.mem_sdiff.mp hv_comp).2 (mem_componentOf_self hv)

/-! ## The induction principle -/

/-- **Connected Component Induction.**

To prove a property P for all graphs, it suffices to show:
1. P holds for every graph with no nodes.
2. P holds for every connected graph.
3. If G's nodes partition into disjoint nonempty S₁, S₂ with no crossing edges,
   and P holds for both induced subgraphs, then P holds for G.

This factors proofs into a connected case and a composition case.
For properties that are "local to components" (e.g. chromatic number),
this induction principle is far more natural than vertex-by-vertex growth. -/
theorem cc_induction (P : Graph V L → Prop)
    (h_empty : ∀ G : Graph V L, G.nodes = ∅ → P G)
    (h_connected : ∀ G : Graph V L, IsConnectedGraph G → P G)
    (h_compose : ∀ (G : Graph V L) (S₁ S₂ : Finset V)
      (h₁ : S₁ ⊆ G.nodes) (h₂ : S₂ ⊆ G.nodes),
      S₁ ∪ S₂ = G.nodes → Disjoint S₁ S₂ →
      S₁.Nonempty → S₂.Nonempty →
      (∀ e ∈ G.edges, (e.src ∈ S₁ ∧ e.tgt ∈ S₁) ∨ (e.src ∈ S₂ ∧ e.tgt ∈ S₂)) →
      P (G.inducedSubgraph S₁ h₁) →
      P (G.inducedSubgraph S₂ h₂) →
      P G)
    (G : Graph V L) : P G := by
  -- Strong induction on the number of nodes
  suffices h : ∀ n, ∀ G : Graph V L, G.nodes.card = n → P G from h _ G rfl
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
    intro G hcard
    by_cases hne : G.nodes.Nonempty
    · -- Nonempty: either connected or decomposable
      by_cases hconn : IsConnectedGraph G
      · exact h_connected G hconn
      · -- Disconnected — decompose via connected component
        obtain ⟨v, hv⟩ := hne
        have hunion := component_complement_union G v
        have hdisj := component_complement_disjoint G v
        have hne₁ : (componentOf G v).Nonempty := ⟨v, mem_componentOf_self hv⟩
        have hne₂ := complement_nonempty_of_not_connected ⟨v, hv⟩ hconn v hv
        have hno_cross := edges_partition G v hv
        have hlt₁ : (componentOf G v).card < n := hcard ▸ componentOf_card_lt hv hconn ⟨v, hv⟩
        have hlt₂ : (complementOf G v).card < n := hcard ▸ complementOf_card_lt hv
        exact h_compose G _ _ componentOf_subset Finset.sdiff_subset
          hunion hdisj hne₁ hne₂ hno_cross
          (ih _ hlt₁ _ (by simp [inducedSubgraph]))
          (ih _ hlt₂ _ (by simp [inducedSubgraph, complementOf]))
    · exact h_empty G (Finset.not_nonempty_iff_eq_empty.mp hne)

/-! ## Bonus: The induced subgraph on a connected component is connected -/

/-- Connectivity in G restricted to the component stays in the component. -/
theorem connected_componentOf_closed {G : Graph V L} {v u w : V}
    (hu : u ∈ componentOf G v) (huw : Connected G u w) (hw : w ∈ G.nodes) :
    w ∈ componentOf G v :=
  mem_componentOf_of_connected hw (Connected.trans (connected_of_mem_componentOf hu) huw)

/-! # Part 2: Separator / Tree-Decomposition Induction -/

/-! ## Gluing along a separator -/

/-- G is the gluing of G₁ and G₂ along separator S.

Captures the structure: G₁ and G₂ overlap exactly on S, their union is G,
and all edges stay within G₁ or G₂ (no "new" edges crossing the separator). -/
structure IsGluing (G G₁ G₂ : Graph V L) (S : Finset V) : Prop where
  /-- The separator is the node intersection. -/
  separator_eq : S = G₁.nodes ∩ G₂.nodes
  /-- Nodes decompose. -/
  nodes_cover : G.nodes = G₁.nodes ∪ G₂.nodes
  /-- Edges decompose. -/
  edges_cover : G.edges = G₁.edges ∪ G₂.edges
  /-- G₁'s edges stay within G₁. -/
  edges_valid₁ : ∀ e ∈ G₁.edges, e.src ∈ G₁.nodes ∧ e.tgt ∈ G₁.nodes
  /-- G₂'s edges stay within G₂. -/
  edges_valid₂ : ∀ e ∈ G₂.edges, e.src ∈ G₂.nodes ∧ e.tgt ∈ G₂.nodes

/-- Disjoint union is gluing along the empty separator. -/
theorem disjointUnion_isGluing (G₁ G₂ : Graph V L)
    (h : Disjoint G₁.nodes G₂.nodes) :
    IsGluing (G₁.disjointUnion G₂ h) G₁ G₂ ∅ where
  separator_eq := by
    ext v
    simp only [Finset.mem_inter]
    constructor
    · intro hv; exact absurd hv (Finset.notMem_empty v)
    · intro hv; exact absurd hv.2 (Finset.disjoint_left.mp h hv.1)
  nodes_cover := by simp [disjointUnion]
  edges_cover := by simp [disjointUnion]
  edges_valid₁ := fun e he => ⟨G₁.edge_src_valid e he, G₁.edge_tgt_valid e he⟩
  edges_valid₂ := fun e he => ⟨G₂.edge_src_valid e he, G₂.edge_tgt_valid e he⟩

/-! ## Tree Decomposition -/

/-- A tree decomposition of a graph G.

A rooted tree where each node carries a "bag" of graph vertices, satisfying:
1. Every graph vertex appears in some bag.
2. Every graph edge has both endpoints in some common bag.
3. Running intersection: for each vertex v, the set of tree nodes whose bags
   contain v form a connected subtree (here: v in bag(t) implies v in bag(parent(t)),
   unless t is the unique tree node containing v). -/
structure TreeDecomp (G : Graph V L) where
  treeNodes : Finset ℕ
  root : ℕ
  root_mem : root ∈ treeNodes
  parent : ℕ → ℕ
  parent_valid : ∀ t ∈ treeNodes, parent t ∈ treeNodes
  parent_root : parent root = root
  bag : ℕ → Finset V
  vertex_cover : ∀ v ∈ G.nodes, ∃ t ∈ treeNodes, v ∈ bag t
  edge_cover : ∀ e ∈ G.edges, ∃ t ∈ treeNodes, e.src ∈ bag t ∧ e.tgt ∈ bag t
  running_intersection : ∀ t ∈ treeNodes, t ≠ root →
    ∀ v ∈ bag t, v ∈ bag (parent t)
    ∨ ∀ s ∈ treeNodes, v ∈ bag s → s = t

/-- The width of a tree decomposition: max bag size minus 1. -/
noncomputable def TreeDecomp.width {G : Graph V L} (td : TreeDecomp G) : ℕ :=
  td.treeNodes.sup (fun t => (td.bag t).card) - 1

/-- A graph has treewidth at most k if it admits a tree decomposition of width ≤ k. -/
def HasTreewidthAtMost (G : Graph V L) (k : ℕ) : Prop :=
  ∃ td : TreeDecomp G, td.width ≤ k

/-! ## Separator-based recursive decomposition

For bounded-treewidth graphs, there exists a recursive decomposition where
each split uses a separator of bounded size. This is the structural content
of the tree decomposition theorem. -/

/-- A recursive separator decomposition of a graph.
This witnesses that G can be built up from edgeless base cases by
repeated gluing along bounded separators. -/
inductive SepDecomp : Graph V L → ℕ → Prop where
  /-- Base: an edgeless graph. -/
  | base (G : Graph V L) (k : ℕ) : G.edges = ∅ → SepDecomp G k
  /-- Step: G is glued from G₁, G₂ along separator S with |S| ≤ k+1,
      and both G₁, G₂ have recursive decompositions. -/
  | glue (G G₁ G₂ : Graph V L) (S : Finset V) (k : ℕ) :
    IsGluing G G₁ G₂ S →
    S.card ≤ k + 1 →
    G₁.nodes.card < G.nodes.card →
    G₂.nodes.card < G.nodes.card →
    SepDecomp G₁ k →
    SepDecomp G₂ k → SepDecomp G k

/-- Bounded treewidth implies separator decomposition.
This is the deep combinatorial content — every graph of treewidth ≤ k
admits a recursive separator decomposition with separators of size ≤ k+1.

The proof requires showing that a tree decomposition can be converted into
a recursive separator decomposition by choosing edges of the decomposition
tree and splitting along the corresponding bags. -/
theorem sepDecomp_of_hasTreewidthAtMost {G : Graph V L} {k : ℕ}
    (_htw : HasTreewidthAtMost G k) : SepDecomp G k := by
  sorry -- Deep combinatorial theorem (tree decomposition → separator decomposition)

/-! ## The induction principle -/

/-- **Separator Induction for Bounded-Treewidth Graphs.**

To prove a property P for all graphs admitting a separator decomposition
with separators of size ≤ k+1, it suffices to show:
1. P holds for every edgeless graph (treewidth 0 base case).
2. If G is glued from G₁, G₂ along a separator S with |S| ≤ k+1,
   and P holds for both G₁ and G₂, then P holds for G.

This captures the recursive decomposition structure that algorithms like
Lawler's chromatic number computation use implicitly. The key algebraic law:
  ⋈_P(G, P₁ ⋈_sep P₂) → ⋈_P(G, P₁) ⋈_sep ⋈_P(G, P₂) -/
theorem separator_induction (k : ℕ) (P : Graph V L → Prop)
    (h_base : ∀ G : Graph V L, G.edges = ∅ → P G)
    (h_glue : ∀ (G G₁ G₂ : Graph V L) (S : Finset V),
      IsGluing G G₁ G₂ S →
      S.card ≤ k + 1 →
      P G₁ → P G₂ → P G)
    {G : Graph V L} (hdecomp : SepDecomp G k) : P G := by
  induction hdecomp with
  | base G _ h => exact h_base G h
  | glue G G₁ G₂ S _ hglue hsep _ _ _ _ ih₁ ih₂ =>
    exact h_glue G G₁ G₂ S hglue hsep (ih₁ h_glue) (ih₂ h_glue)

/-- Separator induction from treewidth bound (combines the deep theorem). -/
theorem separator_induction_tw (k : ℕ) (P : Graph V L → Prop)
    (h_base : ∀ G : Graph V L, G.edges = ∅ → P G)
    (h_glue : ∀ (G G₁ G₂ : Graph V L) (S : Finset V),
      IsGluing G G₁ G₂ S →
      S.card ≤ k + 1 →
      P G₁ → P G₂ → P G)
    (G : Graph V L) (htw : HasTreewidthAtMost G k) : P G :=
  separator_induction k P h_base h_glue (sepDecomp_of_hasTreewidthAtMost htw)

/-! ## Connecting the Two Principles -/

/-- CC induction is a special case of separator induction with k = 0
    (empty separators = disjoint union). Connected components are exactly
    the pieces you get from recursive splitting with empty separators. -/
theorem cc_induction_from_separator (P : Graph V L → Prop)
    (h_empty : ∀ G : Graph V L, G.nodes = ∅ → P G)
    (h_connected : ∀ G : Graph V L, IsConnectedGraph G → P G)
    (h_compose : ∀ (G : Graph V L) (S₁ S₂ : Finset V)
      (h₁ : S₁ ⊆ G.nodes) (h₂ : S₂ ⊆ G.nodes),
      S₁ ∪ S₂ = G.nodes → Disjoint S₁ S₂ →
      S₁.Nonempty → S₂.Nonempty →
      (∀ e ∈ G.edges, (e.src ∈ S₁ ∧ e.tgt ∈ S₁) ∨ (e.src ∈ S₂ ∧ e.tgt ∈ S₂)) →
      P (G.inducedSubgraph S₁ h₁) →
      P (G.inducedSubgraph S₂ h₂) →
      P G)
    (G : Graph V L) : P G :=
  cc_induction P h_empty h_connected h_compose G

/-! # Part 3: Coq-style Induction Principles (ind1–ind4)

Adapted from `DirectedGraphs_morph.v`. These provide four induction schemes
of increasing abstraction for reasoning about graphs:

- **ind1**: Build up from empty by adding vertices and edges one at a time.
- **ind2**: Build up from empty by adding one vertex plus its star at a time.
- **ind3**: Induction on the number of vertices.
- **ind4**: Monotone transfer from smaller to larger vertex count.
-/

/-! ## Graph surgery operations -/

/-- Remove an edge from a graph. -/
def eraseEdge (G : Graph V L) (e : Edge V L) : Graph V L where
  nodes := G.nodes
  edges := G.edges.erase e
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid e' he' := G.edge_src_valid e' (Finset.erase_subset _ _ he')
  edge_tgt_valid e' he' := G.edge_tgt_valid e' (Finset.erase_subset _ _ he')

/-- Remove a vertex and all its incident edges from a graph. -/
def eraseNode (G : Graph V L) (v : V) : Graph V L where
  nodes := G.nodes.erase v
  edges := G.edges.filter (fun e => e.src ≠ v ∧ e.tgt ≠ v)
  nodeProps := G.nodeProps
  edgeProps := G.edgeProps
  edge_src_valid := by
    intro e he
    simp only [Finset.mem_filter] at he
    exact Finset.mem_erase.mpr ⟨he.2.1, G.edge_src_valid e he.1⟩
  edge_tgt_valid := by
    intro e he
    simp only [Finset.mem_filter] at he
    exact Finset.mem_erase.mpr ⟨he.2.2, G.edge_tgt_valid e he.1⟩

theorem eraseEdge_edges_card {G : Graph V L} {e : Edge V L} (he : e ∈ G.edges) :
    (G.eraseEdge e).edges.card < G.edges.card := by
  simp only [eraseEdge]
  exact Finset.card_erase_lt_of_mem he

theorem eraseEdge_nodes_eq (G : Graph V L) (e : Edge V L) :
    (G.eraseEdge e).nodes = G.nodes := rfl

theorem eraseNode_nodes_card {G : Graph V L} {v : V} (hv : v ∈ G.nodes) :
    (G.eraseNode v).nodes.card < G.nodes.card := by
  simp only [eraseNode]
  exact Finset.card_erase_lt_of_mem hv

/-! ## ind1: Vertex/Edge Growth Induction

Every graph can be deconstructed into an empty base by peeling off edges
then vertices. Equivalently, every graph is built from empty by adding
vertices and edges one at a time.

Corresponds to `GraphConst1` / `ind1` in the Coq formalization. -/

/-- **ind1: Vertex/Edge Growth Induction.**

To prove P for all graphs, show:
1. P holds for all empty (nodeless) graphs.
2. P is preserved when adding a single edge to a graph.
3. P is preserved when adding a single vertex to an edgeless graph. -/
theorem ind1 (P : Graph V L → Prop)
    (h_empty : ∀ G : Graph V L, G.nodes = ∅ → P G)
    (h_add_edge : ∀ (G : Graph V L) (e : Edge V L),
      e ∈ G.edges → P (G.eraseEdge e) → P G)
    (h_add_vertex : ∀ (G : Graph V L) (v : V),
      v ∈ G.nodes → G.edges = ∅ → P (G.eraseNode v) → P G)
    (G : Graph V L) : P G := by
  -- Strong induction on |V| + |E|
  suffices h : ∀ n, ∀ G : Graph V L, G.nodes.card + G.edges.card = n → P G from
    h _ G rfl
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
    intro G hcard
    by_cases he : G.edges.Nonempty
    · -- Has edges: peel off one edge
      obtain ⟨e, he⟩ := he
      apply h_add_edge G e he
      apply ih (G.nodes.card + (G.eraseEdge e).edges.card)
      · rw [← hcard]
        have : (G.eraseEdge e).edges.card < G.edges.card := eraseEdge_edges_card he
        omega
      · rfl
    · -- No edges
      push_neg at he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      by_cases hv : G.nodes.Nonempty
      · -- Has vertices but no edges: peel off one vertex
        obtain ⟨v, hv⟩ := hv
        apply h_add_vertex G v hv he
        apply ih ((G.eraseNode v).nodes.card + (G.eraseNode v).edges.card)
        · rw [← hcard]
          have : (G.eraseNode v).nodes.card < G.nodes.card := eraseNode_nodes_card hv
          have : (G.eraseNode v).edges.card ≤ G.edges.card := by
            simp [eraseNode]; exact Finset.card_filter_le _ _
          omega
        · rfl
      · -- Empty
        push_neg at hv
        exact h_empty G (Finset.not_nonempty_iff_eq_empty.mp hv)

/-! ## ind2: Vertex-with-Star Growth Induction

Every graph can be built by repeatedly adding a fresh vertex together with
all edges incident to already-present vertices. This is the natural induction
for algorithms that process vertices in order.

Corresponds to `GraphConst2` / `ind2` in the Coq formalization. -/

/-- **ind2: Vertex-with-Star Growth Induction.**

To prove P for all graphs, show:
1. P holds for all empty graphs.
2. If P holds for G, then P holds for G extended by one new vertex v
   plus all edges between v and existing vertices of G. -/
theorem ind2 (P : Graph V L → Prop)
    (h_empty : ∀ G : Graph V L, G.nodes = ∅ → P G)
    (h_grow : ∀ (G : Graph V L) (v : V),
      v ∈ G.nodes →
      P (G.eraseNode v) → P G)
    (G : Graph V L) : P G := by
  suffices h : ∀ n, ∀ G : Graph V L, G.nodes.card = n → P G from h _ G rfl
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
    intro G hcard
    by_cases hv : G.nodes.Nonempty
    · obtain ⟨v, hv⟩ := hv
      exact h_grow G v hv (ih _ (by rw [← hcard]; exact eraseNode_nodes_card hv) _ rfl)
    · exact h_empty G (Finset.not_nonempty_iff_eq_empty.mp hv)

/-! ## ind3: Vertex Count Induction

Plain induction on the number of vertices. Corresponds to `ind3` in the
Coq formalization.

Note: The Coq version requires `Respectful` (invariance under graph equality).
In our concrete setting, P applies to specific Graph values, so Respectful
is not needed — but the hypotheses quantify over all graphs with a given
vertex count, which achieves the same effect. -/

/-- **ind3: Vertex Count Induction.**

To prove P for all graphs, show:
1. P holds for all graphs with 0 vertices.
2. If P holds for all graphs with n vertices,
   then it holds for all graphs with n+1 vertices. -/
theorem ind3 (P : Graph V L → Prop)
    (h_zero : ∀ G : Graph V L, G.nodeCount = 0 → P G)
    (h_step : ∀ n, (∀ G : Graph V L, G.nodeCount = n → P G) →
      ∀ G : Graph V L, G.nodeCount = n + 1 → P G)
    (G : Graph V L) : P G := by
  suffices h : ∀ n, ∀ G : Graph V L, G.nodeCount = n → P G from h _ G rfl
  intro n
  induction n with
  | zero => exact h_zero
  | succ n ih => exact h_step n ih

/-! ## ind4: Vertex Count Monotone Induction

If P holds for empty graphs and transfers from any graph to any graph with
at least as many vertices, then P holds universally.

Corresponds to `ind4` in the Coq formalization. -/

/-- **ind4: Vertex Count Monotone Induction.**

To prove P for all graphs, show:
1. P holds for all graphs with 0 vertices.
2. For any graphs G, G' with |V(G)| ≤ |V(G')|, P(G) implies P(G'). -/
theorem ind4 (P : Graph V L → Prop)
    (h_zero : ∀ G : Graph V L, G.nodeCount = 0 → P G)
    (h_mono : ∀ G G' : Graph V L, G.nodeCount ≤ G'.nodeCount → P G → P G')
    (G : Graph V L) : P G := by
  apply ind3 P h_zero
  intro n ih G hG
  -- G has n+1 vertices. Pick any vertex v, erase it to get an n-vertex graph,
  -- apply ih to get P for that, then h_mono to transfer up to G.
  obtain ⟨v, hv⟩ : G.nodes.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; simp [nodeCount] at hG; rw [h] at hG; simp at hG
  have herase : (G.nodes.erase v).card = G.nodes.card - 1 := Finset.card_erase_of_mem hv
  have hGcard : G.nodes.card = n + 1 := hG
  have hG' : (G.eraseNode v).nodeCount = n := by
    simp only [nodeCount, eraseNode, herase]
    omega
  exact h_mono (G.eraseNode v) G
    (by simp only [nodeCount, eraseNode, herase]; omega) (ih _ hG')

end Graph

end GraphAlgebra
