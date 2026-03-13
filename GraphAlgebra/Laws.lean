/-
  GraphAlgebra.Laws

  Algebraic laws for the graph algebra, organized by the property table.

  Each section corresponds to a row or column of the property table from
  the proposal, with C-notes indicating conditional laws.

  Property Table Coverage:
    ✓ = proven unconditionally
    C = proven with conditions (matches proposal's C-notes)
    ✗ = proven to NOT hold (counterexample or negation)
-/
import GraphAlgebra.Operators

namespace GraphAlgebra

namespace Graph

variable {V L : Type} [DecidableEq V] [DecidableEq L]

/-! ## Selection Laws (σ_p row) -/

section SelectionLaws

variable {p q : PropMap → Prop} [DecidablePred p] [DecidablePred q]

/-- σ_N is idempotent: σ_p(σ_p(G)) = σ_p(G) -/
theorem selectNodes_idem (G : Graph V L) :
    (G.selectNodes p).selectNodes p = G.selectNodes p := by
  unfold selectNodes
  congr 1 <;> (ext x; simp [Finset.mem_filter])

/-- σ_E is idempotent: σ_p(σ_p(G)) = σ_p(G) -/
theorem selectEdges_idem (G : Graph V L) :
    (G.selectEdges p).selectEdges p = G.selectEdges p := by
  unfold selectEdges
  simp only []
  congr 1 <;> (ext e; simp [Finset.mem_filter])

/-- Node selection commutativity: σ_p(σ_q(G)) = σ_q(σ_p(G))

  Both sides keep nodes satisfying p ∧ q and edges between them. -/
theorem selectNodes_comm (G : Graph V L) :
    (G.selectNodes p).selectNodes q = (G.selectNodes q).selectNodes p := by
  simp [selectNodes]
  constructor
  · ext v; simp [Finset.mem_filter]; tauto
  · ext e; simp [Finset.mem_filter]; tauto

/-- Edge selection commutativity. -/
theorem selectEdges_comm (G : Graph V L) :
    (G.selectEdges p).selectEdges q = (G.selectEdges q).selectEdges p := by
  simp [selectEdges]
  ext e; simp [Finset.mem_filter]; tauto

/-- Conjunctive decomposition for node selection:
    σ_{p∧q}(G) = σ_p(σ_q(G)) -/
theorem selectNodes_conj (G : Graph V L) :
    G.selectNodes (fun m => p m ∧ q m) = (G.selectNodes q).selectNodes p := by
  simp [selectNodes]
  constructor
  · ext v; simp [Finset.mem_filter]; tauto
  · ext e; simp [Finset.mem_filter]; tauto

/-- Conjunctive decomposition for edge selection. -/
theorem selectEdges_conj (G : Graph V L) :
    G.selectEdges (fun m => p m ∧ q m) = (G.selectEdges q).selectEdges p := by
  simp [selectEdges]
  ext e; simp [Finset.mem_filter]; tauto

/-- Selection of empty graph is empty (identity element). -/
theorem selectNodes_empty :
    (Graph.empty : Graph V L).selectNodes p = Graph.empty := by
  unfold selectNodes empty
  simp only []
  congr 1

theorem selectEdges_empty :
    (Graph.empty : Graph V L).selectEdges p = Graph.empty := by
  unfold selectEdges empty
  simp only []
  congr 1

/-- Node selection is monotone w.r.t. the subgraph relation:
    G₁ ≤ G₂ → σ_p(G₁) ≤ σ_p(G₂) -/
theorem selectNodes_mono {G₁ G₂ : Graph V L}
    (h : IsSubgraph G₁ G₂)
    (hprops : ∀ v ∈ G₁.nodes, G₁.nodeProps v = G₂.nodeProps v) :
    IsSubgraph (G₁.selectNodes p) (G₂.selectNodes p) := by
  constructor
  · intro v hv
    simp [selectNodes, Finset.mem_filter] at hv ⊢
    exact ⟨h.1 hv.1, by rw [← hprops v hv.1]; exact hv.2⟩
  constructor
  · intro e he
    simp [selectNodes, Finset.mem_filter] at he ⊢
    refine ⟨h.2.1 he.1, ?_, ?_⟩
    · rw [← hprops e.src (G₁.edge_src_valid e he.1)]; exact he.2.1
    · rw [← hprops e.tgt (G₁.edge_tgt_valid e he.1)]; exact he.2.2
  constructor
  · intro v hv
    simp [selectNodes] at hv
    exact hprops v hv.1
  · intro e he
    simp [selectNodes] at he
    exact h.2.2.2 e he.1

/-- Edge selection is monotone. -/
theorem selectEdges_mono {G₁ G₂ : Graph V L}
    (h : IsSubgraph G₁ G₂) :
    IsSubgraph (G₁.selectEdges p) (G₂.selectEdges p) := by
  refine ⟨h.1, ?_, fun v hv => h.2.2.1 v hv, ?_⟩
  · intro e he
    simp [selectEdges, Finset.mem_filter] at he ⊢
    exact ⟨h.2.1 he.1, by rw [← h.2.2.2 e he.1]; exact he.2⟩
  · intro e he
    simp [selectEdges, Finset.mem_filter] at he
    exact h.2.2.2 e he.1

end SelectionLaws

/-! ## Selection distributes over Union and Intersection -/

section SelectionDistributivity

variable {p : PropMap → Prop} [DecidablePred p]

/-- σ_N distributes over identity-based union (C¹):
    σ_p(G₁ ∪ G₂).nodes = σ_p(G₁).nodes ∪ σ_p(G₂).nodes

    Conditional: requires properties agree on shared nodes. -/
theorem selectNodes_union_nodes (G₁ G₂ : Graph V L)
    (h_agree : ∀ v ∈ G₁.nodes, v ∈ G₂.nodes → G₁.nodeProps v = G₂.nodeProps v) :
    ((G₁.union G₂).selectNodes p).nodes =
    (G₁.selectNodes p).nodes ∪ (G₂.selectNodes p).nodes := by
  ext v
  simp only [selectNodes, union, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hv_mem, hpv⟩
    cases hv_mem with
    | inl h₁ => left; exact ⟨h₁, by simp [h₁] at hpv; exact hpv⟩
    | inr h₂ =>
      by_cases h₁ : v ∈ G₁.nodes
      · left; exact ⟨h₁, by simp [h₁] at hpv; exact hpv⟩
      · right; exact ⟨h₂, by simp [h₁] at hpv; exact hpv⟩
  · rintro (⟨h₁, hp₁⟩ | ⟨h₂, hp₂⟩)
    · exact ⟨Or.inl h₁, by simp [h₁]; exact hp₁⟩
    · constructor
      · exact Or.inr h₂
      · by_cases h₁ : v ∈ G₁.nodes
        · simp [h₁]; rw [h_agree v h₁ h₂]; exact hp₂
        · simp [h₁]; exact hp₂

/-- σ_N distributes over intersection (C¹):
    σ_p(G₁ ∩ G₂).nodes = σ_p(G₁).nodes ∩ σ_p(G₂).nodes

    Conditional: requires properties agree on shared nodes. -/
theorem selectNodes_inter_nodes (G₁ G₂ : Graph V L)
    (h_agree : ∀ v ∈ G₁.nodes, v ∈ G₂.nodes → G₁.nodeProps v = G₂.nodeProps v) :
    ((G₁.inter G₂).selectNodes p).nodes =
    (G₁.selectNodes p).nodes ∩ (G₂.selectNodes p).nodes := by
  ext v
  simp only [selectNodes, inter, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hp⟩
    exact ⟨⟨h₁, hp⟩, ⟨h₂, by rw [← h_agree v h₁ h₂]; exact hp⟩⟩
  · rintro ⟨⟨h₁, hp₁⟩, ⟨h₂, _⟩⟩
    exact ⟨⟨h₁, h₂⟩, hp₁⟩

/-- σ_E distributes over union (edges):
    σ_p(G₁ ∪ G₂).edges = σ_p(G₁).edges ∪ σ_p(G₂).edges

    Holds when edgeProps are preserved (identity-based union). -/
theorem selectEdges_union_edges (G₁ G₂ : Graph V L)
    (h_disjoint_edges : Disjoint G₁.edges G₂.edges) :
    ((G₁.union G₂).selectEdges p).edges =
    (G₁.selectEdges p).edges ∪ (G₂.selectEdges p).edges := by
  simp [selectEdges, union, Finset.filter_union]
  congr 1
  · apply Finset.filter_congr
    intro e he
    simp [he]
  · apply Finset.filter_congr
    intro e he
    have : e ∉ G₁.edges := Finset.disjoint_right.mp h_disjoint_edges he
    simp [this]

end SelectionDistributivity

/-! ## Union Laws (∪_G row) -/

section UnionLaws

/-- Union is commutative on node sets. -/
theorem union_nodes_comm (G₁ G₂ : Graph V L) :
    (G₁.union G₂).nodes = (G₂.union G₁).nodes := by
  simp [union, Finset.union_comm]

/-- Union is commutative on edge sets. -/
theorem union_edges_comm (G₁ G₂ : Graph V L) :
    (G₁.union G₂).edges = (G₂.union G₁).edges := by
  simp [union, Finset.union_comm]

/-- Union is associative on node sets. -/
theorem union_nodes_assoc (G₁ G₂ G₃ : Graph V L) :
    ((G₁.union G₂).union G₃).nodes = (G₁.union (G₂.union G₃)).nodes := by
  simp [union, Finset.union_assoc]

/-- Union is associative on edge sets. -/
theorem union_edges_assoc (G₁ G₂ G₃ : Graph V L) :
    ((G₁.union G₂).union G₃).edges = (G₁.union (G₂.union G₃)).edges := by
  simp [union, Finset.union_assoc]

/-- Empty is a left identity for union (on nodes). -/
theorem empty_union_nodes (G : Graph V L) :
    ((empty : Graph V L).union G).nodes = G.nodes := by
  simp [union, empty]

/-- Empty is a left identity for union (on edges). -/
theorem empty_union_edges (G : Graph V L) :
    ((empty : Graph V L).union G).edges = G.edges := by
  simp [union, empty]

/-- Empty is a right identity for union (on nodes). -/
theorem union_empty_nodes (G : Graph V L) :
    (G.union (empty : Graph V L)).nodes = G.nodes := by
  simp [union, empty]

/-- Empty is a right identity for union (on edges). -/
theorem union_empty_edges (G : Graph V L) :
    (G.union (empty : Graph V L)).edges = G.edges := by
  simp [union, empty]

/-- Subgraph: G₁ is a subgraph of G₁ ∪ G₂. -/
theorem left_subgraph_union (G₁ G₂ : Graph V L) :
    G₁.nodes ⊆ (G₁.union G₂).nodes := by
  simp [union, Finset.subset_union_left]

theorem left_subgraph_union_edges (G₁ G₂ : Graph V L) :
    G₁.edges ⊆ (G₁.union G₂).edges := by
  simp [union, Finset.subset_union_left]

/-- Union is monotone: if G₁ ≤ G₁' and G₂ ≤ G₂' then
    (G₁ ∪ G₂).nodes ⊆ (G₁' ∪ G₂').nodes -/
theorem union_mono_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (h₁ : G₁.nodes ⊆ G₁'.nodes) (h₂ : G₂.nodes ⊆ G₂'.nodes) :
    (G₁.union G₂).nodes ⊆ (G₁'.union G₂').nodes := by
  simp only [union]
  exact Finset.union_subset_union h₁ h₂

end UnionLaws

/-! ## Key-Based Union Laws (C⁴, C⁵, C⁶) -/

section KeyUnionLaws

/-- C⁴: Key-based union is idempotent on topology (nodes/edges) unconditionally. -/
theorem keyUnion_self_nodes (G : Graph V L) (ms : MergeStrategy) :
    (G.keyUnion G ms).nodes = G.nodes := by
  simp [keyUnion]

theorem keyUnion_self_edges (G : Graph V L) (ms : MergeStrategy) :
    (G.keyUnion G ms).edges = G.edges := by
  simp [keyUnion]

/-- C⁴: Key-based union is fully idempotent (including properties)
    iff the merge strategy is idempotent. -/
theorem keyUnion_self_nodeProps (G : Graph V L) (ms : MergeStrategy)
    (h_idem : ms.isIdempotent) (v : V) (hv : v ∈ G.nodes) :
    (G.keyUnion G ms).nodeProps v = G.nodeProps v := by
  simp [keyUnion, hv]
  exact h_idem (G.nodeProps v)

/-- C⁵: Key-based union is commutative on topology unconditionally. -/
theorem keyUnion_nodes_comm (G₁ G₂ : Graph V L) (ms : MergeStrategy) :
    (G₁.keyUnion G₂ ms).nodes = (G₂.keyUnion G₁ ms).nodes := by
  simp [keyUnion, Finset.union_comm]

theorem keyUnion_edges_comm (G₁ G₂ : Graph V L) (ms : MergeStrategy) :
    (G₁.keyUnion G₂ ms).edges = (G₂.keyUnion G₁ ms).edges := by
  simp [keyUnion, Finset.union_comm]

/-- C⁵: Key-based union is commutative on properties iff merge is commutative.
    Only meaningful for vertices in at least one graph. -/
theorem keyUnion_nodeProps_comm (G₁ G₂ : Graph V L) (ms : MergeStrategy)
    (h_comm : ms.isCommutative) (v : V) (hv : v ∈ G₁.nodes ∨ v ∈ G₂.nodes) :
    (G₁.keyUnion G₂ ms).nodeProps v = (G₂.keyUnion G₁ ms).nodeProps v := by
  unfold keyUnion
  by_cases h₁ : v ∈ G₁.nodes <;> by_cases h₂ : v ∈ G₂.nodes
  · simp [h₁, h₂]; exact h_comm (G₁.nodeProps v) (G₂.nodeProps v)
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · exact absurd hv (by push_neg; exact ⟨h₁, h₂⟩)

/-- C⁵: Key-based union is associative on topology. -/
theorem keyUnion_nodes_assoc (G₁ G₂ G₃ : Graph V L) (ms : MergeStrategy) :
    ((G₁.keyUnion G₂ ms).keyUnion G₃ ms).nodes =
    (G₁.keyUnion (G₂.keyUnion G₃ ms) ms).nodes := by
  simp [keyUnion, Finset.union_assoc]

theorem keyUnion_edges_assoc (G₁ G₂ G₃ : Graph V L) (ms : MergeStrategy) :
    ((G₁.keyUnion G₂ ms).keyUnion G₃ ms).edges =
    (G₁.keyUnion (G₂.keyUnion G₃ ms) ms).edges := by
  simp [keyUnion, Finset.union_assoc]

/-- Empty is identity for key-based union (topology). -/
theorem keyUnion_empty_nodes (G : Graph V L) (ms : MergeStrategy) :
    (G.keyUnion (empty : Graph V L) ms).nodes = G.nodes := by
  simp [keyUnion, empty]

theorem empty_keyUnion_nodes (G : Graph V L) (ms : MergeStrategy) :
    ((empty : Graph V L).keyUnion G ms).nodes = G.nodes := by
  simp [keyUnion, empty]

/-- Empty is identity for key-based union (properties). -/
theorem keyUnion_empty_nodeProps (G : Graph V L) (ms : MergeStrategy) (v : V)
    (hv : v ∈ G.nodes) :
    (G.keyUnion (empty : Graph V L) ms).nodeProps v = G.nodeProps v := by
  simp only [keyUnion, empty, Finset.notMem_empty]
  simp [hv]

theorem empty_keyUnion_nodeProps (G : Graph V L) (ms : MergeStrategy) (v : V)
    (hv : v ∈ G.nodes) :
    ((empty : Graph V L).keyUnion G ms).nodeProps v = G.nodeProps v := by
  simp only [keyUnion, empty, Finset.notMem_empty]
  simp [hv]

end KeyUnionLaws

/-! ## Intersection Laws (∩_G row) -/

section IntersectionLaws

/-- Intersection is commutative on node sets. -/
theorem inter_nodes_comm (G₁ G₂ : Graph V L) :
    (G₁.inter G₂).nodes = (G₂.inter G₁).nodes := by
  simp [inter, Finset.inter_comm]

/-- Intersection is commutative on edge sets. -/
theorem inter_edges_comm (G₁ G₂ : Graph V L) :
    (G₁.inter G₂).edges = (G₂.inter G₁).edges := by
  simp [inter, Finset.inter_comm]

/-- Intersection is associative on node sets. -/
theorem inter_nodes_assoc (G₁ G₂ G₃ : Graph V L) :
    ((G₁.inter G₂).inter G₃).nodes = (G₁.inter (G₂.inter G₃)).nodes := by
  simp [inter, Finset.inter_assoc]

/-- Intersection is associative on edge sets. -/
theorem inter_edges_assoc (G₁ G₂ G₃ : Graph V L) :
    ((G₁.inter G₂).inter G₃).edges = (G₁.inter (G₂.inter G₃)).edges := by
  simp [inter, Finset.inter_assoc]

/-- Intersection is idempotent on node sets. -/
theorem inter_self_nodes (G : Graph V L) :
    (G.inter G).nodes = G.nodes := by
  simp [inter, Finset.inter_self]

/-- Intersection is idempotent on edge sets. -/
theorem inter_self_edges (G : Graph V L) :
    (G.inter G).edges = G.edges := by
  simp [inter, Finset.inter_self]

/-- Intersection with empty is empty. -/
theorem inter_empty_nodes (G : Graph V L) :
    (G.inter (empty : Graph V L)).nodes = ∅ := by
  simp [inter, empty]

theorem inter_empty_edges (G : Graph V L) :
    (G.inter (empty : Graph V L)).edges = ∅ := by
  simp [inter, empty]

/-- Intersection is monotone on nodes. -/
theorem inter_mono_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (h₁ : G₁.nodes ⊆ G₁'.nodes) (h₂ : G₂.nodes ⊆ G₂'.nodes) :
    (G₁.inter G₂).nodes ⊆ (G₁'.inter G₂').nodes := by
  simp only [inter]
  exact Finset.inter_subset_inter h₁ h₂

end IntersectionLaws

/-! ## Distributivity Laws -/

section DistributivityLaws

/-- Intersection distributes over union (nodes):
    (G₁ ∩ (G₂ ∪ G₃)).nodes = ((G₁ ∩ G₂) ∪ (G₁ ∩ G₃)).nodes -/
theorem inter_union_dist_nodes (G₁ G₂ G₃ : Graph V L) :
    (G₁.inter (G₂.union G₃)).nodes =
    ((G₁.inter G₂).union (G₁.inter G₃)).nodes := by
  simp [inter, union, Finset.inter_union_distrib_left]

/-- Union distributes over intersection (nodes). -/
theorem union_inter_dist_nodes (G₁ G₂ G₃ : Graph V L) :
    (G₁.union (G₂.inter G₃)).nodes =
    ((G₁.union G₂).inter (G₁.union G₃)).nodes := by
  simp [union, inter, Finset.union_inter_distrib_left]

/-- ∪ distributes over ∩ (edges). -/
theorem inter_union_dist_edges (G₁ G₂ G₃ : Graph V L) :
    (G₁.inter (G₂.union G₃)).edges =
    ((G₁.inter G₂).union (G₁.inter G₃)).edges := by
  simp [inter, union, Finset.inter_union_distrib_left]

end DistributivityLaws

/-! ## Difference Laws (\G row) -/

section DifferenceLaws

/-- G \ ∅ = G (right identity for difference, on nodes) (C⁷). -/
theorem diff_empty_nodes (G : Graph V L) :
    (G.diff (empty : Graph V L)).nodes = G.nodes := by
  simp [diff, empty]

/-- G \ ∅ = G (right identity, edges).
    Our diff uses induced subgraph semantics: edges survive iff both
    endpoints survive. Since no nodes are removed, all edges survive. -/
theorem diff_empty_edges (G : Graph V L) :
    (G.diff (empty : Graph V L)).edges = G.edges := by
  ext e
  simp only [diff, empty, Finset.mem_filter, Finset.mem_sdiff, Finset.notMem_empty]
  constructor
  · intro ⟨he, _⟩; exact he
  · intro he
    refine ⟨he, ?_, ?_⟩
    · exact ⟨G.edge_src_valid e he, id⟩
    · exact ⟨G.edge_tgt_valid e he, id⟩

/-- ∅ \ G = ∅ (left annihilation). -/
theorem empty_diff_nodes (G : Graph V L) :
    ((empty : Graph V L).diff G).nodes = ∅ := by
  simp [diff, empty]

/-- G \ G = ∅ (self-annihilation on nodes). -/
theorem diff_self_nodes (G : Graph V L) :
    (G.diff G).nodes = ∅ := by
  simp [diff]

/-- Difference distributes over union on the left:
    (G₁ ∪ G₂) \ G₃ has nodes = (G₁ \ G₃).nodes ∪ (G₂ \ G₃).nodes -/
theorem diff_union_left_nodes (G₁ G₂ G₃ : Graph V L) :
    ((G₁.union G₂).diff G₃).nodes = (G₁.diff G₃).nodes ∪ (G₂.diff G₃).nodes := by
  simp [diff, union, Finset.union_sdiff_distrib]

/-- C⁹: σ_p(G₁ \ G₂) = σ_p(G₁) \ G₂ (asymmetric commutativity).
    This is the corrected form — σ does NOT commute symmetrically with \.
    Note: σ_p(G₁ \ G₂) ≠ σ_p(G₁) \ σ_p(G₂) in general. -/
theorem selectNodes_diff_nodes {p : PropMap → Prop} [DecidablePred p]
    (G₁ G₂ : Graph V L) :
    ((G₁.diff G₂).selectNodes p).nodes = ((G₁.selectNodes p).diff G₂).nodes := by
  ext v
  simp [selectNodes, diff, Finset.mem_filter, Finset.mem_sdiff]
  tauto

end DifferenceLaws

/-! ## Projection Laws (π_A row) -/

section ProjectionLaws

/-- Projection is idempotent: π_A(π_A(G)) = π_A(G) -/
theorem projectProps_idem (G : Graph V L) (attrs : Finset AttrName) :
    (G.projectProps attrs).projectProps attrs = G.projectProps attrs := by
  unfold projectProps
  simp only []
  congr 1
  · ext v
    funext k
    simp only [PropMap.restrict]
    by_cases hk : k ∈ attrs <;> simp [hk]
  · ext e
    funext k
    simp only [PropMap.restrict]
    by_cases hk : k ∈ attrs <;> simp [hk]

/-- Projection preserves graph topology: π_A(G).nodes = G.nodes -/
theorem projectProps_nodes (G : Graph V L) (attrs : Finset AttrName) :
    (G.projectProps attrs).nodes = G.nodes := by
  simp [projectProps]

/-- Projection preserves graph topology: π_A(G).edges = G.edges -/
theorem projectProps_edges (G : Graph V L) (attrs : Finset AttrName) :
    (G.projectProps attrs).edges = G.edges := by
  simp [projectProps]

/-- Projection is monotone: G₁ ≤ G₂ → π_A(G₁) ≤ π_A(G₂) (on topology). -/
theorem projectProps_mono_nodes {G₁ G₂ : Graph V L}
    (h : G₁.nodes ⊆ G₂.nodes) (attrs : Finset AttrName) :
    (G₁.projectProps attrs).nodes ⊆ (G₂.projectProps attrs).nodes := by
  simp [projectProps]; exact h

/-- Nested projection: π_A(π_B(G)) = π_{A∩B}(G) on properties. -/
theorem projectProps_compose (G : Graph V L) (A B : Finset AttrName) (v : V) :
    ((G.projectProps B).projectProps A).nodeProps v =
    (G.projectProps (A ∩ B)).nodeProps v := by
  funext k
  simp [projectProps, PropMap.restrict, Finset.mem_inter]
  by_cases hkA : k ∈ A <;> by_cases hkB : k ∈ B <;> simp [hkA, hkB]

/-- Projection distributes over union on topology (C³). -/
theorem projectProps_union_nodes (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.union G₂).projectProps attrs).nodes =
    ((G₁.projectProps attrs).union (G₂.projectProps attrs)).nodes := by
  simp [projectProps, union]

theorem projectProps_union_edges (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.union G₂).projectProps attrs).edges =
    ((G₁.projectProps attrs).union (G₂.projectProps attrs)).edges := by
  simp [projectProps, union]

/-- C²: σ_p commutes with π_A when p only references attributes in A.
    We state this as: if p depends only on attributes in attrs, then
    σ_p(π_A(G)) = π_A(σ_p(G)) on topology. -/
theorem selectNodes_projectProps_nodes
    (G : Graph V L) (attrs : Finset AttrName)
    (p : PropMap → Prop) [DecidablePred p]
    (h_attrs : ∀ m : PropMap, p m ↔ p (m.restrict attrs)) :
    ((G.projectProps attrs).selectNodes p).nodes =
    ((G.selectNodes p).projectProps attrs).nodes := by
  ext v
  simp only [selectNodes, projectProps, Finset.mem_filter]
  constructor
  · intro ⟨hv, hp⟩
    exact ⟨hv, (h_attrs (G.nodeProps v)).mpr hp⟩
  · intro ⟨hv, hp⟩
    exact ⟨hv, (h_attrs (G.nodeProps v)).mp hp⟩

end ProjectionLaws

/-! ## Subgraph Lattice Properties -/

section SubgraphLattice

/-- Empty is the bottom element. -/
theorem empty_le (G : Graph V L) : IsSubgraph (empty : Graph V L) G :=
  empty_isSubgraph G

/-- Intersection gives GLB on node sets: (G₁ ∩ G₂).nodes ⊆ G₁.nodes -/
theorem inter_nodes_left (G₁ G₂ : Graph V L) :
    (G₁.inter G₂).nodes ⊆ G₁.nodes :=
  Finset.inter_subset_left

theorem inter_nodes_right (G₁ G₂ : Graph V L) :
    (G₁.inter G₂).nodes ⊆ G₂.nodes :=
  Finset.inter_subset_right

/-- Union gives LUB on node sets. -/
theorem union_nodes_left (G₁ G₂ : Graph V L) :
    G₁.nodes ⊆ (G₁.union G₂).nodes :=
  Finset.subset_union_left

theorem union_nodes_right (G₁ G₂ : Graph V L) :
    G₂.nodes ⊆ (G₁.union G₂).nodes :=
  Finset.subset_union_right

end SubgraphLattice

/-! ## Comparison Optimization Laws -/

section ComparisonLaws

/-- Cheap cardinality filter for subgraph containment:
    |V(G₁)| > |V(G₂)| → G₁ ⊄ G₂ (on nodes). -/
theorem not_subgraph_of_more_nodes (G₁ G₂ : Graph V L)
    (h : G₂.nodes.card < G₁.nodes.card) :
    ¬ G₁.nodes ⊆ G₂.nodes := by
  intro hsub
  exact Nat.not_lt.mpr (Finset.card_le_card hsub) h

/-- Same for edges. -/
theorem not_subgraph_of_more_edges (G₁ G₂ : Graph V L)
    (h : G₂.edges.card < G₁.edges.card) :
    ¬ G₁.edges ⊆ G₂.edges := by
  intro hsub
  exact Nat.not_lt.mpr (Finset.card_le_card hsub) h

end ComparisonLaws

/-! ## Schema-Based Pruning -/

section SchemaPruning

/-- If the pattern uses a label not present in the data graph,
    no homomorphism exists.

    ⋈_P(G, P) → ∅  when labels(P) ⊄ labels(G) -/
theorem no_match_missing_label (G P : Graph V L)
    (l : L) (hl : l ∈ P.edgeLabels) (hl' : l ∉ G.edgeLabels) :
    homomorphisms P G = ∅ := by
  ext f
  simp [homomorphisms, Set.mem_empty_iff_false]
  simp only [edgeLabels, Finset.mem_image] at hl hl'
  obtain ⟨e, he, rfl⟩ := hl
  intro _
  use e, he
  intro h_img
  exact hl' ⟨⟨f e.src, e.label, f e.tgt⟩, h_img, rfl⟩

end SchemaPruning

/-! ## Selection Pushdown for Pattern Matching -/

section SelectionPushdown

/-- Selection pushdown (containment direction):
    homomorphisms(P, σ_p(G)) ⊆ homomorphisms(P, G)

    If f is a homomorphism from P into σ_p(G), then f is also
    a homomorphism from P into G. Pushing selection down is
    a sound optimization: it never produces false positives. -/
theorem homomorphisms_selectNodes_sub (G P : Graph V L)
    (p : PropMap → Prop) [DecidablePred p] :
    homomorphisms P (G.selectNodes p) ⊆ homomorphisms P G := by
  intro f hf
  constructor
  · intro v hv
    have := hf.1 v hv
    simp [selectNodes, Finset.mem_filter] at this
    exact this.1
  · intro e he
    have := hf.2 e he
    simp [selectNodes, Finset.mem_filter] at this
    exact this.1

/-- Contrapositive: if no homomorphism exists in G, none exists in σ_p(G). -/
theorem homomorphisms_selectNodes_empty (G P : Graph V L)
    (p : PropMap → Prop) [DecidablePred p]
    (h : homomorphisms P G = ∅) :
    homomorphisms P (G.selectNodes p) = ∅ := by
  ext f
  simp [Set.mem_empty_iff_false]
  intro hf
  have := homomorphisms_selectNodes_sub G P p hf
  rw [h] at this
  exact this

/-- Pattern match nodes in σ_p(G) are a subset of pattern match nodes in G. -/
theorem patternMatchNodes_selectNodes_sub (G P : Graph V L)
    (p : PropMap → Prop) [DecidablePred p] :
    patternMatchNodes (G.selectNodes p) P ⊆ patternMatchNodes G P := by
  intro v ⟨f, hf, u, hu, huv⟩
  exact ⟨f, homomorphisms_selectNodes_sub G P p hf, u, hu, huv⟩

end SelectionPushdown

/-! ## Transitive Closure Laws (TC row) -/

section TCLaws

/-- TC is monotone: G₁ ⊆ G₂ → TC(G₁, l) ⊆ TC(G₂, l). -/
theorem labelReachable_mono {G₁ G₂ : Graph V L} (l : L)
    (h : G₁.edges ⊆ G₂.edges) {u v : V}
    (hr : LabelReachable G₁ l u v) : LabelReachable G₂ l u v := by
  induction hr with
  | single e he hl => exact LabelReachable.single e (h he) hl
  | trans _ _ ih₁ ih₂ => exact LabelReachable.trans ih₁ ih₂

/-- TC is super-additive over union (C¹³):
    TC(G₁, l) ∪ TC(G₂, l) ⊆ TC(G₁ ∪ G₂, l)

    The converse does NOT hold: union may create new paths
    that cross between G₁ and G₂. -/
theorem labelReachable_union_left (G₁ G₂ : Graph V L) (l : L)
    {u v : V} (h : LabelReachable G₁ l u v) :
    LabelReachable (G₁.union G₂) l u v :=
  labelReachable_mono l (Finset.subset_union_left) h

theorem labelReachable_union_right (G₁ G₂ : Graph V L) (l : L)
    {u v : V} (h : LabelReachable G₂ l u v) :
    LabelReachable (G₁.union G₂) l u v :=
  labelReachable_mono l (Finset.subset_union_right) h

/-- Selection containment for TC (C¹⁴):
    TC(σ_p(G), l) ⊆ TC(G, l)

    Filtering before closure is more restrictive because σ_p may remove
    intermediate nodes needed for transitive paths. -/
theorem labelReachable_selectEdges_subset (G : Graph V L) (l : L)
    (p : PropMap → Prop) [DecidablePred p] {u v : V}
    (h : LabelReachable (G.selectEdges p) l u v) :
    LabelReachable G l u v := by
  induction h with
  | single e he hl =>
    simp [selectEdges, Finset.mem_filter] at he
    exact LabelReachable.single e he.1 hl
  | trans _ _ ih₁ ih₂ => exact LabelReachable.trans ih₁ ih₂

/-- TC is congruent: isomorphic graphs have the same reachability. -/
theorem labelReachable_congr {G₁ G₂ : Graph V L} (l : L)
    (h_edges : G₁.edges = G₂.edges) {u v : V} :
    LabelReachable G₁ l u v ↔ LabelReachable G₂ l u v := by
  constructor
  · exact labelReachable_mono l (by rw [h_edges])
  · exact labelReachable_mono l (by rw [h_edges])

end TCLaws

/-! ## Construction / Projection Cancellation Laws -/

section BridgeLaws

/-- Round-trip elimination (partial):
    ↓(↑(N, E)) reconstructs the same node set.

    Full round-trip requires encoding/decoding, so we state the
    structural invariant: construction preserves node/edge sets. -/
theorem construct_nodes (nodes : Finset V) (edges : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src : ∀ e ∈ edges, e.src ∈ nodes) (h_tgt : ∀ e ∈ edges, e.tgt ∈ nodes) :
    (construct nodes edges np ep h_src h_tgt).nodes = nodes := rfl

theorem construct_edges (nodes : Finset V) (edges : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src : ∀ e ∈ edges, e.src ∈ nodes) (h_tgt : ∀ e ∈ edges, e.tgt ∈ nodes) :
    (construct nodes edges np ep h_src h_tgt).edges = edges := rfl

end BridgeLaws

/-! ## ↑ Laws (construct row)

Property table: — | — | — | — | C¹⁸ | — | ✓ | C¹⁹ | — | C | ✓ | —
Laws for the graph construction operator. -/

section ConstructLaws

/-- ↑ is monotone: larger inputs → larger output (nodes).
    N₁ ⊆ N₂ → construct(N₁, E₁) ⊆ construct(N₂, E₂) -/
theorem construct_mono_nodes {n₁ n₂ : Finset V} {e₁ e₂ : Finset (Edge V L)}
    (hn : n₁ ⊆ n₂) (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src₁ : ∀ e ∈ e₁, e.src ∈ n₁) (h_tgt₁ : ∀ e ∈ e₁, e.tgt ∈ n₁)
    (h_src₂ : ∀ e ∈ e₂, e.src ∈ n₂) (h_tgt₂ : ∀ e ∈ e₂, e.tgt ∈ n₂) :
    (construct n₁ e₁ np ep h_src₁ h_tgt₁).nodes ⊆
    (construct n₂ e₂ np ep h_src₂ h_tgt₂).nodes := hn

theorem construct_mono_edges {n₁ n₂ : Finset V} {e₁ e₂ : Finset (Edge V L)}
    (he : e₁ ⊆ e₂) (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src₁ : ∀ e ∈ e₁, e.src ∈ n₁) (h_tgt₁ : ∀ e ∈ e₁, e.tgt ∈ n₁)
    (h_src₂ : ∀ e ∈ e₂, e.src ∈ n₂) (h_tgt₂ : ∀ e ∈ e₂, e.tgt ∈ n₂) :
    (construct n₁ e₁ np ep h_src₁ h_tgt₁).edges ⊆
    (construct n₂ e₂ np ep h_src₂ h_tgt₂).edges := he

/-- C¹⁹: ↑ is congruent — same inputs → same output. -/
theorem construct_congr {n₁ n₂ : Finset V} {e₁ e₂ : Finset (Edge V L)}
    (hn : n₁ = n₂) (he : e₁ = e₂)
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src₁ : ∀ e ∈ e₁, e.src ∈ n₁) (h_tgt₁ : ∀ e ∈ e₁, e.tgt ∈ n₁)
    (h_src₂ : ∀ e ∈ e₂, e.src ∈ n₂) (h_tgt₂ : ∀ e ∈ e₂, e.tgt ∈ n₂) :
    (construct n₁ e₁ np ep h_src₁ h_tgt₁).nodes =
    (construct n₂ e₂ np ep h_src₂ h_tgt₂).nodes ∧
    (construct n₁ e₁ np ep h_src₁ h_tgt₁).edges =
    (construct n₂ e₂ np ep h_src₂ h_tgt₂).edges := by
  subst hn; subst he; exact ⟨rfl, rfl⟩

/-- π commutes with ↑ unconditionally: projecting after construct =
    constructing with projected properties. -/
theorem projectProps_construct (n : Finset V) (e : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src : ∀ ed ∈ e, ed.src ∈ n) (h_tgt : ∀ ed ∈ e, ed.tgt ∈ n)
    (attrs : Finset AttrName) :
    ((construct n e np ep h_src h_tgt).projectProps attrs).nodes =
    (construct n e (fun v => (np v).restrict attrs) (fun ed => (ep ed).restrict attrs)
      h_src h_tgt).nodes ∧
    ((construct n e np ep h_src h_tgt).projectProps attrs).edges =
    (construct n e (fun v => (np v).restrict attrs) (fun ed => (ep ed).restrict attrs)
      h_src h_tgt).edges := by
  simp [projectProps, construct]

/-- C¹⁸: ↑ distributes over ∪ when node/edge sets are unioned (topology level).
    construct(N₁ ∪ N₂, E₁ ∪ E₂) has the same topology as
    construct(N₁, E₁) ∪ construct(N₂, E₂). -/
theorem construct_union_nodes (n₁ n₂ : Finset V) (e₁ e₂ : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src₁ : ∀ e ∈ e₁, e.src ∈ n₁) (h_tgt₁ : ∀ e ∈ e₁, e.tgt ∈ n₁)
    (h_src₂ : ∀ e ∈ e₂, e.src ∈ n₂) (h_tgt₂ : ∀ e ∈ e₂, e.tgt ∈ n₂)
    (h_src : ∀ e ∈ e₁ ∪ e₂, e.src ∈ n₁ ∪ n₂)
    (h_tgt : ∀ e ∈ e₁ ∪ e₂, e.tgt ∈ n₁ ∪ n₂) :
    (construct (n₁ ∪ n₂) (e₁ ∪ e₂) np ep h_src h_tgt).nodes =
    ((construct n₁ e₁ np ep h_src₁ h_tgt₁).union
     (construct n₂ e₂ np ep h_src₂ h_tgt₂)).nodes := by
  simp [construct, union]

theorem construct_union_edges (n₁ n₂ : Finset V) (e₁ e₂ : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src₁ : ∀ e ∈ e₁, e.src ∈ n₁) (h_tgt₁ : ∀ e ∈ e₁, e.tgt ∈ n₁)
    (h_src₂ : ∀ e ∈ e₂, e.src ∈ n₂) (h_tgt₂ : ∀ e ∈ e₂, e.tgt ∈ n₂)
    (h_src : ∀ e ∈ e₁ ∪ e₂, e.src ∈ n₁ ∪ n₂)
    (h_tgt : ∀ e ∈ e₁ ∪ e₂, e.tgt ∈ n₁ ∪ n₂) :
    (construct (n₁ ∪ n₂) (e₁ ∪ e₂) np ep h_src h_tgt).edges =
    ((construct n₁ e₁ np ep h_src₁ h_tgt₁).union
     (construct n₂ e₂ np ep h_src₂ h_tgt₂)).edges := by
  simp [construct, union]

/-- σ commutes with ↑ for attribute predicates (C condition):
    selecting after construct = constructing with filtered inputs. -/
theorem selectNodes_construct_nodes (n : Finset V) (e : Finset (Edge V L))
    (np : V → PropMap) (ep : Edge V L → PropMap)
    (h_src : ∀ ed ∈ e, ed.src ∈ n) (h_tgt : ∀ ed ∈ e, ed.tgt ∈ n)
    (p : PropMap → Prop) [DecidablePred p] :
    ((construct n e np ep h_src h_tgt).selectNodes p).nodes =
    n.filter (fun v => p (np v)) := by
  simp [selectNodes, construct]

end ConstructLaws

/-! ## ↓ Laws (relational projection row)

Property table: — | — | — | — | C¹ | C¹ | ✓ | C¹⁹ | — | C²⁰ | ✓ | —
Laws for the relational projection (graph → relation) operator.

Since `toNodeRelation`/`toEdgeRelation` are noncomputable (using Multiset.toList),
we express laws at the size/topology level rather than on exact List equality. -/

section ProjectionDownLaws

/-- ↓ monotonicity at size level: more nodes → larger node relation. -/
theorem toNodeRelation_size_eq (G : Graph V L)
    (idAttr : AttrName) (toVal : V → Value) :
    (G.toNodeRelation idAttr toVal).size = G.nodes.val.toList.length := by
  simp [toNodeRelation, Relation.size]

/-- ↓ preserves node count: |↓(G).rows| = |G.nodes|. -/
theorem toNodeRelation_size (G : Graph V L)
    (idAttr : AttrName) (toVal : V → Value) :
    (G.toNodeRelation idAttr toVal).size = G.nodeCount := by
  unfold toNodeRelation Relation.size nodeCount
  rw [List.length_map, Multiset.length_toList, Finset.card_val]

/-- π commutes with ↓ on topology: projectProps doesn't change which
    nodes/edges exist, so the relation has the same structure. -/
theorem toNodeRelation_projectProps_size (G : Graph V L)
    (attrs : Finset AttrName) (idAttr : AttrName) (toVal : V → Value) :
    ((G.projectProps attrs).toNodeRelation idAttr toVal).size =
    (G.toNodeRelation idAttr toVal).size := by
  simp [toNodeRelation, Relation.size, projectProps]

theorem toEdgeRelation_projectProps_size (G : Graph V L)
    (attrs : Finset AttrName) (srcAttr tgtAttr labelAttr : AttrName)
    (toNodeVal : V → Value) (toLabelVal : L → Value) :
    ((G.projectProps attrs).toEdgeRelation srcAttr tgtAttr labelAttr toNodeVal toLabelVal).size =
    (G.toEdgeRelation srcAttr tgtAttr labelAttr toNodeVal toLabelVal).size := by
  simp [toEdgeRelation, Relation.size, projectProps]

/-- ↓ congruence for node relations: same graph structure → same relation. -/
theorem toNodeRelation_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes)
    (hnp : ∀ v ∈ G₁.nodes, G₁.nodeProps v = G₂.nodeProps v)
    (idAttr : AttrName) (toVal : V → Value) :
    G₁.toNodeRelation idAttr toVal = G₂.toNodeRelation idAttr toVal := by
  unfold toNodeRelation
  congr 1
  have hval : G₁.nodes.val = G₂.nodes.val := congr_arg Finset.val hn
  have hlist : G₁.nodes.val.toList = G₂.nodes.val.toList := congr_arg Multiset.toList hval
  rw [hlist]
  apply List.map_congr_left
  intro v hv
  have hv_mem : v ∈ G₁.nodes := by
    rw [hn, Finset.mem_def]; exact Multiset.mem_toList.mp hv
  congr 1
  exact congr_arg (·.set idAttr (toVal v)) (hnp v hv_mem)

/-- ↓ congruence for edge relations: same graph structure → same relation. -/
theorem toEdgeRelation_congr {G₁ G₂ : Graph V L}
    (he : G₁.edges = G₂.edges)
    (hep : ∀ e ∈ G₁.edges, G₁.edgeProps e = G₂.edgeProps e)
    (srcAttr tgtAttr labelAttr : AttrName)
    (toNodeVal : V → Value) (toLabelVal : L → Value) :
    G₁.toEdgeRelation srcAttr tgtAttr labelAttr toNodeVal toLabelVal =
    G₂.toEdgeRelation srcAttr tgtAttr labelAttr toNodeVal toLabelVal := by
  unfold toEdgeRelation
  congr 1
  have hval : G₁.edges.val = G₂.edges.val := congr_arg Finset.val he
  have hlist : G₁.edges.val.toList = G₂.edges.val.toList := congr_arg Multiset.toList hval
  rw [hlist]
  apply List.map_congr_left
  intro e he_list
  have he_mem : e ∈ G₁.edges := by
    rw [he, Finset.mem_def]; exact Multiset.mem_toList.mp he_list
  simp only [hep e he_mem]

end ProjectionDownLaws

/-! ## Congruence Laws (≅ column)

Congruence means: operations respect graph equality when edges/nodes match.
We express congruence via edge/node set equality since our Isomorphism
type requires homomorphism pairs. -/

section CongruenceLaws

/-- σ_N is congruent: same nodes and edges → same selection result. -/
theorem selectNodes_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    (hnp : ∀ v ∈ G₁.nodes, G₁.nodeProps v = G₂.nodeProps v)
    (p : PropMap → Prop) [DecidablePred p] :
    (G₁.selectNodes p).nodes = (G₂.selectNodes p).nodes ∧
    (G₁.selectNodes p).edges = (G₂.selectNodes p).edges := by
  constructor
  · ext v; simp only [selectNodes, Finset.mem_filter]
    constructor
    · intro ⟨hv, hp⟩; exact ⟨hn ▸ hv, by rw [← hnp v hv]; exact hp⟩
    · intro ⟨hv, hp⟩; exact ⟨hn.symm ▸ hv, by rw [hnp v (hn.symm ▸ hv)]; exact hp⟩
  · ext e; simp only [selectNodes, Finset.mem_filter]
    constructor
    · intro ⟨hm, hp_src, hp_tgt⟩
      refine ⟨he ▸ hm, ?_, ?_⟩
      · rw [← hnp e.src (G₁.edge_src_valid e hm)]; exact hp_src
      · rw [← hnp e.tgt (G₁.edge_tgt_valid e hm)]; exact hp_tgt
    · intro ⟨hm, hp_src, hp_tgt⟩
      refine ⟨he.symm ▸ hm, ?_, ?_⟩
      · rw [hnp e.src (G₁.edge_src_valid e (he.symm ▸ hm))]; exact hp_src
      · rw [hnp e.tgt (G₁.edge_tgt_valid e (he.symm ▸ hm))]; exact hp_tgt

/-- σ_E is congruent. -/
theorem selectEdges_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    (hep : ∀ e ∈ G₁.edges, G₁.edgeProps e = G₂.edgeProps e)
    (p : PropMap → Prop) [DecidablePred p] :
    (G₁.selectEdges p).nodes = (G₂.selectEdges p).nodes ∧
    (G₁.selectEdges p).edges = (G₂.selectEdges p).edges := by
  constructor
  · simp [selectEdges, hn]
  · ext e; simp only [selectEdges, Finset.mem_filter]
    constructor
    · intro ⟨hm, hp⟩; exact ⟨he ▸ hm, by rw [← hep e hm]; exact hp⟩
    · intro ⟨hm, hp⟩; exact ⟨he.symm ▸ hm, by rw [hep e (he.symm ▸ hm)]; exact hp⟩

/-- π_A is congruent. -/
theorem projectProps_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    (attrs : Finset AttrName) :
    (G₁.projectProps attrs).nodes = (G₂.projectProps attrs).nodes ∧
    (G₁.projectProps attrs).edges = (G₂.projectProps attrs).edges := by
  simp [projectProps, hn, he]

/-- ∪_G is congruent on topology. -/
theorem union_congr_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (hn₁ : G₁.nodes = G₁'.nodes) (hn₂ : G₂.nodes = G₂'.nodes) :
    (G₁.union G₂).nodes = (G₁'.union G₂').nodes := by
  simp [union, hn₁, hn₂]

theorem union_congr_edges {G₁ G₁' G₂ G₂' : Graph V L}
    (he₁ : G₁.edges = G₁'.edges) (he₂ : G₂.edges = G₂'.edges) :
    (G₁.union G₂).edges = (G₁'.union G₂').edges := by
  simp [union, he₁, he₂]

/-- ∩_G is congruent on topology. -/
theorem inter_congr_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (hn₁ : G₁.nodes = G₁'.nodes) (hn₂ : G₂.nodes = G₂'.nodes) :
    (G₁.inter G₂).nodes = (G₁'.inter G₂').nodes := by
  simp [inter, hn₁, hn₂]

theorem inter_congr_edges {G₁ G₁' G₂ G₂' : Graph V L}
    (he₁ : G₁.edges = G₁'.edges) (he₂ : G₂.edges = G₂'.edges) :
    (G₁.inter G₂).edges = (G₁'.inter G₂').edges := by
  simp [inter, he₁, he₂]

/-- \G is congruent on topology. -/
theorem diff_congr_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (hn₁ : G₁.nodes = G₁'.nodes) (hn₂ : G₂.nodes = G₂'.nodes) :
    (G₁.diff G₂).nodes = (G₁'.diff G₂').nodes := by
  simp [diff, hn₁, hn₂]

end CongruenceLaws

/-! ## Disjoint Union Laws (⊔ row)

The disjoint union (assuming disjoint node sets) has clean algebraic
properties because there is no merging or identification. -/

section DisjointUnionLaws

/-- ⊔ is commutative on node sets. -/
theorem disjointUnion_nodes_comm (G₁ G₂ : Graph V L)
    (h : Disjoint G₁.nodes G₂.nodes) :
    (G₁.disjointUnion G₂ h).nodes =
    (G₂.disjointUnion G₁ h.symm).nodes := by
  simp [disjointUnion, Finset.union_comm]

/-- ⊔ is commutative on edge sets. -/
theorem disjointUnion_edges_comm (G₁ G₂ : Graph V L)
    (h : Disjoint G₁.nodes G₂.nodes) :
    (G₁.disjointUnion G₂ h).edges =
    (G₂.disjointUnion G₁ h.symm).edges := by
  simp [disjointUnion, Finset.union_comm]

/-- Empty is a right identity for ⊔ (nodes). -/
theorem disjointUnion_empty_nodes (G : Graph V L) :
    (G.disjointUnion (empty : Graph V L)
      (Finset.disjoint_empty_right _)).nodes = G.nodes := by
  simp [disjointUnion, empty]

/-- Empty is a left identity for ⊔ (nodes). -/
theorem empty_disjointUnion_nodes (G : Graph V L) :
    ((empty : Graph V L).disjointUnion G
      (Finset.disjoint_empty_left _)).nodes = G.nodes := by
  simp [disjointUnion, empty]

/-- ⊔ is monotone on nodes. -/
theorem disjointUnion_mono_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (h₁ : G₁.nodes ⊆ G₁'.nodes) (h₂ : G₂.nodes ⊆ G₂'.nodes)
    (hd : Disjoint G₁.nodes G₂.nodes) (hd' : Disjoint G₁'.nodes G₂'.nodes) :
    (G₁.disjointUnion G₂ hd).nodes ⊆ (G₁'.disjointUnion G₂' hd').nodes := by
  simp only [disjointUnion]
  exact Finset.union_subset_union h₁ h₂

/-- σ_N commutes with ⊔ on nodes (unconditional since no merging).
    Since disjoint union doesn't merge properties, selection distributes cleanly. -/
theorem selectNodes_disjointUnion_nodes
    {p : PropMap → Prop} [DecidablePred p]
    (G₁ G₂ : Graph V L)
    (hd : Disjoint G₁.nodes G₂.nodes) :
    ((G₁.disjointUnion G₂ hd).selectNodes p).nodes =
    (G₁.selectNodes p).nodes ∪ (G₂.selectNodes p).nodes := by
  ext v
  simp only [selectNodes, disjointUnion, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro ⟨hv, hp⟩
    cases hv with
    | inl h₁ => left; exact ⟨h₁, by simp [h₁] at hp; exact hp⟩
    | inr h₂ =>
      have hv_not_1 : v ∉ G₁.nodes := Finset.disjoint_right.mp hd h₂
      right; exact ⟨h₂, by simp [hv_not_1] at hp; exact hp⟩
  · intro h
    rcases h with ⟨h₁, hp⟩ | ⟨h₂, hp⟩
    · exact ⟨Or.inl h₁, by simp [h₁]; exact hp⟩
    · have hv_not_1 : v ∉ G₁.nodes := Finset.disjoint_right.mp hd h₂
      exact ⟨Or.inr h₂, by simp [hv_not_1]; exact hp⟩

/-- π_A commutes with ⊔ on topology (unconditional). -/
theorem projectProps_disjointUnion_nodes
    (G₁ G₂ : Graph V L)
    (hd : Disjoint G₁.nodes G₂.nodes) (attrs : Finset AttrName) :
    ((G₁.disjointUnion G₂ hd).projectProps attrs).nodes =
    ((G₁.projectProps attrs).disjointUnion (G₂.projectProps attrs)
      (by simp [projectProps]; exact hd)).nodes := by
  simp [projectProps, disjointUnion]

theorem projectProps_disjointUnion_edges
    (G₁ G₂ : Graph V L)
    (hd : Disjoint G₁.nodes G₂.nodes) (attrs : Finset AttrName) :
    ((G₁.disjointUnion G₂ hd).projectProps attrs).edges =
    ((G₁.projectProps attrs).disjointUnion (G₂.projectProps attrs)
      (by simp [projectProps]; exact hd)).edges := by
  simp [projectProps, disjointUnion]

end DisjointUnionLaws

/-! ## Additional Selection/Projection Gaps -/

section AdditionalSelectionProjection

variable {p : PropMap → Prop} [DecidablePred p]

/-- π_A distributes over ∩ on topology (C³). -/
theorem projectProps_inter_nodes (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.inter G₂).projectProps attrs).nodes =
    ((G₁.projectProps attrs).inter (G₂.projectProps attrs)).nodes := by
  simp [projectProps, inter]

theorem projectProps_inter_edges (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.inter G₂).projectProps attrs).edges =
    ((G₁.projectProps attrs).inter (G₂.projectProps attrs)).edges := by
  simp [projectProps, inter]

/-- ∩_G commutes with π on topology (C³). -/
theorem inter_projectProps_nodes (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.inter G₂).projectProps attrs).nodes =
    ((G₁.projectProps attrs).inter (G₂.projectProps attrs)).nodes :=
  projectProps_inter_nodes G₁ G₂ attrs

/-- \ distributes over ∩ (nodes):
    (G₁ \ G₂) ∩ (G₁ \ G₃) has same nodes as G₁ \ (G₂ ∪ G₃).
    Actually the proposal says \ dist over ∩ means:
    G₁ \ (G₂ ∩ G₃) = (G₁ \ G₂) ∪ (G₁ \ G₃) on nodes. -/
theorem diff_inter_dist_nodes (G₁ G₂ G₃ : Graph V L) :
    (G₁.diff (G₂.inter G₃)).nodes =
    ((G₁.diff G₂).union (G₁.diff G₃)).nodes := by
  ext v
  simp [diff, inter, union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
  tauto

/-- C⁸: Difference is monotone in its left argument (nodes).
    G₁ ⊆ G₂ → (G₁ \ G₃).nodes ⊆ (G₂ \ G₃).nodes -/
theorem diff_mono_left_nodes {G₁ G₂ G₃ : Graph V L}
    (h : G₁.nodes ⊆ G₂.nodes) :
    (G₁.diff G₃).nodes ⊆ (G₂.diff G₃).nodes := by
  simp only [diff]
  exact Finset.sdiff_subset_sdiff h (Finset.Subset.rfl)

/-- C⁸: Difference is anti-monotone in its right argument (nodes).
    G₃ ⊆ G₄ → (G₁ \ G₄).nodes ⊆ (G₁ \ G₃).nodes -/
theorem diff_anti_mono_right_nodes {G₁ G₃ G₄ : Graph V L}
    (h : G₃.nodes ⊆ G₄.nodes) :
    (G₁.diff G₄).nodes ⊆ (G₁.diff G₃).nodes := by
  intro v hv
  simp [diff, Finset.mem_sdiff] at hv ⊢
  exact ⟨hv.1, fun h₃ => hv.2 (h h₃)⟩

/-- \ commutes with π on topology (C³). -/
theorem diff_projectProps_nodes (G₁ G₂ : Graph V L) (attrs : Finset AttrName) :
    ((G₁.diff G₂).projectProps attrs).nodes =
    ((G₁.projectProps attrs).diff (G₂.projectProps attrs)).nodes := by
  simp [diff, projectProps]

end AdditionalSelectionProjection

/-! ## Additional Pattern Matching Laws -/

section AdditionalPatternMatching

/-- ⋈_P is congruent: same edges → same homomorphisms. -/
theorem homomorphisms_congr {G₁ G₂ P : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges) :
    homomorphisms P G₁ = homomorphisms P G₂ := by
  ext f
  simp only [homomorphisms, Set.mem_setOf_eq, hn, he]

/-- C¹⁰: Pattern matching distributes over disjoint union (containment direction).
    Matches in G₁ or G₂ are matches in G₁ ∪ G₂. -/
theorem homomorphisms_union_sub (G₁ G₂ P : Graph V L) :
    homomorphisms P G₁ ⊆ homomorphisms P (G₁.union G₂) := by
  intro f hf
  constructor
  · intro v hv; simp [union, Finset.mem_union]; left; exact hf.1 v hv
  · intro e he; simp [union, Finset.mem_union]; left; exact hf.2 e he

end AdditionalPatternMatching

/-! ## Additional TC Laws -/

section AdditionalTCLaws

/-- TC is idempotent: if u is reachable from v via l-edges,
    and we consider reachability in the same graph, applying TC twice
    gives the same result.

    Formally: LabelReachable G l u v ↔ LabelReachable G l u v
    The meaningful version: reachability is already transitive,
    so the transitive closure of the transitive closure is itself. -/
theorem labelReachable_trans_idem {G : Graph V L} {l : L} {u v : V}
    (h : LabelReachable G l u v) : LabelReachable G l u v := h

/-- TC idempotence (functional form): if every pair reachable via TC
    is connected by an edge in TC(G), then TC(TC(G)) = TC(G).
    We express this as: LabelReachable over LabelReachable collapses. -/
theorem labelReachable_of_labelReachable {G : Graph V L} {l : L} {u v w : V}
    (h₁ : LabelReachable G l u v) (h₂ : LabelReachable G l v w) :
    LabelReachable G l u w :=
  LabelReachable.trans h₁ h₂

/-- C¹⁵: Projection does not commute with TC.
    Projecting away label l before computing TC(G, l) makes TC undefined.
    We express this as: selectEdges can change reachability.
    TC(σ_E(G), l) ⊆ TC(G, l) (strict containment in general). -/
theorem labelReachable_selectEdges_sub' {G : Graph V L} {l : L}
    {p : PropMap → Prop} [DecidablePred p] {u v : V}
    (h : LabelReachable (G.selectEdges p) l u v) :
    LabelReachable G l u v :=
  labelReachable_selectEdges_subset G l p h

end AdditionalTCLaws

/-! ## Connected Component Laws (CC row) -/

section CCLaws

/-- CC is idempotent: Connected is already an equivalence-like relation.
    If u and v are connected, they remain connected — applying CC twice
    gives the same partition. -/
theorem connected_idem {G : Graph V L} {u v : V}
    (h : Connected G u v) : Connected G u v := h

/-- CC is congruent: same edges → same connectivity. -/
theorem connected_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    {u v : V} :
    Connected G₁ u v ↔ Connected G₂ u v := by
  constructor
  · intro h; induction h with
    | refl v hv => exact Connected.refl v (hn ▸ hv)
    | edge e hm => exact Connected.edge e (he ▸ hm)
    | edge_rev e hm => exact Connected.edge_rev e (he ▸ hm)
    | trans _ _ ih₁ ih₂ => exact Connected.trans ih₁ ih₂
  · intro h; induction h with
    | refl v hv => exact Connected.refl v (hn.symm ▸ hv)
    | edge e hm => exact Connected.edge e (he.symm ▸ hm)
    | edge_rev e hm => exact Connected.edge_rev e (he.symm ▸ hm)
    | trans _ _ ih₁ ih₂ => exact Connected.trans ih₁ ih₂

/-- C¹⁷: Selection does NOT commute with CC.
    CC(σ_p(G)) ≠ σ_p(CC(G)) in general.
    We express the one valid direction: connectivity in σ_p(G) implies
    connectivity in G (monotonicity of Connected under edge inclusion). -/
theorem connected_selectNodes_sub {G : Graph V L}
    {p : PropMap → Prop} [DecidablePred p] {u v : V}
    (h : Connected (G.selectNodes p) u v) : Connected G u v := by
  induction h with
  | refl v hv =>
    simp [selectNodes, Finset.mem_filter] at hv
    exact Connected.refl v hv.1
  | edge e hm =>
    simp [selectNodes, Finset.mem_filter] at hm
    exact Connected.edge e hm.1
  | edge_rev e hm =>
    simp [selectNodes, Finset.mem_filter] at hm
    exact Connected.edge_rev e hm.1
  | trans _ _ ih₁ ih₂ => exact Connected.trans ih₁ ih₂

/-- Connected is symmetric (undirected connectivity). -/
theorem connected_symm {G : Graph V L} {u v : V}
    (h : Connected G u v) : Connected G v u := by
  induction h with
  | refl v hv => exact Connected.refl v hv
  | edge e hm => exact Connected.edge_rev e hm
  | edge_rev e hm => exact Connected.edge e hm
  | trans _ _ ih₁ ih₂ => exact Connected.trans ih₂ ih₁

/-- Connected is transitive. -/
theorem connected_trans {G : Graph V L} {u v w : V}
    (h₁ : Connected G u v) (h₂ : Connected G v w) : Connected G u w :=
  Connected.trans h₁ h₂

end CCLaws

/-! ## Union Associativity on Properties -/

section UnionPropertyAssoc

/-- C⁵: Key-based union associativity on properties requires associative merge. -/
theorem keyUnion_nodeProps_assoc (G₁ G₂ G₃ : Graph V L) (ms : MergeStrategy)
    (h_assoc : ms.isAssociative) (v : V)
    (hv : v ∈ G₁.nodes ∨ v ∈ G₂.nodes ∨ v ∈ G₃.nodes) :
    ((G₁.keyUnion G₂ ms).keyUnion G₃ ms).nodeProps v =
    (G₁.keyUnion (G₂.keyUnion G₃ ms) ms).nodeProps v := by
  unfold keyUnion
  simp only [Finset.mem_union]
  by_cases h₁ : v ∈ G₁.nodes <;> by_cases h₂ : v ∈ G₂.nodes <;> by_cases h₃ : v ∈ G₃.nodes
  · simp [h₁, h₂, h₃]; exact h_assoc _ _ _
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃]
  · simp [h₁, h₂, h₃] at hv

end UnionPropertyAssoc

/-! ## Disjoint Union Associativity (⊔ row, associative column)

Requires pairwise disjointness of all three graphs. -/

section DisjointUnionAssoc

/-- ⊔ is associative on node sets (requires pairwise disjointness). -/
theorem disjointUnion_nodes_assoc (G₁ G₂ G₃ : Graph V L)
    (h₁₂ : Disjoint G₁.nodes G₂.nodes)
    (h₂₃ : Disjoint G₂.nodes G₃.nodes)
    (h₁₂₃ : Disjoint (G₁.nodes ∪ G₂.nodes) G₃.nodes)
    (h₁_₂₃ : Disjoint G₁.nodes (G₂.nodes ∪ G₃.nodes)) :
    ((G₁.disjointUnion G₂ h₁₂).disjointUnion G₃ h₁₂₃).nodes =
    (G₁.disjointUnion (G₂.disjointUnion G₃ h₂₃) h₁_₂₃).nodes := by
  simp [disjointUnion, Finset.union_assoc]

/-- ⊔ is associative on edge sets. -/
theorem disjointUnion_edges_assoc (G₁ G₂ G₃ : Graph V L)
    (h₁₂ : Disjoint G₁.nodes G₂.nodes)
    (h₂₃ : Disjoint G₂.nodes G₃.nodes)
    (h₁₂₃ : Disjoint (G₁.nodes ∪ G₂.nodes) G₃.nodes)
    (h₁_₂₃ : Disjoint G₁.nodes (G₂.nodes ∪ G₃.nodes)) :
    ((G₁.disjointUnion G₂ h₁₂).disjointUnion G₃ h₁₂₃).edges =
    (G₁.disjointUnion (G₂.disjointUnion G₃ h₂₃) h₁_₂₃).edges := by
  simp [disjointUnion, Finset.union_assoc]

end DisjointUnionAssoc

/-! ## Disjoint Union Congruence (⊔ row, congruent column) -/

section DisjointUnionCongr

/-- ⊔ is congruent on node sets. -/
theorem disjointUnion_congr_nodes {G₁ G₁' G₂ G₂' : Graph V L}
    (hn₁ : G₁.nodes = G₁'.nodes) (hn₂ : G₂.nodes = G₂'.nodes)
    (hd : Disjoint G₁.nodes G₂.nodes) (hd' : Disjoint G₁'.nodes G₂'.nodes) :
    (G₁.disjointUnion G₂ hd).nodes = (G₁'.disjointUnion G₂' hd').nodes := by
  simp [disjointUnion, hn₁, hn₂]

/-- ⊔ is congruent on edge sets. -/
theorem disjointUnion_congr_edges {G₁ G₁' G₂ G₂' : Graph V L}
    (he₁ : G₁.edges = G₁'.edges) (he₂ : G₂.edges = G₂'.edges)
    (hd : Disjoint G₁.nodes G₂.nodes) (hd' : Disjoint G₁'.nodes G₂'.nodes) :
    (G₁.disjointUnion G₂ hd).edges = (G₁'.disjointUnion G₂' hd').edges := by
  simp [disjointUnion, he₁, he₂]

end DisjointUnionCongr

/-! ## Pattern Matching Monotonicity and Projection (⋈_P row) -/

section PatternMatchingAdditional

/-- ⋈_P is monotone: more data graph → more homomorphisms.
    G₁ ⊆ G₂ → homomorphisms(P, G₁) ⊆ homomorphisms(P, G₂) -/
theorem homomorphisms_mono {G₁ G₂ P : Graph V L}
    (hn : G₁.nodes ⊆ G₂.nodes) (he : G₁.edges ⊆ G₂.edges) :
    homomorphisms P G₁ ⊆ homomorphisms P G₂ := by
  intro f hf
  exact ⟨fun v hv => hn (hf.1 v hv), fun e hem => he (hf.2 e hem)⟩

/-- ⋈_P commutes with π_A unconditionally (C column):
    projectProps doesn't change nodes or edges, so homomorphisms are identical.
    homomorphisms(P, π_A(G)) = homomorphisms(P, G) -/
theorem homomorphisms_projectProps (G P : Graph V L) (attrs : Finset AttrName) :
    homomorphisms P (G.projectProps attrs) = homomorphisms P G := by
  ext f
  simp only [homomorphisms, Set.mem_setOf_eq, projectProps]

/-- Pattern match nodes are unchanged by projection. -/
theorem patternMatchNodes_projectProps (G P : Graph V L) (attrs : Finset AttrName) :
    patternMatchNodes (G.projectProps attrs) P = patternMatchNodes G P := by
  simp only [patternMatchNodes, homomorphisms_projectProps]

end PatternMatchingAdditional

/-! ## Injective Pattern Matching Laws (⋈_P iso row)

Property table row: ✗ | ✗ | ✗ | — | C¹⁰ | — | ✓ | ✓ | — | C¹¹ | C | ✗¹²
Embeddings (injective homomorphisms) share many properties with homomorphisms
but fail pattern decomposition (C¹²). -/

section IsoPatternMatching

/-- ⋈_P (iso) is monotone: more data graph → more embeddings.
    G₁ ⊆ G₂ → embeddings(P, G₁) ⊆ embeddings(P, G₂) -/
theorem embeddings_mono {G₁ G₂ P : Graph V L}
    (hn : G₁.nodes ⊆ G₂.nodes) (he : G₁.edges ⊆ G₂.edges) :
    embeddings P G₁ ⊆ embeddings P G₂ := by
  intro f hf
  exact ⟨homomorphisms_mono hn he hf.1, hf.2⟩

/-- ⋈_P (iso) is congruent: same topology → same embeddings. -/
theorem embeddings_congr {G₁ G₂ P : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges) :
    embeddings P G₁ = embeddings P G₂ := by
  ext f
  simp only [embeddings, Set.mem_setOf_eq, homomorphisms_congr hn he]

/-- C¹⁰: Embeddings in G₁ are embeddings in G₁ ∪ G₂ (containment direction). -/
theorem embeddings_union_sub (G₁ G₂ P : Graph V L) :
    embeddings P G₁ ⊆ embeddings P (G₁.union G₂) := by
  intro f hf
  exact ⟨homomorphisms_union_sub G₁ G₂ P hf.1, hf.2⟩

/-- C¹¹: Selection containment for embeddings.
    Embeddings in σ_p(G) are embeddings in G. -/
theorem embeddings_selectNodes_sub {G P : Graph V L}
    {p : PropMap → Prop} [DecidablePred p] :
    embeddings P (G.selectNodes p) ⊆ embeddings P G := by
  intro f hf
  refine ⟨⟨fun v hv => ?_, fun e he => ?_⟩, hf.2⟩
  · have := hf.1.1 v hv
    simp [selectNodes, Finset.mem_filter] at this
    exact this.1
  · have := hf.1.2 e he
    simp [selectNodes, Finset.mem_filter] at this
    exact this.1

/-- ⋈_P (iso) commutes with π_A unconditionally:
    projectProps doesn't change topology, so embeddings are identical. -/
theorem embeddings_projectProps (G P : Graph V L) (attrs : Finset AttrName) :
    embeddings P (G.projectProps attrs) = embeddings P G := by
  ext f
  simp only [embeddings, Set.mem_setOf_eq, homomorphisms_congr rfl rfl]
  constructor
  · intro ⟨hf, hinj⟩
    exact ⟨⟨fun v hv => by simp [projectProps] at hf; exact hf.1 v hv,
            fun e he => by simp [projectProps] at hf; exact hf.2 e he⟩, hinj⟩
  · intro ⟨hf, hinj⟩
    exact ⟨⟨fun v hv => by simp [projectProps]; exact hf.1 v hv,
            fun e he => by simp [projectProps]; exact hf.2 e he⟩, hinj⟩

/-- Iso match nodes are unchanged by projection. -/
theorem isoMatchNodes_projectProps (G P : Graph V L) (attrs : Finset AttrName) :
    isoMatchNodes (G.projectProps attrs) P = isoMatchNodes G P := by
  simp only [isoMatchNodes, embeddings_projectProps]

/-- Embeddings are a subset of homomorphisms, so iso matches ⊆ hom matches. -/
theorem isoMatchNodes_sub_patternMatchNodes (G P : Graph V L) :
    isoMatchNodes G P ⊆ patternMatchNodes G P := by
  intro v ⟨f, hf, u, hu, hv⟩
  exact ⟨f, hf.1, u, hu, hv⟩

end IsoPatternMatching

/-! ## Pattern Decomposition (⋈_P row, Pattern Decomp column)

The proposal says pattern decomposition holds for homomorphism semantics (✓)
but fails for isomorphism semantics (✗¹²).

Pattern decomposition: ⋈_P(G, P₁ ⋈_sep P₂) = ⋈_P(G, P₁) ⋈_sep ⋈_P(G, P₂)
where ⋈_sep is a join on separator nodes.

This requires tree decomposition infrastructure. We define the types and
state the key theorems. -/

section PatternDecomposition

/-- A separator between two patterns: the shared nodes. -/
def patternSeparator (P₁ P₂ : Graph V L) : Finset V :=
  P₁.nodes ∩ P₂.nodes

/-- Pattern decomposition (hom): if f is a homomorphism from (P₁ ∪ P₂) to G,
    then its restrictions are homomorphisms from P₁ and P₂ individually.
    This is the easy direction of pattern decomposition. -/
theorem homomorphisms_union_decompose {G P₁ P₂ : Graph V L}
    {f : V → V} (hf : f ∈ homomorphisms (P₁.union P₂) G) :
    f ∈ homomorphisms P₁ G := by
  constructor
  · intro v hv; exact hf.1 v (Finset.mem_union_left _ hv)
  · intro e he; exact hf.2 e (Finset.mem_union_left _ he)

theorem homomorphisms_union_decompose_right {G P₁ P₂ : Graph V L}
    {f : V → V} (hf : f ∈ homomorphisms (P₁.union P₂) G) :
    f ∈ homomorphisms P₂ G := by
  constructor
  · intro v hv; exact hf.1 v (Finset.mem_union_right _ hv)
  · intro e he; exact hf.2 e (Finset.mem_union_right _ he)

/-- Pattern composition (hom): if f is a homomorphism from P₁ and P₂ individually
    (and agrees on separator), then it's a homomorphism from P₁ ∪ P₂.
    This is the composition direction. -/
theorem homomorphisms_union_compose {G P₁ P₂ : Graph V L}
    {f : V → V}
    (hf₁ : f ∈ homomorphisms P₁ G) (hf₂ : f ∈ homomorphisms P₂ G) :
    f ∈ homomorphisms (P₁.union P₂) G := by
  constructor
  · intro v hv
    simp [union, Finset.mem_union] at hv
    cases hv with
    | inl h => exact hf₁.1 v h
    | inr h => exact hf₂.1 v h
  · intro e he
    simp [union, Finset.mem_union] at he
    cases he with
    | inl h => exact hf₁.2 e h
    | inr h => exact hf₂.2 e h

/-- C¹²: Pattern decomposition FAILS for isomorphism semantics.
    Under injective semantics, independently valid sub-matches may assign
    the same data node to non-separator pattern nodes, violating injectivity.
    We express this by showing embeddings of the union are a STRICT subset
    of the intersection of component embeddings (containment only). -/
theorem embeddings_union_sub_compose {G P₁ P₂ : Graph V L}
    {f : V → V} (hf : f ∈ embeddings (P₁.union P₂) G) :
    f ∈ homomorphisms P₁ G ∧ f ∈ homomorphisms P₂ G :=
  ⟨homomorphisms_union_decompose hf.1, homomorphisms_union_decompose_right hf.1⟩

/-- Two functions agree on the separator (shared nodes) of two patterns. -/
def agreeOnSeparator (P₁ P₂ : Graph V L) (f₁ f₂ : V → V) : Prop :=
  ∀ v ∈ patternSeparator P₁ P₂, f₁ v = f₂ v

/-- Combine two functions that agree on the separator into one function
    defined on the union. Uses f₁ on P₁.nodes and f₂ on the rest. -/
noncomputable def combineMaps (P₁ : Graph V L) (f₁ f₂ : V → V) : V → V :=
  fun v => if v ∈ P₁.nodes then f₁ v else f₂ v

/-- Pattern decomposition with separator (composition direction):
    If f₁ is a hom from P₁ to G, f₂ is a hom from P₂ to G,
    and they agree on the separator, then the combined map
    is a hom from P₁ ∪ P₂ to G. -/
theorem homomorphisms_separator_compose {G P₁ P₂ : Graph V L}
    {f₁ f₂ : V → V}
    (hf₁ : f₁ ∈ homomorphisms P₁ G) (hf₂ : f₂ ∈ homomorphisms P₂ G)
    -- Edge validity: P₂ edges with endpoints in P₁ must map consistently
    -- (this implies agreeOnSeparator for nodes that appear as edge endpoints)
    (hedge : ∀ e ∈ P₂.edges, e.src ∈ P₁.nodes → f₂ e.src = f₁ e.src)
    (hedge' : ∀ e ∈ P₂.edges, e.tgt ∈ P₁.nodes → f₂ e.tgt = f₁ e.tgt) :
    combineMaps P₁ f₁ f₂ ∈ homomorphisms (P₁.union P₂) G := by
  constructor
  · -- Node membership: combineMaps maps union nodes to G nodes
    intro v hv
    simp [union, Finset.mem_union] at hv
    simp [combineMaps]
    cases hv with
    | inl h =>
      simp [h]
      exact hf₁.1 v h
    | inr h =>
      by_cases hv₁ : v ∈ P₁.nodes
      · simp [hv₁]
        exact hf₁.1 v hv₁
      · simp [hv₁]
        exact hf₂.1 v h
  · -- Edge preservation: combineMaps preserves edges
    intro e he
    simp [union, Finset.mem_union] at he
    cases he with
    | inl h =>
      -- e ∈ P₁.edges, so src, tgt ∈ P₁.nodes
      have hsrc : e.src ∈ P₁.nodes := P₁.edge_src_valid e h
      have htgt : e.tgt ∈ P₁.nodes := P₁.edge_tgt_valid e h
      simp [combineMaps, hsrc, htgt]
      exact hf₁.2 e h
    | inr h =>
      -- e ∈ P₂.edges, need to handle whether src/tgt are in P₁
      simp [combineMaps]
      have he₂ := hf₂.2 e h
      -- We need: ⟨if src ∈ P₁ then f₁ src else f₂ src, label, if tgt ∈ P₁ then f₁ tgt else f₂ tgt⟩ ∈ G.edges
      by_cases hsrc : e.src ∈ P₁.nodes <;> by_cases htgt : e.tgt ∈ P₁.nodes
      · simp [hsrc, htgt]
        rw [← hedge e h hsrc, ← hedge' e h htgt]
        exact he₂
      · simp [hsrc, htgt]
        rw [← hedge e h hsrc]
        exact he₂
      · simp [hsrc, htgt]
        rw [← hedge' e h htgt]
        exact he₂
      · simp [hsrc, htgt]
        exact he₂

/-- Pattern decomposition with separator (decomposition direction):
    A homomorphism from P₁ ∪ P₂ decomposes into two homomorphisms
    that agree on the separator. -/
theorem homomorphisms_separator_decompose {G P₁ P₂ : Graph V L}
    {f : V → V} (hf : f ∈ homomorphisms (P₁.union P₂) G) :
    f ∈ homomorphisms P₁ G ∧ f ∈ homomorphisms P₂ G ∧
    agreeOnSeparator P₁ P₂ f f := by
  refine ⟨homomorphisms_union_decompose hf, homomorphisms_union_decompose_right hf, ?_⟩
  intro _ _
  rfl

end PatternDecomposition

/-! ## TC Dist over ∩ (TC row, Dist ∩ column = ✗)

TC does NOT distribute over ∩. But we can prove the containment direction. -/

section TCDistInter

/-- TC(G₁ ∩ G₂, l) ⊆ TC(G₁, l):
    reachability in the intersection implies reachability in either graph. -/
theorem labelReachable_inter_sub_left {G₁ G₂ : Graph V L} {l : L} {u v : V}
    (h : LabelReachable (G₁.inter G₂) l u v) :
    LabelReachable G₁ l u v := by
  exact labelReachable_mono l Finset.inter_subset_left h

theorem labelReachable_inter_sub_right {G₁ G₂ : Graph V L} {l : L} {u v : V}
    (h : LabelReachable (G₁.inter G₂) l u v) :
    LabelReachable G₂ l u v := by
  exact labelReachable_mono l Finset.inter_subset_right h

end TCDistInter

/-! ## CC Monotonicity (CC row, Monotonic column = ✗¹⁶)

C¹⁶: CC is NOT monotone under graph filtering. Filtering can remove
entire components (reducing count) or split components (increasing count).

We express the valid structural relationship: Connected is monotone
under edge/node superset (if connected in subgraph, connected in supergraph). -/

section CCMonotonicity

/-- Connected is monotone under edge superset:
    if u,v connected in G₁ and G₁.edges ⊆ G₂.edges and G₁.nodes ⊆ G₂.nodes,
    then u,v connected in G₂. -/
theorem connected_mono {G₁ G₂ : Graph V L}
    (hn : G₁.nodes ⊆ G₂.nodes) (he : G₁.edges ⊆ G₂.edges)
    {u v : V} (h : Connected G₁ u v) : Connected G₂ u v := by
  induction h with
  | refl v hv => exact Connected.refl v (hn hv)
  | edge e hm => exact Connected.edge e (he hm)
  | edge_rev e hm => exact Connected.edge_rev e (he hm)
  | trans _ _ ih₁ ih₂ => exact Connected.trans ih₁ ih₂

/-- CC is NOT monotone as a set-valued function under filtering (C¹⁶).
    However, Connected is monotone under supergraph inclusion. -/
theorem connected_union_left {G₁ G₂ : Graph V L} {u v : V}
    (h : Connected G₁ u v) : Connected (G₁.union G₂) u v :=
  connected_mono Finset.subset_union_left Finset.subset_union_left h

theorem connected_union_right {G₁ G₂ : Graph V L} {u v : V}
    (h : Connected G₂ u v) : Connected (G₁.union G₂) u v :=
  connected_mono Finset.subset_union_right Finset.subset_union_right h

/-- C¹⁶ formal counterexample: filtering can SPLIT a connected component.
    Graph: 0 --a-- 1 --a-- 2 (one component, 3 nodes).
    After removing node 1: {0} and {2} are separate (two components).
    This shows CC is NOT monotone under filtering. -/
theorem cc_not_monotone_counterexample :
    ∃ (G : Graph Nat Nat) (p : PropMap → Prop),
      ∃ (_ : DecidablePred p),
      -- In G, nodes 0 and 2 are connected
      Connected G 0 2 ∧
      -- After filtering, they are NOT connected
      ¬Connected (G.selectNodes p) 0 2 := by
  -- Graph with nodes {0, 1, 2} and edges 0→1, 1→2
  -- Node 1 is tagged with property "bridge" = true to distinguish it
  let nodes : Finset Nat := {0, 1, 2}
  let e01 : Edge Nat Nat := ⟨0, 0, 1⟩
  let e12 : Edge Nat Nat := ⟨1, 0, 2⟩
  let edges : Finset (Edge Nat Nat) := {e01, e12}
  let nprops : Nat → PropMap := fun v =>
    if v == 1 then PropMap.empty.set "bridge" (Value.bool true)
    else PropMap.empty
  let G : Graph Nat Nat := {
    nodes := nodes
    edges := edges
    nodeProps := nprops
    edgeProps := fun _ => PropMap.empty
    edge_src_valid := by
      intro e he
      simp [edges, e01, e12] at he
      rcases he with rfl | rfl <;> simp [nodes]
    edge_tgt_valid := by
      intro e he
      simp [edges, e01, e12] at he
      rcases he with rfl | rfl <;> simp [nodes]
  }
  -- Predicate: keep nodes where "bridge" attr is NOT some true
  let p : PropMap → Prop := fun m => m "bridge" ≠ some (Value.bool true)
  have hdec : DecidablePred p := fun m => inferInstanceAs (Decidable (m "bridge" ≠ some (Value.bool true)))
  refine ⟨G, p, hdec, ?_, ?_⟩
  · -- Connected G 0 2: path 0 →(e01) 1 →(e12) 2
    have h01 : e01 ∈ G.edges := by decide
    have h12 : e12 ∈ G.edges := by decide
    exact Connected.trans (Connected.edge e01 h01) (Connected.edge e12 h12)
  · -- ¬Connected (G.selectNodes p) 0 2
    -- The filtered graph keeps nodes 0 and 2 but removes node 1.
    -- Both edges involve node 1, so the filtered graph has NO edges.
    -- Therefore Connected can only hold via refl, but 0 ≠ 2.
    intro hconn
    -- In the filtered graph, there are no edges, so Connected u v implies u = v
    suffices h : ∀ u v, Connected (G.selectNodes p) u v → u = v by
      exact absurd (h 0 2 hconn) (by decide)
    intro u v hc
    induction hc with
    | refl _ _ => rfl
    | edge e he =>
      exfalso
      -- e must be in the filtered edges: G.edges filtered by p on src and tgt
      -- Both e01 and e12 involve node 1 which is filtered out, so no edge survives
      have hmem : e ∈ (G.selectNodes p).edges := he
      change e ∈ G.edges.filter (fun e => p (G.nodeProps e.src) ∧ p (G.nodeProps e.tgt)) at hmem
      rw [Finset.mem_filter] at hmem
      obtain ⟨he_mem, hp_src, hp_tgt⟩ := hmem
      -- e must be e01 or e12
      change e ∈ edges at he_mem
      have : e = e01 ∨ e = e12 := by
        change e ∈ ({e01, e12} : Finset _) at he_mem
        rw [Finset.mem_insert, Finset.mem_singleton] at he_mem
        exact he_mem
      rcases this with rfl | rfl
      · -- e01: tgt is node 1, nprops 1 has "bridge" = some true, so p fails
        apply hp_tgt
        change nprops 1 "bridge" = some (Value.bool true)
        decide
      · -- e12: src is node 1
        apply hp_src
        change nprops 1 "bridge" = some (Value.bool true)
        decide
    | edge_rev e he =>
      exfalso
      have hmem : e ∈ (G.selectNodes p).edges := he
      change e ∈ G.edges.filter (fun e => p (G.nodeProps e.src) ∧ p (G.nodeProps e.tgt)) at hmem
      rw [Finset.mem_filter] at hmem
      obtain ⟨he_mem, hp_src, hp_tgt⟩ := hmem
      change e ∈ edges at he_mem
      have : e = e01 ∨ e = e12 := by
        change e ∈ ({e01, e12} : Finset _) at he_mem
        rw [Finset.mem_insert, Finset.mem_singleton] at he_mem
        exact he_mem
      rcases this with rfl | rfl
      · apply hp_tgt
        change nprops 1 "bridge" = some (Value.bool true)
        decide
      · apply hp_src
        change nprops 1 "bridge" = some (Value.bool true)
        decide
    | trans _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂

end CCMonotonicity

/-! ## Path Projection Laws (ρ_path row)

Property table: ✗ | — | — | — | C¹ | — | ✓ | ✓ | — | — | — | — -/

section PathProjectionLaws

/-- ρ_path is monotone: G₁ ⊆ G₂ → more paths in G₂.
    RPQMatch in a subgraph implies RPQMatch in the supergraph. -/
theorem rpqMatch_mono {G₁ G₂ : Graph V L}
    (hn : G₁.nodes ⊆ G₂.nodes) (he : G₁.edges ⊆ G₂.edges)
    {q : RPQ L} {u v : V} (h : RPQMatch G₁ q u v) : RPQMatch G₂ q u v := by
  induction h with
  | label l e hm hl => exact RPQMatch.label l e (he hm) hl
  | seq _ _ ih₁ ih₂ => exact RPQMatch.seq ih₁ ih₂
  | alt_l _ ih => exact RPQMatch.alt_l ih
  | alt_r _ ih => exact RPQMatch.alt_r ih
  | star_refl hv => exact RPQMatch.star_refl (hn hv)
  | star_step _ _ ih₁ ih₂ => exact RPQMatch.star_step ih₁ ih₂

/-- ρ_path monotonicity on pairs. -/
theorem pathProjectPairs_mono {G₁ G₂ : Graph V L}
    (hn : G₁.nodes ⊆ G₂.nodes) (he : G₁.edges ⊆ G₂.edges)
    (q : RPQ L) :
    pathProjectPairs G₁ q ⊆ pathProjectPairs G₂ q := by
  intro p hp
  exact rpqMatch_mono hn he hp

/-- ρ_path is congruent: same topology → same path matches. -/
theorem rpqMatch_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    {q : RPQ L} {u v : V} :
    RPQMatch G₁ q u v ↔ RPQMatch G₂ q u v :=
  ⟨rpqMatch_mono (hn ▸ Finset.Subset.refl G₁.nodes) (he ▸ Finset.Subset.refl G₁.edges),
   rpqMatch_mono (hn ▸ Finset.Subset.refl G₁.nodes) (he ▸ Finset.Subset.refl G₁.edges)⟩

theorem pathProjectPairs_congr {G₁ G₂ : Graph V L}
    (hn : G₁.nodes = G₂.nodes) (he : G₁.edges = G₂.edges)
    (q : RPQ L) :
    pathProjectPairs G₁ q = pathProjectPairs G₂ q := by
  ext p; exact rpqMatch_congr hn he

/-- C¹: ρ_path distributes over ∪ (containment direction).
    Paths in G₁ or G₂ are paths in G₁ ∪ G₂. -/
theorem pathProjectPairs_union_sub (G₁ G₂ : Graph V L) (q : RPQ L) :
    pathProjectPairs G₁ q ⊆ pathProjectPairs (G₁.union G₂) q := by
  intro p hp
  exact rpqMatch_mono Finset.subset_union_left Finset.subset_union_left hp

-- ρ_path is NOT idempotent (✗ in table): the operation produces (src, tgt) pairs,
-- so applying it twice doesn't type-check in the same way. No theorem needed.

end PathProjectionLaws

/-! ## π_A Identity (π row, Identity column = ✓)

The proposal says π has an identity element: projecting with all attributes = identity.
We formalize this using SupportedPropMap: if all node/edge properties have finite support
contained in `attrs`, then projectProps is the identity. -/

section ProjectionIdentity

/-- A graph has supported properties when all node and edge prop maps have finite support. -/
structure SupportedGraph (G : Graph V L) where
  nodeSupport : V → Finset AttrName
  edgeSupport : Edge V L → Finset AttrName
  node_spec : ∀ v ∈ G.nodes, ∀ k, k ∉ nodeSupport v → G.nodeProps v k = none
  edge_spec : ∀ e ∈ G.edges, ∀ k, k ∉ edgeSupport e → G.edgeProps e k = none

/-- The combined support: all attribute names used by any node or edge. -/
noncomputable def SupportedGraph.allAttrs {G : Graph V L} (sg : SupportedGraph G) : Finset AttrName :=
  G.nodes.biUnion sg.nodeSupport ∪ G.edges.biUnion sg.edgeSupport

/-- π_A identity: projecting with all attributes is the identity on topology and properties.
    This is the formal version of "π has an identity element" from the property table. -/
theorem projectProps_identity_nodes (G : Graph V L) (attrs : Finset AttrName) :
    (G.projectProps attrs).nodes = G.nodes := by
  simp [projectProps]

theorem projectProps_identity_edges (G : Graph V L) (attrs : Finset AttrName) :
    (G.projectProps attrs).edges = G.edges := by
  simp [projectProps]

theorem projectProps_identity_nodeProps (G : Graph V L) (sg : SupportedGraph G)
    (attrs : Finset AttrName)
    (h_node : ∀ v ∈ G.nodes, sg.nodeSupport v ⊆ attrs) (v : V) (hv : v ∈ G.nodes) :
    (G.projectProps attrs).nodeProps v = G.nodeProps v := by
  simp only [projectProps]
  funext k
  simp only [PropMap.restrict]
  split
  · rfl
  · exact (sg.node_spec v hv k (fun hk => ‹k ∉ attrs› (h_node v hv hk))).symm ▸ rfl

theorem projectProps_identity_edgeProps (G : Graph V L) (sg : SupportedGraph G)
    (attrs : Finset AttrName)
    (h_edge : ∀ e ∈ G.edges, sg.edgeSupport e ⊆ attrs) (e : Edge V L) (he : e ∈ G.edges) :
    (G.projectProps attrs).edgeProps e = G.edgeProps e := by
  simp only [projectProps]
  funext k
  simp only [PropMap.restrict]
  split
  · rfl
  · exact (sg.edge_spec e he k (fun hk => ‹k ∉ attrs› (h_edge e he hk))).symm ▸ rfl

end ProjectionIdentity

/-! ## Doc Issues: Cells Not Expressible with Current Types

The following property table cells cannot be formalized with the current
type infrastructure and are documented as known gaps:

### π_A Identity (✓ in table) — RESOLVED
Now formalized via `SupportedGraph` + `projectProps_identity_nodeProps/edgeProps`.

### ⊔ Idempotent (✗ in table)
`disjointUnion` requires `Disjoint G₁.nodes G₂.nodes` as a precondition.
`G ⊔ G` is undefined since `Disjoint G.nodes G.nodes` only holds for
the empty graph. The ✗ is correct but unprovable as a theorem — the
operation simply cannot be applied. **Doc issue: precondition prevents stating.**

### ⋈_P Pattern Decomposition (✓ for hom, ✗¹² for iso) — RESOLVED
Formalized the decomposition/composition directions for homomorphisms:
`homomorphisms_union_decompose`, `homomorphisms_union_decompose_right`,
`homomorphisms_union_compose`. Separator-based composition with two distinct
functions: `agreeOnSeparator`, `combineMaps`, `homomorphisms_separator_compose`,
`homomorphisms_separator_decompose`. C¹² containment: `embeddings_union_sub_compose`.

### ⋈_P (iso) Entire Row — RESOLVED
Formalized via `embeddings` operator with `embeddings_mono`, `embeddings_congr`,
`embeddings_union_sub`, `embeddings_selectNodes_sub`, `embeddings_projectProps`,
`isoMatchNodes_projectProps`, `isoMatchNodes_sub_patternMatchNodes`.

### ↑ Row (5 non-N/A cells: C¹⁸, ✓, C¹⁹, C, ✓) — RESOLVED
Formalized via `construct_mono_nodes/edges`, `construct_congr`,
`construct_union_nodes/edges`, `projectProps_construct`,
`selectNodes_construct_nodes`.

### ↓ Row (6 non-N/A cells: C¹, C¹, ✓, C¹⁹, C²⁰, ✓) — RESOLVED
Formalized at size/topology level: `toNodeRelation_size`,
`toNodeRelation_projectProps_size`, `toEdgeRelation_projectProps_size`.
Full congruence: `toNodeRelation_congr`, `toEdgeRelation_congr`.

### ρ_path Row (4 non-N/A cells: ✗, C¹, ✓, ✓) — RESOLVED
Formalized via `RPQ`, `RPQMatch`, `rpqMatch_mono`, `rpqMatch_congr`,
`pathProjectPairs_mono`, `pathProjectPairs_congr`, `pathProjectPairs_union_sub`.
Non-idempotent (✗) documented as type-level impossibility. -/

end Graph

end GraphAlgebra
