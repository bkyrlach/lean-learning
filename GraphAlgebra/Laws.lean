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

end CCMonotonicity

/-! ## Doc Issues: Cells Not Expressible with Current Types

The following property table cells cannot be formalized with the current
type infrastructure and are documented as known gaps:

### π_A Identity (✓ in table)
Requires `PropMap.support` — since `PropMap = AttrName → Option Value` is a
function type, there is no finite "all attributes" set. We cannot state
`π_all(G) = G` without a finite support concept. **Doc issue.**

### ⊔ Idempotent (✗ in table)
`disjointUnion` requires `Disjoint G₁.nodes G₂.nodes` as a precondition.
`G ⊔ G` is undefined since `Disjoint G.nodes G.nodes` only holds for
the empty graph. The ✗ is correct but unprovable as a theorem — the
operation simply cannot be applied. **Doc issue: precondition prevents stating.**

### ⋈_P Pattern Decomposition (✓ for hom, ✗¹² for iso)
Requires formalizing treewidth, tree decompositions, and separator-based
join. This is a substantial formalization effort beyond the current scope.
**Deferred: needs treewidth infrastructure.**

### ⋈_P (iso) Entire Row
Requires formalizing injective homomorphism matching (subgraph isomorphism).
The `Embedding` structure exists in Graph.lean but no matching operator
is defined. **Deferred: needs injective matching operator.**

### ↑ Row (5 non-N/A cells: C¹⁸, ✓, C¹⁹, C, ✓)
The `construct` operator is minimal — it takes explicit Finsets, not
relational data. Meaningful laws (dist over relational ∪, commutativity
with σ/π across the boundary) require a richer relational-to-graph
bridge. **Deferred: needs enriched ↑ operator.**

### ↓ Row (6 non-N/A cells: C¹, C¹, ✓, C¹⁹, C²⁰, ✓)
`toNodeRelation`/`toEdgeRelation` are noncomputable and produce
`Relation` (List Record). Laws relating graph operations to relational
operations across the boundary require decidable record equality and
schema tracking. **Deferred: needs enriched ↓ operator.**

### ρ_path Row (4 non-N/A cells: ✗, C¹, ✓, ✓)
The path projection operator is not defined at all. Requires formalizing
regular path queries (RPQs). **Deferred: operator not defined.** -/

end Graph

end GraphAlgebra
