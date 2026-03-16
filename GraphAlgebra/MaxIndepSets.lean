/-
  GraphAlgebra.MaxIndepSets

  Bron-Kerbosch algorithm for enumerating all maximal independent sets of a graph.

  A set I is a **maximal independent set** if:
  1. I is independent (no edge has both endpoints in I)
  2. No proper superset of I that is a subset of G.nodes is independent

  The algorithm uses the "pick one vertex, branch on include/exclude" formulation:
    BK(R, P, X):
      if P = ∅ ∧ X = ∅: yield R
      if P = ∅: dead end
      pick v ∈ P (minimum element)
      include branch: BK(R ∪ {v}, P' ∩ nonNbrs(v), X ∩ nonNbrs(v))
      exclude branch: BK(R, P', X ∪ {v})
      where P' = P \ {v}

  Main results:
  1. `maxIndepSets G` computes all maximal independent sets (computable, no Classical)
  2. Soundness: every output is independent and maximal
  3. Completeness: every maximal independent set appears in the output
-/
import GraphAlgebra.Lawler
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

namespace GraphAlgebra

namespace Graph

variable {V L : Type} [DecidableEq V] [DecidableEq L]

/-! ## Computable Adjacency -/

/-- Decidable adjacency check: are u and v connected by an edge (in either direction)? -/
def adjBool (G : Graph V L) (u v : V) : Bool :=
  decide (∃ e ∈ G.edges, (e.src = u ∧ e.tgt = v) ∨ (e.src = v ∧ e.tgt = u))

theorem adjBool_comm (G : Graph V L) (u v : V) : G.adjBool u v = G.adjBool v u := by
  simp only [adjBool]
  rw [decide_eq_decide]
  simp only [or_comm, and_comm]

theorem adjBool_true_iff (G : Graph V L) (u v : V) :
    G.adjBool u v = true ↔
      ∃ e ∈ G.edges, (e.src = u ∧ e.tgt = v) ∨ (e.src = v ∧ e.tgt = u) := by
  simp [adjBool, decide_eq_true_eq]

/-- The set of non-neighbors of v in S: vertices in S that are not v and not adjacent to v. -/
def nonNeighborSet (G : Graph V L) (v : V) (S : Finset V) : Finset V :=
  S.filter fun u => u != v && !G.adjBool u v

theorem nonNeighborSet_subset (G : Graph V L) (v : V) (S : Finset V) :
    G.nonNeighborSet v S ⊆ S :=
  Finset.filter_subset _ _

theorem not_mem_nonNeighborSet_self (G : Graph V L) (v : V) (S : Finset V) :
    v ∉ G.nonNeighborSet v S := by
  simp [nonNeighborSet, Finset.mem_filter]

/-! ## Maximal Independent Set Specification -/

/-- A set I ⊆ G.nodes is a maximal independent set: independent and no vertex
    outside I (but in G.nodes) can be added while preserving independence. -/
def IsMaxIndepSet (G : Graph V L) (I : Finset V) : Prop :=
  I ⊆ G.nodes ∧
  IsIndepSet G I = true ∧
  ∀ v ∈ G.nodes, v ∉ I → IsIndepSet G (I ∪ {v}) = false

/-- Decidable version of IsMaxIndepSet. -/
def isMaxIndepSet (G : Graph V L) (I : Finset V) : Bool :=
  decide (I ⊆ G.nodes) &&
  G.IsIndepSet I &&
  decide (∀ v ∈ G.nodes, v ∉ I → G.IsIndepSet (I ∪ {v}) = false)

/-! ## Bron-Kerbosch Algorithm -/

/-- **Bron-Kerbosch for maximal independent sets.**

  `bronKerboschAux G R P X` returns all maximal independent sets I such that:
  - R ⊆ I (R is the "required" set, already selected)
  - I \ R ⊆ P (remaining vertices come from candidates P)
  - No vertex in X can extend I (X contains excluded/explored vertices)

  Invariants maintained by callers:
  - R is independent
  - Every vertex in P ∪ X is a non-neighbor of every vertex in R
  - P and X are disjoint -/
def bronKerboschAux [LinearOrder V] (G : Graph V L)
    (R P X : Finset V) : Finset (Finset V) :=
  if hP : P = ∅ then
    if X = ∅ then {R} else ∅
  else
    have hPne : P.Nonempty := Finset.nonempty_of_ne_empty hP
    let v := P.min' hPne
    have hv : v ∈ P := Finset.min'_mem P hPne
    let P' := P.erase v
    have hP'card : P'.card < P.card := Finset.card_erase_lt_of_mem hv
    let nonNbrs := G.nonNeighborSet v
    -- Include v: recurse with R ∪ {v}, restricting P and X to non-neighbors of v
    let include_result := bronKerboschAux G (R ∪ {v}) (nonNbrs P') (nonNbrs X)
    -- Exclude v: recurse with R, removing v from P, adding v to X
    let exclude_result := bronKerboschAux G R P' (X ∪ {v})
    include_result ∪ exclude_result
termination_by P.card
decreasing_by
  all_goals simp_wf
  · calc (nonNbrs P').card ≤ P'.card := Finset.card_le_card (nonNeighborSet_subset G v P')
      _ < P.card := hP'card
  · exact hP'card

/-- Compute all maximal independent sets of G. -/
def maxIndepSets [LinearOrder V] (G : Graph V L) : Finset (Finset V) :=
  bronKerboschAux G ∅ G.nodes ∅

/-! ## Correctness Proofs -/

-- Helper: independence is monotone downward (subsets of independent sets are independent)
theorem isIndepSet_subset {G : Graph V L} {I J : Finset V}
    (hIJ : I ⊆ J) (hJ : IsIndepSet G J = true) : IsIndepSet G I = true := by
  simp only [IsIndepSet, decide_eq_true_eq] at hJ ⊢
  intro e he ⟨hsrc, htgt⟩
  exact hJ e he ⟨hIJ hsrc, hIJ htgt⟩

-- Helper: if I is independent and v is not adjacent to any vertex in I,
-- then I ∪ {v} is independent.
-- Requires NoSelfLoops G to handle the self-loop case (v self-adjacent).
theorem isIndepSet_insert {G : Graph V L} {I : Finset V} {v : V}
    (hI : IsIndepSet G I = true)
    (hloops : NoSelfLoops G)
    (hv : ∀ u ∈ I, G.adjBool u v = false) :
    IsIndepSet G (I ∪ {v}) = true := by
  simp only [IsIndepSet, decide_eq_true_eq] at hI ⊢
  intro e he ⟨hsrc, htgt⟩
  rcases Finset.mem_union.mp hsrc with hsrcI | hsrcV
  · rcases Finset.mem_union.mp htgt with htgtI | htgtV
    · exact hI e he ⟨hsrcI, htgtI⟩
    · -- e.src ∈ I, e.tgt = v: adjBool e.src v = false but e witnesses adjBool e.src v = true
      rw [Finset.mem_singleton] at htgtV
      subst htgtV
      have hadj : G.adjBool e.src e.tgt = true := by
        rw [adjBool_true_iff]; exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
      simp [hv e.src hsrcI] at hadj
  · rw [Finset.mem_singleton] at hsrcV
    subst hsrcV
    rcases Finset.mem_union.mp htgt with htgtI | htgtV
    · -- e.src = v, e.tgt ∈ I: adjBool e.tgt v = false but e witnesses adjBool e.tgt v = true
      have hadj : G.adjBool e.tgt e.src = true := by
        rw [adjBool_true_iff]; exact ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
      simp [hv e.tgt htgtI] at hadj
    · -- e.src = v, e.tgt = v: self-loop, contradicts NoSelfLoops
      rw [Finset.mem_singleton] at htgtV
      exact absurd htgtV.symm (hloops e he)

-- Helper: nonNeighborSet preserves non-adjacency with v
theorem mem_nonNeighborSet_iff (G : Graph V L) (v : V) (S : Finset V) (u : V) :
    u ∈ G.nonNeighborSet v S ↔ u ∈ S ∧ u ≠ v ∧ G.adjBool u v = false := by
  simp only [nonNeighborSet, Finset.mem_filter, Bool.and_eq_true, bne_iff_ne,
    Bool.not_eq_true']

open Classical in
/-- **Soundness — Independence**: every set returned by `bronKerboschAux` is independent,
    assuming R is independent and all candidates in P are non-adjacent to R. -/
theorem bronKerboschAux_indep [LinearOrder V] {G : Graph V L}
    {R P X : Finset V}
    (hloops : NoSelfLoops G)
    (hR : IsIndepSet G R = true)
    (hRP : ∀ v ∈ P, ∀ u ∈ R, G.adjBool u v = false) :
    ∀ I ∈ bronKerboschAux G R P X, IsIndepSet G I = true := by
  -- Induction on P.card
  suffices h : ∀ n (R P X : Finset V), P.card = n →
      IsIndepSet G R = true →
      (∀ v ∈ P, ∀ u ∈ R, G.adjBool u v = false) →
      ∀ I ∈ bronKerboschAux G R P X, IsIndepSet G I = true from
    h P.card R P X rfl hR hRP
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro R P X hPcard hR hRP I hI
  unfold bronKerboschAux at hI
  split at hI
  · -- P = ∅
    rename_i hPemp
    split at hI
    · -- X = ∅: I = R
      simp at hI; subst hI; exact hR
    · -- X ≠ ∅: no results
      simp at hI
  · -- P ≠ ∅: branch on v = P.min'
    rename_i hPne
    have hPne' : P.Nonempty := Finset.nonempty_of_ne_empty hPne
    simp only [Finset.mem_union] at hI
    rcases hI with hIncl | hExcl
    · -- Include branch: R' = R ∪ {v}, P' = nonNeighborSet v (P.erase v)
      let v := P.min' hPne'
      have hv : v ∈ P := Finset.min'_mem P hPne'
      -- R ∪ {v} is independent
      have hRv : IsIndepSet G (R ∪ {v}) = true := by
        apply isIndepSet_insert hR hloops
        intro u hu
        exact hRP v hv u hu
      -- All candidates in nonNeighborSet v (P.erase v) are non-adjacent to R ∪ {v}
      have hRP' : ∀ w ∈ G.nonNeighborSet v (P.erase v), ∀ u ∈ R ∪ {v},
          G.adjBool u w = false := by
        intro w hw u hu
        rw [mem_nonNeighborSet_iff] at hw
        obtain ⟨hwP, hwne, hwadj⟩ := hw
        rcases Finset.mem_union.mp hu with huR | huV
        · have := hRP w (Finset.mem_of_mem_erase hwP) u huR
          rwa [adjBool_comm] at this ⊢
        · rw [Finset.mem_singleton] at huV; subst huV
          rwa [adjBool_comm]
      have hcard : (G.nonNeighborSet v (P.erase v)).card < P.card := by
        calc (G.nonNeighborSet v (P.erase v)).card
            ≤ (P.erase v).card := Finset.card_le_card (nonNeighborSet_subset G v _)
          _ < P.card := Finset.card_erase_lt_of_mem hv
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl hRv hRP' I hIncl
    · -- Exclude branch: R stays, P' = P.erase v
      let v := P.min' hPne'
      have hv : v ∈ P := Finset.min'_mem P hPne'
      have hcard : (P.erase v).card < P.card := Finset.card_erase_lt_of_mem hv
      have hRP' : ∀ w ∈ P.erase v, ∀ u ∈ R, G.adjBool u w = false := by
        intro w hw u hu
        exact hRP w (Finset.mem_of_mem_erase hw) u hu
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl hR hRP' I hExcl

/-- **Soundness for maxIndepSets**: every output is independent. -/
theorem maxIndepSets_indep [LinearOrder V] (G : Graph V L) (hloops : NoSelfLoops G) :
    ∀ I ∈ maxIndepSets G, IsIndepSet G I = true := by
  apply bronKerboschAux_indep hloops
  · simp [IsIndepSet, decide_eq_true_eq]
  · intro v _ u hu; simp at hu

open Classical in
/-- **Soundness — Subset of nodes**: every set returned is a subset of G.nodes,
    assuming R ⊆ G.nodes and P ⊆ G.nodes. -/
theorem bronKerboschAux_subset_nodes [LinearOrder V] {G : Graph V L}
    {R P X : Finset V}
    (hR : R ⊆ G.nodes) (hP : P ⊆ G.nodes) :
    ∀ I ∈ bronKerboschAux G R P X, I ⊆ G.nodes := by
  suffices h : ∀ n (R P X : Finset V), P.card = n →
      R ⊆ G.nodes → P ⊆ G.nodes →
      ∀ I ∈ bronKerboschAux G R P X, I ⊆ G.nodes from
    h P.card R P X rfl hR hP
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro R P X hPcard hR hP I hI
  unfold bronKerboschAux at hI
  split at hI
  · split at hI
    · simp at hI; subst hI; exact hR
    · simp at hI
  · rename_i hPne
    have hPne' : P.Nonempty := Finset.nonempty_of_ne_empty hPne
    let v := P.min' hPne'
    have hv : v ∈ P := Finset.min'_mem P hPne'
    simp only [Finset.mem_union] at hI
    rcases hI with hIncl | hExcl
    · have hcard : (G.nonNeighborSet v (P.erase v)).card < P.card :=
        calc _ ≤ (P.erase v).card := Finset.card_le_card (nonNeighborSet_subset G v _)
          _ < P.card := Finset.card_erase_lt_of_mem hv
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl
        (Finset.union_subset hR (Finset.singleton_subset_iff.mpr (hP hv)))
        (fun u hu => hP (nonNeighborSet_subset G v _ hu |> Finset.mem_of_mem_erase))
        I hIncl
    · have hcard : (P.erase v).card < P.card := Finset.card_erase_lt_of_mem hv
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl hR
        (fun u hu => hP (Finset.mem_of_mem_erase hu))
        I hExcl

/-- **Soundness for maxIndepSets**: every output is a subset of G.nodes. -/
theorem maxIndepSets_subset_nodes [LinearOrder V] (G : Graph V L) :
    ∀ I ∈ maxIndepSets G, I ⊆ G.nodes := by
  apply bronKerboschAux_subset_nodes
  · exact Finset.empty_subset _
  · exact Finset.Subset.refl _

open Classical in
/-- **Soundness — Maximality**: every set returned by bronKerboschAux is maximal
    with respect to P ∪ X. No vertex in P ∪ X outside I can be added. -/
theorem bronKerboschAux_maximal [LinearOrder V] {G : Graph V L}
    {R P X : Finset V}
    (hRP : ∀ v ∈ P ∪ X, ∀ u ∈ R, G.adjBool u v = false)
    (hPX : Disjoint P X) :
    ∀ I ∈ bronKerboschAux G R P X,
      R ⊆ I ∧ I ⊆ R ∪ P ∧
      ∀ v ∈ P ∪ X, v ∉ I → ∃ u ∈ I, G.adjBool u v = true := by
  suffices h : ∀ n (R P X : Finset V), P.card = n →
      (∀ v ∈ P ∪ X, ∀ u ∈ R, G.adjBool u v = false) →
      Disjoint P X →
      ∀ I ∈ bronKerboschAux G R P X,
        R ⊆ I ∧ I ⊆ R ∪ P ∧
        ∀ v ∈ P ∪ X, v ∉ I → ∃ u ∈ I, G.adjBool u v = true from
    h P.card R P X rfl hRP hPX
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro R P X hPcard hRP hPX I hI
  unfold bronKerboschAux at hI
  split at hI
  · rename_i hPemp
    split at hI
    · -- P = ∅, X = ∅: I = R
      rename_i hXemp
      simp at hI; subst hI
      refine ⟨Finset.Subset.refl _, Finset.subset_union_left, fun v hv _ => ?_⟩
      rw [hPemp, hXemp] at hv; simp at hv
    · simp at hI
  · rename_i hPne
    have hPne' : P.Nonempty := Finset.nonempty_of_ne_empty hPne
    let v := P.min' hPne'
    have hv : v ∈ P := Finset.min'_mem P hPne'
    simp only [Finset.mem_union] at hI
    rcases hI with hIncl | hExcl
    · -- Include branch
      have hcard : (G.nonNeighborSet v (P.erase v)).card < P.card :=
        calc _ ≤ (P.erase v).card := Finset.card_le_card (nonNeighborSet_subset G v _)
          _ < P.card := Finset.card_erase_lt_of_mem hv
      have hRP_incl : ∀ w ∈ G.nonNeighborSet v (P.erase v) ∪ G.nonNeighborSet v X,
          ∀ u ∈ R ∪ {v}, G.adjBool u w = false := by
        intro w hw u hu
        rcases Finset.mem_union.mp hw with hwP | hwX
        · rw [mem_nonNeighborSet_iff] at hwP
          rcases Finset.mem_union.mp hu with huR | huV
          · have := hRP w (Finset.mem_union_left _ (Finset.mem_of_mem_erase hwP.1)) u huR
            rwa [adjBool_comm] at this ⊢
          · rw [Finset.mem_singleton] at huV; subst huV; rw [adjBool_comm]; exact hwP.2.2
        · rw [mem_nonNeighborSet_iff] at hwX
          rcases Finset.mem_union.mp hu with huR | huV
          · have := hRP w (Finset.mem_union_right _ hwX.1) u huR
            rwa [adjBool_comm] at this ⊢
          · rw [Finset.mem_singleton] at huV; subst huV; rw [adjBool_comm]; exact hwX.2.2
      have hPX_incl : Disjoint (G.nonNeighborSet v (P.erase v)) (G.nonNeighborSet v X) := by
        exact Finset.disjoint_of_subset_right (nonNeighborSet_subset G v X)
          (Finset.disjoint_of_subset_left
            ((nonNeighborSet_subset G v _).trans (Finset.erase_subset v P)) hPX)
      obtain ⟨hRI, hIP, hImax⟩ := ih _ (hPcard ▸ hcard) _ _ _ rfl hRP_incl hPX_incl I hIncl
      refine ⟨?_, ?_, ?_⟩
      · -- R ⊆ I: R ⊆ R ∪ {v} ⊆ I
        exact Finset.subset_union_left.trans hRI
      · -- I ⊆ R ∪ P: I ⊆ (R ∪ {v}) ∪ nonNeighborSet v (P.erase v) ⊆ R ∪ P
        intro w hw
        have := hIP hw
        rcases Finset.mem_union.mp this with hwRv | hwNN
        · rcases Finset.mem_union.mp hwRv with hwR | hwV
          · exact Finset.mem_union_left _ hwR
          · rw [Finset.mem_singleton] at hwV; subst hwV
            exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase (nonNeighborSet_subset G v _ hwNN))
      · -- Maximality
        intro w hw hwI
        cases hwadj : G.adjBool w v
        · -- G.adjBool w v = false: w is in the restricted P' ∪ X'
          rcases Finset.mem_union.mp hw with hwP | hwX
          · -- w ∈ P
            by_cases hwv : w = v
            · subst hwv; exact absurd (hRI (Finset.mem_union_right _ (Finset.mem_singleton_self v))) hwI
            · have hwNN : w ∈ G.nonNeighborSet v (P.erase v) := by
                rw [mem_nonNeighborSet_iff]
                exact ⟨Finset.mem_erase.mpr ⟨hwv, hwP⟩, hwv, hwadj⟩
              exact hImax w (Finset.mem_union_left _ hwNN) hwI
          · -- w ∈ X
            have hwNN : w ∈ G.nonNeighborSet v X := by
              rw [mem_nonNeighborSet_iff]
              refine ⟨hwX, ?_, hwadj⟩
              intro hwv; subst hwv
              exact Finset.disjoint_right.mp hPX hwX hv
            exact hImax w (Finset.mem_union_right _ hwNN) hwI
        · -- G.adjBool w v = true: v ∈ I witnesses adjacency
          exact ⟨v, hRI (Finset.mem_union_right _ (Finset.mem_singleton_self v)),
                 by rw [adjBool_comm]; exact hwadj⟩
    · -- Exclude branch
      have hcard : (P.erase v).card < P.card := Finset.card_erase_lt_of_mem hv
      have hRP_excl : ∀ w ∈ P.erase v ∪ (X ∪ {v}), ∀ u ∈ R, G.adjBool u w = false := by
        intro w hw u hu
        rcases Finset.mem_union.mp hw with hwP | hwXv
        · exact hRP w (Finset.mem_union_left _ (Finset.mem_of_mem_erase hwP)) u hu
        · rcases Finset.mem_union.mp hwXv with hwX | hwV
          · exact hRP w (Finset.mem_union_right _ hwX) u hu
          · rw [Finset.mem_singleton] at hwV; subst hwV
            exact hRP v (Finset.mem_union_left _ hv) u hu
      have hPX_excl : Disjoint (P.erase v) (X ∪ {v}) := by
        rw [Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset v P) hPX,
               by rw [Finset.disjoint_singleton_right]; exact Finset.not_mem_erase v P⟩
      obtain ⟨hRI, hIP, hImax⟩ := ih _ (hPcard ▸ hcard) _ _ _ rfl hRP_excl hPX_excl I hExcl
      refine ⟨hRI, ?_, ?_⟩
      · -- I ⊆ R ∪ P
        intro w hw
        have := hIP hw
        rcases Finset.mem_union.mp this with hwR | hwP'
        · exact Finset.mem_union_left _ hwR
        · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hwP')
      · -- Maximality: IH covers P.erase v ∪ (X ∪ {v}) = P ∪ X
        intro w hw hwI
        have : w ∈ P.erase v ∪ (X ∪ {v}) := by
          rcases Finset.mem_union.mp hw with hwP | hwX
          · by_cases hwv : w = v
            · subst hwv
              exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton_self v))
            · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwv, hwP⟩)
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hwX)
        exact hImax w this hwI

/-- **Soundness for maxIndepSets**: every output is a maximal independent set. -/
theorem maxIndepSets_maximal [LinearOrder V] (G : Graph V L) (hloops : NoSelfLoops G) :
    ∀ I ∈ maxIndepSets G, IsMaxIndepSet G I := by
  intro I hI
  have hindep := maxIndepSets_indep G hloops I hI
  have hsubset := maxIndepSets_subset_nodes G I hI
  have hmax := bronKerboschAux_maximal
    (by intro v hv u hu; simp at hu)
    (by simp [Finset.disjoint_empty_right])
    I hI
  obtain ⟨_, _, hImax⟩ := hmax
  refine ⟨hsubset, hindep, fun v hv hvI => ?_⟩
  -- v ∈ G.nodes, v ∉ I. By maximality, ∃ u ∈ I adjacent to v.
  have ⟨u, hu, hadj⟩ := hImax v (by simp [hv]) hvI
  -- So I ∪ {v} is not independent (u and v are adjacent, both in I ∪ {v})
  rw [adjBool_true_iff] at hadj
  obtain ⟨e, he, hends⟩ := hadj
  simp only [IsIndepSet]
  rw [decide_eq_false_iff_not]; push_neg
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨e, he, Finset.mem_union_left _ hu, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  · exact ⟨e, he, Finset.mem_union_right _ (Finset.mem_singleton_self _), Finset.mem_union_left _ hu⟩

open Classical in
/-- **Completeness**: every maximal independent set I ⊆ G.nodes appears in `maxIndepSets G`. -/
theorem maxIndepSets_complete [LinearOrder V] (G : Graph V L)
    (hloops : NoSelfLoops G)
    (I : Finset V) (hI : IsMaxIndepSet G I) :
    I ∈ maxIndepSets G := by
  -- Prove the stronger invariant for bronKerboschAux
  suffices h : ∀ n (R P X : Finset V), P.card = n →
      R ⊆ I → I \ R ⊆ P → Disjoint (I \ R) X →
      IsIndepSet G R = true →
      (∀ v ∈ P ∪ X, ∀ u ∈ R, G.adjBool u v = false) →
      Disjoint P X →
      P ∪ X ⊆ G.nodes →
      Disjoint R (P ∪ X) →
      I ∈ bronKerboschAux G R P X from
    h G.nodes.card ∅ G.nodes ∅ rfl
      (Finset.empty_subset _)
      (by simp; exact hI.1)
      (by simp)
      (by simp [IsIndepSet, decide_eq_true_eq])
      (by intro v _ u hu; simp at hu)
      (by simp)
      (by simp)
      (by simp)
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro R P X hPcard hRI hIRP hIX hR hRP hPX hPXnodes hRPX
  unfold bronKerboschAux
  split
  · -- P = ∅
    rename_i hPemp
    split
    · -- X = ∅: must show I = R
      simp only [Finset.mem_singleton]
      ext v
      constructor
      · intro hv
        by_contra hvR
        have : v ∈ I \ R := Finset.mem_sdiff.mpr ⟨hv, hvR⟩
        have := hIRP this
        rw [hPemp] at this
        exact Finset.not_mem_empty _ this
      · exact fun hv => hRI hv
    · -- X ≠ ∅: contradiction — some element of X is in I \ R
      rename_i hXne
      -- Since I \ R ⊆ P = ∅, I ⊆ R, so I = R (since R ⊆ I)
      -- Then every v ∈ X is not adjacent to any u ∈ R = I,
      -- but maximality says v can't be added, meaning some u ∈ I is adjacent to v.
      -- This uses the maximality from hRP and the hypothesis about X.
      exfalso
      have hIeqR : I = R := by
        ext v; constructor
        · intro hv
          by_contra hvR
          exact Finset.not_mem_empty _ (hPemp ▸ hIRP (Finset.mem_sdiff.mpr ⟨hv, hvR⟩))
        · exact fun hv => hRI hv
      -- X is nonempty, pick w ∈ X
      have ⟨w, hw⟩ := Finset.nonempty_of_ne_empty hXne
      -- w ∉ I (since Disjoint (I \ R) X and I = R means I \ R = ∅, so disjointness is vacuous)
      -- But we need: w ∉ I. Since R ⊆ I and I = R, we need w ∉ R.
      -- w ∈ X, and Disjoint P X, so w ∉ P = ∅ (vacuous). But we need w ∉ R.
      -- From hRP: ∀ v ∈ P ∪ X, ∀ u ∈ R, adjBool u v = false
      -- So ∀ u ∈ I, adjBool u w = false (since w ∈ X and I = R)
      have hnotadj : ∀ u ∈ I, G.adjBool u w = false := by
        intro u hu
        rw [hIeqR] at hu
        exact hRP w (Finset.mem_union_right _ hw) u hu
      -- Since I is maximal and w ∈ G.nodes (need to show this from invariants),
      -- if w ∉ I then ∃ u ∈ I, adjBool u w = true, contradiction.
      -- But wait, we need w ∈ G.nodes. This follows from the calling convention.
      -- Actually, we need to track that X ⊆ G.nodes too. Let me use that
      -- I is maximal + w can't be added = some u ∈ I adj to w.
      -- We have IsIndepSet G (I ∪ {w}) should be false by maximality of I,
      -- if w ∈ G.nodes and w ∉ I.
      have hwI : w ∉ I := by
        intro hwI
        rw [hIeqR] at hwI
        exact Finset.disjoint_right.mp hRPX (Finset.mem_union_right _ hw) hwI
      have hwNodes : w ∈ G.nodes := hPXnodes (Finset.mem_union_right _ hw)
      -- I ∪ {w} should be independent (since no u ∈ I is adjacent to w)
      -- but maximality of I says it's not
      have hIwIndep : IsIndepSet G (I ∪ {w}) = true :=
        isIndepSet_insert hI.2.1 hloops hnotadj
      exact Bool.false_ne_true (hI.2.2 w hwNodes hwI ▸ hIwIndep)
  · -- P ≠ ∅
    rename_i hPne
    have hPne' : P.Nonempty := Finset.nonempty_of_ne_empty hPne
    let v := P.min' hPne'
    have hv : v ∈ P := Finset.min'_mem P hPne'
    simp only [Finset.mem_union]
    -- Branch: does I contain v?
    by_cases hvI : v ∈ I
    · -- v ∈ I: take the include branch
      left
      have hcard : (G.nonNeighborSet v (P.erase v)).card < P.card :=
        calc _ ≤ (P.erase v).card := Finset.card_le_card (nonNeighborSet_subset G v _)
          _ < P.card := Finset.card_erase_lt_of_mem hv
      -- R ∪ {v} ⊆ I
      have hRvI : R ∪ {v} ⊆ I :=
        Finset.union_subset hRI (Finset.singleton_subset_iff.mpr hvI)
      -- I \ (R ∪ {v}) ⊆ nonNeighborSet v (P.erase v)
      have hIRvP : I \ (R ∪ {v}) ⊆ G.nonNeighborSet v (P.erase v) := by
        intro w hw
        rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, not_or] at hw
        obtain ⟨hwI, hwR, hwv⟩ := hw
        rw [mem_nonNeighborSet_iff]
        refine ⟨Finset.mem_erase.mpr ⟨hwv, ?_⟩, hwv, ?_⟩
        · exact hIRP (Finset.mem_sdiff.mpr ⟨hwI, hwR⟩)
        · -- w and v are both in I, I is independent, so they're not adjacent
          by_contra h
          have h_eq : G.adjBool w v = true := by
            cases h_eq : G.adjBool w v
            · exact absurd h_eq h
            · rfl
          rw [adjBool_true_iff] at h_eq
          obtain ⟨e, he, hends⟩ := h_eq
          have hIndep := hI.2.1
          simp only [IsIndepSet, decide_eq_true_eq] at hIndep
          rcases hends with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
          · exact hIndep e he ⟨hsrc ▸ hwI, htgt ▸ hvI⟩
          · exact hIndep e he ⟨hsrc ▸ hvI, htgt ▸ hwI⟩
      -- Disjoint (I \ (R ∪ {v})) (nonNeighborSet v X)
      have hIX' : Disjoint (I \ (R ∪ {v})) (G.nonNeighborSet v X) := by
        rw [Finset.disjoint_left]
        intro w hw hwNN
        rw [mem_nonNeighborSet_iff] at hwNN
        have : w ∈ I \ R := by
          rw [Finset.mem_sdiff] at hw ⊢
          exact ⟨hw.1, fun h => hw.2 (Finset.mem_union_left _ h)⟩
        exact Finset.disjoint_left.mp hIX this hwNN.1
      have hRv : IsIndepSet G (R ∪ {v}) = true := by
        apply isIndepSet_insert hR hloops
        intro u hu; exact hRP v (Finset.mem_union_left _ hv) u hu
      have hRP' : ∀ w ∈ G.nonNeighborSet v (P.erase v) ∪ G.nonNeighborSet v X,
          ∀ u ∈ R ∪ {v}, G.adjBool u w = false := by
        intro w hw u hu
        rcases Finset.mem_union.mp hw with hwP | hwX
        · rw [mem_nonNeighborSet_iff] at hwP
          rcases Finset.mem_union.mp hu with huR | huV
          · have := hRP w (Finset.mem_union_left _ (Finset.mem_of_mem_erase hwP.1)) u huR
            rwa [adjBool_comm] at this ⊢
          · rw [Finset.mem_singleton] at huV; subst huV; rw [adjBool_comm]; exact hwP.2.2
        · rw [mem_nonNeighborSet_iff] at hwX
          rcases Finset.mem_union.mp hu with huR | huV
          · have := hRP w (Finset.mem_union_right _ hwX.1) u huR
            rwa [adjBool_comm] at this ⊢
          · rw [Finset.mem_singleton] at huV; subst huV; rw [adjBool_comm]; exact hwX.2.2
      have hPX' : Disjoint (G.nonNeighborSet v (P.erase v)) (G.nonNeighborSet v X) := by
        exact Finset.disjoint_of_subset_right (nonNeighborSet_subset G v X)
          (Finset.disjoint_of_subset_left
            ((nonNeighborSet_subset G v _).trans (Finset.erase_subset v P)) hPX)
      have hPXnodes' : G.nonNeighborSet v (P.erase v) ∪ G.nonNeighborSet v X ⊆ G.nodes :=
        (Finset.union_subset_union (nonNeighborSet_subset G v _) (nonNeighborSet_subset G v _)).trans
          ((Finset.union_subset_union (Finset.erase_subset v P) (Finset.Subset.refl X)).trans hPXnodes)
      have hRPX' : Disjoint (R ∪ {v}) (G.nonNeighborSet v (P.erase v) ∪ G.nonNeighborSet v X) := by
        rw [Finset.disjoint_union_left]
        exact ⟨Finset.disjoint_of_subset_right
            ((Finset.union_subset_union (nonNeighborSet_subset G v _) (nonNeighborSet_subset G v _)).trans
              (Finset.union_subset_union (Finset.erase_subset v P) (Finset.Subset.refl X))) hRPX,
          by rw [Finset.disjoint_singleton_left]
             intro h; rcases Finset.mem_union.mp h with h1 | h2
             · exact not_mem_nonNeighborSet_self G v _ h1
             · exact not_mem_nonNeighborSet_self G v _ h2⟩
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl hRvI hIRvP hIX' hRv hRP' hPX' hPXnodes' hRPX'
    · -- v ∉ I: take the exclude branch
      right
      have hcard : (P.erase v).card < P.card := Finset.card_erase_lt_of_mem hv
      -- I \ R ⊆ P.erase v (since v ∉ I)
      have hIRP' : I \ R ⊆ P.erase v := by
        intro w hw
        have := hIRP hw
        rw [Finset.mem_erase]
        exact ⟨fun hwv => hvI (hwv ▸ (Finset.mem_sdiff.mp hw).1), this⟩
      -- Disjoint (I \ R) (X ∪ {v})
      have hIX' : Disjoint (I \ R) (X ∪ {v}) := by
        rw [Finset.disjoint_union_right]
        exact ⟨hIX, by rw [Finset.disjoint_singleton_right]; intro h; exact hvI (Finset.mem_sdiff.mp h).1⟩
      have hRP' : ∀ w ∈ P.erase v ∪ (X ∪ {v}), ∀ u ∈ R, G.adjBool u w = false := by
        intro w hw u hu
        rcases Finset.mem_union.mp hw with hwP | hwXv
        · exact hRP w (Finset.mem_union_left _ (Finset.mem_of_mem_erase hwP)) u hu
        · rcases Finset.mem_union.mp hwXv with hwX | hwV
          · exact hRP w (Finset.mem_union_right _ hwX) u hu
          · rw [Finset.mem_singleton] at hwV; subst hwV
            exact hRP v (Finset.mem_union_left _ hv) u hu
      have hPX' : Disjoint (P.erase v) (X ∪ {v}) := by
        rw [Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset v P) hPX,
               by rw [Finset.disjoint_singleton_right]; exact Finset.not_mem_erase v P⟩
      have hPXnodes_excl : P.erase v ∪ (X ∪ {v}) ⊆ G.nodes := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · exact hPXnodes (Finset.mem_union_left _ (Finset.mem_of_mem_erase h1))
        · rcases Finset.mem_union.mp h2 with h3 | h4
          · exact hPXnodes (Finset.mem_union_right _ h3)
          · rw [Finset.mem_singleton] at h4; subst h4
            exact hPXnodes (Finset.mem_union_left _ hv)
      have hRPX_excl : Disjoint R (P.erase v ∪ (X ∪ {v})) := by
        rw [Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_right
            ((Finset.erase_subset v P).trans Finset.subset_union_left)
            hRPX,
          by rw [Finset.disjoint_union_right]
             exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right hRPX,
                    by rw [Finset.disjoint_singleton_right]
                       intro hv_in_R
                       exact Finset.disjoint_left.mp hRPX hv_in_R (Finset.mem_union_left _ hv)⟩⟩
      exact ih _ (hPcard ▸ hcard) _ _ _ rfl hRI hIRP' hIX' hR hRP' hPX' hPXnodes_excl hRPX_excl

end Graph

end GraphAlgebra
