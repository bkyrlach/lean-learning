/-
  GraphAlgebra.Lawler

  Lawler's (1976) dynamic programming algorithm for chromatic number computation.

  The algorithm computes χ(G) via DP over vertex subsets:
    chromDP(∅) = 0
    chromDP(S) = min { 1 + chromDP(S \ I) : I ⊆ S, I nonempty, I independent }

  Main results:
  1. `lawlerChromatic G G.nodes` computes a valid coloring bound (soundness)
  2. For treewidth-k graphs: `lawlerChromatic G G.nodes ≤ k + 1` (via separator induction)
-/
import GraphAlgebra.Induction
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Basic

namespace GraphAlgebra

namespace Graph

variable {V L : Type} [DecidableEq V] [DecidableEq L]

/-! ## Coloring Definitions -/

/-- A proper c-coloring of G: adjacent vertices get different colors. -/
def ProperColoring (G : Graph V L) (c : ℕ) (f : V → Fin c) : Prop :=
  ∀ e ∈ G.edges, f e.src ≠ f e.tgt

/-- G is c-colorable if there exists a proper c-coloring. -/
def Colorable (G : Graph V L) (c : ℕ) : Prop :=
  ∃ f : V → Fin c, ProperColoring G c f

/-- G has no self-loops. -/
def NoSelfLoops (G : Graph V L) : Prop :=
  ∀ e ∈ G.edges, e.src ≠ e.tgt

/-! ## Independent Sets (Decidable/Computable) -/

/-- A set of vertices is independent if no edge has both endpoints in it. -/
def IsIndepSet (G : Graph V L) (I : Finset V) : Bool :=
  decide (∀ e ∈ G.edges, ¬(e.src ∈ I ∧ e.tgt ∈ I))

/-- All nonempty independent subsets of S in G. -/
def indepSubsets (G : Graph V L) (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun I => I.card > 0 && G.IsIndepSet I

theorem indepSubsets_sub {G : Graph V L} {S : Finset V} {I : Finset V}
    (hI : I ∈ indepSubsets G S) : I ⊆ S := by
  simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset] at hI
  exact hI.1

theorem indepSubsets_nonempty {G : Graph V L} {S : Finset V} {I : Finset V}
    (hI : I ∈ indepSubsets G S) : I.Nonempty := by
  simp only [indepSubsets, Finset.mem_filter, decide_eq_true_eq, Bool.and_eq_true] at hI
  exact Finset.card_pos.mp hI.2.1

theorem sdiff_card_lt_of_sub_nonempty {S I : Finset V}
    (hsub : I ⊆ S) (hne : I.Nonempty) : (S \ I).card < S.card := by
  rw [Finset.card_sdiff hsub]
  have hS : 0 < S.card := by
    calc S.card ≥ I.card := Finset.card_le_card hsub
        _ > 0 := Finset.Nonempty.card_pos hne
  exact Nat.sub_lt hS (Finset.Nonempty.card_pos hne)

/-! ## Lawler's DP Algorithm -/

/-- **Lawler's chromatic DP**: minimum colors to properly color G restricted to vertex set S.

Computes `chromDP(S)` by the recurrence:
- `chromDP(∅) = 0`
- `chromDP(S) = min { 1 + chromDP(S \ I) : I ⊆ S, I independent, I nonempty }`

Uses `Finset.fold min` for computability (avoids noncomputable `Finset.toList`).
Falls back to `|S|` if no independent subset is found (only happens with self-loops). -/
def lawlerChromatic (G : Graph V L) (S : Finset V) : ℕ :=
  if S.card = 0 then 0
  else
    (indepSubsets G S).fold min S.card fun I =>
      if h : I ⊆ S ∧ I.Nonempty then
        have : (S \ I).card < S.card := sdiff_card_lt_of_sub_nonempty h.1 h.2
        1 + lawlerChromatic G (S \ I)
      else S.card
termination_by S.card

/-- The chromatic number bound for the whole graph. -/
def lawlerChromaticNumber (G : Graph V L) : ℕ :=
  lawlerChromatic G G.nodes

/-! ## Soundness: DP Gives Valid Colorings -/

-- Helper: edges of the induced subgraph on S \ I are edges of the induced subgraph on S
-- whose endpoints are both in S \ I.
private theorem inducedSubgraph_sdiff_edges {G : Graph V L} {S I : Finset V}
    {hS : S ⊆ G.nodes} {hSI : S \ I ⊆ G.nodes}
    {e : Edge V L} (he : e ∈ (G.inducedSubgraph (S \ I) hSI).edges) :
    e ∈ (G.inducedSubgraph S hS).edges := by
  simp only [inducedSubgraph, Finset.mem_filter] at he ⊢
  exact ⟨he.1, Finset.mem_sdiff.mp he.2.1 |>.1, Finset.mem_sdiff.mp he.2.2 |>.1⟩

open Classical in
/-- Key lemma: if G[S] is c-colorable, then lawlerChromatic G S ≤ c. -/
theorem lawlerChromatic_le_of_colorable {G : Graph V L}
    (S : Finset V) (hS : S ⊆ G.nodes) (c : ℕ)
    (hcol : Colorable (G.inducedSubgraph S hS) c) :
    lawlerChromatic G S ≤ c := by
  -- Strong induction on S.card
  suffices h : ∀ n (S : Finset V) (hS : S ⊆ G.nodes), S.card = n →
      ∀ c, Colorable (G.inducedSubgraph S hS) c → lawlerChromatic G S ≤ c from
    h S.card S hS rfl c hcol
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro S hS hScard c hcol
  -- Base case: S is empty
  by_cases hcard : S.card = 0
  · simp [lawlerChromatic, hcard]
  -- S is nonempty
  · have hSne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
    -- c must be positive (can't color nonempty graph with 0 colors)
    obtain ⟨f, hf⟩ := hcol
    by_cases hc : c = 0
    · subst hc; obtain ⟨v₀, _⟩ := hSne; exact Fin.elim0 (f v₀)
    ·
      -- Pick v₀ ∈ S and form color class I = {v ∈ S : f v = f v₀}
      obtain ⟨v₀, hv₀⟩ := hSne
      let color₀ := f v₀
      let I := S.filter (fun v => f v = color₀)
      -- I ⊆ S
      have hIsub : I ⊆ S := Finset.filter_subset _ _
      -- I is nonempty (contains v₀)
      have hIne : I.Nonempty := ⟨v₀, Finset.mem_filter.mpr ⟨hv₀, rfl⟩⟩
      -- I is independent: no edge has both endpoints in I
      have hIindep : G.IsIndepSet I = true := by
        simp only [IsIndepSet, decide_eq_true_eq]
        intro e he hboth
        have he_sub : e ∈ (G.inducedSubgraph S hS).edges := by
          simp only [inducedSubgraph, Finset.mem_filter]
          exact ⟨he, hIsub hboth.1, hIsub hboth.2⟩
        have := hf e he_sub
        have hboth1 : f e.src = color₀ := by
          have := Finset.mem_filter.mp hboth.1; exact this.2
        have hboth2 : f e.tgt = color₀ := by
          have := Finset.mem_filter.mp hboth.2; exact this.2
        rw [hboth1, hboth2] at this
        exact this rfl
      -- I ∈ indepSubsets G S
      have hImem : I ∈ indepSubsets G S := by
        unfold indepSubsets
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_powerset.mpr hIsub, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Finset.Nonempty.card_pos hIne, hIindep⟩
      -- lawlerChromatic G (S \ I) ≤ c - 1
      have hSI_sub : S \ I ⊆ G.nodes := Finset.Subset.trans Finset.sdiff_subset hS
      have hSI_lt : (S \ I).card < S.card := sdiff_card_lt_of_sub_nonempty hIsub hIne
      have hIH : lawlerChromatic G (S \ I) ≤ c - 1 := by
        by_cases hc1 : c = 1
        · -- When c = 1, all vertices get the same color, so S \ I = ∅
          have hSI_empty : (S \ I).card = 0 := by
            rw [Finset.card_eq_zero]
            ext v; constructor
            · intro hv
              have hvS := Finset.mem_sdiff.mp hv |>.1
              have hvI := Finset.mem_sdiff.mp hv |>.2
              have : f v = f v₀ := by
                ext; have := (f v).isLt; have := (f v₀).isLt; omega
              exact absurd (Finset.mem_filter.mpr ⟨hvS, this⟩) hvI
            · intro hv; exact absurd hv (Finset.notMem_empty _)
          simp [lawlerChromatic, hSI_empty, hc1]
        · -- c ≥ 2, so c - 1 ≥ 1, and S \ I is (c-1)-colorable
          have hc2 : 2 ≤ c := by omega
          have hSI_col : Colorable (G.inducedSubgraph (S \ I) hSI_sub) (c - 1) := by
            -- Remap colors: skip color₀ by shifting down colors above it
            let remap (i : Fin c) : Fin (c - 1) :=
              if h : i.val < color₀.val then
                ⟨i.val, by omega⟩
              else if _ : i.val = color₀.val then
                ⟨0, by omega⟩
              else
                ⟨i.val - 1, by omega⟩
            -- remap is injective on values ≠ color₀
            have remap_inj : ∀ a b : Fin c, a ≠ color₀ → b ≠ color₀ →
                remap a = remap b → a = b := by
              intro a b ha hb heq
              have ha_val : a.val ≠ color₀.val := fun h => ha (Fin.ext h)
              have hb_val : b.val ≠ color₀.val := fun h => hb (Fin.ext h)
              simp only [remap] at heq
              split at heq <;> split at heq <;> rename_i h1 h2
              all_goals (simp only [Fin.mk.injEq] at heq; try (ext; omega))
            refine ⟨fun v => remap (f v), fun e he => ?_⟩
            have he' := @inducedSubgraph_sdiff_edges V L _ _ G S I hS hSI_sub e he
            have hne := hf e he'
            simp only [inducedSubgraph, Finset.mem_filter, Finset.mem_sdiff] at he
            have hsrc_ne : f e.src ≠ color₀ := by
              intro heq
              exact he.2.1.2 (Finset.mem_filter.mpr ⟨he.2.1.1, heq⟩)
            have htgt_ne : f e.tgt ≠ color₀ := by
              intro heq
              exact he.2.2.2 (Finset.mem_filter.mpr ⟨he.2.2.1, heq⟩)
            intro hremap_eq
            exact hne (remap_inj _ _ hsrc_ne htgt_ne hremap_eq)
          exact ih (S \ I).card (hScard ▸ hSI_lt) (S \ I) hSI_sub rfl (c - 1) hSI_col
      -- Unfold lawlerChromatic for nonempty S
      have hLC : lawlerChromatic G S =
          (indepSubsets G S).fold min S.card (fun I =>
            if h : I ⊆ S ∧ I.Nonempty then
              1 + lawlerChromatic G (S \ I)
            else S.card) := by
        rw [lawlerChromatic]
        simp [hcard]
      rw [hLC]
      -- fold min ≤ f I for I in the finset
      have : (indepSubsets G S).fold min S.card (fun I =>
            if h : I ⊆ S ∧ I.Nonempty then
              1 + lawlerChromatic G (S \ I)
            else S.card) ≤
          (if h : I ⊆ S ∧ I.Nonempty then
              1 + lawlerChromatic G (S \ I)
            else S.card) := by
        rw [Finset.fold_min_le]
        exact Or.inr ⟨I, hImem, le_refl _⟩
      simp only [hIsub, hIne, and_self, dite_true] at this
      calc _ ≤ 1 + lawlerChromatic G (S \ I) := this
        _ ≤ 1 + (c - 1) := by omega
        _ = c := by omega

-- Monotonicity: if G is c-colorable and c ≤ c', then G is c'-colorable.
theorem colorable_mono {G : Graph V L} {c c' : ℕ} (hcol : Colorable G c) (hle : c ≤ c') :
    Colorable G c' := by
  obtain ⟨f, hf⟩ := hcol
  refine ⟨fun v => ⟨(f v).val, by omega⟩, fun e he => ?_⟩
  intro heq
  have hveq : (f e.src).val = (f e.tgt).val := by
    have := Fin.mk.inj heq; exact this
  exact hf e he (Fin.val_injective hveq)

-- fold min achievability: the result is either b or f x for some x in s.
private theorem fold_min_achievable [DecidableEq α] {s : Finset α} {b : ℕ} {f : α → ℕ} :
    s.fold min b f = b ∨ ∃ x ∈ s, s.fold min b f = f x := by
  induction s using Finset.induction_on with
  | empty => left; simp [Finset.fold_empty]
  | insert a s hna ih =>
    rw [Finset.fold_insert hna]
    rcases ih with hval | ⟨x, hx, hval⟩
    · -- fold over s was b
      rw [hval]
      simp only [min_def]
      split
      · right; exact ⟨a, Finset.mem_insert_self a s, rfl⟩
      · left; rfl
    · -- fold over s was f x
      rw [hval]
      simp only [min_def]
      split
      · right; exact ⟨a, Finset.mem_insert_self a s, rfl⟩
      · right; exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩

-- Trivial coloring: any graph with no self-loops on S vertices is S.card-colorable
-- by injecting vertices via an equivalence with Fin S.card.
open Classical in
private theorem colorable_card {G : Graph V L} (S : Finset V) (hS : S ⊆ G.nodes)
    (hloops : NoSelfLoops G) (hne : S.Nonempty) :
    Colorable (G.inducedSubgraph S hS) S.card := by
  have hcard : S.card > 0 := Finset.Nonempty.card_pos hne
  let equiv := S.equivFin
  refine ⟨fun v => if h : v ∈ S then equiv ⟨v, h⟩ else ⟨0, hcard⟩, ?_⟩
  intro e he
  simp only [inducedSubgraph, Finset.mem_filter] at he
  have hsrc := he.2.1
  have htgt := he.2.2
  simp only [dif_pos hsrc, dif_pos htgt]
  intro heq
  have hinj := equiv.injective heq
  simp only [Subtype.mk.injEq] at hinj
  exact hloops e he.1 hinj

-- Color extension: if I is independent in G, I ⊆ S, and G[S\I] is c-colorable,
-- then G[S] is (1+c)-colorable.
open Classical in
private theorem colorable_extend_indep {G : Graph V L} {S I : Finset V}
    {c : ℕ} (hS : S ⊆ G.nodes) (hSI : S \ I ⊆ G.nodes)
    (hIsub : I ⊆ S) (hIindep : G.IsIndepSet I = true)
    (hcol : Colorable (G.inducedSubgraph (S \ I) hSI) c) :
    Colorable (G.inducedSubgraph S hS) (1 + c) := by
  obtain ⟨f, hf⟩ := hcol
  -- Color: vertices in I get color c (the new color), vertices in S\I keep their old color
  let newColor : Fin (1 + c) := ⟨c, by omega⟩
  let coloring : V → Fin (1 + c) := fun v =>
    if v ∈ I then newColor
    else ⟨(f v).val, by omega⟩
  refine ⟨coloring, fun e he => ?_⟩
  simp only [inducedSubgraph, Finset.mem_filter] at he
  obtain ⟨heG, hsrcS, htgtS⟩ := he
  simp only [coloring]
  -- Case analysis on whether src and tgt are in I
  by_cases hsrcI : e.src ∈ I
  · by_cases htgtI : e.tgt ∈ I
    · -- Both in I: contradicts independence
      simp only [IsIndepSet, decide_eq_true_eq] at hIindep
      exact absurd ⟨hsrcI, htgtI⟩ (hIindep e heG)
    · -- src in I, tgt not in I: colors are c vs (f e.tgt).val < c
      simp only [hsrcI, htgtI, ite_true, ite_false, newColor]
      intro heq
      have : c = (f e.tgt).val := congrArg Fin.val heq
      omega
  · by_cases htgtI : e.tgt ∈ I
    · -- src not in I, tgt in I: colors are (f e.src).val < c vs c
      simp only [hsrcI, htgtI, ite_false, ite_true, newColor]
      intro heq
      have : (f e.src).val = c := congrArg Fin.val heq
      omega
    · -- Neither in I: use the old coloring
      simp only [hsrcI, htgtI, ite_false]
      intro heq
      have hveq : (f e.src).val = (f e.tgt).val := by
        have := Fin.mk.inj heq; exact this
      have he' : e ∈ (G.inducedSubgraph (S \ I) hSI).edges := by
        simp only [inducedSubgraph, Finset.mem_filter, Finset.mem_sdiff]
        exact ⟨heG, ⟨hsrcS, hsrcI⟩, ⟨htgtS, htgtI⟩⟩
      exact hf e he' (Fin.val_injective hveq)

open Classical in
/-- Soundness: G[S] is lawlerChromatic-colorable (for nonempty S ⊆ nodes).

Note: `S.Nonempty` is required because `lawlerChromatic G ∅ = 0` and `Colorable G[∅] 0`
needs `V → Fin 0`, which is impossible for nonempty `V`. -/
theorem colorable_of_lawlerChromatic {G : Graph V L}
    (S : Finset V) (hS : S ⊆ G.nodes) (hloops : NoSelfLoops G) (hSne : S.Nonempty) :
    Colorable (G.inducedSubgraph S hS) (lawlerChromatic G S) := by
  -- Strong induction on S.card
  suffices h : ∀ n (S : Finset V) (hS : S ⊆ G.nodes), S.Nonempty → S.card = n →
      Colorable (G.inducedSubgraph S hS) (lawlerChromatic G S) from
    h S.card S hS hSne rfl
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
  intro S hS hSne hScard
  have hcard : S.card ≠ 0 := Finset.Nonempty.card_pos hSne |>.ne'
  · -- S is nonempty
    -- Unfold lawlerChromatic
    have hLC : lawlerChromatic G S =
        (indepSubsets G S).fold min S.card (fun I =>
          if h : I ⊆ S ∧ I.Nonempty then
            1 + lawlerChromatic G (S \ I)
          else S.card) := by
      conv_lhs => rw [lawlerChromatic]
      simp only [hcard, ↓reduceIte]
    rw [hLC]
    -- The fold min is either S.card or 1 + lawlerChromatic G (S\I) for some I
    let f := fun I : Finset V =>
      if h : I ⊆ S ∧ I.Nonempty then
        1 + lawlerChromatic G (S \ I)
      else S.card
    have hachieve := @fold_min_achievable _ _ (indepSubsets G S) S.card f
    rcases hachieve with hval | ⟨I, hImem, hval⟩
    · -- fold = S.card: trivial coloring
      rw [hval]
      exact colorable_card S hS hloops hSne
    · -- fold = f I = 1 + lawlerChromatic G (S\I) for some I in indepSubsets
      rw [hval]
      simp only [f]
      have hIsub := indepSubsets_sub hImem
      have hIne := indepSubsets_nonempty hImem
      simp only [hIsub, hIne, and_self, dite_true]
      -- I is independent
      have hIindep : G.IsIndepSet I = true := by
        simp only [indepSubsets, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hImem
        exact hImem.2.2
      -- S \ I ⊆ G.nodes
      have hSI : S \ I ⊆ G.nodes := Finset.Subset.trans Finset.sdiff_subset hS
      -- (S\I).card < S.card
      have hSI_lt : (S \ I).card < S.card := sdiff_card_lt_of_sub_nonempty hIsub hIne
      -- IH: G[S\I] is colorable with lawlerChromatic G (S\I) colors
      by_cases hSIne : (S \ I).Nonempty
      · have hIH := ih (S \ I).card (hScard ▸ hSI_lt) (S \ I) hSI hSIne rfl
        exact colorable_extend_indep hS hSI hIsub hIindep hIH
      · -- S \ I is empty, so I ⊇ S; lawlerChromatic G ∅ = 0
        rw [Finset.not_nonempty_iff_eq_empty] at hSIne
        have hSI_zero : lawlerChromatic G (S \ I) = 0 := by
          rw [hSIne]; unfold lawlerChromatic; simp
        rw [hSI_zero]
        -- Need: Colorable G[S] 1. Since S ⊆ I and I is independent,
        -- G[S] has no edges, so the constant coloring works.
        simp only [IsIndepSet, decide_eq_true_eq] at hIindep
        refine ⟨fun _ => ⟨0, by omega⟩, fun e he => ?_⟩
        simp only [inducedSubgraph, Finset.mem_filter] at he
        -- e.src ∈ S ⊆ I and e.tgt ∈ S ⊆ I, contradicting independence
        have : S ⊆ I := by
          intro v hv; by_contra hvI
          exact Finset.notMem_empty _ (hSIne ▸ Finset.mem_sdiff.mpr ⟨hv, hvI⟩)
        exact absurd ⟨this he.2.1, this he.2.2⟩ (hIindep e he.1)

/-! ## Treewidth Bound via Separator Induction -/

open Classical in
/-- The set of all neighbors of v (both directions). -/
def allNeighbors (G : Graph V L) (v : V) : Finset V :=
  G.nodes.filter (fun u => u ≠ v ∧
    ∃ e ∈ G.edges, (e.src = v ∧ e.tgt = u) ∨ (e.src = u ∧ e.tgt = v))

theorem allNeighbors_subset (G : Graph V L) (v : V) :
    G.allNeighbors v ⊆ G.nodes :=
  Finset.filter_subset _ _

open Classical in
theorem not_mem_allNeighbors_self (G : Graph V L) (v : V) :
    v ∉ G.allNeighbors v := by
  simp only [allNeighbors, Finset.mem_filter]; intro ⟨_, habs, _⟩; exact habs rfl

/-! ### Coloring Lemmas -/

open Classical in
/-- If a finset of colors has fewer than n elements, there's a color not in it. -/
theorem exists_free_color {n : ℕ} (used : Finset (Fin n)) (h : used.card < n) :
    ∃ c : Fin n, c ∉ used := by
  by_contra h_all
  push_neg at h_all
  have hsub : Finset.univ ⊆ used := fun c _ => h_all c
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_fin] at hle
  omega

open Classical in
theorem noSelfLoops_graphMinusVertex {G : Graph V L} (hG : NoSelfLoops G) (v : V) :
    NoSelfLoops (graphMinusVertex G v) := by
  intro e he
  simp only [graphMinusVertex, Finset.mem_filter] at he
  exact hG e he.1

theorem graphMinusVertex_nodes_card {G : Graph V L} {v : V} (hv : v ∈ G.nodes) :
    (graphMinusVertex G v).nodes.card < G.nodes.card := by
  show (G.nodes.erase v).card < G.nodes.card
  exact Finset.card_erase_lt_of_mem hv

/-! ### Unique-Bag Degree Bound -/

open Classical in
theorem allNeighbors_subset_bag {G : Graph V L}
    (td : TreeDecomp G) (v : V) (_hv : v ∈ G.nodes)
    (t : ℕ) (_ht : t ∈ td.treeNodes) (_hvt : v ∈ td.bag t)
    (h_unique : ∀ s ∈ td.treeNodes, v ∈ td.bag s → s = t) :
    G.allNeighbors v ⊆ (td.bag t).erase v := by
  intro u hu
  simp only [allNeighbors, Finset.mem_filter] at hu
  obtain ⟨_, hne, e, he, hends⟩ := hu
  obtain ⟨s, hs, hse⟩ := td.edge_cover e he
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Finset.mem_erase.mpr ⟨hne, (h_unique s hs hse.1) ▸ hse.2⟩
  · exact Finset.mem_erase.mpr ⟨hne, (h_unique s hs hse.2) ▸ hse.1⟩

open Classical in
theorem degree_le_of_unique_bag {G : Graph V L} {k : ℕ}
    (td : TreeDecomp G) (hwidth : td.width ≤ k)
    (v : V) (hv : v ∈ G.nodes)
    (t : ℕ) (ht : t ∈ td.treeNodes) (hvt : v ∈ td.bag t)
    (h_unique : ∀ s ∈ td.treeNodes, v ∈ td.bag s → s = t) :
    (G.allNeighbors v).card ≤ k := by
  have h1 := Finset.card_le_card (allNeighbors_subset_bag td v hv t ht hvt h_unique)
  have h2 : ((td.bag t).erase v).card ≤ (td.bag t).card - 1 :=
    Nat.le_sub_one_of_lt (Finset.card_erase_lt_of_mem hvt)
  have h3 := bag_card_le_of_width td hwidth t ht
  omega

/-! ### Coloring Extension -/

open Classical in
private theorem coloring_extend_src {G : Graph V L} {n : ℕ}
    {v : V} {c : Fin n} {f' : V → Fin n}
    (hloops : NoSelfLoops G) (hc : c ∉ (G.allNeighbors v).image f')
    (e : Edge V L) (he : e ∈ G.edges) (hsv : e.src = v) :
    (Function.update f' v c) e.src ≠ (Function.update f' v c) e.tgt := by
  have htgt : e.tgt ≠ v := by intro h; exact hloops e he (hsv.trans h.symm)
  simp only [Function.update_apply, hsv, if_neg htgt]
  intro heq
  exact hc (Finset.mem_image.mpr ⟨e.tgt, by
    simp only [allNeighbors, Finset.mem_filter]
    exact ⟨G.edge_tgt_valid e he, htgt, e, he, Or.inl ⟨hsv, rfl⟩⟩, heq.symm⟩)

open Classical in
private theorem coloring_extend_tgt {G : Graph V L} {n : ℕ}
    {v : V} {c : Fin n} {f' : V → Fin n}
    (_hloops : NoSelfLoops G) (hc : c ∉ (G.allNeighbors v).image f')
    (e : Edge V L) (he : e ∈ G.edges) (hsv : e.src ≠ v) (htv : e.tgt = v) :
    (Function.update f' v c) e.src ≠ (Function.update f' v c) e.tgt := by
  simp only [Function.update_apply, htv, if_neg hsv]
  intro heq
  exact hc (Finset.mem_image.mpr ⟨e.src, by
    simp only [allNeighbors, Finset.mem_filter]
    exact ⟨G.edge_src_valid e he, hsv, e, he, Or.inr ⟨rfl, htv⟩⟩, heq⟩)

/-! ### (k+1)-Colorability for Bounded Treewidth -/

open Classical in
/-- Every graph of treewidth ≤ k without self-loops is (k+1)-colorable. -/
theorem colorable_of_hasTreewidthAtMost {G : Graph V L} {k : ℕ}
    (htw : HasTreewidthAtMost G k) (hloops : NoSelfLoops G) :
    Colorable G (k + 1) := by
  suffices h : ∀ n (G : Graph V L), G.nodes.card = n →
      HasTreewidthAtMost G k → NoSelfLoops G → Colorable G (k + 1) from
    h _ G rfl htw hloops
  intro n
  induction n using Nat.strongRecOn' with
  | _ n ih =>
    intro G hcard htw hloops
    by_cases hbase : G.nodes.card ≤ k + 1
    · -- Base: ≤ k+1 vertices, trivially colorable
      suffices h : ∀ m (G : Graph V L), G.nodes.card = m → m ≤ k + 1 →
          NoSelfLoops G → Colorable G (k + 1) from h _ G rfl hbase hloops
      intro m
      induction m using Nat.strongRecOn' with
      | _ m ihm =>
        intro G hcm hle hloops
        by_cases hne : G.nodes.Nonempty
        · obtain ⟨v, hv⟩ := hne
          have hG'card := graphMinusVertex_nodes_card hv
          obtain ⟨f', hf'⟩ := ihm (graphMinusVertex G v).nodes.card (by omega)
            (graphMinusVertex G v) rfl (by omega) (noSelfLoops_graphMinusVertex hloops v)
          by_cases hn : k + 1 = 0
          · omega
          · let usedColors : Finset (Fin (k + 1)) := (G.allNeighbors v).image f'
            have hneigh : (G.allNeighbors v).card ≤ G.nodes.card - 1 := by
              have hlt : (G.allNeighbors v).card < G.nodes.card :=
                lt_of_lt_of_le (Finset.card_lt_card ⟨allNeighbors_subset G v,
                  fun h => not_mem_allNeighbors_self G v (h hv)⟩) le_rfl
              omega
            have hused : usedColors.card < k + 1 := by
              calc usedColors.card ≤ (G.allNeighbors v).card := Finset.card_image_le
                _ ≤ G.nodes.card - 1 := hneigh
                _ < k + 1 := by omega
            obtain ⟨c, hc⟩ := exists_free_color usedColors hused
            refine ⟨Function.update f' v c, ?_⟩
            intro e he
            by_cases hsv : e.src = v
            · exact coloring_extend_src hloops hc e he hsv
            · by_cases htv : e.tgt = v
              · exact coloring_extend_tgt hloops hc e he hsv htv
              · rw [Function.update_of_ne hsv, Function.update_of_ne htv]
                exact hf' e (by
                  simp only [graphMinusVertex, Finset.mem_filter]; exact ⟨he, hsv, htv⟩)
        · push_neg at hne; rw [Finset.not_nonempty_iff_eq_empty] at hne
          exact ⟨fun _ => ⟨0, by omega⟩, fun e he =>
            absurd (G.edge_src_valid e he) (by simp [hne])⟩
    · -- Step: find unique-bag vertex, remove, recurse
      push_neg at hbase
      obtain ⟨td, hwidth⟩ := htw
      obtain ⟨v, hv, t, ht, hvt, h_unique⟩ :=
        exists_unique_bag_vertex td hwidth hbase
      have hdeg := degree_le_of_unique_bag td hwidth v hv t ht hvt h_unique
      have hG'tw : HasTreewidthAtMost (graphMinusVertex G v) k :=
        ⟨treeDecompMinusVertex td v, treeDecompMinusVertex_width_le td v hwidth⟩
      have hG'card := graphMinusVertex_nodes_card hv
      obtain ⟨f', hf'⟩ := ih (graphMinusVertex G v).nodes.card (by omega)
        (graphMinusVertex G v) rfl hG'tw (noSelfLoops_graphMinusVertex hloops v)
      let usedColors : Finset (Fin (k + 1)) := (G.allNeighbors v).image f'
      have hused : usedColors.card < k + 1 :=
        calc usedColors.card
            ≤ (G.allNeighbors v).card := Finset.card_image_le
          _ ≤ k := hdeg
          _ < k + 1 := Nat.lt_succ_of_le le_rfl
      obtain ⟨c, hc⟩ := exists_free_color usedColors hused
      refine ⟨Function.update f' v c, ?_⟩
      intro e he
      by_cases hsv : e.src = v
      · exact coloring_extend_src hloops hc e he hsv
      · by_cases htv : e.tgt = v
        · exact coloring_extend_tgt hloops hc e he hsv htv
        · rw [Function.update_of_ne hsv, Function.update_of_ne htv]
          exact hf' e (by
            simp only [graphMinusVertex, Finset.mem_filter]; exact ⟨he, hsv, htv⟩)

/-! ## Main Result: Lawler's DP Bound for Bounded Treewidth

Using `separator_induction_tw`, we show the DP produces an optimal bound
that matches the (k+1)-colorability theorem. -/

open Classical in
/-- **Lawler's bound via separator induction**: for treewidth-k graphs without self-loops,
    the chromatic number (and hence Lawler's DP) gives ≤ k+1.

    Proof by `separator_induction_tw`:
    - Base (|V| ≤ k+1): at most k+1 vertices, so k+1 colors suffice trivially.
    - Glue (G = G₁ ∪_S G₂, |S| ≤ k+1): if both pieces are (k+1)-colorable,
      their gluing is too (recolor to agree on the separator). -/
theorem lawler_treewidth_bound {G : Graph V L} {k : ℕ}
    (htw : HasTreewidthAtMost G k) (hloops : NoSelfLoops G) :
    lawlerChromaticNumber G ≤ k + 1 := by
  -- The DP is bounded by the colorability:
  -- G is (k+1)-colorable → lawlerChromatic ≤ k+1
  have hcol := colorable_of_hasTreewidthAtMost htw hloops
  exact lawlerChromatic_le_of_colorable G.nodes (Finset.Subset.refl _) (k + 1) (by
    -- Convert Colorable G (k+1) to Colorable (inducedSubgraph G.nodes _) (k+1)
    obtain ⟨f, hf⟩ := hcol
    exact ⟨f, fun e he => by
      simp only [inducedSubgraph, Finset.mem_filter] at he
      exact hf e he.1⟩)

end Graph

end GraphAlgebra
