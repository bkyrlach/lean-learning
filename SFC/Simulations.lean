/-
  General Simulation Framework

  A Lean 4 formalization of simulation relations between labeled transition
  systems, inspired by the Coq formalization in:
    github.com/gstew5/cage/blob/UnifiedNetworkingCoq10_1/simulations.v

  Components:
  1. Type classes: HasInit, HasFinal, HasStep, LTS
  2. Multi-step relations: StepN (n-step), StepPlus (1+), StepStar (0+)
  3. Key lemmas: transitivity, conversions between step relations
  4. Simulation record with stuttering support via well-founded ordering
  5. Lock-step simulation: simplified constructor for non-stuttering cases
  6. Step-plus diagram: lift simulation from single steps to multi-steps
-/

-- ============================================================================
-- Type Classes for Labeled Transition Systems
-- ============================================================================

class HasInit (S : Type) where
  init : S → Prop

class HasFinal (S : Type) where
  final : S → Prop

class HasStep (S : Type) where
  step : S → S → Prop

class LTS (S : Type) extends HasInit S, HasFinal S, HasStep S

-- ============================================================================
-- Multi-Step Relations
-- ============================================================================

-- n-step relation: exactly n transitions
inductive StepN [HasStep S] : Nat → S → S → Prop where
  | zero : ∀ s, StepN 0 s s
  | succ : ∀ n s1 s2 s3, HasStep.step s1 s2 → StepN n s2 s3 → StepN (n + 1) s1 s3

-- One-or-more steps (transitive closure)
inductive StepPlus [HasStep S] : S → S → Prop where
  | single : ∀ s1 s2, HasStep.step s1 s2 → StepPlus s1 s2
  | cons   : ∀ s1 s2 s3, HasStep.step s1 s2 → StepPlus s2 s3 → StepPlus s1 s3

-- Zero-or-more steps (reflexive transitive closure)
inductive StepStar [HasStep S] : S → S → Prop where
  | refl : ∀ s, StepStar s s
  | step : ∀ s1 s2 s3, HasStep.step s1 s2 → StepStar s2 s3 → StepStar s1 s3

-- ============================================================================
-- Lemmas: StepN
-- ============================================================================

section StepLemmas

variable {S : Type} [HasStep S]

theorem stepN_trans {n m : Nat} {s1 s2 s3 : S} :
    StepN n s1 s2 → StepN m s2 s3 → StepN (n + m) s1 s3 := by
  intro H1 H2
  induction H1 with
  | zero _ => simpa using H2
  | succ n' a b _ Hab _ ih =>
    have : n' + 1 + m = (n' + m) + 1 := by omega
    rw [this]
    exact StepN.succ (n' + m) a b _ Hab (ih H2)

theorem stepN_one {s1 s2 : S} :
    HasStep.step s1 s2 → StepN 1 s1 s2 :=
  fun h => StepN.succ 0 s1 s2 s2 h (StepN.zero s2)

-- ============================================================================
-- Lemmas: StepPlus
-- ============================================================================

theorem stepPlus_trans {s1 s2 s3 : S} :
    StepPlus s1 s2 → StepPlus s2 s3 → StepPlus s1 s3 := by
  intro H1 H2
  induction H1 with
  | single a b Hab => exact StepPlus.cons a b s3 Hab H2
  | cons a b _ Hab _ ih => exact StepPlus.cons a b s3 Hab (ih H2)

-- ============================================================================
-- Lemmas: StepStar
-- ============================================================================

theorem stepStar_trans {s1 s2 s3 : S} :
    StepStar s1 s2 → StepStar s2 s3 → StepStar s1 s3 := by
  intro H1 H2
  induction H1 with
  | refl _ => exact H2
  | step a b _ Hab _ ih => exact StepStar.step a b s3 Hab (ih H2)

theorem stepStar_single {s1 s2 : S} :
    HasStep.step s1 s2 → StepStar s1 s2 :=
  fun h => StepStar.step s1 s2 s2 h (StepStar.refl s2)

-- ============================================================================
-- Conversions Between Step Relations
-- ============================================================================

theorem stepPlus_stepStar {s1 s2 : S} :
    StepPlus s1 s2 → StepStar s1 s2 := by
  intro H
  induction H with
  | single a b Hab => exact stepStar_single Hab
  | cons a b c Hab _ ih => exact StepStar.step a b c Hab ih

theorem stepN_stepStar {n : Nat} {s1 s2 : S} :
    StepN n s1 s2 → StepStar s1 s2 := by
  intro H
  induction H with
  | zero _ => exact StepStar.refl _
  | succ _ a b c Hab _ ih => exact StepStar.step a b c Hab ih

theorem stepN_stepPlus {n : Nat} {s1 s2 : S} :
    StepN (n + 1) s1 s2 → StepPlus s1 s2 := by
  induction n generalizing s1 s2 with
  | zero =>
    intro H
    cases H with
    | succ _ _ b _ Hab Hrest =>
      cases Hrest with
      | zero => exact StepPlus.single _ _ Hab
  | succ k ih =>
    intro H
    cases H with
    | succ _ _ b _ Hab Hrest =>
      exact StepPlus.cons _ b _ Hab (ih Hrest)

theorem stepPlus_stepN {s1 s2 : S} :
    StepPlus s1 s2 → ∃ n, StepN (n + 1) s1 s2 := by
  intro H
  induction H with
  | single a b Hab => exact ⟨0, stepN_one Hab⟩
  | cons a b c Hab _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n + 1, StepN.succ (n + 1) a b c Hab Hn⟩

theorem stepStar_stepPlus_stepPlus {s1 s2 s3 : S} :
    StepStar s1 s2 → StepPlus s2 s3 → StepPlus s1 s3 := by
  intro H1 H2
  induction H1 with
  | refl _ => exact H2
  | step a b _ Hab _ ih => exact StepPlus.cons a b s3 Hab (ih H2)

end StepLemmas

-- ============================================================================
-- Simulation Record
-- ============================================================================

/-
  A simulation from source LTS S to target LTS T, parameterized by:
  - Ord: type for the stuttering index
  - ordLt: well-founded strict ordering on Ord

  The step_diagram captures both progress and stuttering:
  - Progress: target takes one-or-more steps (StepPlus)
  - Stuttering: the ordering index decreases (prevents infinite stutter
    by well-foundedness)

  For lock-step simulations (no stuttering), use Ord = Unit with empty ordering.
-/
structure Simulation (S T : Type) [LTS S] [LTS T]
    (Ord : Type) (ordLt : Ord → Ord → Prop) (hWf : WellFounded ordLt) where
  match_states : Ord → S → T → Prop
  init_diagram : ∀ (s : S), HasInit.init s →
    (∃ (t : T), HasInit.init t) ∧
    (∀ (t : T), HasInit.init t → ∃ x, match_states x s t)
  final_diagram : ∀ x (s : S) (t : T), match_states x s t →
    HasFinal.final s → HasFinal.final t
  step_diagram : ∀ x (s : S) (t : T), match_states x s t → ∀ (s' : S),
    HasStep.step s s' →
    ∃ x', (ordLt x' x ∧ match_states x' s' t) ∨
           (∃ (t' : T), StepPlus t t' ∧ match_states x' s' t')

-- ============================================================================
-- Lock-Step Simulation (Simplified Constructor)
-- ============================================================================

-- The empty relation on Unit is trivially well-founded
def emptyRel (_ _ : Unit) : Prop := False

theorem emptyRel_wf : WellFounded emptyRel :=
  ⟨fun a => ⟨a, fun _ h => absurd h id⟩⟩

/-
  When every source step is matched by exactly one target step (no stuttering),
  the ordering parameter is trivial: Unit with the empty relation.
-/
def Simulation.lockStep {S T : Type} [LTS S] [LTS T]
    (matchFn : S → T → Prop)
    (h_init : ∀ (s : S), HasInit.init s →
      (∃ (t : T), HasInit.init t) ∧
      (∀ (t : T), HasInit.init t → matchFn s t))
    (h_final : ∀ (s : S) (t : T), matchFn s t → HasFinal.final s → HasFinal.final t)
    (h_step : ∀ (s : S) (t : T), matchFn s t → ∀ (s' : S),
      HasStep.step s s' → ∃ (t' : T), HasStep.step t t' ∧ matchFn s' t')
    : Simulation S T Unit emptyRel emptyRel_wf where
  match_states := fun _ s t => matchFn s t
  init_diagram := fun s hs =>
    let ⟨hex, hmatch⟩ := h_init s hs
    ⟨hex, fun t ht => ⟨(), hmatch t ht⟩⟩
  final_diagram := fun _ s t hm hf => h_final s t hm hf
  step_diagram := fun _ s t hm s' hs =>
    let ⟨t', ht', hm'⟩ := h_step s t hm s' hs
    ⟨(), Or.inr ⟨t', StepPlus.single t t' ht', hm'⟩⟩

-- ============================================================================
-- Derived Theorem: StepPlus Diagram (Lock-Step)
-- ============================================================================

/-
  If a lock-step simulation exists and the source takes StepPlus steps,
  the target also takes StepPlus steps with matching states preserved.
-/
theorem Simulation.lockStep_stepPlus_diagram
    {S T : Type} [LTS S] [LTS T]
    (sim : Simulation S T Unit emptyRel emptyRel_wf)
    {s s' : S} {t : T}
    (hm : sim.match_states () s t)
    (hplus : StepPlus s s') :
    ∃ t', StepPlus t t' ∧ sim.match_states () s' t' := by
  induction hplus generalizing t with
  | single s1 s2 hs =>
    obtain ⟨w, hdiag⟩ := sim.step_diagram () s1 t hm s2 hs
    rcases hdiag with ⟨h, -⟩ | ⟨t', ht', hm'⟩
    · exact absurd h id
    · exact ⟨t', ht', by rwa [show w = () from rfl] at hm'⟩
  | cons s1 s2 s3 hs _ ih =>
    obtain ⟨w, hdiag⟩ := sim.step_diagram () s1 t hm s2 hs
    rcases hdiag with ⟨h, -⟩ | ⟨t2, ht2, hm2⟩
    · exact absurd h id
    · have hm2' : sim.match_states () s2 t2 := by rwa [show w = () from rfl] at hm2
      obtain ⟨t3, ht3, hm3⟩ := ih hm2'
      exact ⟨t3, stepPlus_trans ht2 ht3, hm3⟩

-- Lift to StepStar
theorem Simulation.lockStep_stepStar_diagram
    {S T : Type} [LTS S] [LTS T]
    (sim : Simulation S T Unit emptyRel emptyRel_wf)
    {s s' : S} {t : T}
    (hm : sim.match_states () s t)
    (hstar : StepStar s s') :
    ∃ t', StepStar t t' ∧ sim.match_states () s' t' := by
  induction hstar generalizing t with
  | refl _ => exact ⟨t, StepStar.refl t, hm⟩
  | step a b c hab _ ih =>
    obtain ⟨w, hdiag⟩ := sim.step_diagram () a t hm b hab
    rcases hdiag with ⟨h, -⟩ | ⟨t2, ht2, hm2⟩
    · exact absurd h id
    · have hm2' : sim.match_states () b t2 := by rwa [show w = () from rfl] at hm2
      obtain ⟨t3, ht3, hm3⟩ := ih hm2'
      exact ⟨t3, stepStar_trans (stepPlus_stepStar ht2) ht3, hm3⟩

-- ============================================================================
-- Bisimulation (Shared Match Relation with Step Diagrams in Both Directions)
-- ============================================================================

/-
  A bisimulation between LTS S and LTS T with a single shared match relation.
  Unlike a pair of independent simulations, this enforces that both directions
  use the same state correspondence.

  The step diagrams mirror the Simulation's step_diagram:
  - step_forward: when S steps, T responds (progress or stuttering)
  - step_backward: when T steps, S responds (progress or stuttering)
-/
structure Bisimulation (S T : Type) [LTS S] [LTS T]
    (Ord : Type) (ordLt : Ord → Ord → Prop) (hWf : WellFounded ordLt) where
  match_states : Ord → S → T → Prop
  init_diagram : ∀ (s : S), HasInit.init s →
    (∃ (t : T), HasInit.init t) ∧
    (∀ (t : T), HasInit.init t → ∃ x, match_states x s t)
  init_diagram_backward : ∀ (t : T), HasInit.init t →
    (∃ (s : S), HasInit.init s) ∧
    (∀ (s : S), HasInit.init s → ∃ x, match_states x s t)
  final_diagram_forward : ∀ x (s : S) (t : T), match_states x s t →
    HasFinal.final s → HasFinal.final t
  final_diagram_backward : ∀ x (s : S) (t : T), match_states x s t →
    HasFinal.final t → HasFinal.final s
  step_forward : ∀ x (s : S) (t : T), match_states x s t → ∀ (s' : S),
    HasStep.step s s' →
    ∃ x', (ordLt x' x ∧ match_states x' s' t) ∨
           (∃ (t' : T), StepPlus t t' ∧ match_states x' s' t')
  step_backward : ∀ x (s : S) (t : T), match_states x s t → ∀ (t' : T),
    HasStep.step t t' →
    ∃ x', (ordLt x' x ∧ match_states x' s t') ∨
           (∃ (s' : S), StepPlus s s' ∧ match_states x' s' t')

-- ============================================================================
-- Bisimulation Projections to Simulation
-- ============================================================================

def Bisimulation.toForward {S T : Type} [LTS S] [LTS T]
    {Ord : Type} {ordLt : Ord → Ord → Prop} {hWf : WellFounded ordLt}
    (b : Bisimulation S T Ord ordLt hWf) : Simulation S T Ord ordLt hWf where
  match_states := b.match_states
  init_diagram := b.init_diagram
  final_diagram := b.final_diagram_forward
  step_diagram := b.step_forward

def Bisimulation.toBackward {S T : Type} [LTS S] [LTS T]
    {Ord : Type} {ordLt : Ord → Ord → Prop} {hWf : WellFounded ordLt}
    (b : Bisimulation S T Ord ordLt hWf) : Simulation T S Ord ordLt hWf where
  match_states := fun x t s => b.match_states x s t
  init_diagram := b.init_diagram_backward
  final_diagram := fun x t s hm hf => b.final_diagram_backward x s t hm hf
  step_diagram := fun x t s hm t' ht => b.step_backward x s t hm t' ht

-- ============================================================================
-- Lock-Step Bisimulation (Simplified Constructor)
-- ============================================================================

/-
  When every step in either direction is matched by exactly one step in the
  other (no stuttering), the ordering parameter is trivial: Unit with the
  empty relation.
-/
def Bisimulation.lockStep {S T : Type} [LTS S] [LTS T]
    (matchFn : S → T → Prop)
    (h_init : ∀ (s : S), HasInit.init s →
      (∃ (t : T), HasInit.init t) ∧
      (∀ (t : T), HasInit.init t → matchFn s t))
    (h_init_back : ∀ (t : T), HasInit.init t →
      (∃ (s : S), HasInit.init s) ∧
      (∀ (s : S), HasInit.init s → matchFn s t))
    (h_final_fwd : ∀ (s : S) (t : T), matchFn s t →
      HasFinal.final s → HasFinal.final t)
    (h_final_bwd : ∀ (s : S) (t : T), matchFn s t →
      HasFinal.final t → HasFinal.final s)
    (h_step_fwd : ∀ (s : S) (t : T), matchFn s t → ∀ (s' : S),
      HasStep.step s s' → ∃ (t' : T), HasStep.step t t' ∧ matchFn s' t')
    (h_step_bwd : ∀ (s : S) (t : T), matchFn s t → ∀ (t' : T),
      HasStep.step t t' → ∃ (s' : S), HasStep.step s s' ∧ matchFn s' t')
    : Bisimulation S T Unit emptyRel emptyRel_wf where
  match_states := fun _ s t => matchFn s t
  init_diagram := fun s hs =>
    let ⟨hex, hmatch⟩ := h_init s hs
    ⟨hex, fun t ht => ⟨(), hmatch t ht⟩⟩
  init_diagram_backward := fun t ht =>
    let ⟨hex, hmatch⟩ := h_init_back t ht
    ⟨hex, fun s hs => ⟨(), hmatch s hs⟩⟩
  final_diagram_forward := fun _ s t hm hf => h_final_fwd s t hm hf
  final_diagram_backward := fun _ s t hm hf => h_final_bwd s t hm hf
  step_forward := fun _ s t hm s' hs =>
    let ⟨t', ht', hm'⟩ := h_step_fwd s t hm s' hs
    ⟨(), Or.inr ⟨t', StepPlus.single t t' ht', hm'⟩⟩
  step_backward := fun _ s t hm t' ht =>
    let ⟨s', hs', hm'⟩ := h_step_bwd s t hm t' ht
    ⟨(), Or.inr ⟨s', StepPlus.single s s' hs', hm'⟩⟩
