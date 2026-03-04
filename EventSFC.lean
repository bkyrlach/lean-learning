/-
  Event-Aware Sequential Function Charts (EventSFC)

  IEC 61131-3 separates events (messages received by a step) from guards
  (boolean conditions on transitions). Our base SFC.lean conflates these by
  encoding messages as `Guard.Eq "msg" N` inside the guard.

  This file factors events out of guards into a dedicated field on transitions,
  then proves the semantics equivalent to the original SFC when events are
  folded back into guards.
-/
import SFC

-- ============================================================================
-- EventTransition: transition with dedicated event field
-- ============================================================================

structure EventTransition where
  sources  : List StepId
  targets  : List StepId
  event    : Nat              -- message/event ID
  guard    : Guard            -- pure boolean condition (no event encoding)
  priority : Nat := 0
deriving Repr, DecidableEq

-- ============================================================================
-- EventSFC: SFC with event-aware transitions
-- ============================================================================

structure EventSFC where
  steps       : List Step
  transitions : List EventTransition
  eventVar    : Var := "msg"   -- which valuation variable carries the event
deriving Repr

-- ============================================================================
-- EventTransition.enabled
-- ============================================================================

def EventTransition.enabled (t : EventTransition) (cfg : Config) (eventVar : Var) : Bool :=
  allActive t.sources cfg.active &&
  (cfg.valuation eventVar == t.event) &&
  t.guard.eval cfg.valuation

-- ============================================================================
-- EventSFCStep: step relation for event-aware SFC
-- ============================================================================

inductive EventSFCStep (esfc : EventSFC) : Config → Config → Prop where
  | fireTransition : ∀ cfg (t : EventTransition) cfg',
      t ∈ esfc.transitions →
      t.enabled cfg esfc.eventVar = true →
      (∀ t' ∈ esfc.transitions,
        t'.sources = t.sources →
        t'.enabled cfg esfc.eventVar = true →
        t.priority ≤ t'.priority) →
      cfg'.active = activate (deactivate cfg.active t.sources) t.targets →
      cfg'.valuation = cfg.valuation →
      EventSFCStep esfc cfg cfg'

-- ============================================================================
-- Translation: EventSFC → SFC
-- ============================================================================

/-- Fold the event check into the guard: `.And (.Eq eventVar event) guard` -/
def EventTransition.toTransition (t : EventTransition) (eventVar : Var) : Transition :=
  { sources  := t.sources
    targets  := t.targets
    guard    := .And (.Eq eventVar t.event) t.guard
    priority := t.priority }

/-- Convert an EventSFC to a plain SFC by folding events into guards -/
def EventSFC.toSFC (esfc : EventSFC) : SFC :=
  { steps       := esfc.steps
    transitions := esfc.transitions.map (·.toTransition esfc.eventVar) }

-- ============================================================================
-- Key Lemma: enabled equivalence
-- ============================================================================

theorem EventTransition.enabled_eq_toTransition
    (t : EventTransition) (cfg : Config) (eventVar : Var) :
    t.enabled cfg eventVar = (t.toTransition eventVar).enabled cfg := by
  simp [enabled, toTransition, Transition.enabled, Guard.eval, Bool.and_assoc]

-- ============================================================================
-- Main Equivalence Theorem
-- ============================================================================

theorem eventSFC_iff_sfc (esfc : EventSFC) (cfg cfg' : Config) :
    EventSFCStep esfc cfg cfg' ↔ SFCStep esfc.toSFC cfg cfg' := by
  constructor
  · -- Forward: EventSFCStep → SFCStep
    intro h
    cases h with
    | fireTransition t cfg' hmem hen hpri hact hval =>
      apply SFCStep.fireTransition (t := t.toTransition esfc.eventVar)
      · -- Membership: t.toTransition ∈ esfc.toSFC.transitions
        simp only [EventSFC.toSFC]
        exact List.mem_map_of_mem hmem
      · -- Enabled
        rw [← EventTransition.enabled_eq_toTransition]; exact hen
      · -- Priority
        intro t' ht'mem ht'src ht'en
        simp only [EventSFC.toSFC] at ht'mem
        obtain ⟨et', het'mem, rfl⟩ := List.mem_map.mp ht'mem
        simp only [EventTransition.toTransition] at ht'src
        rw [← EventTransition.enabled_eq_toTransition] at ht'en
        exact hpri et' het'mem ht'src ht'en
      · -- Active steps
        simp only [fireTransition, EventTransition.toTransition] at hact ⊢
        exact hact
      · -- Valuation
        exact hval
  · -- Backward: SFCStep → EventSFCStep
    intro h
    cases h with
    | fireTransition t cfg' hmem hen hpri hact hval =>
      simp only [EventSFC.toSFC] at hmem
      obtain ⟨et, hetmem, heq⟩ := List.mem_map.mp hmem
      apply EventSFCStep.fireTransition (t := et)
      · exact hetmem
      · rw [EventTransition.enabled_eq_toTransition, heq]; exact hen
      · intro t' ht'mem ht'src ht'en
        have h1 : (t'.toTransition esfc.eventVar) ∈ esfc.toSFC.transitions := by
          simp only [EventSFC.toSFC]
          exact List.mem_map_of_mem ht'mem
        have h2 : (t'.toTransition esfc.eventVar).sources = t.sources := by
          simp only [EventTransition.toTransition, ht'src, ← heq]
        have h3 : (t'.toTransition esfc.eventVar).enabled cfg = true := by
          rw [← EventTransition.enabled_eq_toTransition]; exact ht'en
        have h4 := hpri _ h1 h2 h3
        rw [← heq] at h4
        simp only [EventTransition.toTransition] at h4
        exact h4
      · rw [← heq] at hact
        simp only [EventTransition.toTransition, fireTransition] at hact
        exact hact
      · exact hval

-- ============================================================================
-- EventSFCBisimulation
-- ============================================================================

structure EventSFCBisimulation (S : Type) where
  esfc : EventSFC
  toId : S → StepId
  step : S → Valuation → S → Prop
  forward : ∀ s s' v, step s v s' →
    EventSFCStep esfc ⟨[toId s], v⟩ ⟨[toId s'], v⟩
  backward : ∀ s v cfg',
    EventSFCStep esfc ⟨[toId s], v⟩ cfg' →
    ∃ s', cfg'.active = [toId s'] ∧ cfg'.valuation = v ∧ step s v s'

-- ============================================================================
-- Derived: EventSFCBisimulation → SFCBisimulation
-- ============================================================================

def EventSFCBisimulation.toSFCBisimulation (eb : EventSFCBisimulation S) :
    SFCBisimulation S where
  sfc := eb.esfc.toSFC
  toId := eb.toId
  step := eb.step
  forward := fun s s' v h =>
    (eventSFC_iff_sfc eb.esfc ⟨[eb.toId s], v⟩ ⟨[eb.toId s'], v⟩).mp (eb.forward s s' v h)
  backward := fun s v cfg' h =>
    eb.backward s v cfg' ((eventSFC_iff_sfc eb.esfc ⟨[eb.toId s], v⟩ cfg').mpr h)
