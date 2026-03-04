import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Erase

/-- Property keys are strings --/
abbrev PropertyKey := String

/-- Property values are strings --/
abbrev PropertyValue := String

/-- Edge types are strings --/
abbrev EdgeType := String

/-- Node IDs are natural numbers --/
abbrev NodeId := Nat

/-- A journal event represents a single operation on a node --/
inductive JournalEvent where
  | setProperty : PropertyKey → PropertyValue → JournalEvent
  | removeProperty : PropertyKey → JournalEvent
  | addEdge : EdgeType → NodeId → JournalEvent
  | removeEdge : EdgeType → NodeId → JournalEvent

/-- The state of a node derived from applying journal events --/
structure NodeState where
  properties : Finset PropertyKey
  edges : Finset (EdgeType × NodeId)

/-- Apply a single event to a node state --/
def applyEvent : NodeState → JournalEvent → NodeState
  | s, .setProperty k _ => { s with properties := insert k s.properties }
  | s, .removeProperty k => { s with properties := s.properties.erase k }
  | s, .addEdge t n => { s with edges := insert (t, n) s.edges }
  | s, .removeEdge t n => { s with edges := s.edges.erase (t, n) }

/-- A node state is empty when it has no properties and no edges --/
def NodeState.isEmpty (s : NodeState) : Prop :=
  s.properties = ∅ ∧ s.edges = ∅

/-- Apply a list of events to get the current state --/
def currentState (history : List JournalEvent) : NodeState :=
  history.foldl applyEvent ⟨∅, ∅⟩

/-- A history is non-interesting if the resulting node state is empty --/
def hasNonInterestingHistory (history : List JournalEvent) : Prop :=
  (currentState history).isEmpty
