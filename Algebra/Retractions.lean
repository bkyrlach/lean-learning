import Mathlib.Data.Set.Basic
open Set        -- pulls the notations into scope

#check ({1} : Set Nat)      -- singleton works
#check (∅  : Set α)         -- empty set notation
#check (· ∈ ·)              -- membership




inductive Op
| add     : Nat → Op
| retract : Nat → Op
deriving Repr, DecidableEq

abbrev Trace := List Op                      -- oldest first, as before

inductive Step : Op -> Set Nat -> Set Nat → Prop
| add     {a s}         : Step (Op.add a)     s            (insert a s)
| retract {a s} (h : a ∈ s) :
                        Step (Op.retract a)  s            (Set.diff s {a})

inductive Exec : Trace → Set Nat → Set Nat → Prop
| nil  {s}                                   : Exec []          s s
| cons {op tr s₀ s₁ s₂}
        (h₁ : Step op s₀ s₁)
        (h₂ : Exec tr s₁ s₂)                : Exec (op :: tr)  s₀ s₂


def eval (tr : Trace) : Set Nat → Set Nat → Prop := Exec tr
def finalSet (tr : Trace) : Set Nat :=
  by
    classical
    by_cases h : ∃ s, Exec tr (∅ : Set Nat) s
    · exact Classical.choose h
    · exact ∅

lemma exec_det {tr s s₁ s₂}
    (h₁ : Exec tr s s₁) (h₂ : Exec tr s s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | nil =>
      cases h₂; rfl
  | cons hstep₁ hexec₁ ih =>
      cases h₂ with
      | cons hstep₂ hexec₂ =>
          cases hstep₁ <;> cases hstep₂ <;> sorry

inductive WellFormed : Trace → Set Nat → Prop
| nil  {s}                       : WellFormed [] s
| add  {a tr s}
       (wf : WellFormed tr (insert a s))     : WellFormed (Op.add a :: tr) s
| retract {a tr s}
       (mem : a ∈ s)
       (wf  : WellFormed tr (Set.diff s {a}))     : WellFormed (Op.retract a :: tr) s

lemma wf_exec_exists {tr s} (wf : WellFormed tr s) :
    ∃ s', Exec tr s s' := by
    sorry


def ex : Trace := [Op.add 1, Op.add 2, Op.retract 1, Op.add 3]

open Properties in
#eval
  match (wf_exec_exists (by
        -- a trivial WF proof for `ex` starting from ∅
        repeat
          first
          | apply WellFormed.add
          | apply WellFormed.retract
            <;> simp [Set.mem_insert, Set.mem_singleton]
          | apply WellFormed.nil)) with
  | ⟨s, _⟩ => s.toList   -- prints `[2, 3]`
-- => [2, 3]

end RetractionTrace



/-

abbrev QueryPartId := Nat

inductive WatchPropState : Type
| no_state
| prop_state (r : Row)

inductive OperatorState : Type
| WatchState : WatchPropState → OperatorState

inductive UnitState : Type
| no_state

inductive InstancedOperator : Type
| unit_plan_instance (id : QueryPartId) (state : UnitState)
| watch_prop_instance (id : QueryPartId) (pname : String) (state : WatchPropState) : InstancedOperator
-- future: | productInstance ...

inductive Value : Type :=
| IntValue : Nat → Value
| StringValue : String → Value

abbrev Binding := String × Value

structure Row where
  data : List Binding
  no_dup_key : (data.map (λ p ↦ p.fst)).Nodup

abbrev Results := List Row

inductive EdgeDirection : Type :=
| Incomming
| Outgoing
| Bidirectional

structure HalfEdge where
  other : Nat
  type : String
  direction : EdgeDirection

structure Node where
  id : Nat
  data : Row
  local_query : List InstancedOperator
  labels : List String
  label_is_set : labels.Nodup
  edges : List HalfEdge

inductive QueryPlan : Type
| UnitPlan
| ProductPlan (xs : List QueryPlan)
| WatchProp (name : String)
| SubscribeAcrossEdgePlan (type : String) (direction : EdgeDirection) (subplan : QueryPlan)

structure Graph where
  node_id : Nat
  query_part_id : Nat
  nodes : List Node
  plans : List QueryPlan
  no_dup_nodes : (nodes.map (λ n ↦ n.id)).Nodup

inductive NodeEvent : Type :=
| NoEvent
| SetProperty (s : String) (v : Value)
| InstallPlan (plan : QueryPlan)

inductive GraphEvent : Type :=
| CreateNodeFresh
| InstallPlan (planId : Nat) (nodeId : Nat)

inductive Delta where
| add : QueryPartId → Row → Delta
| del : QueryPartId → Row → Delta

def mk_row (key : String) (val : Value) : Row :=
{
  data := [(key, val)],
  no_dup_key := by simp
}

-- inductive EvalWatchProp : Node → NodeEvent → QueryPartId → String → WatchPropState → WatchPropState → List Delta → Prop
-- | watch_noop : ∀ n qpid pname st,
--     EvalWatchProp n NodeEvent.NoEvent qpid pname st st []
-- | watch_assert : ∀ n qpid pname v, EvalWatchProp n (NodeEvent.SetProperty pname v) qpid pname WatchPropState.no_state (WatchPropState.prop_state (mk_row pname v)) [Delta.add qpid (mk_row pname v)]
-- | watch_no_dup_assert : ∀ n qpid pname v, EvalWatchProp n (NodeEvent.SetProperty pname v) qpid pname (WatchPropState.prop_state (mk_row pname v)) (WatchPropState.prop_state (mk_row pname v)) []
-- | watch_assert_change : ∀ n qpid pname v v', v ≠ v' → EvalWatchProp n (NodeEvent.SetProperty pname v') qpid pname (WatchPropState.prop_state (mk_row pname v)) (WatchPropState.prop_state (mk_row pname v')) [Delta.add qpid (mk_row pname v')]
-- | watch_retract ...
-- | watch_reassert ...

-- inductive Eval : Node → NodeEvent → InstancedOperator → InstancedOperator → List Delta → Prop
-- | eval_watch : ∀ n e qpid pname st st' d,
--     EvalWatchProp n e qpid pname st st' d →
--     Eval n e (InstancedOperator.watch_prop_instance qpid pname st) (InstancedOperator.watch_prop_instance qpid pname st') d

def replace_node (target : Node) (nodes : List Node) : List Node :=
  match nodes with
  | h::t => if (h.id = target.id) then target::t else h::(replace_node target t)
  | [] => []

def ids (xs : List Node) : List Nat := xs.map (·.id)

@[simp] theorem ids_nil : ids [] = [] := rfl
@[simp] theorem ids_cons (h : Node) (t : List Node) : ids (h :: t) = h.id :: ids t := by
  simp [ids]

theorem ids_replace_node (t : Node) :
  ∀ xs, ids (replace_node t xs) = ids xs
| []      => by simp [replace_node, ids]
| (h::xs) => by
  by_cases hEq : h.id = t.id
  · simp [replace_node, ids, hEq]
  · have ih := ids_replace_node t xs
    simp [replace_node, ids, hEq, ih]
    simp [ids] at ih
    exact ih

theorem replace_nodes_preserves_nodup
  (t : Node) (xs : List Node)
  (H : (ids xs).Nodup) :
  (ids (replace_node t xs)).Nodup :=
by simpa [ids_replace_node t xs] using H

@[simp] theorem replace_node_nil (t : Node) : replace_node t [] = [] := rfl

@[simp] theorem replace_node_cons_hit (t h : Node) (xs : List Node)
  (hEq : h.id = t.id) :
  replace_node t (h :: xs) = t :: xs := by simp [replace_node, hEq]

@[simp] theorem replace_node_cons_miss (t h : Node) (xs : List Node)
  (hNe : h.id ≠ t.id) :
  replace_node t (h :: xs) = h :: replace_node t xs := by simp [replace_node, hNe]

def Graph.replaceNode (g : Graph) (n' : Node) : Graph :=
  let nodes' := replace_node n' g.nodes
  { g with nodes := nodes', no_dup_nodes := replace_nodes_preserves_nodup n' g.nodes g.no_dup_nodes }

-- def Graph.insertFresh (g : Graph) (n : Node)
--   (fresh : n.id ∉ g.nodes.map (·.id)) : Graph :=
-- { g with
--   nodes := n :: g.nodes,
--   no_dup_nodes := nodup_ids_cons fresh g.no_dup_nodes }

-- @[simp] theorem insertFresh_nodes (g n h) :
--   (g.insertFresh n h).nodes = n :: g.nodes := rfl

inductive EvalInstallPlan : Graph → Node → QueryPlan → Graph → Node → Prop
| eval_install_unit_plan :
    ∀ (g g₁ : Graph) (n n₁ : Node) (next_id : QueryPartId),
    next_id = g.query_part_id + 1 →
    n₁ = { n₁ with local_query := [InstancedOperator.unit_plan_instance next_id UnitState.no_state] } →
    g₁ = { (g.replaceNode n₁) with query_part_id := next_id } →
    EvalInstallPlan g n QueryPlan.UnitPlan g₁ n₁
| eval_install_watch_plan :
    ∀ g g₁ n n₁ next_id pname,
    next_id = g.query_part_id + 1 →
    n₁ = { n₁ with local_query := [InstancedOperator.watch_prop_instance next_id pname WatchPropState.no_state] } →
    g₁ = { (g.replaceNode n₁) with query_part_id := next_id} →
    EvalInstallPlan g n (QueryPlan.WatchProp pname) g₁ n₁

inductive EvalEventNode : Graph → Node → NodeEvent → Graph → Node → List Delta → Prop
| eval_install_plan : ∀ n g n₁ g₁ qp, EvalInstallPlan g n qp g₁ n₁ → EvalEventNode g n (NodeEvent.InstallPlan qp) g₁ n₁ []


inductive EvalStepGraph : Graph → GraphEvent → Graph → List Delta → Prop
| eval_create_node_no_plans :
    ∀ g g₁ n next_id,
      next_id = g.node_id + 1 →
      next_id ∉ g.nodes.map (λ n ↦ n.id) →
      n = {
        id := next_id
        data := []

      } →
      g.plans = [] →
      g₁ = {
        node_id := next_id
        query_part_id := g.query_part_id
        plans := g.plans
        nodes := n::g.nodes
        no_dup_nodes := sorry
      } →
      EvalStepGraph g GraphEvent.CreateNodeFresh g₁ []
| eval_create_node_with_plans :
    ∀ g g₁ g₂ n next_id plans h t,
      next_id = g.node_id + 1 →
      next_id ∉ g.nodes.map (λ n ↦ n.id) →
      plans = h::t →
      g.plans = plans →
      g₁ = {
        node_id := next_id
        query_part_id := sorry
        plans := g.plans
        nodes := n::g.nodes
        no_dup_nodes := sorry
      } →
      EvalStepGraph.eval_install_plan g₁ g₂ h
| eval_install_plan :
    ∀ g g₁ qp plan_idx n n₁ node_id,
      n.id = node_id →
      plan_idx < g.plans.length →
      n ∈ g.nodes →
      EvalEventNode g n (NodeEvent.InstallPlan qp) g₁ n₁ [] →
      n₁ ∈ g₁.nodes →
      EvalStepGraph g (GraphEvent.InstallPlan plan_idx node_id) g₁ []

inductive EvalStream : Graph → List GraphEvent → Graph → List (List Delta) → Prop
| eval_no_events : ∀ g g₁, EvalStream g [] g₁ []
| eval_events : ∀ g g₁ g₂ deltas rest h t, EvalStepGraph g h g₁ deltas → EvalStream g₁ t g₂ rest → EvalStream g (h::t) g₂ (deltas::rest)

def empty_props : Row :=
{
  data := []
  no_dup_key := by decide
}

def example_node : Node :=
{
  id := 1
  data := empty_props
  local_query := []
  labels := ["Foo"]
  label_is_set := by decide
  edges := []
}

def example_node₁ : Node :=
{
  id := 1
  data := empty_props
  local_query := [
    InstancedOperator.unit_plan_instance 1 UnitState.no_state
  ]
  labels := ["Foo"]
  label_is_set := by decide
  edges := []
}

def example_graph : Graph :=
{
  node_id := 1
  query_part_id := 0
  nodes := [example_node]
  plans := [QueryPlan.UnitPlan]
  no_dup_nodes := by decide
}

def example_graph₁ : Graph :=
{
  node_id := 1,
  query_part_id := 1,  -- incremented from 0 → 1
  nodes := [example_node₁],  -- local_query updated with unit_plan_instance
  plans := [QueryPlan.UnitPlan],
  no_dup_nodes := by decide
}

def install_unit_plan : GraphEvent :=
  GraphEvent.InstallPlan 0 1

def graph_events_example : List GraphEvent :=
  [install_unit_plan]

def install_unit_plan_proof : EvalStream example_graph graph_events_example example_graph₁ [[]] := by
  apply EvalStream.eval_events example_graph example_graph₁ example_graph₁ [] [] install_unit_plan []
  · apply EvalStepGraph.eval_install_plan example_graph example_graph₁ QueryPlan.UnitPlan 0 example_node example_node₁ 1
    · simp [example_node]
    · simp [example_graph]
    · simp [example_graph]
    · apply EvalEventNode.eval_install_plan example_node example_graph example_node₁ example_graph₁ QueryPlan.UnitPlan
      · apply EvalInstallPlan.eval_install_unit_plan example_graph example_graph₁ example_node example_node₁  1
        · simp [example_graph]
        · simp [example_node₁, example_node]
        · simp [example_graph, example_graph₁, Graph.replaceNode, example_node₁, example_node]
    · simp [example_graph₁]
  · exact EvalStream.eval_no_events example_graph₁ example_graph₁

def sample_props : Row :=
{
  data := [
    ("foo", Value.StringValue "bar")
  ]
  no_dup_key := by decide
}

def example_node₂ : Node :=
{
  id := 1
  data := sample_props
  local_query := []
  labels := ["Foo"]
  label_is_set := by decide
  edges := []
}

def example_node₃ : Node :=
{
  id := 1
  data := sample_props
  local_query := [
    InstancedOperator.watch_prop_instance 1 "foo" WatchPropState.no_state
  ]
  labels := ["Foo"]
  label_is_set := by decide
  edges := []
}

def example_graph₂ : Graph :=
{
  node_id := 1
  query_part_id := 0
  nodes := [example_node₂]
  plans := [QueryPlan.WatchProp "foo"]
  no_dup_nodes := by decide
}

def example_graph₃ : Graph :=
{
  node_id := 1,
  query_part_id := 1,
  nodes := [example_node₃],
  plans := [QueryPlan.WatchProp "foo"],
  no_dup_nodes := by decide
}

def install_watch_plan : GraphEvent :=
  GraphEvent.InstallPlan 0 1

def graph_events_example₁ : List GraphEvent :=
  [install_watch_plan]

def install_watch_plan_proof : EvalStream example_graph₂ graph_events_example₁ example_graph₃ [[]] := by
  apply EvalStream.eval_events example_graph₂ example_graph₃ example_graph₃ [] [] install_watch_plan []
  · apply EvalStepGraph.eval_install_plan example_graph₂ example_graph₃ (QueryPlan.WatchProp "foo") 0 example_node₂ example_node₃ 1
    · simp [example_node₂]
    · simp [example_graph₂]
    · simp [example_graph₂]
    · apply EvalEventNode.eval_install_plan example_node₂ example_graph₂ example_node₃ example_graph₃ (QueryPlan.WatchProp "foo")
      · apply EvalInstallPlan.eval_install_watch_plan example_graph₂ example_graph₃ example_node₂ example_node₃ 1 "foo"
        · simp [example_graph₂]
        · simp [example_node₃, example_node₂]
        · simp [example_graph₃, example_graph₂, example_node₃, Graph.replaceNode, example_node₂, Graph.replaceNode]
    · simp [example_graph₃]
  · exact EvalStream.eval_no_events example_graph₃ example_graph₃

def example_node₄ : Node :=
{
  id := 1
  data := empty_props
  local_query := []
  labels := []
  label_is_set := by decide
  edges := []
}

def example_graph₄ : Graph :=
{
  node_id := 0
  query_part_id := 0
  nodes := []
  plans := []
  no_dup_nodes := by decide
}

def example_graph₅ : Graph :=
{
  node_id := 1,
  query_part_id := 0,
  nodes := [example_node₄],
  plans := [],
  no_dup_nodes := by decide
}

def create_node : GraphEvent :=
  GraphEvent.CreateNodeFresh

def graph_events_example₂ : List GraphEvent :=
  [create_node]

def create_node_proof : EvalStream example_graph₄ graph_events_example₂ example_graph₅ [[]] := by
  apply EvalStream.eval_events example_graph₄ example_graph₅ example_graph₅ [] [] create_node []
  · apply EvalStepGraph.eval_create_node_no_plans example_graph₄ example_graph₅ example_node₄ 1
    · simp [example_graph₄]
    · simp [example_graph₄]
    · simp [example_graph₄]
    · simp [example_graph₅, example_graph₄]
  · exact EvalStream.eval_no_events example_graph₅ example_graph₅

--def create_node_installs_plans : EvalStream
 -/
