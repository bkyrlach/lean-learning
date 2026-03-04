theorem modus_ponens_fr : forall (P Q), ¬(P /\ Q) -> ¬P ∨ ¬Q := by
  intro P
  intro Q
  intro Hnot
  unfold Not at Hnot
  unfold Not
  by_cases hP : P
  .
    right
    intro Hq
    apply Hnot
    constructor
    exact hP
    exact Hq
  .
    left
    exact hP
