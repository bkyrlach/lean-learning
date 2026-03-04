import Std.Data.HashMap
open Std

set_option linter.unusedVariables false

inductive Value where
| int (n : Nat)
| str (s : String)
| map (data : List (String × Value))
deriving BEq, Repr

-- namespace Value

-- mutual

-- -- decidable equality for lists of pairs
-- private def decEqList : (xs ys : List (String × Value)) → Decidable (xs = ys)
-- | [],      []      => isTrue rfl
-- | [],      _       => isFalse (by intro h; cases h)
-- | _ ,      []      => isFalse (by intro h; cases h)
-- | x::xs,   y::ys   =>
--   match decEqPair x y, decEqList xs ys with
--   | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
--   | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
--   | _,          isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

-- -- decidable equality for Value
-- private def decEqValue : (x y : Value) → Decidable (x = y)
-- | .int n, .int m =>
--   match decEq n m with
--   | isTrue h  => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
-- | .str s, .str t =>
--   match decEq s t with
--   | isTrue h  => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
-- | .map xs, .map ys =>
--   match decEqList xs ys with
--   | isTrue h  => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
-- | .int _, .str _ | .int _, .map _
-- | .str _, .int _ | .str _, .map _
-- | .map _, .int _ | .map _, .str _ => isFalse (by intro h; cases h)

-- -- decidable equality for pairs
-- private def decEqPair : (x y : String × Value) → Decidable (x = y)
-- | ⟨k1,v1⟩, ⟨k2,v2⟩ =>
--   match decEq k1 k2, decEqValue v1 v2 with
--   | isTrue hk,  isTrue hv  => isTrue (by cases hk; cases hv; rfl)
--   | isFalse hk, _          => isFalse (by intro h; cases h; exact hk rfl)
--   | _,          isFalse hv => isFalse (by intro h; cases h; exact hv rfl)

-- end

-- end Value

-- instance : DecidableEq Value := Value.decEqValue

abbrev Γ := List (String × Value)

axiom Γeq_dec : ∀ (g g₁ : Γ), (g == g₁) = true ↔ g = g₁

def Γ.keys (env : Γ) : List String := env.map Prod.fst

abbrev Δ := List (Γ × Int)

abbrev Φ : List (Γ × Int) := []

inductive WatchPartState (pname : String) (env : Γ) (st : Δ) (out_st : Δ) (out : Δ) where
| nothing : WatchPartState pname env st out_st out

def valid_env (e : Γ) : Prop := (e.map Prod.fst).Nodup
def valid_delta (d : Δ) : Prop := (d.map Prod.fst).Nodup

theorem valid_delta_valid_tail : ∀ h t, valid_delta (h::t) → valid_delta t := by
  intro h t Hvalid_cons
  simp [valid_delta]
  simp [valid_delta] at Hvalid_cons
  have Hright := And.right Hvalid_cons
  exact Hright

def Δ.keys (d : Δ) : List Γ := d.map Prod.fst

def Δ.get? (d : Δ) (k : Γ) : Option Int :=
  (d.find? λ p ↦ p.fst == k).map Prod.snd

def Δ.equals (d d₁ : Δ) : Prop :=
  valid_delta d →
  valid_delta d₁ →
  ∀ k v, k ∈ d.keys ∧ d.get? k = some v ↔
         k ∈ d₁.keys ∧ d₁.get? k = some v

infixl:64 " === " => Δ.equals

def Δ.erase (d : Δ) (k : Γ) : Δ :=
  match d with
  | h::t => if (h.fst == k) then t else h::(Δ.erase t k)
  | [] => []

theorem erase_not_in : ∀ d e, valid_delta d → valid_env e → e ∉ (Δ.erase d e).keys := by
  intro d e Hd_valid He_valid Hcontra
  unfold Δ.erase at Hcontra
  induction d with
  | nil =>
    simp at Hcontra
    simp [Δ.keys] at Hcontra
  | cons h t Ihd =>
    by_cases He_eq : h.fst == e
    · simp at Hcontra
      rw [He_eq] at Hcontra
      simp at Hcontra
      simp at Ihd
      have thing := valid_delta_valid_tail h t Hd_valid
      have thing₁ := Ihd thing
      -- 1) pull out “head not in tail” from Nodup on keys of (h :: t)
      have nodup_keys : List.Nodup ((h :: t).map Prod.fst) := by
        simpa [valid_delta] using Hd_valid

      have h_not_in_tail : h.fst ∉ (t.map Prod.fst) :=
        (List.nodup_cons.mp (by simpa [List.map_cons] using nodup_keys)).1

      have hfst_eq_e : h.fst = e := (Γeq_dec h.fst e).mp He_eq

      -- 3) use Hcontra and rewrite with that equality to get membership of h.fst
      have h_in_tail : h.fst ∈ (t.map Prod.fst) := by
        have : e ∈ (t.map Prod.fst) := by simpa [Δ.keys] using Hcontra
        simpa [hfst_eq_e] using this

      -- 4) contradiction
      exact h_not_in_tail h_in_tail
    · sorry

def Δ.update (d : Δ) (k : Γ) (v : Int) : Δ :=
  match d with
  | h::t => if (h.fst == k) then (h.fst,v)::t else h::(Δ.update t k v)
  | [] => []

def Δ.insert (d : Δ) (k : Γ) (v : Int) : Δ :=
  let is_update := (d.find? (λ p ↦ p.fst == k)).isSome
  if is_update then Δ.update d k v else (k,v)::d

def Δ.getD (d : Δ) (k : Γ) (v : Int) :=
  ((d.find? λ p ↦ p.fst == k).map Prod.snd).getD v

def insertNZ (m : Δ) (k : Γ) (v : Int) : Δ :=
  if v = 0 then m.erase k else m.insert k v

theorem insertNZ_erase_valid : ∀ (d : Δ) (e : Γ), valid_delta d → valid_env e → e ∉ (insertNZ d e 0).keys := by
  intro d e Hd_isvalid He_isvalid Hcontra
  simp [insertNZ] at Hcontra
  induction d with
  | nil =>
    simp [Δ.erase] at Hcontra
    contradiction
  | cons h t Ihd =>
    have Hvalid_tail := valid_delta_valid_tail h t Hd_isvalid
    have He_in := Ihd Hvalid_tail
    simp [Δ.erase] at Hcontra
    by_cases Heq : h.fst == e
    · rw [Heq] at Hcontra
      simp at Hcontra
      sorry
    --have Hfalse := He_in Hcontra
    sorry

def dec_multi (a : Δ) (k : Γ) : Δ :=
  match a.get? k with
  | some n =>
      let n' := n - 1
      insertNZ a k n'
  | none => a

def Γ.get? (env : Γ) (k : String) : Option (String × Value) :=
  env.find? (fun p => p.fst == k)

theorem pair_in {α β : Type} : forall (a : α) (b : β) (xs : List (α × β)), (a,b) ∈ xs → a ∈ xs.map Prod.fst := by
  intro a b xs Hpair_in
  apply List.mem_map.mpr
  exists (a, b)

theorem Γ.get?_not_in : ∀ env k, valid_env env → k ∉ env.keys → env.get? k = none := by
  intro env k His_valid Hk_not_in
  simp [Γ.get?]
  intro a b Hin Hnot
  simp [Γ.keys] at Hk_not_in
  have Hcontra := Hk_not_in b
  rw [Hnot] at Hin
  have answer := Hcontra Hin
  exact answer

def diff_one (d d₁ : Δ) (acc : Δ) (e : Γ) : Δ :=
  let old := d.getD e 0
  let new := d₁.getD e 0
  acc.insert e (new - old)

def diff_multi (d d₁ : Δ) : Δ :=
  let combined_keys := d.keys ++ d₁.keys
  combined_keys.foldl (diff_one d d₁) Φ

def watch_prop_step (key : String) (st : Δ) (env : Γ) : Δ × Δ :=
  let st₁ := st.keys.foldl dec_multi st
  let newState :=
    match env.get? key with
    | some p => insertNZ st₁ [p] (st₁.getD [p] 0 + 1)
    | none   => st₁
  let delta := diff_multi st newState
  (newState, delta)

inductive watch_prop_stepP : String -> Δ -> Γ -> (Δ × Δ) -> Prop where
  | intro : forall key (st : Δ) st₁ newState delta (env : Γ),
    st₁ = (st.keys.foldl dec_multi st) ->
    (newState = match env.get? key with
    | some p => insertNZ st₁ [p] (st₁.getD [p] 0 + 1)
    | none   => st₁) ->
    delta = diff_multi st newState ->
    watch_prop_stepP key st env (newState, delta)

def env0 : Γ := [("bar", Value.int 3)]
def env1 : Γ := [("bar", Value.int 3), ("foo", Value.str "bar")]

#eval
  let (s1, d1) := watch_prop_step "foo" Φ env0
  let (s2, d2) := watch_prop_step "foo" s1 env1
  let (s3, d3) := watch_prop_step "foo" s2 env1
  (d1, d2, d3)

def mergeΓ : Γ → Γ → Option Γ
| acc, []        => some acc
| acc, (k,v)::t  =>
  match acc.find? (λ p => p.fst == k) with
  | some (_, v') => if v' == v then mergeΓ acc t else none
  | none         => mergeΓ ((k,v)::acc) t

def cart2 (L R : Δ) : Δ :=
  L.foldl (λ acc p ↦
    let envL := p.fst
    let cL := p.snd
    R.foldl (λ acc₁ p₁ =>
      let envR := p₁.fst
      let cR := p₁.snd
      match mergeΓ envL envR with
      | some env => insertNZ acc₁ env (acc₁.getD env 0 + cL * cR)
      | none     => acc₁
    ) acc
  ) Φ

def one : Δ := insertNZ Φ [] 1

def applyDelta (d d₁ : Δ) : Δ :=
  d₁.foldl (λ acc p ↦
    let k := p.fst
    let dv := p.snd
    let nv := acc.getD k 0 + dv
    insertNZ acc k nv
  ) d

infixl:65 " ⊞ " => applyDelta

theorem applyDelta_valid : ∀ d d₁, valid_delta d → valid_delta d₁ → valid_delta (d ⊞ d₁) := by
  intro d d1 Hd_valid Hd₁_valid
  simp [applyDelta, valid_delta]
  sorry

theorem applyDelta_empty_right : ∀ d, valid_delta d → applyDelta d [] === d := by
  intro d Hvalid
  simp [applyDelta]
  simp [Δ.equals]

theorem applyDelta_assoc : ∀ d d₁ d₂, valid_delta d → valid_delta d₁ → valid_delta d₂ → (d ⊞ d₁) ⊞ d₂ === d ⊞ (d₁ ⊞ d₂) := by
  intro d d₁ d₂ Hd_valid Hd₁_valid Hd₂_valid
  simp [Δ.equals]
  sorry

def product_step (state : Array Δ) (update : Nat × Δ) : Array Δ × Δ :=
  let i := update.fst
  let dᵢ := update.snd
  let others := state.eraseIdx! i
  let prod_others := others.foldl cart2 one
  let Δout := cart2 prod_others dᵢ
  let Li' := state[i]! ⊞ dᵢ
  let state' := state.set! i Li'
  (state', Δout)

def init_prod_st : Array Δ := [Φ, Φ].toArray

#eval
  let (w₁s₁, w₁d₁) := watch_prop_step "foo" Φ env1
  let (w₂s₁, w₂d₁) := watch_prop_step "bar" Φ env1
  let (p₁s₁, p₁d₁) := product_step init_prod_st (0, w₁d₁)
  let (p₁s₂, p₁d₂) := product_step p₁s₁ (1, w₂d₁)
  (p₁s₁, p₁d₁, p₁s₂, p₁d₂)

def subscribe_across_edges_step (state : Array Δ) (update : Nat × Δ) : Array Δ × Δ :=
  let i  := update.fst
  let dᵢ := update.snd
  -- Update leg i with its delta
  let Li'    := state[i]! ⊞ dᵢ
  let state' := state.set! i Li'
  -- For a sum across legs, the output delta equals the leg's delta
  (state', dᵢ)

/-- Helper: make a single row (env) with count 1 -/
def row (pairs : List (String × Value)) : Δ :=
  insertNZ Φ pairs 1

/-- Example data -/
def aRow  : Δ := row [("a.foo", Value.str "A1")]
def bRow1 : Δ := row [("b.bar", Value.int 10), ("b.baz", Value.str "X")]
def bRow2 : Δ := row [("b.bar", Value.int 20), ("b.baz", Value.str "Y")]

/-- Sum the two `b` rows (union) -/
def bRows : Δ := (Φ ⊞ bRow1) ⊞ bRow2

#eval
  let init := init_prod_st                          -- #[Φ, Φ]
  let (s1, outA) := product_step init (0, aRow)     -- apply A’s delta
  let (s2, outB) := product_step s1   (1, bRows)    -- then B’s delta
  -- outB is the emitted result rows for the whole pattern
  (outA, outB, cart2 aRow bRows)

/-- helper: one `b` branch = Product(Watch b.bar, Watch b.baz) over a single env -/
def run_b_branch (envB : Γ) : Δ :=
  let (sb, db_bar) := watch_prop_step "bar" Φ envB
  let (sz, db_baz) := watch_prop_step "baz" Φ envB
  let (ps1, out1) := product_step init_prod_st (0, db_bar)
  let (ps2, out2) := product_step ps1          (1, db_baz)
  out2

/-- sample environments: one `a`, two `b`s -/
def envA  : Γ := [("foo", Value.str "foo1")]
def envB1 : Γ := [("bar", Value.int 10), ("baz", Value.str "x")]
def envB2 : Γ := [("bar", Value.int 20), ("baz", Value.str "y")]

--Now run the full tree in streaming order
#eval
  -- Watch a.foo
  let (sa, da) := watch_prop_step "foo" Φ envA

  -- SubscribeAcrossEdge over two b branches (arriving one after the other)
  let b1 := run_b_branch envB1
  let b2 := run_b_branch envB2
  let sub0 := #[Φ]
  let (sub1, d_sub1) := subscribe_across_edges_step sub0 (0, b1)  -- first b arrives
  let (sub2, d_sub2) := subscribe_across_edges_step sub1 (0, b2)  -- second b arrives

  -- Top-level Product( Watch a.foo , SubscribeAcrossEdge(...) )
  let (tp1, out_row1) := product_step init_prod_st (1, d_sub1)    -- first b row emitted
  let (tp2, out_row2) := product_step tp1          (0, da)       -- load a’s delta
  let (tp3, out_row3) := product_step tp2          (1, d_sub2)    -- second b row emitted

  -- Expect two outputs, each a merged env: [("foo","foo1"), ("bar",..), ("baz",..)]
  (out_row2, out_row3)
