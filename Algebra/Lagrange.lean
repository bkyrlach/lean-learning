def Function.Injective {α β : Type} (f : α → β) : Prop :=
  ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

structure Group (α : Type) where
  e : α
  mult : α → α → α
  inv : α → α
  id_left : ∀ (a : α), mult e a = a
  id_right : ∀ (a : α), mult a e = a
  assoc : ∀ (a b c : α), mult (mult a b) c = mult a (mult b c)
  left_inv : ∀ (a : α), mult (inv a) a = e
  right_inv : ∀ (a : α), mult a (inv a) = e

class Finite (α : Type) where
  elems : List α
  complete : ∀ x : α, x ∈ elems
  nodup : elems.Nodup

def Finite.card (α : Type) [F : Finite α] : Nat := F.elems.length

-- Subgroup as a relationship between two groups
-- H is a subgroup of G if there's an injective homomorphism from H into G
structure Subgroup {α : Type} {β : Type} (H : Group α) (G : Group β) where
  embed : α → β
  embed_injective : Function.Injective embed
  embed_e : embed H.e = G.e
  embed_mult : ∀ a b, embed (H.mult a b) = G.mult (embed a) (embed b)
  embed_inv : ∀ a, embed (H.inv a) = G.inv (embed a)

----------------------------------------------------------------
-- Subgroup via carrier set
----------------------------------------------------------------

-- A subgroup of G defined as a subset closed under group operations
structure SubgroupC {β : Type} (G : Group β) where
  carrier : β → Prop
  has_e : carrier G.e
  closed_mult : ∀ a b, carrier a → carrier b → carrier (G.mult a b)
  closed_inv : ∀ a, carrier a → carrier (G.inv a)

----------------------------------------------------------------
-- Equivalence of the two subgroup definitions
----------------------------------------------------------------

-- Direction 1: Subgroup (injective homomorphism) → SubgroupC (carrier set)
-- The image of the embedding forms a carrier set
def Subgroup.toSubgroupC {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) : SubgroupC G where
  carrier := fun b => ∃ a, sub.embed a = b
  has_e := ⟨H.e, sub.embed_e⟩
  closed_mult := fun a b ⟨ha, hha⟩ ⟨hb, hhb⟩ =>
    ⟨H.mult ha hb, by rw [sub.embed_mult, hha, hhb]⟩
  closed_inv := fun a ⟨ha, hha⟩ =>
    ⟨H.inv ha, by rw [sub.embed_inv, hha]⟩

-- Direction 2: SubgroupC (carrier set) → construct a Group on the subtype
def SubgroupC.toGroup {β : Type} {G : Group β} (S : SubgroupC G) :
    Group {x : β // S.carrier x} where
  e := ⟨G.e, S.has_e⟩
  mult := fun a b => ⟨G.mult a.val b.val, S.closed_mult _ _ a.property b.property⟩
  inv := fun a => ⟨G.inv a.val, S.closed_inv _ a.property⟩
  id_left := fun a => Subtype.ext (G.id_left a.val)
  id_right := fun a => Subtype.ext (G.id_right a.val)
  assoc := fun a b c => Subtype.ext (G.assoc a.val b.val c.val)
  left_inv := fun a => Subtype.ext (G.left_inv a.val)
  right_inv := fun a => Subtype.ext (G.right_inv a.val)

-- Direction 2: The inclusion Subtype.val is an injective homomorphism
def SubgroupC.toSubgroup {β : Type} {G : Group β} (S : SubgroupC G) :
    Subgroup S.toGroup G where
  embed := Subtype.val
  embed_injective := fun _ _ h => Subtype.ext h
  embed_e := rfl
  embed_mult := fun _ _ => rfl
  embed_inv := fun _ => rfl

theorem SubgroupC.ext {β : Type} {G : Group β} {S T : SubgroupC G}
    (h : S.carrier = T.carrier) : S = T := by
  cases S; cases T; cases h; rfl

-- The round-trip SubgroupC → Subgroup → SubgroupC is the identity
@[simp]
theorem SubgroupC.roundtrip {β : Type} {G : Group β} (S : SubgroupC G) :
    S.toSubgroup.toSubgroupC = S := by
  apply SubgroupC.ext
  funext b
  exact propext ⟨fun ⟨⟨_, hx⟩, rfl⟩ => hx, fun hb => ⟨⟨b, hb⟩, rfl⟩⟩

----------------------------------------------------------------
-- Interoperability: membership, simp lemmas, transport
----------------------------------------------------------------

-- Membership: write `b ∈ S` for SubgroupC
instance SubgroupC.instMembership {β : Type} {G : Group β} :
    Membership β (SubgroupC G) where
  mem S b := S.carrier b

-- Membership: write `b ∈ sub` for Subgroup (b is in the image)
instance Subgroup.instMembership {α β : Type} {H : Group α} {G : Group β} :
    Membership β (Subgroup H G) where
  mem sub b := ∃ a, sub.embed a = b

-- Simp: membership in SubgroupC is just the carrier
@[simp]
theorem SubgroupC.mem_carrier {β : Type} {G : Group β} (S : SubgroupC G) (b : β) :
    b ∈ S ↔ S.carrier b :=
  Iff.rfl

-- Simp: membership in Subgroup is the image
@[simp]
theorem Subgroup.mem_def {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) (b : β) :
    b ∈ sub ↔ ∃ a, sub.embed a = b :=
  Iff.rfl

-- Simp: carrier of toSubgroupC is membership in the original Subgroup
@[simp]
theorem Subgroup.toSubgroupC_carrier {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) (b : β) :
    sub.toSubgroupC.carrier b ↔ b ∈ sub :=
  Iff.rfl

-- Simp: membership is preserved by conversion
@[simp]
theorem SubgroupC.mem_toSubgroup {β : Type} {G : Group β}
    (S : SubgroupC G) (b : β) :
    b ∈ S.toSubgroup ↔ b ∈ S :=
  ⟨fun ⟨⟨_, hx⟩, rfl⟩ => hx, fun hb => ⟨⟨b, hb⟩, rfl⟩⟩

-- Transport: prove a membership property for SubgroupC, use it for Subgroup
theorem Subgroup.mem_e {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) : G.e ∈ sub :=
  ⟨H.e, sub.embed_e⟩

theorem Subgroup.mem_mult {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) {a b : β} (ha : a ∈ sub) (hb : b ∈ sub) :
    G.mult a b ∈ sub := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨H.mult a' b', sub.embed_mult a' b'⟩

theorem Subgroup.mem_inv {α β : Type} {H : Group α} {G : Group β}
    (sub : Subgroup H G) {a : β} (ha : a ∈ sub) :
    G.inv a ∈ sub := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨H.inv a', sub.embed_inv a'⟩

----------------------------------------------------------------
-- Quotient of subgroup representations ≅ SubgroupC
--
-- This is NOT a quotient group (G/N for normal N). A quotient group
-- is an algebraic construction on cosets internal to G.
-- Here we quotient the *space of subgroup presentations* by
-- "same image" — a type-theoretic quotient over how you present
-- a subgroup, showing SubgroupC is the canonical representative.
----------------------------------------------------------------

-- A subgroup representation: a type, a group on it, and an embedding into G
def SubgroupRep {β : Type} (G : Group β) :=
  Σ (α : Type) (H : Group α), Subgroup H G

-- The image of a representation in G
def SubgroupRep.image {β : Type} {G : Group β} (r : SubgroupRep G) : β → Prop :=
  fun b => ∃ a, r.2.2.embed a = b

-- Two representations are equivalent iff they pick out the same subset of G
def SubgroupRep.SameImage {β : Type} {G : Group β} (r s : SubgroupRep G) : Prop :=
  ∀ b, r.image b ↔ s.image b

theorem SubgroupRep.SameImage.refl {β : Type} {G : Group β} (r : SubgroupRep G) :
    SameImage r r :=
  fun _ => Iff.rfl

theorem SubgroupRep.SameImage.symm {β : Type} {G : Group β} {r s : SubgroupRep G}
    (h : SameImage r s) : SameImage s r :=
  fun b => (h b).symm

theorem SubgroupRep.SameImage.trans {β : Type} {G : Group β} {r s t : SubgroupRep G}
    (h₁ : SameImage r s) (h₂ : SameImage s t) : SameImage r t :=
  fun b => (h₁ b).trans (h₂ b)

instance SubgroupRep.setoid {β : Type} (G : Group β) : Setoid (SubgroupRep G) where
  r := SameImage
  iseqv := ⟨SameImage.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

-- The quotient: subgroup representations up to same image
def SubgroupQuot {β : Type} (G : Group β) := Quotient (SubgroupRep.setoid G)

-- Forward map: SubgroupC → SubgroupQuot (embed as the canonical subtype rep)
def SubgroupC.toQuot {β : Type} {G : Group β} (S : SubgroupC G) : SubgroupQuot G :=
  Quotient.mk' ⟨{x : β // S.carrier x}, S.toGroup, S.toSubgroup⟩

-- Backward map: SubgroupQuot → SubgroupC (extract the image as a carrier set)
-- First show toSubgroupC respects the equivalence relation
theorem Subgroup.toSubgroupC_respects {β : Type} {G : Group β}
    (r s : SubgroupRep G) (h : SubgroupRep.SameImage r s) :
    r.2.2.toSubgroupC = s.2.2.toSubgroupC := by
  apply SubgroupC.ext
  funext b
  exact propext (h b)

def SubgroupQuot.toSubgroupC {β : Type} {G : Group β} (q : SubgroupQuot G) : SubgroupC G :=
  Quotient.lift (fun r : SubgroupRep G => r.2.2.toSubgroupC)
    (fun r s h => Subgroup.toSubgroupC_respects r s h) q

-- Round-trip 1: SubgroupC → Quot → SubgroupC = id
theorem SubgroupQuot.left_inv {β : Type} {G : Group β} (S : SubgroupC G) :
    S.toQuot.toSubgroupC = S := by
  show S.toSubgroup.toSubgroupC = S
  exact SubgroupC.roundtrip S

-- Round-trip 2: Quot → SubgroupC → Quot = id
theorem SubgroupQuot.right_inv {β : Type} {G : Group β} (q : SubgroupQuot G) :
    q.toSubgroupC.toQuot = q := by
  induction q using Quotient.ind
  case a r =>
    apply Quotient.sound
    intro b
    show (∃ (a : {x // ∃ a', r.2.2.embed a' = x}), a.val = b) ↔ (∃ a, r.2.2.embed a = b)
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
      exact ⟨a, rfl⟩
    · intro ⟨a, ha⟩
      exact ⟨⟨r.2.2.embed a, ⟨a, rfl⟩⟩, ha⟩

-- The two subgroup definitions pick out the same subsets of G.
--
-- Given a group G and a property P on elements of G, the following are equivalent:
--
-- (Left) There exists a carrier-set subgroup whose carrier is P.
--   A "carrier" is just a predicate saying which elements of G belong to
--   the subgroup. It must contain the identity, and be closed under
--   multiplication and inverses.
--
-- (Right) There exists some type α, a group H on α, and an injective
--   homomorphism (called "embed") from H into G, such that the image
--   of embed is exactly P.
--   "embed" is a function α → β that preserves the group structure:
--     - embed(H.e) = G.e
--     - embed(H.mult a b) = G.mult (embed a) (embed b)
--     - embed(H.inv a) = G.inv (embed a)
--   "Injective" means distinct inputs give distinct outputs.
--   "Image of embed is P" means: b satisfies P iff b = embed(a) for some a.
--
-- In other words: a subset of G is a subgroup (closed under operations)
-- if and only if it arises as the image of an injective homomorphism
-- from some external group.
theorem subgroupC_iff_subgroup {β : Type} (G : Group β) (P : β → Prop) :
    (∃ S : SubgroupC G, S.carrier = P) ↔
    (∃ (α : Type) (H : Group α) (sub : Subgroup H G), ∀ b, (∃ a, sub.embed a = b) ↔ P b) := by
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨_, S.toGroup, S.toSubgroup, fun b =>
      ⟨fun ⟨⟨_, hx⟩, rfl⟩ => hx, fun hb => ⟨⟨b, hb⟩, rfl⟩⟩⟩
  · intro ⟨α, H, sub, himage⟩
    refine ⟨sub.toSubgroupC, funext fun b => propext ?_⟩
    exact ⟨fun ⟨a, ha⟩ => (himage b).mp ⟨a, ha⟩, fun hb => (himage b).mpr hb⟩

-- Lagrange's theorem: |G| is divisible by |H| when H is a subgroup of G
theorem lagrange :
  ∀ (α β : Type) [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    (H : Group α) (G : Group β),
    Subgroup H G → Finite.card β % Finite.card α = 0 := by
      intro α β _ _ _ _ H G ⟨embed, _, _, _, _⟩
      sorry

----------------------------------------------------------------
-- Cosets
----------------------------------------------------------------

-- Right coset Hg = { embed(h) * g | h ∈ H }
def right_coset {α β : Type} [Finite α]
    (H : Group α) (G : Group β) (sub : Subgroup H G) (g : β) : List β :=
  Finite.elems.map (λ a ↦ G.mult (sub.embed a) g)

-- Left coset gH = { g * embed(h) | h ∈ H }
def left_coset {α β : Type} [Finite α]
    (H : Group α) (G : Group β) (sub : Subgroup H G) (g : β) : List β :=
  sorry

----------------------------------------------------------------
-- Coset Theorems (needed for Lagrange)
----------------------------------------------------------------

-- Every coset has the same size as H
theorem right_coset_card {α β : Type} [DecidableEq β] [Finite α] [Finite β]
    (H : Group α) (G : Group β) (sub : Subgroup H G) (g : β) :
    (right_coset H G sub g).length = Finite.card α := by
  unfold right_coset
  unfold Finite.card
  exact List.length_map _

-- The coset by identity is the embedded subgroup
theorem right_coset_e {α β : Type} [DecidableEq β] [Finite α]
    (H : Group α) (G : Group β) (sub : Subgroup H G) :
    right_coset H G sub G.e = Finite.elems.map sub.embed := by
  unfold right_coset
  congr 1
  funext a
  exact G.id_right _


-- An element is in its own coset
theorem mem_right_coset_self {α β : Type} [DecidableEq β] [Finite α]
    (H : Group α) (G : Group β) (sub : Subgroup H G) (g : β) :
    g ∈ right_coset H G sub g := by
  sorry

-- Two cosets are either equal or disjoint
theorem right_coset_eq_or_disjoint {α β : Type} [DecidableEq β] [Finite α] [Finite β]
    (H : Group α) (G : Group β) (sub : Subgroup H G) (g₁ g₂ : β) :
    right_coset H G sub g₁ = right_coset H G sub g₂ ∨
    ∀ x, x ∈ right_coset H G sub g₁ → x ∉ right_coset H G sub g₂ := by
  sorry

----------------------------------------------------------------
-- S3: The symmetric group on 3 elements
----------------------------------------------------------------

inductive S3 where
  | e | r | r2 | s | sr | sr2
  deriving DecidableEq

def S3.all : List S3 := [.e, .r, .r2, .s, .sr, .sr2]

instance : Finite S3 where
  elems := S3.all
  complete := by
    intro x
    unfold S3.all
    cases x <;> simp
  nodup := by decide

def S3.mult : S3 → S3 → S3
-- identity cases
| .e, x => x
| x, .e => x
-- rotations: r³ = e
| .r, .r => .r2
| .r, .r2 => .e
| .r2, .r => .e
| .r2, .r2 => .r
-- reflection squared: s² = e
| .s, .s => .e
-- rotation × reflection
| .r, .s => .sr2
| .r2, .s => .sr
| .r, .sr => .s
| .r2, .sr => .sr2
| .r, .sr2 => .sr
| .r2, .sr2 => .s
-- reflection × rotation
| .s, .r => .sr
| .s, .r2 => .sr2
| .s, .sr => .r
| .s, .sr2 => .r2
-- mixed reflections: (sr)² = e, (sr2)² = e
| .sr, .sr => .e
| .sr2, .sr2 => .e
-- sr × sr2 and vice versa
| .sr, .sr2 => .r
| .sr2, .sr => .r2
-- sr × others
| .sr, .s => .r2
| .sr, .r => .sr2
| .sr, .r2 => .s
-- sr2 × others
| .sr2, .s => .r
| .sr2, .r => .s
| .sr2, .r2 => .sr

def S3.inv : S3 → S3
| .e => .e
| .r => .r2
| .r2 => .r
| .s => .s
| .sr => .sr
| .sr2 => .sr2

def s3_group : Group S3 := {
  e := .e
  mult := .mult
  inv := .inv
  id_left := by intro a; cases a <;> rfl
  id_right := by intro a; cases a <;> rfl
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl
}

----------------------------------------------------------------
-- Rots: The rotation subgroup as a subtype of S3
----------------------------------------------------------------

def S3.rotsList : List S3 := [.e, .r, .r2]

-- Rots is the type of S3 elements that are in the rotations list
def Rots := { x : S3 // x ∈ S3.rotsList }

instance : DecidableEq Rots := fun a b =>
  decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

-- Helper to construct Rots elements
def Rots.e : Rots := ⟨.e, by decide⟩
def Rots.r : Rots := ⟨.r, by decide⟩
def Rots.r2 : Rots := ⟨.r2, by decide⟩

instance : Finite Rots where
  elems := [Rots.e, Rots.r, Rots.r2]
  complete := fun ⟨x, hx⟩ => by
    unfold S3.rotsList at hx
    cases x with
    | e => decide +revert
    | r => decide +revert
    | r2 => decide +revert
    | s => simp at hx
    | sr => simp at hx
    | sr2 => simp at hx
  nodup := by decide

-- Prove that rotations are closed under S3.mult
theorem rots_closed_mult (a b : Rots) : S3.mult a.val b.val ∈ S3.rotsList := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  unfold S3.rotsList at ha hb ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb ⊢
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

-- Prove that rotations are closed under S3.inv
theorem rots_closed_inv (a : Rots) : S3.inv a.val ∈ S3.rotsList := by
  obtain ⟨a, ha⟩ := a
  unfold S3.rotsList at ha ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  rcases ha with rfl | rfl | rfl <;> decide

def Rots.mult (a b : Rots) : Rots := ⟨S3.mult a.val b.val, rots_closed_mult a b⟩
def Rots.inv (a : Rots) : Rots := ⟨S3.inv a.val, rots_closed_inv a⟩

def rots_group : Group Rots := {
  e := Rots.e
  mult := Rots.mult
  inv := Rots.inv
  id_left := by
    intro a
    simp only [Rots.mult, Rots.e]
    apply Subtype.ext
    simp only [S3.mult]
  id_right := by
    intro a
    simp only [Rots.mult, Rots.e]
    apply Subtype.ext
    obtain ⟨a, ha⟩ := a
    unfold S3.rotsList at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> rfl
  assoc := by
    intro a b c
    apply Subtype.ext
    simp only [Rots.mult]
    exact s3_group.assoc a.val b.val c.val
  left_inv := by
    intro a
    apply Subtype.ext
    simp only [Rots.inv, Rots.mult, Rots.e]
    exact s3_group.left_inv a.val
  right_inv := by
    intro a
    apply Subtype.ext
    simp only [Rots.inv, Rots.mult, Rots.e]
    exact s3_group.right_inv a.val
}

----------------------------------------------------------------
-- Rots is a Subgroup of S3
----------------------------------------------------------------

def rots_subgroup_of_s3 : Subgroup rots_group s3_group := {
  embed := Subtype.val
  embed_injective := fun _ _ h => Subtype.ext h
  embed_e := rfl
  embed_mult := fun _ _ => rfl
  embed_inv := fun _ => rfl
}

----------------------------------------------------------------
-- Lagrange for S3/Rots (concrete instance)
----------------------------------------------------------------

theorem lagrange_s3_rots :
  Finite.card S3 % Finite.card Rots = 0 := by decide
