/-
  Entitlements Protocol: Inductive Operational Semantics ↔ SFC Bisimulation

  Formalizes the Scala `EntitlementsProtocol` (a Pekko actor-based license
  management state machine from thatdot/quine-plus) as a Sequential Function
  Chart. Proves bisimulation using the `SFCBisimulation` struct.

  ═══════════════════════════════════════════════════════════════════════════
  SEQUENTIAL FUNCTION CHART — Entitlements Protocol
  5 steps · 21 transitions · 6 message types · 4 condition variables
  ═══════════════════════════════════════════════════════════════════════════

  MESSAGES ("msg" variable)                 CONDITIONS (0=false, ≥1=true)
  ─────────────────────────                 ─────────────────────────────
    1 = ClusterAnchorLoaded                   shutdownOk : shutdown timer > 0
    2 = PersistenceFailure                    hasData    : persisted entitlements
    3 = EntitlementsReceived                  jwtValid   : JWT signature valid
    4 = LicenseServerContactError             graceOk    : grace period > 0
    5 = LicenseServerJwtInvalid
    6 = DecrementDurations

  ─── STATE TOPOLOGY ──────────────────────────────────────────────────────
  All flows shown. Self-loops (↺) annotated inside state boxes.
  Transition numbers (T1–T21) reference the table below.

                               ╔═════════════╗
                               ║  BOOT  (★)  ║  ★ = initial step
                               ╚══════╤══════╝
                              T1 ╱         ╲ T2
                          msg=1 ╱           ╲ msg=2
                               ╱             ╲
                              ▼               ▼
            ╔══════════════════════╗    ╔══════════════════════════════╗
            ║  CONTACTING 1ST TIME ║    ║                              ║
            ╚═══╤═══╤═══╤═════════╝    ║                              ║
                │   │   │              ║                              ║
           T3   │   │   │ T4,T6,T7    ║                              ║
        [msg=3  │   │   ╰──────────▶  ║                              ║
        ok≥1]   │   │                  ║       SHUTTING DOWN          ║
                │   │ T5               ║                              ║
                │   │[msg=4            ║    (terminal — no outgoing   ║
                │   │ d≥1,j≥1,ok≥1]   ║     transitions; absorbs     ║
                │   │                  ║     all further messages)     ║
                ▼   ▼                  ║                              ║
  ╔══════════════╗ ╔════════════════╗  ║                              ║
  ║  OPERATING   ║ ║ GRACE          ║  ║                              ║
  ║              ║ ║ OPERATING      ║  ║                              ║
  ║ self-loops:  ║ ║                ║  ║                              ║
  ║ ↺T8  msg=3  ║ ║ self-loops:    ║  ║    ▲  ▲  ▲  ▲  ▲  ▲  ▲     ║
  ║      ok≥1   ║ ║ ↺T17 msg=4    ║  ║    │  │  │  │  │  │  │     ║
  ║ ↺T13 msg=6  ║ ║       j≥1     ║  ║    │  │  │  │  │  │  │     ║
  ║      ok≥1   ║ ║ ↺T20 msg=6    ║  ║    │failure paths from     ║
  ║              ║ ║       g≥1,ok≥1║  ║    │ Boot(1), CF(3),       ║
  ╚══╤═══════╤══╝ ╚═╤══════════╤══╝  ║    │ Op(4), GO(4)          ║
     │       │      │          │      ║                              ║
     │       │      │          ╰───▶  ║  T9,T11,T12,T14 from Op    ║
     │       │      │                 ║  T16,T18,T19,T21 from GO   ║
     │       │      │ T15 [msg=3,ok≥1]║                              ║
     │       │      ╰─────────────╮   ╚══════════════════════════════╝
     │       │                    │
     │       │ T10 [msg=4,j≥1]   │
     │       ╰──────────╮        │
     │                   ▼       ▼
     │              ╔═══════╗ ╔═══════╗
     ╰──────────────╢ GO    ║ ║  Op   ║
       T10 grace    ╚═══════╝ ╚═══════╝
       entry             T15 recovery

       Op ──[msg=4,j≥1]──▶ GO    (grace entry)
       GO ──[msg=3,ok≥1]──▶ Op    (recovery)

  ─── COMPLETE TRANSITION TABLE ───────────────────────────────────────────

  FROM BOOT (2 transitions):
  ┌─────┬────────────────────────────────────────┬──────────────┬──────────────────┐
  │  #  │ Guard                                  │ Target       │ Meaning          │
  ├─────┼────────────────────────────────────────┼──────────────┼──────────────────┤
  │ T1  │ msg = 1                                │ CF           │ Anchor loaded    │
  │ T2  │ msg = 2                                │ SD           │ Persist failure  │
  └─────┴────────────────────────────────────────┴──────────────┴──────────────────┘

  FROM CONTACTING FIRST TIME (5 transitions):
  ┌─────┬────────────────────────────────────────┬──────────────┬──────────────────┐
  │  #  │ Guard                                  │ Target       │ Meaning          │
  ├─────┼────────────────────────────────────────┼──────────────┼──────────────────┤
  │ T3  │ msg=3 ∧ shutdownOk ≥ 1                │ Op           │ Licensed OK      │
  │ T4  │ msg=3 ∧ shutdownOk = 0                │ SD           │ Licensed, expired│
  │ T5  │ msg=4 ∧ hasData≥1 ∧ jwtValid≥1        │ GO           │ Server err,      │
  │     │        ∧ shutdownOk≥1                  │              │   enter grace    │
  │ T6  │ msg=4 ∧ (hasData=0 ∨ jwtValid=0       │ SD           │ Server err,      │
  │     │         ∨ shutdownOk=0)                │              │   no fallback    │
  │ T7  │ msg = 5                                │ SD           │ JWT invalid      │
  └─────┴────────────────────────────────────────┴──────────────┴──────────────────┘

  FROM OPERATING (7 transitions, 2 self-loops):
  ┌─────┬────────────────────────────────────────┬──────────────┬──────────────────┐
  │  #  │ Guard                                  │ Target       │ Meaning          │
  ├─────┼────────────────────────────────────────┼──────────────┼──────────────────┤
  │ T8  │ msg=3 ∧ shutdownOk ≥ 1                │ Op ↺         │ Checkin OK       │
  │ T9  │ msg=3 ∧ shutdownOk = 0                │ SD           │ Checkin, expired │
  │ T10 │ msg=4 ∧ jwtValid ≥ 1                  │ GO           │ Grace entry      │
  │ T11 │ msg=4 ∧ jwtValid = 0                  │ SD           │ Err, no JWT      │
  │ T12 │ msg = 5                                │ SD           │ JWT invalid      │
  │ T13 │ msg=6 ∧ shutdownOk ≥ 1                │ Op ↺         │ Timer tick OK    │
  │ T14 │ msg=6 ∧ shutdownOk = 0                │ SD           │ Timer expired    │
  └─────┴────────────────────────────────────────┴──────────────┴──────────────────┘

  FROM GRACE OPERATING (7 transitions, 2 self-loops):
  ┌─────┬────────────────────────────────────────┬──────────────┬──────────────────┐
  │  #  │ Guard                                  │ Target       │ Meaning          │
  ├─────┼────────────────────────────────────────┼──────────────┼──────────────────┤
  │ T15 │ msg=3 ∧ shutdownOk ≥ 1                │ Op           │ Recovery checkin │
  │ T16 │ msg=3 ∧ shutdownOk = 0                │ SD           │ Checkin, expired │
  │ T17 │ msg=4 ∧ jwtValid ≥ 1                  │ GO ↺         │ Still in grace   │
  │ T18 │ msg=4 ∧ jwtValid = 0                  │ SD           │ JWT revoked      │
  │ T19 │ msg = 5                                │ SD           │ JWT invalid      │
  │ T20 │ msg=6 ∧ graceOk≥1 ∧ shutdownOk≥1      │ GO ↺         │ Grace tick OK    │
  │ T21 │ msg=6 ∧ (graceOk=0 ∨ shutdownOk=0)    │ SD           │ Timer(s) expired │
  └─────┴────────────────────────────────────────┴──────────────┴──────────────────┘

  FROM SHUTTING DOWN: (no transitions — terminal absorbing state)

  ─── KEY FLOWS ───────────────────────────────────────────────────────────

  Happy path:     Boot ─T1→ CF ─T3→ Op ↺T8,T13  (licensed, periodic checkins)
  Grace entry:    Op ─T10→ GO                     (server unreachable, cached JWT)
  Grace survival: GO ↺T17,T20                     (still unreachable, timers OK)
  Recovery:       GO ─T15→ Op                     (server reachable again)
  Shutdown:       any ──→ SD                      (timer expired, JWT bad, or
                                                   persistence failure)

  Guards are mutually exclusive for each source state (given a fixed message
  number), so all transitions have priority 0 and no priority ordering is
  needed.
  ═══════════════════════════════════════════════════════════════════════════
-/
import SFC

-- ============================================================================
-- Inductive Small-Step Semantics for Entitlements Protocol
-- ============================================================================

inductive EntState where
  | Boot | ContactingFirstTime | Operating | GraceOperating | ShuttingDown
deriving DecidableEq, Repr

open EntState

def EntState.toId : EntState → StepId
  | Boot => "Boot"
  | ContactingFirstTime => "ContactingFirstTime"
  | Operating => "Operating"
  | GraceOperating => "GraceOperating"
  | ShuttingDown => "ShuttingDown"

-- Inference rules (21 transitions):
--
--   From Boot:
--     msg = 1                                    msg = 2
--   ──────────── (BootLoaded)                  ──────────── (BootPersistFail)
--   Boot → CF                                  Boot → SD
--
--   From ContactingFirstTime:
--     msg = 3, shutdownOk ≥ 1                  msg = 3, shutdownOk = 0
--   ────────────────────────── (CfEntOk)       ──────────────────────── (CfEntBad)
--   CF → Op                                    CF → SD
--
--     msg = 4, hasData ≥ 1, jwtValid ≥ 1, shutdownOk ≥ 1
--   ──────────────────────────────────────────────────────── (CfErrGrace)
--   CF → GO
--
--     msg = 4, hasData = 0 ∨ jwtValid = 0 ∨ shutdownOk = 0
--   ────────────────────────────────────────────────────────── (CfErrFail)
--   CF → SD
--
--     msg = 5
--   ────────── (CfJwtInvalid)
--   CF → SD
--
--   From Operating:
--     msg = 3, shutdownOk ≥ 1                  msg = 3, shutdownOk = 0
--   ────────────────────────── (OpCheckinOk)    ────────────────────────── (OpCheckinBad)
--   Op → Op  ↺                                 Op → SD
--
--     msg = 4, jwtValid ≥ 1                    msg = 4, jwtValid = 0
--   ──────────────────────── (OpErrGrace)       ──────────────────────── (OpErrFail)
--   Op → GO                                    Op → SD
--
--     msg = 5                                   msg = 6, shutdownOk ≥ 1
--   ────────── (OpJwtInvalid)                   ────────────────────────── (OpDecrOk)
--   Op → SD                                    Op → Op  ↺
--
--     msg = 6, shutdownOk = 0
--   ────────────────────────── (OpDecrBad)
--   Op → SD
--
--   From GraceOperating:
--     msg = 3, shutdownOk ≥ 1                  msg = 3, shutdownOk = 0
--   ────────────────────────── (GoCheckinOk)    ────────────────────────── (GoCheckinBad)
--   GO → Op  (recovery)                        GO → SD
--
--     msg = 4, jwtValid ≥ 1                    msg = 4, jwtValid = 0
--   ──────────────────────── (GoErrStay)        ──────────────────────── (GoErrFail)
--   GO → GO  ↺                                 GO → SD
--
--     msg = 5                                   msg = 6, graceOk ≥ 1, shutdownOk ≥ 1
--   ────────── (GoJwtInvalid)                   ──────────────────────────────────────── (GoDecrOk)
--   GO → SD                                    GO → GO  ↺
--
--     msg = 6, graceOk = 0 ∨ shutdownOk = 0
--   ──────────────────────────────────────────── (GoDecrBad)
--   GO → SD

inductive EntStep : EntState → Valuation → EntState → Prop where
  -- From Boot
  | bootLoaded      : ∀ v, v "msg" = 1 →
      EntStep Boot v ContactingFirstTime
  | bootPersistFail : ∀ v, v "msg" = 2 →
      EntStep Boot v ShuttingDown
  -- From ContactingFirstTime
  | cfEntitlementsOk  : ∀ v, v "msg" = 3 → v "shutdownOk" ≥ 1 →
      EntStep ContactingFirstTime v Operating
  | cfEntitlementsBad : ∀ v, v "msg" = 3 → v "shutdownOk" = 0 →
      EntStep ContactingFirstTime v ShuttingDown
  | cfContactErrGrace : ∀ v, v "msg" = 4 → v "hasData" ≥ 1 →
      v "jwtValid" ≥ 1 → v "shutdownOk" ≥ 1 →
      EntStep ContactingFirstTime v GraceOperating
  | cfContactErrFail  : ∀ v, v "msg" = 4 →
      (v "hasData" = 0 ∨ v "jwtValid" = 0 ∨ v "shutdownOk" = 0) →
      EntStep ContactingFirstTime v ShuttingDown
  | cfJwtInvalid      : ∀ v, v "msg" = 5 →
      EntStep ContactingFirstTime v ShuttingDown
  -- From Operating
  | opCheckinOk       : ∀ v, v "msg" = 3 → v "shutdownOk" ≥ 1 →
      EntStep Operating v Operating
  | opCheckinBad      : ∀ v, v "msg" = 3 → v "shutdownOk" = 0 →
      EntStep Operating v ShuttingDown
  | opContactErrGrace : ∀ v, v "msg" = 4 → v "jwtValid" ≥ 1 →
      EntStep Operating v GraceOperating
  | opContactErrFail  : ∀ v, v "msg" = 4 → v "jwtValid" = 0 →
      EntStep Operating v ShuttingDown
  | opJwtInvalid      : ∀ v, v "msg" = 5 →
      EntStep Operating v ShuttingDown
  | opDecrementOk     : ∀ v, v "msg" = 6 → v "shutdownOk" ≥ 1 →
      EntStep Operating v Operating
  | opDecrementBad    : ∀ v, v "msg" = 6 → v "shutdownOk" = 0 →
      EntStep Operating v ShuttingDown
  -- From GraceOperating
  | goCheckinOk       : ∀ v, v "msg" = 3 → v "shutdownOk" ≥ 1 →
      EntStep GraceOperating v Operating
  | goCheckinBad      : ∀ v, v "msg" = 3 → v "shutdownOk" = 0 →
      EntStep GraceOperating v ShuttingDown
  | goContactErrStay  : ∀ v, v "msg" = 4 → v "jwtValid" ≥ 1 →
      EntStep GraceOperating v GraceOperating
  | goContactErrFail  : ∀ v, v "msg" = 4 → v "jwtValid" = 0 →
      EntStep GraceOperating v ShuttingDown
  | goJwtInvalid      : ∀ v, v "msg" = 5 →
      EntStep GraceOperating v ShuttingDown
  | goDecrementOk     : ∀ v, v "msg" = 6 → v "graceOk" ≥ 1 →
      v "shutdownOk" ≥ 1 →
      EntStep GraceOperating v GraceOperating
  | goDecrementBad    : ∀ v, v "msg" = 6 →
      (v "graceOk" = 0 ∨ v "shutdownOk" = 0) →
      EntStep GraceOperating v ShuttingDown

-- ============================================================================
-- Properties of the Inductive Semantics
-- ============================================================================

theorem entStep_deterministic : ∀ s v s1 s2,
    EntStep s v s1 → EntStep s v s2 → s1 = s2 := by
  intro s v s1 s2 H1 H2
  cases H1 <;> cases H2 <;> first | rfl | omega | (rename_i h1 h2; rcases h1 with h | h | h <;> omega) | (rename_i h1 h2; rcases h2 with h | h | h <;> omega)

-- ============================================================================
-- SFC Definition
-- ============================================================================

def entitlementsSFC : SFC := {
  steps := [
    { id := "Boot", isInitial := true },
    { id := "ContactingFirstTime" },
    { id := "Operating" },
    { id := "GraceOperating" },
    { id := "ShuttingDown" }
  ],
  transitions := [
    -- From Boot (2)
    { sources := ["Boot"], targets := ["ContactingFirstTime"],
      guard := .Eq "msg" 1 },
    { sources := ["Boot"], targets := ["ShuttingDown"],
      guard := .Eq "msg" 2 },
    -- From ContactingFirstTime (5)
    { sources := ["ContactingFirstTime"], targets := ["Operating"],
      guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) },
    { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) },
    { sources := ["ContactingFirstTime"], targets := ["GraceOperating"],
      guard := .And (.Eq "msg" 4)
        (.And (.Ge "hasData" 1) (.And (.Ge "jwtValid" 1) (.Ge "shutdownOk" 1))) },
    { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 4)
        (.Or (.Eq "hasData" 0) (.Or (.Eq "jwtValid" 0) (.Eq "shutdownOk" 0))) },
    { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
      guard := .Eq "msg" 5 },
    -- From Operating (7)
    { sources := ["Operating"], targets := ["Operating"],
      guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) },
    { sources := ["Operating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) },
    { sources := ["Operating"], targets := ["GraceOperating"],
      guard := .And (.Eq "msg" 4) (.Ge "jwtValid" 1) },
    { sources := ["Operating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 4) (.Eq "jwtValid" 0) },
    { sources := ["Operating"], targets := ["ShuttingDown"],
      guard := .Eq "msg" 5 },
    { sources := ["Operating"], targets := ["Operating"],
      guard := .And (.Eq "msg" 6) (.Ge "shutdownOk" 1) },
    { sources := ["Operating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 6) (.Eq "shutdownOk" 0) },
    -- From GraceOperating (7)
    { sources := ["GraceOperating"], targets := ["Operating"],
      guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) },
    { sources := ["GraceOperating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) },
    { sources := ["GraceOperating"], targets := ["GraceOperating"],
      guard := .And (.Eq "msg" 4) (.Ge "jwtValid" 1) },
    { sources := ["GraceOperating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 4) (.Eq "jwtValid" 0) },
    { sources := ["GraceOperating"], targets := ["ShuttingDown"],
      guard := .Eq "msg" 5 },
    { sources := ["GraceOperating"], targets := ["GraceOperating"],
      guard := .And (.Eq "msg" 6)
        (.And (.Ge "graceOk" 1) (.Ge "shutdownOk" 1)) },
    { sources := ["GraceOperating"], targets := ["ShuttingDown"],
      guard := .And (.Eq "msg" 6)
        (.Or (.Eq "graceOk" 0) (.Eq "shutdownOk" 0)) }
  ]
}

-- ============================================================================
-- Configuration Correspondence
-- ============================================================================

def toEntConfig (s : EntState) (v : Valuation) : Config :=
  { active := [s.toId], valuation := v }

-- ============================================================================
-- Forward Direction: EntStep → SFCStep
-- ============================================================================

theorem ent_to_sfc (s s' : EntState) (v : Valuation) :
    EntStep s v s' →
    SFCStep entitlementsSFC (toEntConfig s v) (toEntConfig s' v) := by
  intro H
  cases H with
  -- Boot transitions
  | bootLoaded v Hmsg =>
    apply SFCStep.fireTransition
      (t := { sources := ["Boot"], targets := ["ContactingFirstTime"],
              guard := .Eq "msg" 1 })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | bootPersistFail v Hmsg =>
    apply SFCStep.fireTransition
      (t := { sources := ["Boot"], targets := ["ShuttingDown"],
              guard := .Eq "msg" 2 })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  -- ContactingFirstTime transitions
  | cfEntitlementsOk v Hmsg Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["ContactingFirstTime"], targets := ["Operating"],
              guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | cfEntitlementsBad v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | cfContactErrGrace v Hmsg Hdata Hjwt Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["ContactingFirstTime"], targets := ["GraceOperating"],
              guard := .And (.Eq "msg" 4)
                (.And (.Ge "hasData" 1) (.And (.Ge "jwtValid" 1) (.Ge "shutdownOk" 1))) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | cfContactErrFail v Hmsg Hfail =>
    apply SFCStep.fireTransition
      (t := { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 4)
                (.Or (.Eq "hasData" 0) (.Or (.Eq "jwtValid" 0) (.Eq "shutdownOk" 0))) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]
      rcases Hfail with h | h | h <;> omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | cfJwtInvalid v Hmsg =>
    apply SFCStep.fireTransition
      (t := { sources := ["ContactingFirstTime"], targets := ["ShuttingDown"],
              guard := .Eq "msg" 5 })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  -- Operating transitions
  | opCheckinOk v Hmsg Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["Operating"],
              guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opCheckinBad v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opContactErrGrace v Hmsg Hjwt =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["GraceOperating"],
              guard := .And (.Eq "msg" 4) (.Ge "jwtValid" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opContactErrFail v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 4) (.Eq "jwtValid" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opJwtInvalid v Hmsg =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["ShuttingDown"],
              guard := .Eq "msg" 5 })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opDecrementOk v Hmsg Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["Operating"],
              guard := .And (.Eq "msg" 6) (.Ge "shutdownOk" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | opDecrementBad v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["Operating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 6) (.Eq "shutdownOk" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  -- GraceOperating transitions
  | goCheckinOk v Hmsg Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["Operating"],
              guard := .And (.Eq "msg" 3) (.Ge "shutdownOk" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goCheckinBad v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 3) (.Eq "shutdownOk" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goContactErrStay v Hmsg Hjwt =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["GraceOperating"],
              guard := .And (.Eq "msg" 4) (.Ge "jwtValid" 1) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goContactErrFail v Hmsg Hbad =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 4) (.Eq "jwtValid" 0) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goJwtInvalid v Hmsg =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["ShuttingDown"],
              guard := .Eq "msg" 5 })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goDecrementOk v Hmsg Hgrace Hok =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["GraceOperating"],
              guard := .And (.Eq "msg" 6)
                (.And (.Ge "graceOk" 1) (.Ge "shutdownOk" 1)) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]; omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl
  | goDecrementBad v Hmsg Hfail =>
    apply SFCStep.fireTransition
      (t := { sources := ["GraceOperating"], targets := ["ShuttingDown"],
              guard := .And (.Eq "msg" 6)
                (.Or (.Eq "graceOk" 0) (.Eq "shutdownOk" 0)) })
    · simp [entitlementsSFC]
    · simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId]
      rcases Hfail with h | h <;> omega
    · intro _ _ _ _; simp
    · simp [fireTransition, activate, deactivate, toEntConfig, EntState.toId]
    · rfl

-- ============================================================================
-- Backward Direction: SFCStep → EntStep
-- ============================================================================

theorem sfc_to_ent (s : EntState) (v : Valuation) (cfg' : Config) :
    SFCStep entitlementsSFC (toEntConfig s v) cfg' →
    ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ EntStep s v s' := by
  intro H
  cases H with
  | fireTransition =>
    rename_i t Hin Hen Hpri Hact Hval
    simp [entitlementsSFC] at Hin
    rcases Hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (
      simp [Transition.enabled, allActive, isActive, Guard.eval,
            toEntConfig, EntState.toId] at Hen
      cases s <;> simp [toEntConfig, EntState.toId] at Hen Hact ⊢
      simp [fireTransition, activate, deactivate] at Hact
      simp [toEntConfig] at Hval
    )
    -- Each remaining goal: ∃ s', cfg'.active = [s'.toId] ∧ cfg'.valuation = v ∧ EntStep ...
    -- Provide explicit target state witness; omega handles Nat arithmetic
    all_goals first
      | (refine ⟨ContactingFirstTime, ?_, Hval, EntStep.bootLoaded _ (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.bootPersistFail _ (by omega)⟩
         simp; exact Hact)
      | (refine ⟨Operating, ?_, Hval, EntStep.cfEntitlementsOk _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.cfEntitlementsBad _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨GraceOperating, ?_, Hval, EntStep.cfContactErrGrace _ (by omega) (by omega) (by omega) (by omega)⟩
         simp; exact Hact)
      | (obtain ⟨_, hdisj⟩ := Hen
         refine ⟨ShuttingDown, ?_, Hval, EntStep.cfContactErrFail _ (by omega) ?_⟩
         · simp; exact Hact
         · rcases hdisj with h | h | h <;> simp_all <;> omega)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.cfJwtInvalid _ (by omega)⟩
         simp; exact Hact)
      | (refine ⟨Operating, ?_, Hval, EntStep.opCheckinOk _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.opCheckinBad _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨GraceOperating, ?_, Hval, EntStep.opContactErrGrace _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.opContactErrFail _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.opJwtInvalid _ (by omega)⟩
         simp; exact Hact)
      | (refine ⟨Operating, ?_, Hval, EntStep.opDecrementOk _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.opDecrementBad _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨Operating, ?_, Hval, EntStep.goCheckinOk _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.goCheckinBad _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨GraceOperating, ?_, Hval, EntStep.goContactErrStay _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.goContactErrFail _ (by omega) (by omega)⟩
         simp; exact Hact)
      | (refine ⟨ShuttingDown, ?_, Hval, EntStep.goJwtInvalid _ (by omega)⟩
         simp; exact Hact)
      | (refine ⟨GraceOperating, ?_, Hval, EntStep.goDecrementOk _ (by omega) (by omega) (by omega)⟩
         simp; exact Hact)
      | (obtain ⟨_, hdisj⟩ := Hen
         refine ⟨ShuttingDown, ?_, Hval, EntStep.goDecrementBad _ (by omega) ?_⟩
         · simp; exact Hact
         · rcases hdisj with h | h <;> simp_all <;> omega)

-- ============================================================================
-- Bisimulation Instance
-- ============================================================================

def entitlementsBisim : SFCBisimulation EntState where
  sfc := entitlementsSFC
  toId := EntState.toId
  step := EntStep
  forward := ent_to_sfc
  backward := sfc_to_ent
