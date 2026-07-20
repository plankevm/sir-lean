import NestedEvmYul.ObservableTriple

/-!
# `Behaves` — the for-all-programs behavior predicate, nested side

Nested analog of the flat `BytecodeLayer.Hoare.Behaves`
(EVM/BytecodeLayer/Hoare/Behaves.lean:45), closing parity-verdict gap #1
(docs/planning/exp004-parity-verdict-2026-07-19.md §4). The flat predicate
quantifies over every entry `CallParams` running a given `code` and constrains
the named `Outcome` of `messageCall`; here the world is `NestedWorld` (the 19
positional `Θ` arguments, SharedObservable.lean), the driver is the fuel-free
`runΘ`, and the conclusion is stated at the `SharedObservable` altitude
(`observe_nested`) — the toolchain-neutral layer both engines project into.

## Design decisions (recorded)

* **Observable-altitude definition.** Flat's `post` ranges over its engine's
  named `Outcome`; a verbatim nested mirror would range over
  `Except ExecutionException ThetaResult`. We instead state `post` over
  `SharedObservable`, because that is the nested side's canonical comparison
  surface (convergence report §3) and every already-closed conclusion lemma
  (`completedWith`, `ΘRuns_completedWith`, `doNothing_completedWith`) already
  lives there. The predicate is otherwise verbatim: ∀-world, code slot pinned,
  `pre` first.

* **Gas/fuel is a precondition — with a permanent asymmetry vs flat.** Flat's
  doctrine ("gas is a precondition, kept first-class") carries the gas floor
  inside `pre`. The nested analog of that residue is the T2 cofinal pivot's
  `k ≤ seedFuel w` offset side condition (`ΘRuns.runΘ_complete'`,
  ThetaRuns.lean — the keystone that would remove it is UNPROVEN: refuted
  pre-2026-07-20 while CREATE absorbed inner `OutOfFuel`, reopened but not
  proven by the vendored patch of that date, see the post-mortem there). So
  the producers below take a per-world bounded-offset cofinal family as part
  of their pre-side obligations: the fuel envelope enters via `pre`,
  honestly, and cannot be discharged once-and-for-all. Flat has
  unconditional adequacy at this spot (verdict §4 item 6); the nested side
  does not today (a proved keystone would change that; none exists).

* **Flat parity EXCEEDED on the consumer side.** The flat `Behaves` has ZERO
  consuming lemmas repo-wide (verified by grep: nothing takes a
  `Behaves … → …` hypothesis). This file ships `Behaves.storage_out` — a
  theorem CONSUMING a `Behaves` hypothesis to produce a concrete semantic
  fact — plus a fired instance at an explicit world literal
  (`doNothingWorld_storage_zero`), so the nested predicate is demonstrably
  non-decorative from day one.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-- **`Behaves pre cd post`** (precondition first) — nested mirror of the flat
`BytecodeLayer.Hoare.Behaves`: for **every** world `w` whose called code is
`cd` and which satisfies `pre`, the shared observable of the seeded fuel-free
run satisfies `post`. The fuel/gas envelope lives inside `pre` (see the module
docstring: the `k ≤ seedFuel w` residue of the cofinal pivot surfaces on the
producer rules' pre-side obligations). -/
def Behaves (pre : NestedWorld → Prop) (cd : ByteArray)
    (post : SharedObservable → Prop) : Prop :=
  ∀ w : NestedWorld, w.c = .Code cd → pre w → post (observe_nested (runΘ w))

/-! ## Pure-logic rules (mirror the `XiTriple.conseq`/`.conj` shapes)

Consumers only in the trivial sense — the semantics is never touched. -/

/-- Consequence rule: strengthen the precondition, weaken the postcondition.
PROVED — pure logic. -/
theorem Behaves.conseq {pre pre' : NestedWorld → Prop} {cd : ByteArray}
    {post post' : SharedObservable → Prop}
    (hpre : ∀ w, pre' w → pre w) (hpost : ∀ obs, post obs → post' obs)
    (h : Behaves pre cd post) : Behaves pre' cd post' :=
  fun w hc hp => hpost _ (h w hc (hpre w hp))

/-- Conjunction rule. PROVED — pure logic (the SAME run feeds both halves; no
fuel reconciliation, exactly as in `ThetaTriple.conj`). -/
theorem Behaves.conj {pre pre' : NestedWorld → Prop} {cd : ByteArray}
    {post post' : SharedObservable → Prop}
    (h : Behaves pre cd post) (h' : Behaves pre' cd post') :
    Behaves (fun w => pre w ∧ pre' w) cd (fun obs => post obs ∧ post' obs) :=
  fun w hc hp => ⟨h w hc hp.1, h' w hc hp.2⟩

/-! ## Producer rules over the ∀-fuel veneer -/

/-- **Producer over the cofinal veneer.** If every pre-world running `cd` has a
cofinal success family at some offset `k ≤ seedFuel w` (the honest per-world
fuel-envelope obligation — this is where the T2 pivot's side condition enters,
as a `pre`-side clause) whose post-map reads `v` at `(addr, key)`, then the
program `Behaves` with `completedWith` at that cell.

PROVED — pure plumbing through `ΘRuns_completedWith`
(ObservableTriple.lean). -/
theorem behaves_of_cofinal (pre : NestedWorld → Prop) (cd : ByteArray)
    (addr key v : Nat)
    (h : ∀ w, w.c = .Code cd → pre w →
      ∃ (k : ℕ) (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (g' : UInt256) (A' : Substate) (o : ByteArray),
        k ≤ seedFuel w ∧
        (∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts
          w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p
          w.v w.v' w.d w.e w.H w.w = .ok (cA, σ', g', A', true, o)) ∧
        (match σ'.toList.find? (fun p => p.1.val = addr) with
         | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
         | none => 0) = v) :
    Behaves pre cd (fun obs => completedWith obs addr key v) := by
  intro w hc hpre
  obtain ⟨k, cA, σ', g', A', o, hk, hruns, hread⟩ := h w hc hpre
  exact ΘRuns_completedWith w addr key v k hk hruns hread

/-- **Triple-to-`Behaves` rule** — the substantive producer: a procedure spec
`ThetaTriple P (.Code cd) Q` lifts to an all-worlds `Behaves` conclusion. The
nested analog of flat's "the external-call rule supplies a gas floor inside
`pre`": the three obligations are (1) `pre` entails the triple's precondition
at the entry state, (2) every pre-world produces a bounded-offset **cofinal
success family** — the honest producer obligation, since triples only consume
success runs and the fuel envelope is not dischargeable once-and-for-all
(`k ≤ seedFuel w` is permanent, see module docstring) — and (3) `Q` pins the
storage read.

PROVED — routes through `ΘRuns.runΘ_complete'` (veneer adequacy) and
`completedWith_of_thetaTriple` (triple-to-observable plumbing). -/
theorem behaves_of_thetaTriple
    {P : AccountMap → Substate → Prop}
    {Q : AccountMap → Substate → ByteArray → Prop}
    (pre : NestedWorld → Prop) (cd : ByteArray) (addr key v : Nat)
    (hT : ThetaTriple P (.Code cd) Q)
    (h1 : ∀ w, pre w → P w.σ w.A)
    (h2 : ∀ w, w.c = .Code cd → pre w →
      ∃ (k : ℕ) (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (g' : UInt256) (A' : Substate) (o : ByteArray),
        k ≤ seedFuel w ∧
        (∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts
          w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p
          w.v w.v' w.d w.e w.H w.w = .ok (cA, σ', g', A', true, o)))
    (hread : ∀ (σ'' : AccountMap) (A'' : Substate) (o' : ByteArray),
      Q σ'' A'' o' →
      (match σ''.toList.find? (fun p => p.1.val = addr) with
       | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
       | none => 0) = v) :
    Behaves pre cd (fun obs => completedWith obs addr key v) := by
  intro w hc hpre
  obtain ⟨k, cA, σ', g', A', o, hk, hruns⟩ := h2 w hc hpre
  have hrun : runΘ w = .ok (cA, σ', g', A', true, o) :=
    ΘRuns.runΘ_complete' w _ k hk hruns
  have hT' : ThetaTriple P w.c Q := by rw [hc]; exact hT
  exact completedWith_of_thetaTriple w addr key v hT' (h1 w hpre) hread hrun

/-! ## Non-vacuity: the do-nothing program `Behaves` -/

/-- The single-`STOP` code, named so it can occupy `Behaves`'s code slot. -/
def code00 : ByteArray := ⟨#[0x00]⟩

/-- `Refinement.IsDoNothing` minus its `code` conjunct — the code slot is
carried by `Behaves` itself, so the precondition holds the non-code fields:
empty map, default substate, zero value, in-bounds depth. -/
structure IsDoNothingPre (w : NestedWorld) : Prop where
  /-- The account map is empty (untouched): every storage slot reads `0`. -/
  empty : w.σ = ∅
  /-- The substate is the default (empty log series). -/
  subst : w.A = default
  /-- No value is transferred. -/
  value : w.v = ⟨0⟩
  /-- The call depth is within bounds (fuel envelope positive). -/
  depth : w.e ≤ 1024

/-- **Non-vacuity.** The do-nothing program `Behaves`: every pre-world
completes with value `0` at EVERY storage cell. PROVED — repackage the split
precondition into `IsDoNothing` and apply `doNothing_completedWith`. -/
theorem behaves_doNothing :
    Behaves IsDoNothingPre code00
      (fun obs => ∀ addr key, completedWith obs addr key 0) :=
  fun w hc hpre =>
    doNothing_completedWith w ⟨hc, hpre.empty, hpre.subst, hpre.value, hpre.depth⟩

/-! ## THE consuming lemma, and its firing

The flat `Behaves` has ZERO consuming lemmas repo-wide (verified by grep —
nothing takes a flat `Behaves` hypothesis). The two theorems below therefore
EXCEED flat parity: `Behaves.storage_out` consumes a `Behaves` hypothesis to
produce a concrete semantic fact, and `doNothingWorld_storage_zero` fires it
at an explicit world literal, ending in a hypothesis-free equation about a
concrete `runΘ`. That firing is what makes the predicate non-decorative. -/

/-- **The consuming lemma**: a `Behaves` hypothesis with a `completedWith`
postcondition yields, for every pre-world running the code, the concrete
storage-read equation on the seeded fuel-free run's observable. -/
theorem Behaves.storage_out {pre : NestedWorld → Prop} {cd : ByteArray}
    {addr key v : Nat}
    (h : Behaves pre cd (fun obs => completedWith obs addr key v)) :
    ∀ w, w.c = .Code cd → pre w →
      (observe_nested (runΘ w)).storageAt addr key = v :=
  fun w hc hpre => (h w hc hpre).2

/-- An explicit do-nothing `NestedWorld` literal: single-`STOP` code, empty
map, default substate, zero value, depth `0`. Every field concrete. -/
def doNothingWorld : NestedWorld where
  blobVersionedHashes := []
  createdAccounts := ∅
  genesisBlockHeader := default
  blocks := #[]
  σ := ∅
  σ₀ := ∅
  A := default
  s := default
  o := default
  r := default
  c := .Code code00
  g := ⟨0⟩
  p := ⟨0⟩
  v := ⟨0⟩
  v' := ⟨0⟩
  d := ByteArray.empty
  e := 0
  H := default
  w := false

/-- The literal satisfies the split do-nothing precondition. -/
theorem doNothingWorld_pre : IsDoNothingPre doNothingWorld :=
  ⟨rfl, rfl, rfl, Nat.zero_le _⟩

/-- **The consumer, FIRED**: a hypothesis-free storage equation at the
concrete world. Route: `behaves_doNothing` (producer) → specialize its `post`
to one cell → `Behaves.storage_out` (consumer) → instantiate at
`doNothingWorld`. The `Behaves` predicate is load-bearing in this derivation:
the consumed hypothesis `hB` is a genuine `Behaves` fact. -/
theorem doNothingWorld_storage_zero (addr key : Nat) :
    (observe_nested (runΘ doNothingWorld)).storageAt addr key = 0 := by
  have hB : Behaves IsDoNothingPre code00
      (fun obs => completedWith obs addr key 0) :=
    fun w hc hpre => behaves_doNothing w hc hpre addr key
  exact Behaves.storage_out hB doNothingWorld rfl doNothingWorld_pre

end NestedEvmYul
