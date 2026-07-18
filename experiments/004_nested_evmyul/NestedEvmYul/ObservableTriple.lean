import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.ThetaRuns
import NestedEvmYul.XiTriple

/-!
# Observable-level link: `completedWith` over `observe_nested`,
# and the honest endgame gap statement

**STATUS (post-T1/T2 promotion): everything in this file is sorry-free and
foundation-grade EXCEPT the single endgame statement**
(`nested_twoCall_completedWith`), which remains a classified hard `sorry`
until T4 rebuilds it on the T1 XLoop vocabulary (per-opcode rules,
`X_decompose`, `step_call_eq` — all now proven in `NestedEvmYul.XLoop`). The
study-era stated-only seed vocabulary (`IterStep`/`Iters`/…) is kept below
ONLY as the endgame statement's input language, superseded-note attached; T4
retires it.

## What this file does

1. Gives the nested side the flat `Outcome.completedWith` vocabulary, verbatim,
   at the `SharedObservable` altitude (`completedWith`).
2. Pins the two projection lemmas (`observe_ok_tag`, `observe_storageAt`) that
   make every observable conclusion a `rw`+`rfl` above `runΘ`/`observe_nested`.
3. Connects XiTriple's `ThetaTriple` to an observable conclusion
   (`completedWith_of_thetaTriple`) and exhibits an inhabited instance via the
   do-nothing refinement (`doNothing_completedWith`).
4. Lifts the ∀-fuel relational veneer to the observable
   (`ΘRuns_completedWith`) — sorry-free since the T2 forall-fuel pivot: the
   cofinal encoding needs NO fuel-irrelevance keystone, only the
   `k ≤ seedFuel w` offset side condition.
5. States the FULL nested analog of flat `twoCall_completedWith`
   (TwoCallExample.lean:103) as the remaining SORRY-CLASS-hard endgame; its
   original blocker — no X-loop opcode logic between the two calls — has been
   removed by T1 (XLoop.lean), and T4 owns the rebuild.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## The flat vocabulary at the shared-observable altitude -/

/-- **`completedWith`** — verbatim mirror of the flat `Outcome.completedWith`
(EVM/BytecodeLayer) at the `SharedObservable` altitude: the run completed
successfully and storage cell `(addr, key)` reads `v`. -/
def completedWith (obs : SharedObservable) (addr key v : Nat) : Prop :=
  obs.tag = "ok" ∧ obs.storageAt addr key = v

/-! ## Projection lemmas: the observable layer earns its keep

Both are `rw`+`rfl` on `observe_nested`'s match — the observable layer was
built to make exactly this cheap (convergence report §3.2). `observe_storageAt`
pins the observable's storage read *shape* so Q-side predicates can be phrased
against it verbatim, dodging all RBMap `find?`/`toList` theory. -/

/-- A successful (`z = true`) seeded run observes with tag `"ok"`.
PROVED — `rw` + `rfl` on `observe_nested`'s match. -/
theorem observe_ok_tag (w : NestedWorld)
    {cA : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {o : ByteArray}
    (h : runΘ w = .ok (cA, σ', g', A', true, o)) :
    (observe_nested (runΘ w)).tag = "ok" := by
  rw [h]; rfl

/-- The observable's storage read of a completed run IS the literal
`find?`/`lookupStorage` match-expression over the post-map `σ'`.
PROVED — `rfl` after `rw`; every storage-side Q predicate below is phrased as
this exact expression so no RBMap lemma is ever needed. -/
theorem observe_storageAt (w : NestedWorld)
    {cA : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {z : Bool} {o : ByteArray} (addr key : Nat)
    (h : runΘ w = .ok (cA, σ', g', A', z, o)) :
    (observe_nested (runΘ w)).storageAt addr key
      = (match σ'.toList.find? (fun p => p.1.val = addr) with
         | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
         | none => 0) := by
  rw [h]; rfl

/-! ## From T2's triples to observable conclusions -/

/-- **Triple-to-observable plumbing.** A `ThetaTriple` for the world's own code
`w.c`, whose precondition holds at the world's entry state and whose
postcondition pins the storage read, yields `completedWith` of the seeded run.

PREAMBLE CAVEAT (inherited from T2's design decision, XiTriple.lean:79-85):
`ThetaTriple`'s `P` is over the **pre-transfer** `σ` — exactly the map `runΘ`
hands to `Θ`, so `hP` instantiates at `w.σ`/`w.A` directly. Had T2 chosen the
post-transfer-`σ₁` variant, this rule would need the `thetaTransfer` bookkeeping
here instead. `hread` is phrased as the literal `observe_storageAt`
match-expression, so the storage leg is `.trans`.

PROVED — pure plumbing: `runΘ` supplies the fuel (`seedFuel w`) and the 19
ambient arguments to the ∀-fuel triple; tag and storage legs are the two
projection lemmas. -/
theorem completedWith_of_thetaTriple
    {P : AccountMap → Substate → Prop}
    {Q : AccountMap → Substate → ByteArray → Prop}
    (w : NestedWorld) (addr key v : Nat)
    {cA : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {o : ByteArray}
    (hT : ThetaTriple P w.c Q)
    (hP : P w.σ w.A)
    (hread : ∀ (σ'' : AccountMap) (A'' : Substate) (o' : ByteArray),
      Q σ'' A'' o' →
      (match σ''.toList.find? (fun p => p.1.val = addr) with
       | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
       | none => 0) = v)
    (hrun : runΘ w = .ok (cA, σ', g', A', true, o)) :
    completedWith (observe_nested (runΘ w)) addr key v := by
  refine ⟨observe_ok_tag w hrun, ?_⟩
  have hΘ : Θ (seedFuel w) w.blobVersionedHashes w.createdAccounts
      w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v
      w.v' w.d w.e w.H w.w = .ok (cA, σ', g', A', true, o) := hrun
  have hQ : Q σ' A' o :=
    hT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hΘ rfl
  exact (observe_storageAt w addr key hrun).trans (hread σ' A' o hQ)

/-! ## The inhabited instance: the do-nothing world -/

/-- **Non-vacuity.** The do-nothing world (single-`STOP` call on the empty map,
Refinement.lean) `completedWith` value `0` at EVERY cell. PROVED sorry-free —
tag via the refinement's `dataAgrees.1`, storage via `storageAgrees` pointwise
against `emptyObs`'s all-zero storage (`Refinement.nested_refines_emptyObs`). -/
theorem doNothing_completedWith (w : NestedWorld) (h : IsDoNothing w) :
    ∀ addr key, completedWith (observe_nested (runΘ w)) addr key 0 := by
  intro addr key
  obtain ⟨hdata, hstor⟩ := nested_refines_emptyObs w h
  exact ⟨hdata.1, hstor addr key⟩

/-! ## From the ∀-fuel veneer to observable conclusions -/

/-- **Veneer-to-observable plumbing** (∀-fuel encoding, T2 pivot). A cofinal
veneer witness — offset `k` within the seeding envelope (`k ≤ seedFuel w`) —
for a completed (`z = true`) result whose post-map reads `v` at `(addr, key)`
yields `completedWith` of the seeded fuel-free run.

PROVED sorry-free: `ΘRuns.runΘ_complete'` instantiates the cofinal family at
`f := seedFuel w - k`; no fuel-irrelevance keystone anywhere. (The pre-pivot
existential version of this theorem inherited the quarantined
`Θ_fuel_mono_*` sorries; see ThetaRuns.lean, `section
DeprecatedFuelExistential`.) The offset hypothesis is taken explicitly (rather
than through `ΘRuns`'s `∃ k`) precisely so the `k ≤ seedFuel w` side condition
can be stated — that side condition is the honest residue of the pivot. -/
theorem ΘRuns_completedWith (w : NestedWorld)
    {cA : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {o : ByteArray} (addr key v : Nat)
    (k : ℕ) (hk : k ≤ seedFuel w)
    (hruns : ∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts
      w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v
      w.v' w.d w.e w.H w.w = .ok (cA, σ', g', A', true, o))
    (hread : (match σ'.toList.find? (fun p => p.1.val = addr) with
              | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
              | none => 0) = v) :
    completedWith (observe_nested (runΘ w)) addr key v := by
  have hrun : runΘ w = .ok (cA, σ', g', A', true, o) :=
    ΘRuns.runΘ_complete' w _ k hk hruns
  exact ⟨observe_ok_tag w hrun, (observe_storageAt w addr key hrun).trans hread⟩

/-! ## Seed vocabulary for the missing X-loop logic (stated only, no lemmas)

**SUPERSEDED (T1, XLoop.lean): this stated-only vocabulary now has a
lemma-backed replacement.** `NestedEvmYul.XLoop` proves the per-opcode rules
(`X_push1`/`X_sstore`/`X_jump`/`X_jumpi_*`), the branch combinator
(`X_branch`), and the decomposition theorem (`X_decompose`) over the ∀-fuel,
`.getD`-faithful relations `IterStepU`/`IterHaltU`/`ItersN` — fixing this
section's two recorded defects (the `∃ f` fuel clause and the `decode = some`
fidelity gap; `X` reads `decode … |>.getD (.STOP, .none)`). The definitions
below are kept verbatim ONLY as the study's labeled artifact; T4 retires them
when the endgame statement is rebuilt on the XLoop vocabulary. Do not build
on them.

The relations below only NAME the shape of one `X`-loop iteration — decode,
`Z` gate, `step`, `H` check — proving nothing about them. They exist so the
hard sorry below can state the caller's run decomposition at all. They are
exactly the vocabulary the nested side lacks lemmas for: there is no analog of
flat's `runs_*` per-opcode rules to *establish* an `IterStep`, and no
X-decomposition lemma to glue `Iters` segments back into an `X`-run. -/

/-- One non-halting `X`-loop iteration: the code at `s.pc` decodes to `op`,
the `Z` gate passes, `step` succeeds, and `H` does not halt (`none`), so the
loop would recurse on `s'`. Stated only — no lemmas (the per-opcode rules that
would populate this relation are exactly the missing program logic). -/
def IterStep (vj : Array UInt256) (s s' : EVM.State) : Prop :=
  ∃ (f cost : ℕ) (op : Operation) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    decode s.executionEnv.code s.pc = some (op, arg) ∧
    Z vj op s = .ok (s₁, cost) ∧
    EVM.step f cost (some (op, arg)) s₁ = .ok s' ∧
    H s'.toMachineState op = none

/-- The CALL-pinned `IterStep`: one non-halting `X`-loop iteration whose
decoded opcode is `.CALL`. Used at the two call sites below so the sandwich
hypotheses at least NAME the right opcode. NOTE (per the sharpened T3 review
finding): `step`'s real CALL arm invokes `call` on the *post-`Z` bumped* state
`s₁` (the unconditional `execLength + 1` at Semantics.lean:234) and then applies
`replaceStackAndIncrPC` (`stack.push x`), so the raw `call` output is **never
itself a `step` successor** — the successor `s'` here and any `call` output
state are necessarily *different* states. Stated only — no lemmas. -/
def IterCallStep (vj : Array UInt256) (s s' : EVM.State) : Prop :=
  ∃ (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    decode s.executionEnv.code s.pc = some (.CALL, arg) ∧
    Z vj .CALL s = .ok (s₁, cost) ∧
    EVM.step f cost (some (.CALL, arg)) s₁ = .ok s' ∧
    H s'.toMachineState .CALL = none

/-- The halting sibling: one `X`-loop iteration whose `H` returns `some o`
(a non-`REVERT` halt, so `X` would package `.success s' o`). Stated only. -/
def IterHalt (vj : Array UInt256) (s s' : EVM.State) (o : ByteArray) : Prop :=
  ∃ (f cost : ℕ) (op : Operation) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    decode s.executionEnv.code s.pc = some (op, arg) ∧
    Z vj op s = .ok (s₁, cost) ∧
    EVM.step f cost (some (op, arg)) s₁ = .ok s' ∧
    H s'.toMachineState op = some o ∧
    op ≠ .REVERT

/-- Straight-line runs: the reflexive-transitive closure of `IterStep`
(refl + tail, self-contained — no Mathlib `Relation` dependency). Stated only. -/
inductive Iters (vj : Array UInt256) : EVM.State → EVM.State → Prop
  | refl (s : EVM.State) : Iters vj s s
  | tail {s s' s'' : EVM.State} :
      Iters vj s s' → IterStep vj s' s'' → Iters vj s s''

/-- The entry `EVM.State` that `Θ`'s `.Code` arm hands to `Ξ`/`X` for a caller
world `w` executing code `cd`: the post-transfer map (`thetaTransfer`, T2's
verbatim transcription of Θ's balance preamble), the world's substate, and the
execution env Θ builds from its arguments (transcribed from the closed
`runΘ_doNothing`/`Xi_stop` reductions — Θ is never unfolded here). -/
def callerEntry (w : NestedWorld) (cd : ByteArray) : EVM.State :=
  { (default : EVM.State) with
      accountMap := thetaTransfer w.σ w.s w.r w.v
      σ₀ := w.σ₀
      substate := w.A
      executionEnv :=
        { codeOwner := w.r, sender := w.o, source := w.s, weiValue := w.v',
          calldata := w.d, code := cd, gasPrice := w.p.toNat, header := w.H,
          depth := w.e, perm := w.w,
          blobVersionedHashes := w.blobVersionedHashes }
      blocks := w.blocks
      genesisBlockHeader := w.genesisBlockHeader
      createdAccounts := w.createdAccounts
      gasAvailable := w.g }

/-! ## The endgame gap: the full nested `twoCall_completedWith` analog -/

/-- **The FULL flat-analog endgame** — nested mirror of flat
`twoCall_completedWith` (EVM/BytecodeLayer/Examples/TwoCallExample.lean:103):
a caller whose code contains two CALLs, per-callee `ThetaTriple`s, and a
decomposition of the caller's execution as
prefix-iterations / call₁ / middle-iterations / call₂ / suffix / halt,
concluding `completedWith` of the CALLER's top-level `runΘ`.

Hypothesis-by-hypothesis mirror of the flat statement: `hentry`/`hvj` play
flat's `EntersAsCode`; `hpre`/`hmiddle`/`hpost` play the three flat `Runs`
segments; `hcall₁ₓ`/`hcall₂ₓ` (a CALL-pinned `IterCallStep` each) with the
`call`-level successes (`hcall₁`/`hcall₂`, flat's `CallReturns`) landing in
**fresh** output states `evR₁`/`evR₂`, deliberately untied to the iteration
successors `sR₁`/`sR₂` — see diagnosis point (2) for why endpoint-sharing
would be refutable; `hhalt`+`hread`+`hne` play `stepFrame last = halted` +
`hsucc` + `hcell`.

-- SORRY-CLASS: hard — see the diagnosis comment in the proof body.

DIAGNOSIS (the study's deliverable): the missing ingredient is an **X-loop
iteration logic** — per-opcode rules populating `IterStep` (the nested analog
of flat's `runs_*` rules) plus a loop-decomposition lemma over `X`'s fuel
recursion gluing `Iters` segments into an `X`-run (the nested analog of flat's
`Runs.trans`), which exp004 never built. WITHOUT it there is no vocabulary to
*discharge* "the caller executed straight-line code between the two calls":
`sC₁`/`sR₁`/`sC₂`/`sR₂`/`sEnd`/`sHalt` enter as free data pinned only by
hypotheses that nothing in the repo can establish. Concretely, a proof needs,
none of which exist: (1) `X`-decomposition — `Iters vj s₀ sEnd → IterHalt vj
sEnd sHalt out → ∀ sufficient fuel, X fuel vj s₀ = .ok (.success sHalt out)` —
a fresh induction over `X`'s fuel recursion, PLUS fuel transport for each
`IterStep`'s private `∃ f` step-fuel witness (T1's unproved keystone again);
(2) the tie between an `IterCallStep` and the `call`/`Θ` recursion — the
SHARPENED finding (T3 fix round): without per-opcode `step` lemmas the nested
side cannot even *STATE* the call-site tie consistently. The naive
endpoint-sharing shape (asserting `call … sC₁ = .ok (⟨1⟩, sR₁)` with `sR₁` the
`IterStep` successor) is **refutable**: every `step` `.ok` successor has
`execLength = source.execLength + 1` (the unconditional bump at
EVMYulLean/EvmYul/EVM/Semantics.lean:234 is the sole `execLength` write site,
every arm derives from the bumped state, and `Z` preserves `execLength`),
while any `call` output preserves `execLength` (and `pc`/stack) verbatim — a
contradiction over ℕ that would make the whole theorem vacuously true.
Concretely, `step`'s real CALL arm invokes `call` on the post-`Z` bumped state
and then applies `replaceStackAndIncrPC` (`stack.push x`), so the raw `call`
output is never a `step` successor; hence `hcall₁`/`hcall₂` below land in
FRESH states `evR₁`/`evR₂`, and the `evR₁`↔`sR₁` tie is exactly `step`'s CALL
arm, unreachable without opening the 140-arm match per-opcode;
(3) propagation of the callees' `Q₁`/`Q₂` through the middle/suffix segments to
establish `hread` at the halt state — flat does this with `runs_*` + framing;
nested has `PreservesAccount` (T2) but nothing to discharge it per-opcode. The
sorry's shape IS the finding: T2's triples compose cheaply BELOW the caller,
but the caller's own straight-line code is a logic-free zone. -/
theorem nested_twoCall_completedWith
    (w : NestedWorld) (he : w.e ≤ 1024) (cd : ByteArray) (vj : Array UInt256)
    (hc : w.c = .Code cd) (hvj : vj = D_J cd ⟨0⟩)
    {P₁ P₂ : AccountMap → Substate → Prop}
    {Q₁ Q₂ : AccountMap → Substate → ByteArray → Prop}
    {t₁ t₂ : UInt256} {s₀ sC₁ sR₁ sC₂ sR₂ sEnd sHalt : EVM.State}
    -- fresh `call`-output states, deliberately UNTIED to sR₁/sR₂ (see
    -- diagnosis (2): tying them would be refutable via the execLength bump)
    {evR₁ evR₂ : EVM.State}
    {f₁ f₂ gc₁ gc₂ : ℕ} {bvh₁ bvh₂ : List ByteArray}
    {gas₁ src₁ rcp₁ v₁ w₁ io₁ is₁ oo₁ os₁ : UInt256}
    {gas₂ src₂ rcp₂ v₂ w₂ io₂ is₂ oo₂ os₂ : UInt256}
    {perm₁ perm₂ : Bool} {out : ByteArray} (addr key v : Nat)
    -- entry: the caller's X-run starts at Θ's entry state on the caller's code
    (hentry : s₀ = callerEntry w cd)
    -- per-callee procedure specs (T2 vocabulary), at the two call sites
    (hΘ₁ : ThetaTriple P₁ (toExecute sC₁.accountMap (AccountAddress.ofUInt256 t₁)) Q₁)
    (hΘ₂ : ThetaTriple P₂ (toExecute sC₂.accountMap (AccountAddress.ofUInt256 t₂)) Q₂)
    (hP₁ : P₁ sC₁.accountMap (callAccessSubstate sC₁ t₁))
    (hP₂ : P₂ sC₂.accountMap (callAccessSubstate sC₂ t₂))
    -- the sandwich: prefix / call₁ / middle / call₂ / suffix / halt
    (hpre : Iters vj s₀ sC₁)
    (hcall₁ₓ : IterCallStep vj sC₁ sR₁)
    (hcall₁ : call f₁ gc₁ bvh₁ gas₁ src₁ rcp₁ t₁ v₁ w₁ io₁ is₁ oo₁ os₁ perm₁ sC₁
      = .ok (⟨1⟩, evR₁))
    (hmiddle : Iters vj sR₁ sC₂)
    (hcall₂ₓ : IterCallStep vj sC₂ sR₂)
    (hcall₂ : call f₂ gc₂ bvh₂ gas₂ src₂ rcp₂ t₂ v₂ w₂ io₂ is₂ oo₂ os₂ perm₂ sC₂
      = .ok (⟨1⟩, evR₂))
    (hpost : Iters vj sR₂ sEnd)
    (hhalt : IterHalt vj sEnd sHalt out)
    -- Θ's `σ'' == ∅` rollback postprocessing does not fire (non-degenerate halt)
    (hne : (sHalt.accountMap == (∅ : AccountMap)) = false)
    -- the halt state's map reads `v` at (addr, key) — in a real proof this
    -- would be DERIVED from Q₁/Q₂ + framing through hmiddle/hpost; supplied
    -- here because that derivation is exactly the missing logic
    (hread : (match sHalt.accountMap.toList.find? (fun p => p.1.val = addr) with
              | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
              | none => 0) = v) :
    completedWith (observe_nested (runΘ w)) addr key v := by
  -- SORRY-CLASS: hard — needs the X-loop iteration logic exp004 never built:
  -- (1) an X-decomposition lemma over the fuel recursion (Iters + IterHalt →
  -- X = .ok (.success sHalt out) at all sufficient fuels, incl. per-IterStep
  -- fuel transport = T1's unproved keystone); (2) the step-CALL-arm tie
  -- linking hcall₁'s fresh output evR₁ to the iteration successor sR₁
  -- (per-opcode rules, the nested analog of flat's runs_*; sharing the
  -- endpoint instead is refutable via the execLength bump — see docstring);
  -- (3) Q-propagation/framing through the middle and suffix segments. See the
  -- docstring diagnosis; this sorry's shape is the study's deliverable.
  sorry

/-! ## Findings

The three-track data point, in one place (study tracks: T1 = ThetaRuns.lean,
T2 = XiTriple.lean, T3 = this file), UPDATED for the overnight promotions
(XLoop T1 + forall-fuel pivot T2):

* **(a) Relational veneer — keystone tax DELETED by the cofinal re-encoding.**
  The study's fuel-existential `ΘRuns` paid a single unproved fuel-irrelevance
  mutual induction (`Θ_fuel_mono_ok`, a 6-layer `gas_mono`-shaped strong
  induction priced at a ~1500-line helper family) for EVERY cross-fuel lemma.
  The forall-fuel pivot re-encoded the veneer offset-cofinally
  (`∃ k, ∀ f, Θ (k + f) … = .ok res`), after which determinism,
  adequacy-under-side-condition, and this file's `ΘRuns_completedWith` close
  sorry-free by pure instantiation. The honest residue: single fuel points no
  longer enter the veneer, and adequacy carries a `k ≤ seedFuel w` side
  condition — removing either is exactly the keystone, now quarantined in
  ThetaRuns.lean's `DeprecatedFuelExistential` section as T4's
  prove-or-delete target.

* **(b) ∀-fuel triples — cheap composition, expensive footprints.** T2's
  `XiTriple`/`ThetaTriple` are fuel-free for free (universal quantification
  needs no transport), the call-site rule and two-call composition are function
  applications, and this file's `completedWith_of_thetaTriple` shows the
  observable link is pure plumbing (projection lemmas `observe_ok_tag`/
  `observe_storageAt` are `rw`+`rfl` — the observable layer earns its keep).
  The semantic frame rule is trivial, but *discharging* a footprint
  (`PreservesAccount`) for real code is per-program `Ξ`-reasoning — the same
  missing logic as (c).

* **(c) The caller-internal gap — the headline negative result.** Composing
  callee triples into a TOP-LEVEL observable conclusion
  (`nested_twoCall_completedWith`) is blocked on a missing X-loop program
  logic: per-opcode rules to populate `IterStep` (flat's `runs_*` surface has
  no nested counterpart), an `X` loop-decomposition lemma (flat's
  `Runs.trans`), and the step-CALL-arm tie linking an iteration to the
  `call`/`Θ` recursion. The tie is worse than merely unprovable: without
  per-opcode `step` lemmas it cannot even be *stated* consistently — the
  naive shape sharing the iteration's endpoints is refutable outright (`step`
  successors carry the unconditional `execLength` bump that `call` outputs
  lack), so the call result must enter as a fresh, hypothesis-only state.
  Between the two calls, the caller's straight-line code
  was a logic-free zone: its intermediate states could only be hypothesized,
  never derived. **UPDATE (T1, XLoop.lean): that zone is now colonized** —
  per-opcode rules (`X_push1`/`X_sstore`/`X_jump`/`X_jumpi_*`), the branch
  combinator (`X_branch`), the sequencing/decomposition theorem
  (`X_decompose`), and the CALL-arm dispatcher tie (`step_call_eq`) are all
  proven sorry-free. The endgame statement above remains the last consumer to
  rebuild on that vocabulary (T4).
-/

end NestedEvmYul
