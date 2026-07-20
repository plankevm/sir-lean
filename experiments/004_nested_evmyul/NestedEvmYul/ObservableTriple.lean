import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.ThetaRuns
import NestedEvmYul.XiTriple

/-!
# Observable-level link: `completedWith` over `observe_nested`,
# and the PROVED endgame

**STATUS (post-T4): this file is sorry-free and foundation-grade throughout,
endgame included.** `nested_twoCall_completedWith` — the full nested analog of
flat `twoCall_completedWith` — is now a theorem, rebuilt on the T1 XLoop
vocabulary (per-opcode rules, `ItersN_X` chain transport, `step_call_eq` /
`X_call_iter`, `X_stop_halt`) and the T2 cofinal veneer
(`ΘRuns_completedWith`). The study-era stated-only seed vocabulary
(`IterStep`/`IterCallStep`/`IterHalt`/`Iters`) is retired; its refutability
finding is preserved in the endgame's docstring HISTORY note.

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
5. Proves the layer-crossing forward plumbing (`Xi_forward`, `Θ_code_forward`)
   and the FULL nested analog of flat `twoCall_completedWith`
   (TwoCallExample.lean:103): two lemma-backed CALL sites, both callee
   `ThetaTriple`s firing, storage read DERIVED from `Q₂`, conclusion at the
   caller's fuel-free `runΘ` observable.
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
existential version of this theorem inherited the `Θ_fuel_mono_*` keystone,
since found FALSE and deleted; see ThetaRuns.lean's keystone post-mortem.)
The offset hypothesis is taken explicitly (rather
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

/-! ## The caller's entry state -/

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

/-! ## Forward plumbing: `Ξ` and `Θ` families from an `X` family

The two layer-crossing equations the endgame needs: given a cofinal `X`
success family on the entry state, produce the matching `Ξ` family (one
`Ξ`-unfold) and then the `Θ` family (one `Θ`-unfold: transfer preamble +
rollback arm). Fuel offsets follow the source: `Ξ (n+1)` runs `X n`,
`Θ (n+1)` runs `Ξ n`. -/

/-- **`Ξ` forward lemma**: a cofinal `X` success family on `Ξ`'s fresh entry
state yields the `Ξ` family, with the result 4-tuple read off the halt state's
fields. PROVED — one `Ξ`-unfold; the state-literal alignment uses the
`simp only [] at` zeta-nudge from `Refinement.Xi_stop`. -/
theorem Xi_forward (m : ℕ) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) (sH : EVM.State) (out : ByteArray)
    (hX : ∀ f, X (f + m + 2) (D_J I.code ⟨0⟩)
      { (default : EVM.State) with
          accountMap := σ, σ₀ := σ₀, substate := A, executionEnv := I,
          blocks := bl, genesisBlockHeader := gh, createdAccounts := cA,
          gasAvailable := g } = .ok (.success sH out)) :
    ∀ f, Ξ (f + m + 3) cA gh bl σ σ₀ g A I
      = .ok (.success (sH.createdAccounts, sH.accountMap, sH.gasAvailable, sH.substate) out) := by
  intro f
  show Ξ ((f + m + 2) + 1) cA gh bl σ σ₀ g A I = _
  rw [Ξ]
  simp only [bind, Except.bind]
  have hXf := hX f
  simp only [] at hXf
  rw [hXf]

/-- **`Θ` forward lemma** (`.Code` arm, general entry map): a cofinal `Ξ`
success family at the post-transfer map (`thetaTransfer`, T2's transcription
of Θ's balance preamble) and Θ's own execution env yields the `Θ` family with
`z = true`, provided the `σ'' == ∅` rollback arm does not fire (`hne`).
PROVED — one `Θ`-unfold + goal-side `split` on the `Ξ` match; each branch is
tied to the supplied family by `Eq.trans` (the defeq between `thetaTransfer`
and Θ's inline transfer matches is settled by the elaborator, exactly as in
`theta_of_xi`). -/
theorem Θ_code_forward (m : ℕ) {bvh : List ByteArray}
    {cA cA' : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ σ'' : AccountMap} {A A'' : Substate}
    {s o r : AccountAddress} {cd : ByteArray} {g p v v' g'' : UInt256}
    {d : ByteArray} {e : ℕ} {Hd : BlockHeader} {wp : Bool} {out : ByteArray}
    (hΞ : ∀ f, Ξ (f + m + 3) cA gh bl (thetaTransfer σ s r v) σ₀ g A
      { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
        source := s, weiValue := v', depth := e, perm := wp, code := cd,
        header := Hd, blobVersionedHashes := bvh }
      = .ok (.success (cA', σ'', g'', A'') out))
    (hne : (σ'' == (∅ : AccountMap)) = false) :
    ∀ f, Θ (f + m + 4) bvh cA gh bl σ σ₀ A s o r (.Code cd) g p v v' d e Hd wp
      = .ok (cA', σ'', g'', A'', true, out) := by
  intro f
  show Θ ((f + m + 3) + 1) bvh cA gh bl σ σ₀ A s o r (.Code cd) g p v v' d e Hd wp = _
  simp only [Θ, bind, Except.bind, pure, Except.pure]
  split
  · -- `Ξ = .error e`: contradicts the supplied success family
    rename_i heq
    exact absurd ((hΞ f).symm.trans heq) (by simp)
  · -- `Ξ = .ok (.revert g' o)`: ditto
    rename_i heq
    exact absurd ((hΞ f).symm.trans heq) (by simp)
  · -- `Ξ = .ok (.success (a, b, c, d) o)`: the genuine success path
    rename_i a b c dd oo heq
    cases (hΞ f).symm.trans heq
    simp only [hne, Bool.false_eq_true, if_false]

/-! ## The endgame: the full nested `twoCall_completedWith` analog, PROVED -/

/-- **The FULL flat-analog endgame** — nested mirror of flat
`twoCall_completedWith` (EVM/BytecodeLayer/Examples/TwoCallExample.lean:103),
**proved sorry-free** on the T1 XLoop vocabulary: a caller whose code performs
two `CALL`s and halts, per-callee `ThetaTriple`s firing at both sites, and the
conclusion `completedWith` of the CALLER's top-level fuel-free `runΘ` — the
storage read DERIVED from the second callee's postcondition `Q₂`, not
supplied.

Shape of the decomposition (each segment lemma-backed):

* `hpre`/`hmiddle` — straight-line segments as `XLoop.ItersN` chains
  (∀-fuel step clauses, populated by the `IterStepU.*` per-opcode rules);
* each call site — the derivable pieces of one `CALL` iteration: decode
  (`.getD`-faithful), `Z` success, the 7-deep post-`Z` stack shape, and the
  recursive `call`'s **cofinal** success family (`∀ f, call (f + kᵢ) … = .ok
  (⟨1⟩, evRᵢ)` on the **bumped** post-`Z` state — `T3.demo_call₁/₂` produce
  exactly this shape with `kᵢ := 5`). The iteration successor
  `evRᵢ.replaceStackAndIncrPC (restᵢ.push ⟨1⟩)` is **derived** via
  `XLoop.step_call_eq`+`X_call_iter`, never hypothesized;
* the suffix is EMPTY (flat's `TwoCallExample` also halts right after its
  business logic): the halting `STOP` iteration follows call₂ immediately,
  its successor explicit (`XLoop.stopHaltState`), so the final map is chased
  to `evR₂.accountMap` by `Z_ok_toState` + `rfl` and `hread` needs only `Q₂`;
* the fuel side condition `n₁ + n₂ + k₁ + k₂ + 6 ≤ seedFuel w` is the honest
  residue of the T2 cofinal pivot (`ΘRuns_completedWith`'s `k ≤ seedFuel w`).

HISTORY (the study's finding, recorded so it isn't lost): the pre-T1 version
of this statement took the decomposition in a stated-only vocabulary
(`IterStep`/`IterCallStep`/`IterHalt`/`Iters`, retired by this rebuild) and
was a classified-hard sorry with three recorded blockers — no X-decomposition,
no call-site tie, no Q-propagation. The call-site tie was the sharp one: the
naive endpoint-sharing shape (`call … = .ok (⟨1⟩, sR₁)` with `sR₁` the
iteration successor) is **refutable** — every `step` successor carries the
unconditional `execLength + 1` bump (Semantics.lean:234) plus the
`replaceStackAndIncrPC` postprocessing, while raw `call` outputs preserve
`execLength`/`pc`/stack verbatim, so the raw call output is *never* a `step`
successor. T1's `step_call_eq` made the tie stateable (successor = the
POST-PROCESSED call output on the BUMPED entry) and this theorem's `hcallᵢ`
families are exactly that shape; the three blockers dissolved into
`X_decompose`-style chain transport (`ItersN_X`), `X_call_iter`, and the
empty-suffix `Q₂`-read derivation. What remains genuinely supplied: the
per-segment decomposition data itself (the flat statement's hypotheses are the
same kind), and `hne` (Θ's degenerate empty-map rollback does not fire). -/
theorem nested_twoCall_completedWith
    (w : NestedWorld) (cd : ByteArray) (vj : Array UInt256)
    (hc : w.c = .Code cd) (hvj : vj = D_J cd ⟨0⟩)
    {P₁ P₂ : AccountMap → Substate → Prop}
    {Q₁ Q₂ : AccountMap → Substate → ByteArray → Prop}
    {n₁ n₂ k₁ k₂ : ℕ} {sC₁ sZ₁ evR₁ sC₂ sZ₂ evR₂ sZH : EVM.State}
    {arg₁ arg₂ argH : Option (UInt256 × Nat)} {cost₁ cost₂ costH : ℕ}
    {g₁ t₁ v₁ io₁ is₁ oo₁ os₁ : UInt256} {rest₁ : Stack UInt256}
    {g₂ t₂ v₂ io₂ is₂ oo₂ os₂ : UInt256} {rest₂ : Stack UInt256}
    (addr key v : Nat)
    -- the fuel envelope: the decomposition fits under the seeding
    (hfuel : n₁ + n₂ + k₁ + k₂ + 6 ≤ seedFuel w)
    -- prefix: straight-line chain from Θ's entry state to the first call site
    (hpre : XLoop.ItersN vj n₁ (callerEntry w cd) sC₁)
    -- call site 1: decode / gate / stack shape / cofinal call success
    (hdec₁ : (decode sC₁.executionEnv.code sC₁.pc).getD (.STOP, .none) = (.CALL, arg₁))
    (hZ₁ : Z vj .CALL sC₁ = .ok (sZ₁, cost₁))
    (hstk₁ : sZ₁.stack = g₁ :: t₁ :: v₁ :: io₁ :: is₁ :: oo₁ :: os₁ :: rest₁)
    (hcall₁ : ∀ f, call (f + k₁) cost₁ sZ₁.executionEnv.blobVersionedHashes g₁
      (.ofNat sZ₁.executionEnv.codeOwner) t₁ t₁ v₁ v₁ io₁ is₁ oo₁ os₁
      sZ₁.executionEnv.perm (XLoop.bump sZ₁) = .ok (⟨1⟩, evR₁))
    -- callee 1's procedure spec (T2 vocabulary) at the call-site state
    (hΘ₁ : ThetaTriple P₁ (toExecute sZ₁.accountMap (AccountAddress.ofUInt256 t₁)) Q₁)
    (hP₁ : P₁ sZ₁.accountMap (callAccessSubstate sZ₁ t₁))
    -- middle: straight-line chain from call 1's DERIVED successor to site 2
    (hmiddle : XLoop.ItersN vj n₂ (evR₁.replaceStackAndIncrPC (rest₁.push ⟨1⟩)) sC₂)
    -- call site 2, same shape
    (hdec₂ : (decode sC₂.executionEnv.code sC₂.pc).getD (.STOP, .none) = (.CALL, arg₂))
    (hZ₂ : Z vj .CALL sC₂ = .ok (sZ₂, cost₂))
    (hstk₂ : sZ₂.stack = g₂ :: t₂ :: v₂ :: io₂ :: is₂ :: oo₂ :: os₂ :: rest₂)
    (hcall₂ : ∀ f, call (f + k₂) cost₂ sZ₂.executionEnv.blobVersionedHashes g₂
      (.ofNat sZ₂.executionEnv.codeOwner) t₂ t₂ v₂ v₂ io₂ is₂ oo₂ os₂
      sZ₂.executionEnv.perm (XLoop.bump sZ₂) = .ok (⟨1⟩, evR₂))
    (hΘ₂ : ThetaTriple P₂ (toExecute sZ₂.accountMap (AccountAddress.ofUInt256 t₂)) Q₂)
    (hP₂ : P₂ sZ₂.accountMap (callAccessSubstate sZ₂ t₂))
    -- empty suffix: the halting STOP iteration immediately after call 2
    (hdecH : (decode (evR₂.replaceStackAndIncrPC (rest₂.push ⟨1⟩)).executionEnv.code
        (evR₂.replaceStackAndIncrPC (rest₂.push ⟨1⟩)).pc).getD (.STOP, .none)
      = (.STOP, argH))
    (hZH : Z vj .STOP (evR₂.replaceStackAndIncrPC (rest₂.push ⟨1⟩)) = .ok (sZH, costH))
    -- Θ's `σ'' == ∅` rollback postprocessing does not fire
    (hne : (evR₂.accountMap == (∅ : AccountMap)) = false)
    -- the storage read is DERIVED from Q₂ (v1 supplied it at the halt state)
    (hread : ∀ (σ'' : AccountMap) (A'' : Substate) (o' : ByteArray), Q₂ σ'' A'' o' →
      (match σ''.toList.find? (fun p => p.1.val = addr) with
       | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
       | none => 0) = v) :
    Q₁ evR₁.accountMap evR₁.substate evR₁.toMachineState.returnData ∧
    completedWith (observe_nested (runΘ w)) addr key v := by
  subst hvj
  -- (1) both callee specs fire (call_spec at any single fuel of the family)
  have hQ₁ : Q₁ evR₁.accountMap evR₁.substate evR₁.toMachineState.returnData :=
    call_spec (ev := XLoop.bump sZ₁) hΘ₁ (hcall₁ 0) hP₁ rfl
  refine ⟨hQ₁, ?_⟩
  have hQ₂ : Q₂ evR₂.accountMap evR₂.substate evR₂.toMachineState.returnData :=
    call_spec (ev := XLoop.bump sZ₂) hΘ₂ (hcall₂ 0) hP₂ rfl
  have hreadR := hread _ _ _ hQ₂
  -- (2) the composed X family: prefix / call₁ / middle / call₂ / halt,
  -- cofinal above offset n₁ + n₂ + k₁ + k₂ + 2 (fuel bookkeeping via omega)
  have hXfam : ∀ f, X (f + (n₁ + n₂ + k₁ + k₂ + 2) + 2) (D_J cd ⟨0⟩) (callerEntry w cd)
      = .ok (.success (XLoop.stopHaltState sZH costH) ByteArray.empty) := by
    intro f
    have h1 := XLoop.ItersN_X hpre (f + n₂ + k₁ + k₂ + 2)
    have h2 := XLoop.X_call_iter hdec₁ hZ₁ hstk₁ hcall₁ (f + n₂ + k₂ + 2)
    have h3 := XLoop.ItersN_X hmiddle (f + k₁ + k₂ + 1)
    have h4 := XLoop.X_call_iter hdec₂ hZ₂ hstk₂ hcall₂ (f + k₁ + 1)
    have h5 := XLoop.X_stop_halt hdecH hZH (f + k₁ + k₂)
    rw [show f + (n₁ + n₂ + k₁ + k₂ + 2) + 2 = f + n₂ + k₁ + k₂ + 2 + n₁ + 2 from by omega,
        h1,
        show f + n₂ + k₁ + k₂ + 2 + 2 = f + n₂ + k₂ + 2 + k₁ + 2 from by omega,
        h2,
        show f + n₂ + k₂ + 2 + k₁ + 1 = f + k₁ + k₂ + 1 + n₂ + 2 from by omega,
        h3,
        show f + k₁ + k₂ + 1 + 2 = f + k₁ + 1 + k₂ + 2 from by omega,
        h4,
        show f + k₁ + 1 + k₂ + 1 = f + k₁ + k₂ + 2 from by omega,
        h5]
  -- (3) the final map IS the second call's output map (stopHaltState/debit
  -- and replaceStackAndIncrPC don't touch toState; Z only rewrites gas)
  have hmap : (XLoop.stopHaltState sZH costH).accountMap = evR₂.accountMap := by
    show sZH.accountMap = evR₂.accountMap
    rw [show sZH.accountMap = sZH.toState.accountMap from rfl, XLoop.Z_ok_toState hZH]
    rfl
  -- (4) lift through Ξ and Θ (forward plumbing), then finish at the observable
  have hΞfam := Xi_forward (n₁ + n₂ + k₁ + k₂ + 2) w.createdAccounts
    w.genesisBlockHeader w.blocks (thetaTransfer w.σ w.s w.r w.v) w.σ₀ w.g w.A
    { codeOwner := w.r, sender := w.o, gasPrice := w.p.toNat, calldata := w.d,
      source := w.s, weiValue := w.v', depth := w.e, perm := w.w, code := cd,
      header := w.H, blobVersionedHashes := w.blobVersionedHashes }
    (XLoop.stopHaltState sZH costH) ByteArray.empty hXfam
  have hne' : ((XLoop.stopHaltState sZH costH).accountMap == (∅ : AccountMap)) = false := by
    rw [hmap]; exact hne
  have hΘfam := Θ_code_forward (n₁ + n₂ + k₁ + k₂ + 2) hΞfam hne'
  have hruns : ∀ f, Θ ((n₁ + n₂ + k₁ + k₂ + 6) + f) w.blobVersionedHashes
      w.createdAccounts w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r
      w.c w.g w.p w.v w.v' w.d w.e w.H w.w
      = .ok ((XLoop.stopHaltState sZH costH).createdAccounts,
          (XLoop.stopHaltState sZH costH).accountMap,
          (XLoop.stopHaltState sZH costH).gasAvailable,
          (XLoop.stopHaltState sZH costH).substate, true, ByteArray.empty) := by
    intro f
    rw [hc, show (n₁ + n₂ + k₁ + k₂ + 6) + f = f + (n₁ + n₂ + k₁ + k₂ + 2) + 4 from by omega]
    exact hΘfam f
  exact ΘRuns_completedWith w addr key v _ hfuel hruns (by rw [hmap]; exact hreadR)

/-! ## Findings

The three-track data point, in one place (study tracks: T1 = ThetaRuns.lean,
T2 = XiTriple.lean, T3 = this file), UPDATED for the overnight promotions
(XLoop T1 + forall-fuel pivot T2):

* **(a) Relational veneer — keystone tax DELETED by the cofinal re-encoding.**
  The study's fuel-existential `ΘRuns` paid a single unproved fuel-irrelevance
  mutual induction (`Θ_fuel_mono_ok`) for EVERY cross-fuel lemma. The
  forall-fuel pivot re-encoded the veneer offset-cofinally
  (`∃ k, ∀ f, Θ (k + f) … = .ok res`), after which determinism,
  adequacy-under-side-condition, and this file's `ΘRuns_completedWith` close
  sorry-free by pure instantiation. The honest residue: single fuel points no
  longer enter the veneer, and adequacy carries a `k ≤ seedFuel w` side
  condition. T4's keystone attempt found `Θ_fuel_mono_ok` FALSE against the
  then-current semantics — `step`'s CREATE/CREATE2 arms absorbed an inner
  `Lambda` `OutOfFuel` into an ordinary non-error result — and deleted the
  quarantined section; the 2026-07-20 vendored patch made those arms propagate
  the error honestly, so the keystone is now unproven-but-open rather than
  refuted (see ThetaRuns.lean's "keystone post-mortem" note for both halves).
  The cofinal pivot stands on its own: it needs no keystone at all.

* **(b) ∀-fuel triples — cheap composition, expensive footprints.** T2's
  `XiTriple`/`ThetaTriple` are fuel-free for free (universal quantification
  needs no transport), the call-site rule and two-call composition are function
  applications, and this file's `completedWith_of_thetaTriple` shows the
  observable link is pure plumbing (projection lemmas `observe_ok_tag`/
  `observe_storageAt` are `rw`+`rfl` — the observable layer earns its keep).
  The semantic frame rule is trivial, but *discharging* a footprint
  (`PreservesAccount`) for real code is per-program `Ξ`-reasoning — the same
  missing logic as (c).

* **(c) The caller-internal gap — CLOSED.** The study's headline negative
  result was that composing callee triples into a TOP-LEVEL observable
  conclusion was blocked on a missing X-loop program logic: the caller's
  straight-line code was a logic-free zone whose intermediate states could
  only be hypothesized, never derived — and the call-site tie was refutable
  in its naive endpoint-sharing form (`step` successors carry the
  unconditional `execLength` bump + `replaceStackAndIncrPC` postprocessing
  that raw `call` outputs lack). T1 colonized the zone (per-opcode rules,
  `X_branch`, `X_decompose`, `step_call_eq`), and T4 rebuilt and PROVED the
  endgame on that vocabulary (`nested_twoCall_completedWith` above): the
  call-site successor is now DERIVED (`X_call_iter`), the storage read is
  DERIVED from `Q₂` through the explicit halt state (`X_stop_halt` +
  `Z_ok_toState`), and the conclusion lands on the fuel-free `runΘ`
  observable via the T2 cofinal veneer. What the nested side still lacks
  vs flat (the residual parity gap): a `Behaves`-style all-programs predicate
  and a `messageCall`-bridge analog — segment data here enters per-theorem,
  as flat's `Runs` hypotheses do, but flat additionally packages them behind
  a program-level driver.
-/

end NestedEvmYul
