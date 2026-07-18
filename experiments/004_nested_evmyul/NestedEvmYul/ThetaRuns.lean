import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.NeverOutOfFuel
import NestedEvmYul.XLoop

/-!
# T2 — `ΘRuns`: the ∀-fuel (offset-cofinal) relational veneer over the nested `Θ`

**The surface of this file above the quarantine fence is foundation-grade and
sorry-free** (house proof-first rule back in force). The original shape study's
fuel-existential encoding — whose every cross-fuel lemma funnelled through an
unproved ~1500-line fuel-irrelevance keystone — survives only inside the
clearly-fenced `section DeprecatedFuelExistential` at the bottom, renamed
`ΘRunsE`, pending T4's keystone attempt. Nothing outside that section
references anything inside it.

## The pivot (T2)

`ΘRuns w res` now says: **cofinally in fuel, above some offset `k`, `Θ`
returns `.ok res`** — `∃ k, ∀ f, Θ (k + f) … = .ok res`. This is exactly the
shape the closed per-layer reduction lemmas already produce (`Xi_stop` is
`∀ f, Ξ (f + 3) … = .ok …`, Refinement.lean), so producers pay nothing extra,
and every cross-fuel consumer becomes pure instantiation:

* **determinism** (`ΘRuns.deterministic`) — instantiate each witness at the
  other's offset (`k₁ + k₂` vs `k₂ + k₁`, one `Nat.add_comm`), then
  `Except.ok` injectivity. No fuel transport, no keystone. This deletes the
  study's headline tax.
* **adequacy under a side condition** (`ΘRuns.runΘ_complete'`) — a cofinal
  witness whose offset is within the seeding (`k ≤ seedFuel w`) pins the
  seeded fuel-free driver: instantiate `f := seedFuel w - k`.
* **the observable lift** — ObservableTriple.`ΘRuns_completedWith`, plumbing
  over the same instantiation.

## What the ∀-encoding honestly gives up

The existential encoding had a free single-point introduction (`of_runΘ`: one
successful fueled run enters the veneer) and *unconditional* adequacy — but
only by deferring ALL cost to the fuel-irrelevance keystone
(`Θ_fuel_mono_ok`/`Θ_fuel_mono_error`: a fresh 6-layer mutual strong induction
mirroring `gas_mono`, NeverOutOfFuel.lean:4018–4133, plus a re-proved
~1500-line per-layer helper family). The ∀-encoding inverts the trade:
producers must supply **cofinal** witnesses — which the shape lemmas naturally
do (`Xi_stop`; `Θ_doNothing` below) — and in exchange every consumer closes
outright. A bare single fuel point (e.g. `runΘ w = .ok res` alone) does NOT
enter the veneer without the keystone; the `k ≤ seedFuel w` side condition on
adequacy is likewise irremovable without it (`runΘ_never_outOfFuel` excludes
one error at one seeding — it transports nothing). That trade IS the pivot;
it is the honest boundary of this API, not a defect to paper over.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## The veneer -/

/-- **`ΘRuns`** — the fuel-free relational veneer over `Θ`, in offset-cofinal
form: above some fuel offset `k`, EVERY fueled run returns `.ok res`. `w`
bundles the 19 positional `Θ` arguments (`NestedWorld`, SharedObservable.lean);
`res` is `Θ`'s `.ok` payload (`ThetaResult`). -/
def ΘRuns (w : NestedWorld) (res : ThetaResult) : Prop :=
  ∃ k, ∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
    w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res

/-- Introduction from a cofinal family: any offset-uniform success enters the
veneer. PROVED (pure `∃`-intro) — this is the producer-side obligation the
∀-encoding demands: a *cofinal* witness, not a single fuel point. -/
theorem ΘRuns.intro (w : NestedWorld) (res : ThetaResult) (k : ℕ)
    (h : ∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res) :
    ΘRuns w res :=
  ⟨k, h⟩

/-! ## Cross-fuel consequences — now pure instantiation, keystone-free -/

/-- **Determinism of the veneer.** PROVED sorry-free: instantiate the first
witness at the second's offset and vice versa — both land at fuel `k₁ + k₂`
(one `Nat.add_comm`) — then `Except.ok` injectivity. The existential encoding
paid an unproved 6-layer mutual induction for this exact statement
(`ΘRunsE.deterministic`, quarantined below); the cofinal encoding gets it for
the cost of commutativity of `+`. -/
theorem ΘRuns.deterministic (w : NestedWorld) (res₁ res₂ : ThetaResult)
    (h₁ : ΘRuns w res₁) (h₂ : ΘRuns w res₂) : res₁ = res₂ := by
  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  have e₁ := h₁ k₂
  have e₂ := h₂ k₁
  rw [Nat.add_comm k₂ k₁] at e₂
  rw [e₁] at e₂
  exact Except.ok.inj e₂

/-- **Adequacy under a side condition.** A cofinal witness whose offset is
within the seeding envelope pins the seeded fuel-free driver: instantiate
`f := seedFuel w - k` (`Nat.add_sub_cancel'`). PROVED sorry-free.

HONEST BOUNDARY: the side condition `k ≤ seedFuel w` is genuinely needed and
NOT removable via `runΘ_never_outOfFuel` (which excludes one error at one
seeding but transports no result across fuels) — removing it is exactly the
quarantined keystone. Producers built from the shape lemmas satisfy it
trivially (their offsets are small constants; see `ΘRuns_doNothing_runΘ`). -/
theorem ΘRuns.runΘ_complete' (w : NestedWorld) (res : ThetaResult) (k : ℕ)
    (hk : k ≤ seedFuel w)
    (h : ∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res) :
    runΘ w = .ok res := by
  have hf := h (seedFuel w - k)
  rw [Nat.add_sub_cancel' hk] at hf
  exact hf

/-! ## Non-vacuity: cofinal do-nothing witnesses

The ∀-encoding demands *cofinal* producers. Refinement.lean's per-layer
STOP-path lemmas are already fuel-generic in shape (`X_stop`/`Xi_stop` hold at
every `f + 2`/`f + 3`) but return a fresh existential witness at each fuel;
the versions below hoist the witness OUT of the fuel quantifier. This is
legitimate — and keystone-free — because the STOP path never consumes fuel:
`XLoop.step_eq_shared_stop`'s right-hand side is literally fuel-free (the
dispatcher-equation technique, T1), so the run's result is the same term at
every fuel by definitional unfolding, not by transporting a result. -/

/-- Fuel-uniform `step` on `STOP`: one witness state for ALL fuels. The two
`XLoop.step_eq_shared_stop` rewrites route both the generic-`f` goal and the
`f = 0` seed through the same fuel-free `EvmYul.step` term. -/
theorem step_stop_cofinal (s : EVM.State) :
    ∃ s', (∀ f, EVM.step (f + 1) 0 (some (Operation.STOP, none)) s = .ok s')
      ∧ s'.toState = s.toState := by
  obtain ⟨s', h1, hst⟩ := step_stop 0 s
  refine ⟨s', fun f => ?_, hst⟩
  rw [XLoop.step_eq_shared_stop f 0 none s, ← XLoop.step_eq_shared_stop 0 0 none s]
  exact h1

/-- Fuel-uniform single-`STOP` `X` iteration: one witness state for ALL fuels.
Mirror of Refinement.lean's `X_stop`, with the fuel-uniform step. -/
theorem X_stop_cofinal (vj : Array UInt256) (s : EVM.State)
    (hcode : s.executionEnv.code = ⟨#[0x00]⟩) (hpc : s.pc = ⟨0⟩) (hstk : s.stack = []) :
    ∃ s', (∀ f, X (f + 2) vj s = .ok (.success s' .empty)) ∧ s'.toState = s.toState := by
  obtain ⟨s', hstep, hst⟩ :=
    step_stop_cofinal {s with gasAvailable := s.gasAvailable - UInt256.ofNat 0}
  refine ⟨s', fun f => ?_, hst⟩
  unfold X
  simp only [hcode, hpc, decode_stop, Option.getD]
  rw [Z_stop vj s hstk]
  simp only [bind, Except.bind]
  rw [hstep f]
  simp only [H_stop, beq_iff_eq, reduceCtorEq, reduceIte]

/-- Fuel-uniform single-`STOP` `Ξ`: one gas witness for ALL fuels. Mirror of
Refinement.lean's `Xi_stop` with the fuel quantifier inside the existential —
exactly the producer shape `ΘRuns` wants. -/
theorem Xi_stop_cofinal (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩) :
    ∃ g', ∀ f, Ξ (f + 3) cA gh bl σ σ₀ g A I = .ok (.success (cA, σ, g', A) .empty) := by
  obtain ⟨s', hX, hst⟩ := X_stop_cofinal (D_J I.code ⟨0⟩) { (default : EVM.State) with accountMap := σ, σ₀ := σ₀, substate := A, executionEnv := I, blocks := bl, genesisBlockHeader := gh, createdAccounts := cA, gasAvailable := g } hcode rfl rfl
  refine ⟨s'.gasAvailable, fun f => ?_⟩
  rw [Ξ]
  simp only [bind, Except.bind]
  have hXf := hX f
  -- Zeta-reduce `hXf`'s state literal so it matches the goal's (`default.field` form).
  simp only [] at hXf
  rw [hXf]
  simp only []
  have hacc : s'.accountMap = σ := by rw [show s'.accountMap = s'.toState.accountMap from rfl, hst]
  have hsub : s'.substate = A := by rw [show s'.substate = s'.toState.substate from rfl, hst]
  have hcr  : s'.createdAccounts = cA := by
    rw [show s'.createdAccounts = s'.toState.createdAccounts from rfl, hst]
  rw [hacc, hsub, hcr]

/-- **Θ-level ∀-fuel do-nothing forward lemma.** The do-nothing world
(single-`STOP` call on the empty map, Refinement.lean's `IsDoNothing`) runs to
the canonical result at EVERY fuel `f + 4` — the cofinal witness `ΘRuns`
wants, with offset `4`. Mirror of `runΘ_doNothing`'s Θ-reduction (one Θ-peel:
`simp only [Θ, …]` through the transfer preamble on the empty map, then the
cofinal `Ξ` lemma; the `σ'' == ∅` rollback arm computes away by `rfl`). -/
theorem Θ_doNothing (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', ∀ f, Θ (f + 4) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w
      = .ok (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨hc, hσ, hA, hv, he⟩ := h
  obtain ⟨g', hXi⟩ := Xi_stop_cofinal w.createdAccounts w.genesisBlockHeader w.blocks
    ∅ w.σ₀ w.g default
    { codeOwner := w.r, sender := w.o, source := w.s, weiValue := w.v', calldata := w.d,
      code := ⟨#[0x00]⟩, gasPrice := w.p.toNat, header := w.H, depth := w.e, perm := w.w,
      blobVersionedHashes := w.blobVersionedHashes } rfl
  refine ⟨w.createdAccounts, g', fun f => ?_⟩
  rw [hc, hσ, hA, hv]
  -- Θ matches `fuel + 1` with `fuel = f + 3`; the `Code` arm calls `Ξ (f + 3)` on
  -- the entry-balance map `σ₁`. With `σ = ∅`/`v = 0`, the find?/insert
  -- bookkeeping is a no-op: `σ₁` collapses back to `∅`.
  simp only [Θ,
             show Batteries.RBMap.find? (∅ : AccountMap) w.r = none from rfl,
             show (({ val := 0 } : UInt256) != { val := 0 }) = false from by decide,
             Bool.false_eq_true, if_false,
             show Batteries.RBMap.find? (∅ : AccountMap) w.s = none from rfl]
  rw [hXi f]
  -- Θ's `Code` success arm packs `(cA, true, ∅, g', default, .empty)`, then
  -- post-processes: `σ' = if ∅ == ∅ then σ else ∅ = ∅` and
  -- `A' = if ∅ == ∅ then A else _ = default` — all by computation.
  rfl

/-- Non-vacuity of the veneer: the do-nothing world is in `ΘRuns`, with the
entry map/substate returned unchanged. PROVED sorry-free (offset witness `4`,
one `Nat.add_comm` to reorient the cofinal family). -/
theorem ΘRuns_doNothing (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', ΘRuns w (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨cA, g', hf⟩ := Θ_doNothing w h
  refine ⟨cA, g', 4, fun f => ?_⟩
  rw [Nat.add_comm 4 f]
  exact hf f

/-- The seeding envelope covers the do-nothing offset: `4 ≤ seedFuel w` under
the depth bound (`fuelBound ≥ 1`, Refinement.lean's `fuelBound_pos`, plus the
seeding's `+ 3`). The one-line Nat fact that connects the cofinal witness to
the seeded driver. -/
theorem seedFuel_ge_four (w : NestedWorld) (he : w.e ≤ 1024) : 4 ≤ seedFuel w := by
  unfold seedFuel
  have h := fuelBound_pos w.g.toNat w.e he
  omega

/-- The full pipeline, non-vacuously: cofinal do-nothing witness (offset `4`)
+ `4 ≤ seedFuel w` + adequacy-under-side-condition = the seeded driver's
result — recovering Refinement.lean's `runΘ_doNothing` through the new API,
keystone-free. -/
theorem ΘRuns_doNothing_runΘ (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', runΘ w = .ok (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨cA, g', hf⟩ := Θ_doNothing w h
  refine ⟨cA, g', ΘRuns.runΘ_complete' w _ 4 (seedFuel_ge_four w h.depth) (fun f => ?_)⟩
  rw [Nat.add_comm 4 f]
  exact hf f

/-! ---------------------------------------------------------------------------
## QUARANTINE FENCE — deprecated fuel-existential encoding below this line

**`section DeprecatedFuelExistential` — study-status material, quarantined
pending T4's keystone attempt.** Everything below is the pre-pivot
fuel-existential encoding (`ΘRunsE`, né `ΘRuns`) together with the TWO
remaining classified sorries of this file: the fuel-irrelevance keystone pair
`Θ_fuel_mono_ok`/`Θ_fuel_mono_error`. T4 either proves the pair (using T1's
dispatcher-equation technique to stale the ~1500-line pricing below), at which
point this section is promoted, or it deletes the WHOLE section and records
the obstruction in docs. NOTHING outside this section may import or reference
anything inside it — the foundation-grade surface above is self-contained.
--------------------------------------------------------------------------- -/

section DeprecatedFuelExistential

/-- DEPRECATED (quarantined) — the pre-pivot fuel-existential veneer: "some
fuel makes `Θ` return `.ok res`". Every cross-fuel lemma over THIS encoding
funnels through the unproved keystone pair below. Superseded by the
offset-cofinal `ΘRuns` above; kept only as T4's target vocabulary. -/
def ΘRunsE (w : NestedWorld) (res : ThetaResult) : Prop :=
  ∃ fuel, Θ fuel w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
    w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res

/-- DEPRECATED (quarantined). Single-point introduction — the intro rule the
∀-encoding gives up. PROVED (pure `∃`-intro). -/
theorem ΘRunsE.intro (w : NestedWorld) (res : ThetaResult) (fuel : ℕ)
    (h : Θ fuel w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res) :
    ΘRunsE w res :=
  ⟨fuel, h⟩

/-- DEPRECATED (quarantined). The seeded driver lands in the existential
veneer — the other intro rule the ∀-encoding gives up. PROVED. -/
theorem ΘRunsE.of_runΘ (w : NestedWorld) (res : ThetaResult)
    (h : runΘ w = .ok res) : ΘRunsE w res := by
  unfold runΘ at h
  exact ⟨seedFuel w, h⟩

/-! ### The keystone: fuel-irrelevance of `Θ` results

**The missing mutual induction** (T4's target). Neither half below is provable
from anything in `NeverOutOfFuel.lean`: `gas_mono` (line 4071) bounds *gas*,
and `Θ_never_outOfFuel` (line 4665) excludes *one error at one seeding* —
neither transports a *result* across fuels. The proof would be a NEW strong
induction on fuel bundling per-layer predicates, mirroring `*_gas_mono_at`
(NeverOutOfFuel.lean:4018–4071) exactly in shape. Skeleton (kept verbatim from
the study, as a comment — the point is to make the cost legible):

```
-- Per-layer result-stability predicates at a single fuel `n`. Each says: a
-- fuel-decided outcome (`.ok` or a non-OutOfFuel `.error`) at fuel `n` is
-- reproduced verbatim at every fuel `n' ≥ n`. Same argument lists as the
-- corresponding `*_gas_mono_at` (NeverOutOfFuel.lean:4024–4065).

def step_res_mono_at (n : ℕ) : Prop :=
  ∀ (cost : ℕ) (w : Operation) (arg) (s : State) (r),
    step n cost (some (w, arg)) s = r → r ≠ .error .OutOfFuel →
    ∀ n', n ≤ n' → step n' cost (some (w, arg)) s = r

def call_res_mono_at (n : ℕ) : Prop :=
  ∀ (cost : ℕ) (bvh) (gas source recipient t value value' io is oo os : UInt256)
    (perm : Bool) (ev : State) (r),
    call n cost bvh gas source recipient t value value' io is oo os perm ev = r →
    r ≠ .error .OutOfFuel → ∀ n', n ≤ n' → call n' cost bvh gas … perm ev = r

def Θ_res_mono_at (n : ℕ) : Prop :=
  ∀ (bvh) (cA) (gh) (blocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool) (res),
    Θ n bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = res →
    res ≠ .error .OutOfFuel → ∀ n', n ≤ n' → Θ n' bvh cA gh blocks … w = res

def Ξ_res_mono_at (n : ℕ) : Prop :=
  ∀ (cA) (gh) (blocks) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) (res),
    Ξ n cA gh blocks σ σ₀ g A I = res → res ≠ .error .OutOfFuel →
    ∀ n', n ≤ n' → Ξ n' cA gh blocks σ σ₀ g A I = res

def Lambda_res_mono_at (n : ℕ) : Prop :=
  ∀ (bvh) (cA) (gh) (blocks) (σ σ₀) (A) (s o) (g p v : UInt256) (i : ByteArray)
    (e : UInt256) (ζ : Option ByteArray) (Hd) (w : Bool) (res),
    Lambda n bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = res →
    res ≠ .error .OutOfFuel → ∀ n', n ≤ n' → Lambda n' bvh … w = res

def X_res_mono_at (n : ℕ) : Prop :=
  ∀ (vj : Array UInt256) (s : State) (res),
    X n vj s = res → res ≠ .error .OutOfFuel → ∀ n', n ≤ n' → X n' vj s = res

-- The driver, exactly `gas_mono`'s shape (strong induction on `n`, project the
-- IH per layer at every `m < n`, discharge each layer's child hypotheses):
theorem res_mono : ∀ n,
    step_res_mono_at n ∧ call_res_mono_at n ∧ Θ_res_mono_at n ∧
    Ξ_res_mono_at n ∧ Lambda_res_mono_at n ∧ X_res_mono_at n := by
  intro n; induction n using Nat.strong_induction_on with
  | _ n ih => -- 6 conjuncts; each peels ONE fuel layer of its function (the
              -- succ-match), rewrites every recursive occurrence via the IH at
              -- the child's smaller fuel, and closes by congruence. `X` needs a
              -- loop-invariant helper mirroring `X_loop_gas_le_bdd` (line
              -- ~3960); `step` must dispatch its recursive arms (CALL family →
              -- `call`, CREATE family → `Lambda`) WITHOUT unfolding the
              -- 140-arm match wholesale — i.e. it needs per-arm helper lemmas
              -- exactly like the gas-mono Stage-1 helpers (`step_gas_le`,
              -- `call_result_gas_le`, `Θ_gas_le_code`, …), each re-proved for
              -- result-stability. That Stage-1 helper family (~1500 lines on
              -- the gas side) is the *study's* pricing — T4 NOTE: T1's
              -- dispatcher equations (`XLoop.step_eq_shared_*`, fuel-free
              -- RHSes by `rfl`) make the non-recursive `step` arms
              -- fuel-irrelevant definitionally, staling most of that bill;
              -- the recursive CALL/CREATE arms and the loop/layer inductions
              -- remain the real cost.
```

Both halves below are corollaries of `res_mono` (`.ok` is never
`.error .OutOfFuel`; a non-OOF error is excluded by hypothesis). -/

/-- DEPRECATED (quarantined) **keystone, `.ok` half** — a successful `Θ` result
is stable under raising fuel. -/
theorem Θ_fuel_mono_ok
    (f f' : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool) (res : ThetaResult)
    (hok : Θ f bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .ok res)
    (hle : f ≤ f') :
    Θ f' bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .ok res := by
  -- SORRY-CLASS: hard — needs the NEW 6-layer `res_mono` mutual strong
  -- induction skeletonized above (mirrors `gas_mono`, NeverOutOfFuel.lean:4071;
  -- T1's dispatcher equations stale much of the Stage-1 helper bill, but the
  -- recursive arms + layer inductions remain); nothing existing transports a
  -- result across fuels. T4's target.
  sorry

/-- DEPRECATED (quarantined) **keystone, error half** — a non-`OutOfFuel` `Θ`
error is stable under raising fuel (only `OutOfFuel` is a fuel artifact;
semantic errors are fuel-irrelevant). -/
theorem Θ_fuel_mono_error
    (f f' : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool) (err : ExecutionException)
    (herr : Θ f bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .error err)
    (hOOF : err ≠ .OutOfFuel) (hle : f ≤ f') :
    Θ f' bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .error err := by
  -- SORRY-CLASS: hard — error half of the same `res_mono` keystone (one bundled
  -- induction proves both halves); non-OOF errors are fuel-stable but only the
  -- full 6-layer mutual induction can say so. T4's target.
  sorry

/-- DEPRECATED (quarantined). Determinism over the EXISTENTIAL encoding —
inherits the keystone's `sorry` transitively (lift both witnesses to
`max f₁ f₂`, then `Except.ok` injectivity). Superseded sorry-free by
`ΘRuns.deterministic` above. -/
theorem ΘRunsE.deterministic (w : NestedWorld) (res₁ res₂ : ThetaResult)
    (h₁ : ΘRunsE w res₁) (h₂ : ΘRunsE w res₂) : res₁ = res₂ := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  have h₁' := Θ_fuel_mono_ok f₁ (max f₁ f₂) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h₁ (Nat.le_max_left f₁ f₂)
  have h₂' := Θ_fuel_mono_ok f₂ (max f₁ f₂) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h₂ (Nat.le_max_right f₁ f₂)
  rw [h₁'] at h₂'
  exact Except.ok.inj h₂'

/-- DEPRECATED (quarantined). Unconditional adequacy over the EXISTENTIAL
encoding — inherits both keystone halves (plus the closed
`runΘ_never_outOfFuel`). Superseded keystone-free, at the price of the
`k ≤ seedFuel w` side condition, by `ΘRuns.runΘ_complete'` above. -/
theorem ΘRunsE.runΘ_complete (w : NestedWorld) (res : ThetaResult) (he : w.e ≤ 1024)
    (h : ΘRunsE w res) : runΘ w = .ok res := by
  obtain ⟨f, hf⟩ := h
  cases hrun : runΘ w with
  | ok res' =>
      unfold runΘ at hrun
      -- Lift both runs to the common fuel `max f (seedFuel w)` and compare.
      have h₁ := Θ_fuel_mono_ok f (max f (seedFuel w)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hf (Nat.le_max_left _ _)
      have h₂ := Θ_fuel_mono_ok (seedFuel w) (max f (seedFuel w)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hrun (Nat.le_max_right _ _)
      rw [h₁] at h₂
      rw [Except.ok.inj h₂]
  | error err =>
      by_cases hOOF : err = .OutOfFuel
      · -- Fuel artifact: impossible for the seeded driver under the envelope.
        subst hOOF
        exact absurd hrun (runΘ_never_outOfFuel w he)
      · -- Semantic error: fuel-stable, so it clashes with the `.ok` witness at
        -- the common fuel.
        unfold runΘ at hrun
        have h₁ := Θ_fuel_mono_ok f (max f (seedFuel w)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hf (Nat.le_max_left _ _)
        have h₂ := Θ_fuel_mono_error (seedFuel w) (max f (seedFuel w)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hrun hOOF (Nat.le_max_right _ _)
        rw [h₁] at h₂
        exact absurd h₂ (by simp)

/-- DEPRECATED (quarantined). Totality up to semantic error over the
EXISTENTIAL encoding. Sorry-free itself (pure case split + the closed
`runΘ_never_outOfFuel`), but stated against `ΘRunsE`, so it lives inside the
fence; T4 promotes or deletes it with the section. -/
theorem ΘRunsE.total_of_adequate (w : NestedWorld) (he : w.e ≤ 1024) :
    (∃ res, ΘRunsE w res) ∨ (∃ err, err ≠ .OutOfFuel ∧ runΘ w = .error err) := by
  cases hrun : runΘ w with
  | ok res => exact .inl ⟨res, ΘRunsE.of_runΘ w res hrun⟩
  | error err =>
      refine .inr ⟨err, ?_, rfl⟩
      intro hOOF
      subst hOOF
      exact runΘ_never_outOfFuel w he hrun

end DeprecatedFuelExistential

end NestedEvmYul
