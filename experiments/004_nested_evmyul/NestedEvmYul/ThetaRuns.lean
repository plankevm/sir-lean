import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.NeverOutOfFuel
import NestedEvmYul.XLoop
import NestedEvmYul.FuelMono

/-!
# T2 — `ΘRuns`: the ∀-fuel (offset-cofinal) relational veneer over the nested `Θ`

**This file is foundation-grade and placeholder-free throughout** (house proof-first
rule back in force). The original shape study's fuel-existential encoding —
whose every cross-fuel lemma funnelled through a fuel-irrelevance keystone —
was quarantined here and then DELETED by T4: against the semantics
of the time the keystone pair was FALSE as stated, not merely expensive (the
CREATE/CREATE2 `step` arms absorbed an inner `OutOfFuel` into an ordinary
result; the 2026-07-20 vendored patch made them propagate it honestly, which
made the keystone true, and `FuelMono.lean` now proves it). See the "Keystone
post-mortem" note at the bottom of this file.

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
* **adequacy** (`ΘRuns.runΘ_complete'`) — the fuel-monotonicity keystone moves
  the cofinal success and the seeded non-`OutOfFuel` result to a common fuel.
* **the observable lift** — ObservableTriple.`ΘRuns_completedWith`, plumbing
  over the same instantiation.

## What the ∀-encoding gives up

The cofinal encoding remains useful because the shape lemmas naturally produce
families (`Xi_stop`; `Θ_doNothing` below), and its determinism proof is pure
instantiation. After the CREATE/CREATE2 propagation patch, however, the proved
`FuelMono.Θ_fuel_mono_ok` and `_error` pair restores both missing directions:
one successful seeded run can be raised to a cofinal family, and a cofinal
family can be compared with the seeded non-`OutOfFuel` run at a common fuel.
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

/-- A successful seeded run generates a cofinal family by exact-result fuel
monotonicity. No depth or fuel-envelope premise is needed in this direction. -/
theorem ΘRuns.of_runTheta (w : NestedWorld) (res : ThetaResult)
    (h : runΘ w = .ok res) : ΘRuns w res := by
  refine ⟨seedFuel w, fun f => ?_⟩
  exact FuelMono.Θ_fuel_mono_ok (seedFuel w) (seedFuel w + f)
    w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader w.blocks w.σ w.σ₀
    w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w res
    (Nat.le_add_right _ _) h

/-! ## Cross-fuel consequences — now pure instantiation, keystone-free -/

/-- **Determinism of the veneer.** PROVED without placeholders: instantiate the first
witness at the second's offset and vice versa — both land at fuel `k₁ + k₂`
(one `Nat.add_comm`) — then `Except.ok` injectivity. The (deleted) existential
encoding paid the false keystone for this exact statement; the cofinal
encoding gets it for the cost of commutativity of `+`. -/
theorem ΘRuns.deterministic (w : NestedWorld) (res₁ res₂ : ThetaResult)
    (h₁ : ΘRuns w res₁) (h₂ : ΘRuns w res₂) : res₁ = res₂ := by
  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  have e₁ := h₁ k₂
  have e₂ := h₂ k₁
  rw [Nat.add_comm k₂ k₁] at e₂
  rw [e₁] at e₂
  exact Except.ok.inj e₂

/-- **Adequacy without an offset side condition.** Under the structural depth
cap that makes the seeded driver non-`OutOfFuel`, move both the cofinal success
and the seeded result to a common fuel. Success injectivity identifies results;
a semantic error contradicts the cofinal success; seeded `OutOfFuel` is ruled
out by `runΘ_never_outOfFuel`. -/
theorem ΘRuns.runΘ_complete' (w : NestedWorld) (res : ThetaResult) (k : ℕ)
    (he : w.e ≤ 1024)
    (h : ∀ f, Θ (k + f) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res) :
    runΘ w = .ok res := by
  cases hrun : runΘ w with
  | ok res' =>
      have hseed := FuelMono.Θ_fuel_mono_ok (seedFuel w) (seedFuel w + k)
        w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader w.blocks w.σ w.σ₀
        w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w res'
        (Nat.le_add_right _ _) hrun
      have hcofinal := h (seedFuel w)
      rw [Nat.add_comm k (seedFuel w)] at hcofinal
      rw [hcofinal] at hseed
      exact hseed.symm
  | error err =>
      by_cases herr : err = .OutOfFuel
      · subst err
        exact absurd hrun (runΘ_never_outOfFuel w he)
      · have hseed := FuelMono.Θ_fuel_mono_error (seedFuel w) (seedFuel w + k)
          w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader w.blocks w.σ w.σ₀
          w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w err herr
          (Nat.le_add_right _ _) hrun
        have hcofinal := h (seedFuel w)
        rw [Nat.add_comm k (seedFuel w)] at hcofinal
        rw [hcofinal] at hseed
        exact absurd hseed (by simp)

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
entry map/substate returned unchanged. PROVED without placeholders (offset witness `4`,
one `Nat.add_comm` to reorient the cofinal family). -/
theorem ΘRuns_doNothing (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', ΘRuns w (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨cA, g', hf⟩ := Θ_doNothing w h
  refine ⟨cA, g', 4, fun f => ?_⟩
  rw [Nat.add_comm 4 f]
  exact hf f

/-- The full pipeline, non-vacuously: cofinal do-nothing witness (offset `4`)
+ fuel-monotonic adequacy = the seeded driver's result — recovering
Refinement.lean's `runΘ_doNothing` through the relational API. -/
theorem ΘRuns_doNothing_runΘ (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', runΘ w = .ok (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨cA, g', hf⟩ := Θ_doNothing w h
  refine ⟨cA, g', ΘRuns.runΘ_complete' w _ 4 h.depth (fun f => ?_)⟩
  rw [Nat.add_comm 4 f]
  exact hf f

/-! ---------------------------------------------------------------------------
## Keystone post-mortem (T4): the fuel-existential encoding is DELETED because
## its keystone was FALSE against the pre-2026-07-20 semantics

HISTORICAL NOTE (2026-07-20): the absorption this post-mortem pivots on — the
CREATE/CREATE2 `| _ =>` catch-all — was REMOVED by the authorized vendored
patch of the same date (the arms now end in `| .error e => .error e`, honest
propagation). The refutation below is therefore a record about the *pre-patch*
semantics. Under the patched semantics the six-layer `FuelMono.res_mono`
induction proves `Θ_fuel_mono_ok` and `Θ_fuel_mono_error`; the cofinal `ΘRuns`
encoding now has single-point introduction and offset-unbounded adequacy. The
text below is kept verbatim as the historical record.

The pre-pivot fuel-existential veneer (`ΘRunsE := ∃ fuel, Θ fuel … = .ok res`)
and its fuel-irrelevance keystone pair (`Θ_fuel_mono_ok` / `Θ_fuel_mono_error`
— "a fuel-decided non-`OutOfFuel` result is reproduced at every larger fuel")
lived here quarantined as classified-hard sorries, priced by the B3 study at a
~1500-line 6-layer mutual induction mirroring `gas_mono`
(NeverOutOfFuel.lean:4018–4133). T4's attempt DELETED the section under the
house no-placeholder-scaffolds rule, with this obstruction record:

* **Which layer fails: `step`, and fatally.** The T1 dispatcher equations do
  make the ~130 non-recursive `step` arms fuel-irrelevant definitionally (the
  RHS `EvmYul.step op arg (debit s cost)` never mentions fuel), and the CALL
  family propagates an inner `OutOfFuel` honestly through its do-bind. But the
  CREATE/CREATE2 arms match the inner `Lambda` result with a `| _ =>`
  catch-all (EVMYulLean/EvmYul/EVM/Semantics.lean:286 and :344) that ABSORBS
  `.error .OutOfFuel` into an ordinary result tuple
  `(0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)`: execution
  continues with `x = 0` pushed, as if the create had *failed semantically*.

* **Why that kills the statement (not just the proof):** at fuel `n+1` with
  `Lambda n` out of fuel, `step` returns a NON-`OutOfFuel` result — so it
  satisfies the keystone's premise — yet at fuel `n' > n` large enough for the
  init-code run to complete, the CREATE succeeds (`x = a ≠ 0`, real post-map)
  and the results differ. The leak lifts through `X`/`Ξ`/`Θ` (an absorbed
  create followed by `STOP` is a `z = true` `Θ`-success at low fuel, different
  from the high-fuel success). `Θ_fuel_mono_ok` is therefore
  unprovable-as-stated; `res_mono`, the study's skeleton, dies at the `step`
  layer's CREATE arm regardless of how the other five layers are engineered.

* **Caveat on refutation-in-Lean:** a concrete counterexample needs the
  high-fuel side of a CREATE evaluated, which crosses `ffi.KEC` — an `opaque`
  `@[extern]` (EVMYulLean/EvmYul/FFI/ffi.lean:27) with no Lean model — so the
  falsity is established by the absorption argument above, not by a kernel
  witness (the same keccak wall exp005 hit for CREATE witnesses).

* **What a TRUE keystone would need:** either a `create-free` syntactic
  premise on every reachable code (wrong altitude for this veneer), or a
  semantic "no OutOfFuel anywhere in the sub-tree" premise — which is exactly
  what the `fuelBound` envelope of `runΘ_never_outOfFuel` provides at the
  seeding, and what the surviving offset-cofinal `ΘRuns` above builds in by
  quantifying over all sufficient fuels at once.

Consequence (as of the pre-patch semantics): the T2 cofinal pivot was not
merely the cheaper encoding — it was the only correct one of the two, its
`k ≤ seedFuel w` adequacy side condition and the loss of single-fuel-point
introduction non-removable. Post-patch, `FuelMono.Θ_fuel_mono_ok` restores
single-point introduction and the keystone pair removes the offset bound from
adequacy (which retains only the depth cap needed for the seeded never-OOF
fact). The deleted pre-patch material remains readable in git history at
ThetaRuns.lean of commit 6315c911 and in the study doc
(docs/planning/exp004-completion-shape-2026-07-18.md §2.2 + T4 addendum).
--------------------------------------------------------------------------- -/

end NestedEvmYul
