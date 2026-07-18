import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.NeverOutOfFuel

/-!
# T1 — `ΘRuns`: a fuel-free relational veneer over the nested `Θ`, and the
# fuel-irrelevance keystone it exposes

**THIS FILE IS A LABELED EXPLORATORY SHAPE STUDY, NOT A FOUNDATION TO BUILD ON.**

Ground rules (per the track spec, verbatim): statements first; prove only the
genuinely easy ones; the rest get explicit `sorry` with a
`-- SORRY-CLASS: easy|medium|hard — <reason>` comment; this file is a LABELED
EXPLORATORY ARTIFACT, not a foundation to build on — it **deliberately overrides
the house proof-first/no-sorry rule by design**, for the sole purpose of
measuring the shape and cost of a relational surface over the nested recursive
`Θ` semantics; `lake build` must be green after the track.

## What is measured here

`ΘRuns w res` is the fuel-existential graph closure of `Θ`: "some fuel makes
`Θ` return `.ok res` on world `w`". Everything *within* one fuel witness is
free: introduction, non-vacuity (via the closed `runΘ_doNothing`), and totality
(via the closed `runΘ_never_outOfFuel`) are pure `Except`/`∃` logic that never
unfolds the semantics.

## Deliverable finding

The relational veneer is **~free EXCEPT** that every cross-fuel lemma —
determinism, adequacy w.r.t. `runΘ`, and any future transitivity/gluing —
funnels through ONE missing keystone: **fuel-irrelevance of `Θ` results**
(`Θ_fuel_mono_ok` / `Θ_fuel_mono_error` below). That keystone is a fresh
5/6-layer mutual strong induction over `step`/`call`/`Θ`/`Ξ`/`Lambda`/`X`,
mirroring the shape of `NeverOutOfFuel.gas_mono` (NeverOutOfFuel.lean:4018–4133)
but proving a *different* invariant, so nothing there is reusable as-is. The
flat single-counter side never pays this tax: with one interpreter and one
drive, determinism is definitional (function-equation determinism of a single
run) and no cross-fuel transport ever arises. This is the nested-native analog
of a lemma the flat side gets for free — the headline data point of this track.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## The veneer -/

/-- **`ΘRuns`** — the fuel-free relational veneer over `Θ`: the fuel-existential
graph closure. `w` bundles the 19 positional `Θ` arguments (`NestedWorld`,
SharedObservable.lean); `res` is `Θ`'s `.ok` payload (`ThetaResult`). -/
def ΘRuns (w : NestedWorld) (res : ThetaResult) : Prop :=
  ∃ fuel, Θ fuel w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
    w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res

/-- Any successful fueled `Θ` run enters the veneer. PROVED (pure `∃`-intro). -/
theorem ΘRuns.intro (w : NestedWorld) (res : ThetaResult) (fuel : ℕ)
    (h : Θ fuel w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
      w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w = .ok res) :
    ΘRuns w res :=
  ⟨fuel, h⟩

/-- The seeded fuel-free driver `runΘ` lands in the veneer. PROVED (`runΘ`
unfolds by definition; witness `seedFuel w`). -/
theorem ΘRuns.of_runΘ (w : NestedWorld) (res : ThetaResult)
    (h : runΘ w = .ok res) : ΘRuns w res := by
  unfold runΘ at h
  exact ⟨seedFuel w, h⟩

/-- Non-vacuity: the do-nothing world (single-`STOP` call on the empty map,
Refinement.lean) is in the veneer, with the entry map/substate returned
unchanged. PROVED (direct from the closed `runΘ_doNothing`). -/
theorem ΘRuns_doNothing (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', ΘRuns w (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨cA, g', hrun⟩ := runΘ_doNothing w h
  exact ⟨cA, g', ΘRuns.of_runΘ w _ hrun⟩

/-! ## The keystone: fuel-irrelevance of `Θ` results

**The missing mutual induction.** Neither half below is provable from anything
in `NeverOutOfFuel.lean`: `gas_mono` (line 4071) bounds *gas*, and
`Θ_never_outOfFuel` (line 4665) excludes *one error at one seeding* — neither
transports a *result* across fuels. The proof would be a NEW strong induction on
fuel bundling per-layer predicates, mirroring `*_gas_mono_at`
(NeverOutOfFuel.lean:4018–4071) exactly in shape. Skeleton (per the track spec,
as a comment — the point is to make the cost legible, not to pay it):

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
              -- the gas side) is the real cost.
```

Both halves below are corollaries of `res_mono` (`.ok` is never
`.error .OutOfFuel`; a non-OOF error is excluded by hypothesis). -/

/-- **Keystone, `.ok` half** — a successful `Θ` result is stable under raising
fuel. -/
theorem Θ_fuel_mono_ok
    (f f' : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool) (res : ThetaResult)
    (hok : Θ f bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .ok res)
    (hle : f ≤ f') :
    Θ f' bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w = .ok res := by
  -- SORRY-CLASS: hard — needs the NEW 6-layer `res_mono` mutual strong
  -- induction skeletonized above (mirrors `gas_mono`, NeverOutOfFuel.lean:4071,
  -- incl. re-proving its ~1500-line Stage-1 per-layer helper family for
  -- result-stability instead of gas bounds); nothing existing transports a
  -- result across fuels.
  sorry

/-- **Keystone, error half** — a non-`OutOfFuel` `Θ` error is stable under
raising fuel (only `OutOfFuel` is a fuel artifact; semantic errors are
fuel-irrelevant). -/
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
  -- full 6-layer mutual induction can say so.
  sorry

/-! ## Cross-fuel consequences — everything below inherits the keystone -/

/-- **Determinism of the veneer.** PROVED for real *given the keystone*: lift
both witnesses to `max f₁ f₂` via `Θ_fuel_mono_ok`, then `Except.ok`
injectivity. Inherits the keystone's `sorry` transitively — that inheritance IS
the data point: on the flat side, determinism of one interpreter drive is
definitional and costs nothing. -/
theorem ΘRuns.deterministic (w : NestedWorld) (res₁ res₂ : ThetaResult)
    (h₁ : ΘRuns w res₁) (h₂ : ΘRuns w res₂) : res₁ = res₂ := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  have h₁' := Θ_fuel_mono_ok f₁ (max f₁ f₂) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h₁ (Nat.le_max_left f₁ f₂)
  have h₂' := Θ_fuel_mono_ok f₂ (max f₁ f₂) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h₂ (Nat.le_max_right f₁ f₂)
  rw [h₁'] at h₂'
  exact Except.ok.inj h₂'

/-- **Adequacy (completeness of `runΘ` for the veneer).** Any veneer result is
THE result of the seeded fuel-free driver. PROVED given both keystone halves +
the closed `runΘ_never_outOfFuel`: `.ok` clashes resolve by
determinism-at-max-fuel; a non-OOF `.error` contradicts `Θ_fuel_mono_error` at
max fuel; the OOF `.error` is killed by `runΘ_never_outOfFuel`. -/
theorem ΘRuns.runΘ_complete (w : NestedWorld) (res : ThetaResult) (he : w.e ≤ 1024)
    (h : ΘRuns w res) : runΘ w = .ok res := by
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

/-- **Totality up to semantic error.** PROVED sorry-free (no keystone needed):
under the depth envelope, every world either enters the veneer or the seeded
driver reports a genuine (non-fuel) error — pure case split on `runΘ w`, with
the OOF arm killed by the closed `runΘ_never_outOfFuel`. -/
theorem ΘRuns.total_of_adequate (w : NestedWorld) (he : w.e ≤ 1024) :
    (∃ res, ΘRuns w res) ∨ (∃ err, err ≠ .OutOfFuel ∧ runΘ w = .error err) := by
  cases hrun : runΘ w with
  | ok res => exact .inl ⟨res, ΘRuns.of_runΘ w res hrun⟩
  | error err =>
      refine .inr ⟨err, ?_, rfl⟩
      intro hOOF
      subst hOOF
      exact runΘ_never_outOfFuel w he hrun

end NestedEvmYul
