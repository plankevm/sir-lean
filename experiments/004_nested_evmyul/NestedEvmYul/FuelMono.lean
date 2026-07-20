import NestedEvmYul.NeverOutOfFuel
import NestedEvmYul.XLoop

/-!
# The fuel-monotonicity keystone (`res_mono`): fuel-decided results are stable
# under raising fuel

**The keystone pair `Θ_fuel_mono_ok` / `Θ_fuel_mono_error`** — "a fuel-decided
non-`OutOfFuel` result is reproduced at every larger fuel" — proved by a
six-layer mutual strong induction over `step`/`call`/`Θ`/`Ξ`/`Lambda`/`X`,
mirroring `gas_mono`'s architecture (NeverOutOfFuel.lean, Stage 1) with
result-*transport* predicates in place of gas bounds.

This statement was FALSE before the 2026-07-20 vendored patch: the
CREATE/CREATE2 `step` arms absorbed an inner `Lambda` `.error .OutOfFuel` into
an ordinary result tuple, so a low-fuel run could satisfy the premise yet
differ from every high-fuel run (see ThetaRuns.lean's keystone post-mortem for
the full history). Post-patch, EVERY layer propagates `OutOfFuel` honestly:

* `step`'s ~130 non-recursive arms route to the fuel-free shared `EvmYul.step`
  (`XLoop.step_fuel_irrelevant` — reused, not re-proved);
* the CALL-family arms propagate through `call`'s do-bind;
* the CREATE/CREATE2 arms match the inner `Lambda` with an honest
  `| .error e => .error e`;
* `Θ` and `Lambda` rethrow an inner `Ξ` `OutOfFuel` (their `e == .OutOfFuel`
  boolean guards) and absorb only NON-`OutOfFuel` errors — which the error half
  of the induction transports verbatim.

So on the keystone's own premise (the RESULT is not `.error .OutOfFuel`), every
recursive child's result is also non-`OutOfFuel` — the parent would have
propagated it otherwise — and transport composes layer by layer. That premise
discipline is what makes this theorem NOT collapse into `never_oof` (which
excludes one error under a `fuelBound` envelope but transports nothing): here
there is no envelope, no gas arithmetic, no depth accounting — the induction
carries results across fuels unconditionally in all arguments.

Proof-engineering note (why this costs ~700 lines, not the ~1500 the B3 study
priced): the study priced re-proving the Stage-1 *gas* helper family for
result-stability. Transport needs none of that arithmetic. Each layer helper
follows one recipe: rewrite the (single) fuel-dependent redex on both the
`fuel = m` hypothesis side and the `fuel = m'` goal side to the same value —
supplied by the child transport hypothesis — after which the two sides are the
SAME term and `exact h` closes. The old "X-loop offset bookkeeping" hard spot
dissolves for the same reason: `X (f+1)` runs `step f` and recurses at the
literal `f`, and the strong-induction IH transports both children at `f → f'`
for every `f ≤ f'` — no offset arithmetic ever arises.
-/

namespace NestedEvmYul.FuelMono

open EvmYul EvmYul.EVM
open NestedEvmYul.XLoop (step_fuel_irrelevant)
open EvmYul.EVM.NeverOutOfFuel (isCallCreate)

/-! ## 1. Generic transport bricks -/

/-- Generic CALL-family arm transport: `pop … >>= call >>= .ok (assemble …)`
reproduces a non-`OutOfFuel` result when the inner `call` does. The `popv` lift
and the `assemble` post-processing are fuel-free and shared; only `callOf` vs
`callOf'` differ (fuel `m` vs `m'`). Mirror of `noOOF_call_arm_body`'s shape,
consumed by the four CALL-family `step` arms below via defeq coercion. -/
theorem call_arm_res_mono {α : Type}
    (popv : Option α)
    (callOf callOf' : α → Except EVM.ExecutionException (UInt256 × EVM.State))
    (assemble : α → UInt256 × EVM.State → EVM.State)
    (hcall : ∀ x rc, callOf x = rc → rc ≠ .error .OutOfFuel → callOf' x = rc)
    (r : Except EVM.ExecutionException EVM.State)
    (h : (do
      let x ← Option.option (Except.error ExecutionException.StackUnderflow) Except.ok popv
      let p ← callOf x
      Except.ok (assemble x p) : Except EVM.ExecutionException EVM.State) = r)
    (hr : r ≠ .error .OutOfFuel) :
    (do
      let x ← Option.option (Except.error ExecutionException.StackUnderflow) Except.ok popv
      let p ← callOf' x
      Except.ok (assemble x p) : Except EVM.ExecutionException EVM.State) = r := by
  revert h
  simp only [bind, Except.bind]
  cases popv with
  | none => simp only [Option.option]; exact fun h => h
  | some x =>
    simp only [Option.option]
    cases hc : callOf x with
    | error e =>
      intro h
      have h' : Except.error e = r := h
      rw [hcall x (.error e) hc
        (fun hcon => hr (by rw [Except.error.inj hcon] at h'; exact h'.symm))]
      exact h
    | ok p =>
      intro h
      rw [hcall x (.ok p) hc (fun hcon => Except.noConfusion hcon)]
      exact h

/-! ## 2. `step` arm transport (the six recursive arms) -/

/-- `CALL`-arm `step` transport. -/
theorem step_call_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hcall : ∀ (g src rcpt t v v' io is oo os : UInt256) (perm : Bool) (s2 : EVM.State) rc,
      call m cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc →
      rc ≠ .error .OutOfFuel →
      call m' cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc)
    (h : step (m+1) cost (some (.System .CALL, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .CALL, a)) s = r :=
  call_arm_res_mono _ _ _ _
    (fun _ rc hc hnc => hcall _ _ _ _ _ _ _ _ _ _ _ _ rc hc hnc) r h hr

/-- `CALLCODE`-arm `step` transport. -/
theorem step_callcode_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hcall : ∀ (g src rcpt t v v' io is oo os : UInt256) (perm : Bool) (s2 : EVM.State) rc,
      call m cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc →
      rc ≠ .error .OutOfFuel →
      call m' cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc)
    (h : step (m+1) cost (some (.System .CALLCODE, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .CALLCODE, a)) s = r :=
  call_arm_res_mono _ _ _ _
    (fun _ rc hc hnc => hcall _ _ _ _ _ _ _ _ _ _ _ _ rc hc hnc) r h hr

/-- `DELEGATECALL`-arm `step` transport. -/
theorem step_delegatecall_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hcall : ∀ (g src rcpt t v v' io is oo os : UInt256) (perm : Bool) (s2 : EVM.State) rc,
      call m cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc →
      rc ≠ .error .OutOfFuel →
      call m' cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc)
    (h : step (m+1) cost (some (.System .DELEGATECALL, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .DELEGATECALL, a)) s = r :=
  call_arm_res_mono _ _ _ _
    (fun _ rc hc hnc => hcall _ _ _ _ _ _ _ _ _ _ _ _ rc hc hnc) r h hr

/-- `STATICCALL`-arm `step` transport. -/
theorem step_staticcall_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hcall : ∀ (g src rcpt t v v' io is oo os : UInt256) (perm : Bool) (s2 : EVM.State) rc,
      call m cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc →
      rc ≠ .error .OutOfFuel →
      call m' cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2 = rc)
    (h : step (m+1) cost (some (.System .STATICCALL, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .STATICCALL, a)) s = r :=
  call_arm_res_mono _ _ _ _
    (fun _ rc hc hnc => hcall _ _ _ _ _ _ _ _ _ _ _ _ rc hc hnc) r h hr

set_option maxHeartbeats 8000000 in
/-- `CREATE`-arm `step` transport. Post-patch the arm matches the inner
`Lambda` with an honest `| .error e => .error e`, so a non-`OutOfFuel` arm
result pins the inner `Lambda`'s result (`.ok` or a non-`OutOfFuel` error),
which `hΛ` reproduces at fuel `m'`; the rest of the arm (pop3, guards, the
`OutOfGass` post-check) is fuel-free and shared. -/
theorem step_create_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (gh : BlockHeader) (blocks : ProcessedBlocks) (σStar σ₀ : AccountMap)
            (Asub : Substate) (Iₐ Iₒ : AccountAddress) (g p v : UInt256) (i : ByteArray)
            (e : UInt256) (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool) rl,
      Lambda m bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w = rl →
      rl ≠ .error .OutOfFuel →
      Lambda m' bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w = rl)
    (h : step (m+1) cost (some (.System .CREATE, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .CREATE, a)) s = r := by
  dsimp only [EVM.step] at h ⊢
  simp only [pure, Except.pure, bind, Except.bind] at h ⊢
  -- pop3 (the split generalizes the scrutinee in the goal too, so the goal
  -- lands in the same arm)
  split at h
  · -- pop3 = some ⟨stack, μ₀, μ₁, μ₂⟩
    -- the `←`-bound if/Λ-match expression: error vs ok
    split at h
    · -- arm result is `.error e`; `e ≠ OutOfFuel` since `r = .error e`
      rename_i e heq2
      have hne : e ≠ EVM.ExecutionException.OutOfFuel := by
        intro hc; subst hc
        exact hr ((show Except.error EVM.ExecutionException.OutOfFuel = r from h).symm)
      split at heq2
      · -- nonce-overflow branch: `.ok … = .error e`, absurd
        exact absurd heq2 (fun hc => Except.noConfusion hc)
      · -- nonce fine: split the recursion guard
        rename_i hc1
        split at heq2
        · -- guard holds: the Λ match produced the error
          rename_i hguard
          split at heq2
          · exact absurd heq2 (fun hc => Except.noConfusion hc)
          · rename_i heq3
            rename_i e'
            obtain rfl : e' = e := Except.error.inj heq2
            rw [if_neg hc1, if_pos hguard,
              hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq3
                (fun hc => hne (Except.error.inj hc))]
            exact h
        · -- guard-else branch: `.ok … = .error e`, absurd
          exact absurd heq2 (fun hc => Except.noConfusion hc)
    · -- arm result is `.ok val`; the continuation is fuel-free and shared
      rename_i val heq2
      split at heq2
      · -- nonce-overflow branch
        rename_i hc1
        obtain rfl := Except.ok.inj heq2
        rw [if_pos hc1]
        exact h
      · -- nonce fine: split the recursion guard
        rename_i hc1
        split at heq2
        · -- guard holds: the Λ match produced the value
          rename_i hguard
          split at heq2
          · rename_i heq3
            obtain rfl := Except.ok.inj heq2
            rw [if_neg hc1, if_pos hguard,
              hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq3
                (fun hc => Except.noConfusion hc)]
            exact h
          · exact absurd heq2 (fun hc => Except.noConfusion hc)
        · -- guard-else branch
          rename_i hguard
          obtain rfl := Except.ok.inj heq2
          rw [if_neg hc1, if_neg hguard]
          exact h
  · -- pop3 = none: `.error .StackUnderflow` on both sides
    exact h

set_option maxHeartbeats 8000000 in
/-- `CREATE2`-arm `step` transport. As `step_create_res_mono` (the CREATE2 arm
differs only in `pop4`/the salt-derived `ζ`, both fuel-free). -/
theorem step_create2_res_mono (m m' cost : ℕ) (a) (s : EVM.State) (r)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (gh : BlockHeader) (blocks : ProcessedBlocks) (σStar σ₀ : AccountMap)
            (Asub : Substate) (Iₐ Iₒ : AccountAddress) (g p v : UInt256) (i : ByteArray)
            (e : UInt256) (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool) rl,
      Lambda m bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w = rl →
      rl ≠ .error .OutOfFuel →
      Lambda m' bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w = rl)
    (h : step (m+1) cost (some (.System .CREATE2, a)) s = r)
    (hr : r ≠ .error .OutOfFuel) :
    step (m'+1) cost (some (.System .CREATE2, a)) s = r := by
  dsimp only [EVM.step] at h ⊢
  simp only [pure, Except.pure, bind, Except.bind] at h ⊢
  split at h
  · -- pop4 = some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
    split at h
    · -- arm result is `.error e`
      rename_i e heq2
      have hne : e ≠ EVM.ExecutionException.OutOfFuel := by
        intro hc; subst hc
        exact hr ((show Except.error EVM.ExecutionException.OutOfFuel = r from h).symm)
      split at heq2
      · exact absurd heq2 (fun hc => Except.noConfusion hc)
      · rename_i hc1
        split at heq2
        · rename_i hguard
          split at heq2
          · exact absurd heq2 (fun hc => Except.noConfusion hc)
          · rename_i heq3
            rename_i e'
            obtain rfl : e' = e := Except.error.inj heq2
            rw [if_neg hc1, if_pos hguard,
              hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq3
                (fun hc => hne (Except.error.inj hc))]
            exact h
        · exact absurd heq2 (fun hc => Except.noConfusion hc)
    · -- arm result is `.ok val`
      rename_i val heq2
      split at heq2
      · rename_i hc1
        obtain rfl := Except.ok.inj heq2
        rw [if_pos hc1]
        exact h
      · rename_i hc1
        split at heq2
        · rename_i hguard
          split at heq2
          · rename_i heq3
            obtain rfl := Except.ok.inj heq2
            rw [if_neg hc1, if_pos hguard,
              hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq3
                (fun hc => Except.noConfusion hc)]
            exact h
          · exact absurd heq2 (fun hc => Except.noConfusion hc)
        · rename_i hguard
          obtain rfl := Except.ok.inj heq2
          rw [if_neg hc1, if_neg hguard]
          exact h
  · -- pop4 = none
    exact h

/-! ## 3. Per-layer transport lemmas (`call`/`Θ`/`Ξ`/`Lambda`/`X`) -/

set_option maxHeartbeats 2000000 in
/-- `call` layer transport: `call (m+1)` recurses into `Θ m` under the
balance/depth cover `if`; both the cover condition and the result
post-processing are fuel-free and shared. -/
theorem call_res_mono_succ (m m' cost : ℕ) (bvh : List ByteArray)
    (gas source recipient t value value' io is oo os : UInt256) (perm : Bool)
    (ev : EVM.State) (r)
    (hΘ : ∀ (bvh' : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
            (s o rr : AccountAddress) (c : ToExecute) (g p v v'' : UInt256) (d : ByteArray)
            (e : Nat) (Hd : BlockHeader) (w : Bool) rΘ,
      Θ m bvh' cA gh blocks σ σ₀ A s o rr c g p v v'' d e Hd w = rΘ →
      rΘ ≠ .error .OutOfFuel →
      Θ m' bvh' cA gh blocks σ σ₀ A s o rr c g p v v'' d e Hd w = rΘ)
    (h : call (m+1) cost bvh gas source recipient t value value' io is oo os perm ev = r)
    (hr : r ≠ .error .OutOfFuel) :
    call (m'+1) cost bvh gas source recipient t value value' io is oo os perm ev = r := by
  simp only [call, bind, Except.bind, pure, Except.pure] at h ⊢
  split at h
  · -- cover branch: the result comes from `Θ m`
    rename_i hcond
    rw [if_pos hcond]
    split at h
    · -- `Θ m … = .error err`, propagated
      rename_i heq
      rename_i err
      have h' : Except.error err = r := h
      rw [hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq
        (fun hc => hr (by rw [Except.error.inj hc] at h'; exact h'.symm))]
      exact h
    · -- `Θ m … = .ok v`
      rename_i heq
      rw [hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq
        (fun hc => Except.noConfusion hc)]
      exact h
  · -- else branch: fuel-free on both sides
    rename_i hcond
    rw [if_neg hcond]
    exact h

set_option maxHeartbeats 2000000 in
/-- `Θ` layer transport, `.Code` arm: `Θ (m+1)` recurses into `Ξ m`; an inner
`OutOfFuel` is rethrown (excluded by the premise), a non-`OutOfFuel` inner
error is absorbed into a fuel-free result tuple that the error half of `hΞ`
reproduces verbatim, and the transfer preamble/`σ''`-rollback post-processing
are fuel-free and shared. -/
theorem Θ_code_res_mono_succ (m m' : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o rr : AccountAddress) (code : ByteArray)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool) (r)
    (hΞ : ∀ (cA' : Batteries.RBSet AccountAddress compare) (gh' : BlockHeader)
            (blocks' : ProcessedBlocks) (σ' σ₀' : AccountMap) (g' : UInt256) (A' : Substate)
            (I : ExecutionEnv) rΞ,
      Ξ m cA' gh' blocks' σ' σ₀' g' A' I = rΞ → rΞ ≠ .error .OutOfFuel →
      Ξ m' cA' gh' blocks' σ' σ₀' g' A' I = rΞ)
    (h : Θ (m+1) bvh cA gh blocks σ σ₀ A s o rr (.Code code) g p v v' d e Hd w = r)
    (hr : r ≠ .error .OutOfFuel) :
    Θ (m'+1) bvh cA gh blocks σ σ₀ A s o rr (.Code code) g p v v' d e Hd w = r := by
  simp only [Θ, bind, Except.bind, pure, Except.pure] at h ⊢
  set I : ExecutionEnv := _ with hI
  set σ₁ : AccountMap := _ with hσ₁
  cases hΞeq : Ξ m cA gh blocks σ₁ σ₀ g A I with
  | error ee =>
    rw [hΞeq] at h
    have hee : ee ≠ EVM.ExecutionException.OutOfFuel := by
      intro hc; subst hc
      exact hr ((show Except.error EVM.ExecutionException.OutOfFuel = r from h).symm)
    rw [hΞ _ _ _ _ _ _ _ _ _ hΞeq (fun hc => hee (Except.error.inj hc))]
    exact h
  | ok xr =>
    rw [hΞeq] at h
    rw [hΞ _ _ _ _ _ _ _ _ _ hΞeq (fun hc => Except.noConfusion hc)]
    exact h

/-- `Θ` layer, `.Precompiled` arm: fuel never reaches the 10 fuel-free
precompile interpreters (nor the `default` fallthrough), so `Θ` at any two
positive fuels is the same term — by `rfl`. -/
theorem Θ_precompiled_fuel_irrelevant (m m' : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o rr : AccountAddress) (pc : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool) :
    Θ (m+1) bvh cA gh blocks σ σ₀ A s o rr (.Precompiled pc) g p v v' d e Hd w
      = Θ (m'+1) bvh cA gh blocks σ σ₀ A s o rr (.Precompiled pc) g p v v' d e Hd w := rfl

set_option maxHeartbeats 2000000 in
/-- `Ξ` layer transport: `Ξ (m+1)` runs `X m` on the freshly-seeded state; the
seeding and the `success`/`revert` post-processing are fuel-free and shared. -/
theorem Ξ_res_mono_succ (m m' : ℕ)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (r)
    (hX : ∀ (vj : Array UInt256) (s : EVM.State) rx,
      X m vj s = rx → rx ≠ .error .OutOfFuel → X m' vj s = rx)
    (h : Ξ (m+1) cA gh blocks σ σ₀ g A I = r)
    (hr : r ≠ .error .OutOfFuel) :
    Ξ (m'+1) cA gh blocks σ σ₀ g A I = r := by
  unfold Ξ at h ⊢
  simp only [bind, Except.bind] at h ⊢
  -- single-line: mathlib-4.22 `set` cannot parse a multi-line structure literal
  set s0 : EVM.State := { (default : EVM.State) with accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A, createdAccounts := cA, gasAvailable := g, blocks := blocks, genesisBlockHeader := gh } with hs0
  cases hXeq : X m (D_J I.code ⟨0⟩) s0 with
  | error e =>
    rw [hXeq] at h
    have h' : Except.error e = r := h
    rw [hX _ _ _ hXeq
      (fun hc => hr (by rw [Except.error.inj hc] at h'; exact h'.symm))]
    exact h
  | ok xr =>
    rw [hXeq] at h
    rw [hX _ _ _ hXeq (fun hc => Except.noConfusion hc)]
    exact h

/-- File-local twin of `Semantics.lean`'s `local instance : MonadLift Option
(Except EVM.ExecutionException)` (the vendored instance is `local`, hence
invisible here; this definitionally identical twin lets `Lambda_res_mono_succ`
*spell* the `liftM` redex that `Lambda`'s `L_A` bind bakes in — `rw` matches
the two instance constants up to instance-transparency unfolding). -/
local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

set_option maxHeartbeats 4000000 in
/-- `Lambda` layer transport: `Lambda (m+1)` recurses into `Ξ m` on the
initialised creation frame; the `L_A` address lift, the EIP-7610 occupancy
swap, and all three result branches are fuel-free given the inner `Ξ` result
(an inner `OutOfFuel` is rethrown — excluded by the premise). -/
theorem Lambda_res_mono_succ (m m' : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress) (g p v : UInt256)
    (i : ByteArray) (e : UInt256) (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool) (r)
    (hΞ : ∀ (cA' : Batteries.RBSet AccountAddress compare) (gh' : BlockHeader)
            (blocks' : ProcessedBlocks) (σ' σ₀' : AccountMap) (g' : UInt256) (A' : Substate)
            (I : ExecutionEnv) rΞ,
      Ξ m cA' gh' blocks' σ' σ₀' g' A' I = rΞ → rΞ ≠ .error .OutOfFuel →
      Ξ m' cA' gh' blocks' σ' σ₀' g' A' I = rΞ)
    (h : Lambda (m+1) bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = r)
    (hr : r ≠ .error .OutOfFuel) :
    Lambda (m'+1) bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = r := by
  simp only [Lambda, bind, Except.bind] at h ⊢
  cases hla : Lambda.L_A s (Option.option (⟨0⟩ : UInt256) (·.nonce) (σ.find? s) - ⟨1⟩) ζ i with
  | none =>
    rw [hla] at h
    exact h
  | some lₐ =>
    rw [hla] at h
    rw [show (liftM (some lₐ) : Except EVM.ExecutionException ByteArray) = .ok lₐ from rfl] at h ⊢
    dsimp only at h ⊢
    split at h
    · -- inner `Ξ m` errored with `ee`; `OutOfFuel` is rethrown, others absorbed
      rename_i ee heq
      have hee : ee ≠ EVM.ExecutionException.OutOfFuel := by
        intro hc; subst hc
        exact hr ((show Except.error EVM.ExecutionException.OutOfFuel = r from h).symm)
      rw [hΞ _ _ _ _ _ _ _ _ _ heq (fun hc => hee (Except.error.inj hc))]
      exact h
    · -- inner revert
      rename_i g' oo heq
      rw [hΞ _ _ _ _ _ _ _ _ _ heq (fun hc => Except.noConfusion hc)]
      exact h
    · -- inner success
      rename_i tup ret heq
      rw [hΞ _ _ _ _ _ _ _ _ _ heq (fun hc => Except.noConfusion hc)]
      exact h

set_option maxHeartbeats 4000000 in
/-- `X` layer transport: `X (m+1)` decodes (fuel-free), gates through `Z`
(fuel-free), runs `step m`, and either halts (fuel-free `H` post-processing)
or loops as `X m` on the step successor — both children transported by the
hypotheses. This is the layer the old post-mortem priced for "offset
bookkeeping"; with transport hypotheses at every `m → m'` the literal-`f`
recursion needs none. -/
theorem X_res_mono_succ (m m' : ℕ) (vj : Array UInt256) (s : EVM.State) (r)
    (hstep : ∀ (cost : ℕ) (w : Operation) (arg) (s₁ : EVM.State) rs,
      step m cost (some (w, arg)) s₁ = rs → rs ≠ .error .OutOfFuel →
      step m' cost (some (w, arg)) s₁ = rs)
    (hX : ∀ (s₁ : EVM.State) rx,
      X m vj s₁ = rx → rx ≠ .error .OutOfFuel → X m' vj s₁ = rx)
    (h : X (m+1) vj s = r)
    (hr : r ≠ .error .OutOfFuel) :
    X (m'+1) vj s = r := by
  unfold X at h ⊢
  simp only [bind, Except.bind] at h ⊢
  cases hdec : decode s.toState.executionEnv.code s.pc |>.getD (.STOP, .none) with
  | mk w arg =>
    rw [hdec] at h
    simp only [] at h ⊢
    cases hZ : Z vj w s with
    | error e =>
      rw [hZ] at h
      exact h
    | ok sc =>
      obtain ⟨s₁, cost₂⟩ := sc
      rw [hZ] at h
      simp only [] at h ⊢
      cases hs : step m cost₂ (some (w, arg)) s₁ with
      | error e =>
        rw [hs] at h
        have h' : Except.error e = r := h
        rw [hstep _ _ _ _ _ hs
          (fun hc => hr (by rw [Except.error.inj hc] at h'; exact h'.symm))]
        exact h
      | ok ev' =>
        rw [hs] at h
        rw [hstep _ _ _ _ _ hs (fun hc => Except.noConfusion hc)]
        simp only [] at h ⊢
        cases hH : H ev'.toMachineState w with
        | none =>
          rw [hH] at h
          simp only [] at h ⊢
          exact hX _ _ h hr
        | some o =>
          rw [hH] at h
          exact h

/-! ## 4. Six-layer mutual induction and the `Θ` keystone -/

/-- Exact-result fuel transport for `step` at one source fuel. -/
def step_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' cost : ℕ) (w : Operation) (arg) (s : EVM.State) r,
    n ≤ n' → step n cost (some (w, arg)) s = r → r ≠ .error .OutOfFuel →
    step n' cost (some (w, arg)) s = r

/-- Exact-result fuel transport for `call` at one source fuel. -/
def call_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' cost : ℕ) (bvh : List ByteArray)
    (gas source recipient t value value' io is oo os : UInt256) (perm : Bool)
    (s : EVM.State) r,
    n ≤ n' →
    call n cost bvh gas source recipient t value value' io is oo os perm s = r →
    r ≠ .error .OutOfFuel →
    call n' cost bvh gas source recipient t value value' io is oo os perm s = r

/-- Exact-result fuel transport for `Θ` at one source fuel. -/
def Θ_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o rr : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool) r,
    n ≤ n' → Θ n bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = r →
    r ≠ .error .OutOfFuel →
    Θ n' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = r

/-- Exact-result fuel transport for `Ξ` at one source fuel. -/
def Ξ_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' : ℕ) (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) r,
    n ≤ n' → Ξ n cA gh blocks σ σ₀ g A I = r → r ≠ .error .OutOfFuel →
    Ξ n' cA gh blocks σ σ₀ g A I = r

/-- Exact-result fuel transport for `Lambda` at one source fuel. -/
def Lambda_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o : AccountAddress) (g p v : UInt256) (i : ByteArray) (e : UInt256)
    (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool) r,
    n ≤ n' → Lambda n bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = r →
    r ≠ .error .OutOfFuel →
    Lambda n' bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = r

/-- Exact-result fuel transport for `X` at one source fuel. -/
def X_res_mono_at (n : ℕ) : Prop :=
  ∀ (n' : ℕ) (vj : Array UInt256) (s : EVM.State) r,
    n ≤ n' → X n vj s = r → r ≠ .error .OutOfFuel → X n' vj s = r

set_option maxHeartbeats 8000000 in
/-- Exact non-`OutOfFuel` results are stable under increasing fuel, simultaneously
for all six recursively connected semantic layers. -/
theorem res_mono : ∀ n,
    step_res_mono_at n ∧ call_res_mono_at n ∧ Θ_res_mono_at n ∧
    Ξ_res_mono_at n ∧ Lambda_res_mono_at n ∧ X_res_mono_at n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have ihstep : ∀ m, m < n → step_res_mono_at m := fun m hm => (ih m hm).1
    have ihcall : ∀ m, m < n → call_res_mono_at m := fun m hm => (ih m hm).2.1
    have ihΘ : ∀ m, m < n → Θ_res_mono_at m := fun m hm => (ih m hm).2.2.1
    have ihΞ : ∀ m, m < n → Ξ_res_mono_at m := fun m hm => (ih m hm).2.2.2.1
    have ihΛ : ∀ m, m < n → Lambda_res_mono_at m := fun m hm => (ih m hm).2.2.2.2.1
    have ihX : ∀ m, m < n → X_res_mono_at m := fun m hm => (ih m hm).2.2.2.2.2
    have hstep : step_res_mono_at n := by
      intro n' cost w arg s r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [EVM.step] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        have hmm : m ≤ m' := by omega
        by_cases hcc : isCallCreate w
        · unfold isCallCreate at hcc
          rcases hcc with rfl | rfl | rfl | rfl | rfl | rfl
          · exact step_create_res_mono m m' cost arg s r
              (fun bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w rl hΛ hrl =>
                ihΛ m (by omega) m' bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w
                  rl hmm hΛ hrl)
              h hr
          · exact step_create2_res_mono m m' cost arg s r
              (fun bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w rl hΛ hrl =>
                ihΛ m (by omega) m' bvh cA gh blocks σStar σ₀ Asub Iₐ Iₒ g p v i e ζ Hd w
                  rl hmm hΛ hrl)
              h hr
          · exact step_call_res_mono m m' cost arg s r
              (fun g src rcpt t v v' io is oo os perm s2 rl hc hrc =>
                ihcall m (by omega) m' cost s.executionEnv.blobVersionedHashes
                  g src rcpt t v v' io is oo os perm s2 rl hmm hc hrc)
              h hr
          · exact step_callcode_res_mono m m' cost arg s r
              (fun g src rcpt t v v' io is oo os perm s2 rl hc hrc =>
                ihcall m (by omega) m' cost s.executionEnv.blobVersionedHashes
                  g src rcpt t v v' io is oo os perm s2 rl hmm hc hrc)
              h hr
          · exact step_delegatecall_res_mono m m' cost arg s r
              (fun g src rcpt t v v' io is oo os perm s2 rl hc hrc =>
                ihcall m (by omega) m' cost s.executionEnv.blobVersionedHashes
                  g src rcpt t v v' io is oo os perm s2 rl hmm hc hrc)
              h hr
          · exact step_staticcall_res_mono m m' cost arg s r
              (fun g src rcpt t v v' io is oo os perm s2 rl hc hrc =>
                ihcall m (by omega) m' cost s.executionEnv.blobVersionedHashes
                  g src rcpt t v v' io is oo os perm s2 rl hmm hc hrc)
              h hr
        · have hirr := step_fuel_irrelevant w (f := m) (f' := m')
              (cost := cost) (arg := arg) (s := s)
              (by
                cases w with
                | StopArith o => cases o <;> rfl
                | CompBit o => cases o <;> rfl
                | Keccak o =>
                    cases o
                    rfl
                | Env o => cases o <;> rfl
                | Block o => cases o <;> rfl
                | StackMemFlow o => cases o <;> rfl
                | Push o => cases o <;> rfl
                | Dup o => cases o <;> rfl
                | Exchange o => cases o <;> rfl
                | Log o => cases o <;> exact rfl
                | System o =>
                    cases o <;> simp_all [isCallCreate, Operation.isCall])
              (by
                cases w with
                | StopArith o => cases o <;> rfl
                | CompBit o => cases o <;> rfl
                | Keccak o =>
                    cases o
                    rfl
                | Env o => cases o <;> rfl
                | Block o => cases o <;> rfl
                | StackMemFlow o => cases o <;> rfl
                | Push o => cases o <;> rfl
                | Dup o => cases o <;> rfl
                | Exchange o => cases o <;> rfl
                | Log o => cases o <;> exact rfl
                | System o =>
                    cases o <;> simp_all [isCallCreate, Operation.isCreate])
          exact hirr.symm.trans h
    have hcall : call_res_mono_at n := by
      intro n' cost bvh gas source recipient t value value' io is oo os perm s r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [call] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        exact call_res_mono_succ m m' cost bvh gas source recipient t value value' io is oo os
          perm s r
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rΘ hΘ hrΘ =>
            ihΘ m (by omega) m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rΘ
              (by omega) hΘ hrΘ)
          h hr
    have hΘ : Θ_res_mono_at n := by
      intro n' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [Θ] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        cases c with
        | Code code =>
          exact Θ_code_res_mono_succ m m' bvh cA gh blocks σ σ₀ A s o rr code g p v v' d e Hd w r
            (fun _ _ _ _ _ _ _ _ rΞ hΞ hrΞ =>
              ihΞ m (by omega) m' _ _ _ _ _ _ _ _ rΞ (by omega) hΞ hrΞ)
            h hr
        | Precompiled pc =>
          rw [← Θ_precompiled_fuel_irrelevant m m' bvh cA gh blocks σ σ₀ A s o rr pc g p v v' d e Hd w]
          exact h
    have hΞ : Ξ_res_mono_at n := by
      intro n' cA gh blocks σ σ₀ g A I r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [Ξ] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        exact Ξ_res_mono_succ m m' cA gh blocks σ σ₀ g A I r
          (fun _ _ rx hX hrX => ihX m (by omega) m' _ _ rx (by omega) hX hrX)
          h hr
    have hΛ : Lambda_res_mono_at n := by
      intro n' bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [Lambda] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        exact Lambda_res_mono_succ m m' bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w r
          (fun _ _ _ _ _ _ _ _ rΞ hΞ hrΞ =>
            ihΞ m (by omega) m' _ _ _ _ _ _ _ _ rΞ (by omega) hΞ hrΞ)
          h hr
    have hX : X_res_mono_at n := by
      intro n' vj s r hle h hr
      cases n with
      | zero =>
        have : r = .error .OutOfFuel := by simpa [X] using h.symm
        exact (hr this).elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
        exact X_res_mono_succ m m' vj s r
          (fun _ _ _ _ rs hs hrs => ihstep m (by omega) m' _ _ _ _ rs (by omega) hs hrs)
          (fun _ rx hX hrX => ihX m (by omega) m' _ _ rx (by omega) hX hrX)
          h hr
    exact ⟨hstep, hcall, hΘ, hΞ, hΛ, hX⟩

/-- **Fuel-monotonicity keystone, success half.** A successful `Θ` result at
fuel `fuel` is reproduced exactly at every `fuel' ≥ fuel`. -/
theorem Θ_fuel_mono_ok (fuel fuel' : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o rr : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool) res
    (hle : fuel ≤ fuel')
    (h : Θ fuel bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = .ok res) :
    Θ fuel' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = .ok res :=
  (res_mono fuel).2.2.1 fuel' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w
    (.ok res) hle h (fun hc => Except.noConfusion hc)

/-- **Fuel-monotonicity keystone, semantic-error half.** A non-`OutOfFuel`
`Θ` error at fuel `fuel` is reproduced exactly at every `fuel' ≥ fuel`. -/
theorem Θ_fuel_mono_error (fuel fuel' : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o rr : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (err : EVM.ExecutionException) (herr : err ≠ .OutOfFuel) (hle : fuel ≤ fuel')
    (h : Θ fuel bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = .error err) :
    Θ fuel' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w = .error err :=
  (res_mono fuel).2.2.1 fuel' bvh cA gh blocks σ σ₀ A s o rr c g p v v' d e Hd w
    (.error err) hle h (fun hc => herr (Except.error.inj hc))

end NestedEvmYul.FuelMono
