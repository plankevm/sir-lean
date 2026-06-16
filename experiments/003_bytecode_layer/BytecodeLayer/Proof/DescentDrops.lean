import BytecodeLayer.Reasoning.NeverOutOfFuel
import BytecodeLayer.Reasoning.StepGas
import BytecodeLayer.Proof.CallFree

/-!
# Proof — the descent/fallback gas arithmetic (`DescentDrops`)

This file discharges the one remaining hypothesis of the general
`never-out-of-fuel` theorem: `DescentDrops` (the CALL/CREATE *descent* and
`System`-`.next`-*fallback* gas inequalities, obligations 3/4/5 in
`Reasoning/NeverOutOfFuel.lean`). With it proven, the boundary theorem

  `messageCall_never_outOfFuel (p : CallParams) : messageCall p ≠ .error .OutOfFuel`

is **unconditional** — no `DescentDrops`, no `Frame`/fuel in the statement.

## The arithmetic, generously

The descent semantics (`callArm`/`createArm`, `Evm/Semantics/System.lean`) charge
the parent `gasCap + extraCost` *before* suspending and forward the child
`childGas = gasCap (+ Gcallstipend when value ≠ 0)`. The forwarded gas is exactly
conserved against the parent's saved gas, and the call's *own* cost (`extraCost`,
≥ `Gcoldaccountaccess`/`Gwarmaccess` ≥ 100, or ≥ `Gcallvalue` = 9000 with value)
strictly dominates the tiny `+2` measure slack and the `Gcallstipend` (2300)
added to the child. No tight arithmetic is needed — only "the call's own cost is
a positive constant bigger than 2 (resp. 2302)."
-/

namespace BytecodeLayer.Proof
open Evm
open Evm.Operation
open GasConstants

/-! ## `extraCost` lower bounds (the call's own non-forwarded cost) -/

/-- The non-value, non-new-account part of `callExtraCost` is at least `100`
(`accessCost ≥ Gwarmaccess = 100`). -/
theorem callExtraCost_ge_100 (t r : AccountAddress) (val : UInt256)
    (accounts : AccountMap) (substate : Substate) :
    100 ≤ callExtraCost t r val accounts substate := by
  unfold callExtraCost
  have := accessCost_pos t substate
  have h2 : 100 ≤ accessCost t substate := by
    unfold accessCost Gwarmaccess Gcoldaccountaccess; split <;> omega
  omega

/-- For value-carrying calls (`val ≠ 0`), `callExtraCost ≥ Gcallvalue = 9000`
(the `transferCost` is `Gcallvalue`). -/
theorem callExtraCost_ge_9000_of_val (t r : AccountAddress) (val : UInt256)
    (accounts : AccountMap) (substate : Substate) (hval : val ≠ 0) :
    9000 ≤ callExtraCost t r val accounts substate := by
  unfold callExtraCost transferCost
  have hbeq : (val == (0 : UInt256)) = false := by
    rw [Bool.eq_false_iff]; intro h
    exact hval ((UInt256.beq_iff_eq _ _).mp h)
  have hne : (val != (0 : UInt256)) = true := by
    simp only [bne, hbeq, Bool.not_false]
  simp only [hne, if_true]
  unfold Gcallvalue
  omega

/-! ## `callArm` inversion — gas relations on the descent / fallback

`callArm` (a) memory-charges (only lowers gas), (b) computes
`gasCap`/`extraCost`/`childGas` from the charged exec, (c) charges the parent
`gasCap + extraCost` (the suspended `pending.frame.exec`), then either suspends
into `.needsCall { gas := .ofNat childGas } pending` or, on the funds/depth
fallback, returns `.next (resumeAfterCall failed pending).exec`. We read off the
gas relations both arms force. -/

/-- The pivotal `gasCap + childGas` accounting fact: in `callArm`, the parent is
charged `gasCap + extraCost` and the child receives `childGas ≤ gasCap +
Gcallstipend`. So `childGas + (charged parent gas) + 2 ≤ (pre-charge gas)`
provided `extraCost` covers the slack — which it does (≥ 100 always, ≥ 9000 with
value). This is the heart of conjuncts (4)/(5a). -/
theorem childGas_le_of_extraCost
    (codeAddress recipient : AccountAddress) (value gas : UInt256)
    (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) :
    let gasCap := callGasCap codeAddress recipient value gas accounts gasAvailable substate
    let extraCost := callExtraCost codeAddress recipient value accounts substate
    let childGas := if value = 0 then gasCap else gasCap + Gcallstipend
    childGas + 2 ≤ gasCap + extraCost := by
  intro gasCap extraCost childGas
  by_cases hv : value = 0
  · have hext : 100 ≤ extraCost := callExtraCost_ge_100 _ _ _ _ _
    show (if value = 0 then gasCap else gasCap + Gcallstipend) + 2 ≤ gasCap + extraCost
    rw [if_pos hv]; omega
  · have hext : 9000 ≤ extraCost := callExtraCost_ge_9000_of_val _ _ _ _ _ hv
    show (if value = 0 then gasCap else gasCap + Gcallstipend) + 2 ≤ gasCap + extraCost
    rw [if_neg hv]; show gasCap + Gcallstipend + 2 ≤ gasCap + extraCost
    unfold Gcallstipend; omega

/-- **`callArm` `.needsCall` inversion (gas).** When `callArm` suspends into a
child, the child's forwarded gas plus the suspended parent's saved gas plus `2`
do not exceed the parent's pre-`callArm` gas. (Generous: the call's `extraCost`
dominates both the `+2` slack and any value stipend handed to the child.) -/
theorem callArm_needsCall_gas
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {p : CallParams} {pd : PendingCall}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.needsCall p pd)) :
    p.gas.toNat + pd.frame.exec.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat := by
  rw [callArm] at h
  -- mem-charge step
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp [bind, Except.bind] at h
    | ok e1 =>
      rw [he1] at h
      simp only [bind, Except.bind] at h
      -- abbreviations as in callArm (computed from e1)
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp [bind, Except.bind] at h
      | ok e2 =>
        rw [he2] at h
        simp only [bind, Except.bind] at h
        -- now `h` is the final `if … then .ok (.needsCall …) else .ok (.next …)`
        split at h
        · -- needsCall branch
          simp only [Except.ok.injEq, Signal.needsCall.injEq] at h
          obtain ⟨hp, hpd⟩ := h
          -- read off p.gas and pd.frame.exec
          subst hp hpd
          -- p.gas = .ofNat childGas ; pd.frame.exec = e2
          have hmemle : e1.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le he1
          have he2gas : e2.gasAvailable.toNat = e1.gasAvailable.toNat - (gasCap + extraCost)
              ∧ gasCap + extraCost ≤ e1.gasAvailable.toNat := by
            unfold charge at he2
            split at he2
            · simp at he2
            · rename_i hge
              injection he2 with he2; subst he2
              refine ⟨?_, Nat.not_lt.mp hge⟩
              dsimp only
              rw [toNat_sub_ofNat _ _ (Nat.not_lt.mp hge)
                    (Nat.lt_of_le_of_lt (Nat.not_lt.mp hge) e1.gasAvailable.toNat_lt)]
          obtain ⟨he2eq, he2le⟩ := he2gas
          -- childGas + 2 ≤ gasCap + extraCost
          have hslack : childGas + 2 ≤ gasCap + extraCost := by
            have := childGas_le_of_extraCost ca rc value gas e1.accounts e1.gasAvailable e1.substate
            simpa only [← hextra, ← hgcap, ← hcg] using this
          -- childGas < 2^64 (so `.ofNat childGas` round-trips)
          have hcgub : childGas < 2 ^ 64 := by
            have : gasCap + extraCost < 2 ^ 64 :=
              Nat.lt_of_le_of_lt he2le e1.gasAvailable.toNat_lt
            omega
          have hpgas : (UInt64.ofNat childGas).toNat = childGas := by
            rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hcgub
          -- goal
          show (UInt64.ofNat childGas).toNat + e2.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat
          rw [hpgas, he2eq]
          omega
        · -- next (fallback) branch: contradiction, not a needsCall
          simp only [Except.ok.injEq] at h
          exact absurd h (by simp)

/-- **`callArm` `.next` (fallback) inversion (gas).** On the funds/depth
fallback `callArm` resumes the parent immediately with the (failed) forwarded
gas; the resumed parent's gas is *strictly* below the pre-`callArm` gas, because
the call still paid its own `extraCost ≥ 2`. -/
theorem callArm_next_gas
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {exec' : ExecutionState}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [callArm] at h
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp [bind, Except.bind] at h
    | ok e1 =>
      rw [he1] at h
      simp only [bind, Except.bind] at h
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp [bind, Except.bind] at h
      | ok e2 =>
        rw [he2] at h
        simp only [bind, Except.bind] at h
        split at h
        · -- needsCall branch: contradiction
          simp only [Except.ok.injEq] at h
          exact absurd h (by simp)
        · -- next (fallback) branch
          simp only [Except.ok.injEq, Signal.next.injEq] at h
          subst h
          have hmemle : e1.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le he1
          have he2gas : e2.gasAvailable.toNat = e1.gasAvailable.toNat - (gasCap + extraCost)
              ∧ gasCap + extraCost ≤ e1.gasAvailable.toNat := by
            unfold charge at he2
            split at he2
            · simp at he2
            · rename_i hge
              injection he2 with he2; subst he2
              refine ⟨?_, Nat.not_lt.mp hge⟩
              dsimp only
              rw [toNat_sub_ofNat _ _ (Nat.not_lt.mp hge)
                    (Nat.lt_of_le_of_lt (Nat.not_lt.mp hge) e1.gasAvailable.toNat_lt)]
          obtain ⟨he2eq, he2le⟩ := he2gas
          have hslack : childGas + 2 ≤ gasCap + extraCost := by
            have := childGas_le_of_extraCost ca rc value gas e1.accounts e1.gasAvailable e1.substate
            simpa only [← hextra, ← hgcap, ← hcg] using this
          have hcgub : childGas < 2 ^ 64 := by
            have : gasCap + extraCost < 2 ^ 64 :=
              Nat.lt_of_le_of_lt he2le e1.gasAvailable.toNat_lt
            omega
          -- the failed result the fallback resumes with
          set failed : CallResult :=
            { createdAccounts := e2.createdAccounts
              accounts := e1.accounts
              gasRemaining := .ofNat childGas
              substate := (e2.addAccessedAccount ca).substate
              success := false
              output := .empty } with hfailed
          set pending : PendingCall :=
            { frame := { kind := fr.kind, validJumps := fr.validJumps, exec := e2 }
              stack := stack
              callerAccounts := e1.accounts
              value := value
              inOffset := inOffset.toUInt64
              inSize := inSize.toUInt64
              outOffset := outOffset.toUInt64
              outSize := outSize.toUInt64 } with hpending
          -- resumeAfterCall failed pending gives gas ≤ savedParent + childRemaining
          have hres := resumeAfterCall_gas_le failed pending
          have hfgas : failed.gasRemaining.toNat = childGas := by
            show (UInt64.ofNat childGas).toNat = childGas
            rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hcgub
          have hpdgas : pending.frame.exec.gasAvailable.toNat = e2.gasAvailable.toNat := rfl
          -- assemble
          rw [hfgas, hpdgas] at hres
          rw [he2eq] at hres
          omega

/-! ## `createArm` inversion — gas relations on the descent / fallback

`createArm` is entered *after* `systemOp` has already charged `createCost`/`
create2Cost` (the create's own cost). Inside `createArm` there is **no further
charge**: the parent's saved frame keeps the full charged gas `g`, and either

* `.next` (nonce-overflow or failed guard): resumes the parent via
  `resumeAfterCreate failed pending`, whose `failed.gasRemaining =
  allButOneSixtyFourth g`. Because `resumeAfterCreate` sets the parent's gas to
  `g - allButOneSixtyFourth g + gasRemaining = g/64 + (g - g/64) = g`, the
  resumed gas is exactly `g` (modulo UInt64 wrap, which can only lower it). So
  `createArm`'s `.next` gives `exec'.gas.toNat ≤ exec.gas.toNat`; the strict
  drop for conjunct (3) comes from the `createCost` charge in `systemOp`.

* `.needsCreate` into a child: the child receives `allButOneSixtyFourth g` **and**
  the parent's saved frame still holds the full `g`. The forwarded child gas is
  therefore *duplicated* against the saved parent gas until `resumeAfterCreate`
  reconciles it on delivery. This is the obstruction to conjunct (4') — see the
  module note at the bottom of this file.
-/

/-- The `.next` (fallback) branch of `createArm` resumes the parent with gas
`≤ exec.gas` (in fact `= exec.gas` modulo wrap): the `failed` result carries
`allButOneSixtyFourth exec.gas` and `resumeAfterCreate` re-adds it to the
`1/64` the parent kept. -/
theorem createArm_next_gas
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := by
  -- Both `.next` arms resume `resumeAfterCreate failed pending` with the same
  -- `failed` (gasRemaining = allButOneSixtyFourth exec.gas) and `pending`
  -- (frame.exec = exec).  We extract that uniformly.
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- the `failed` CreateResult and `pending` are the let-bound values
  set g := exec.gasAvailable.toNat with hg
  -- A helper: any `resumeAfterCreate failed pending = .ok f` resumes with gas ≤ g.
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth g)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize :=
            (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size } = .ok f →
      f.exec.gasAvailable.toNat ≤ g := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp [throw, throwThe, MonadExceptOf.throw])
    · simp only [Except.ok.injEq] at hf
      subst hf
      simp only [gasNat_replaceStackAndIncrPC]
      -- gas := .ofNat (savedGas - allButOneSixtyFourth savedGas + remaining)
      -- savedGas = g, remaining = allButOneSixtyFourth g
      rw [UInt64.toNat_ofNat']
      refine le_trans (Nat.mod_le _ _) ?_
      -- g - allButOneSixtyFourth g + allButOneSixtyFourth g ≤ g  (with the .toNat of .ofNat)
      have hofNat : (UInt64.ofNat (allButOneSixtyFourth g)).toNat ≤ allButOneSixtyFourth g := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _
      have habf : allButOneSixtyFourth g ≤ g := by unfold allButOneSixtyFourth; omega
      -- the saved frame's gas is `exec.gasAvailable`, so .toNat = g
      show (exec.gasAvailable.toNat - allButOneSixtyFourth exec.gasAvailable.toNat
              + (UInt64.ofNat (allButOneSixtyFourth g)).toNat) ≤ g
      rw [← hg]
      omega
  -- Now case the createArm branching to expose the `.next` arms.
  split at h
  · -- nonce overflow: `.next (resumeAfterCreate failed pending).exec`
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp [bind, Except.bind] at h
    | ok f =>
      intro h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · -- needsCreate branch: not a `.next`
      simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp [bind, Except.bind] at h
      | ok f =>
        intro h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-! ## Precompile gas — a precompile consumes `≤` the forwarded gas

Every precompile returns its gas component as either `0` (insufficient gas) or
`gas - .ofNat requiredGas` taken in the `gas.toNat ≥ requiredGas` branch (so the
subtraction does not wrap). Either way it is `≤ gas.toNat`. -/

/-- The one UInt64 fact: `gas - .ofNat c` never exceeds `gas` (the only `else`
arms use it under `c ≤ gas.toNat`, where it is exact; here we need just `≤`,
which holds because `c < 2^64` follows from `c ≤ gas.toNat`). -/
theorem toNat_sub_ofNat_le {gas : UInt64} {c : ℕ} (hc : c ≤ gas.toNat) :
    (gas - UInt64.ofNat c).toNat ≤ gas.toNat := by
  rw [toNat_sub_ofNat gas c hc (Nat.lt_of_le_of_lt hc gas.toNat_lt)]
  exact Nat.sub_le _ _

/-- A precompile's returned gas (`.2.2.1`) is `≤` the forwarded `gas`. The proof
is uniform: `split` on the `gas.toNat < requiredGas` guard; the `then` arm
returns `0`, the `else` arm returns `gas - .ofNat requiredGas` under
`requiredGas ≤ gas.toNat` (possibly behind an inner `match` that does not touch
the gas). -/
private theorem hsub_le {gas : UInt64} (c : ℕ) (hc : ¬ gas.toNat < c) :
    (gas - UInt64.ofNat c).toNat ≤ gas.toNat :=
  toNat_sub_ofNat_le (Nat.not_lt.mp hc)

-- Precompiles whose gas component does NOT sit behind an inner `match`.
theorem ecRecover_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecRecover a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecRecover; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem sha256_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.sha256 a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.sha256; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem ripemd160_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ripemd160 a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ripemd160; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem identity_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.identity a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.identity; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem modExp_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.modExp a g s e).2.2.1.toNat ≤ g.toNat := by
  -- `requiredGas` is itself an `if`-cascade; abstract it so the gas guard is a
  -- single `if`.
  unfold Precompiles.modExp; dsimp only
  generalize (max 200 _) = rg
  split
  · simp
  · rename_i h; dsimp only; exact hsub_le _ h
-- Precompiles whose gas component sits behind an inner `Except` `match`
-- (the `.error` arm returns gas `0`, the `.ok` arm returns `gas - requiredGas`).
theorem ecAdd_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecAdd a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecAdd; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem ecMul_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecMul a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecMul; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem ecPairing_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecPairing a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecPairing; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem blake2f_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.blake2f a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.blake2f; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem pointEvaluation_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.pointEvaluation a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.pointEvaluation; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp

/-- **Precompile gas (conjunct 5a, the `beginCall` side).** A precompile entry
returns gas `≤ params.gas`. The `beginCall` precompile branch dispatches on the
precompile address; every arm's gas component is bounded by the per-precompile
lemmas above (the `_ => 0` default is bounded trivially). -/
theorem beginCall_inr_gas {p : CallParams} {result : CallResult}
    (h : beginCall p = .inr result) :
    result.gasRemaining.toNat ≤ p.gas.toNat := by
  unfold beginCall at h
  cases hcs : p.codeSource with
  | Code code => rw [hcs] at h; simp at h
  | Precompiled pc =>
    rw [hcs] at h
    simp only [Sum.inr.injEq] at h
    subst h
    dsimp only [CallResult.gasRemaining]
    split
    case _ => exact ecRecover_gas_le _ _ _ _
    case _ => exact sha256_gas_le _ _ _ _
    case _ => exact ripemd160_gas_le _ _ _ _
    case _ => exact identity_gas_le _ _ _ _
    case _ => exact modExp_gas_le _ _ _ _
    case _ => exact ecAdd_gas_le _ _ _ _
    case _ => exact ecMul_gas_le _ _ _ _
    case _ => exact ecPairing_gas_le _ _ _ _
    case _ => exact blake2f_gas_le _ _ _ _
    case _ => exact pointEvaluation_gas_le _ _ _ _
    case _ => simp

/-- **`createArm` `.needsCreate` inversion (saved gas).** `createArm` performs
**no** charge, so the suspended parent's saved gas equals the working `exec`'s
gas. (The forwarded child gas — `allButOneSixtyFourth exec.gas` — is *not*
debited from the parent here; see the bottom-of-file note: this is exactly why
the `totalGas`-descent conjunct (4') cannot hold.) -/
theorem createArm_needsCreate_savedGas
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray}
    {cp : CreateParams} {pd : PendingCreate}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.needsCreate cp pd)) :
    pd.frame.exec.gasAvailable = exec.gasAvailable := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- nonce overflow: `.next`, not `.needsCreate`
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp [bind, Except.bind] at h
    | ok f => intro h; simp [bind, Except.bind, pure, Except.pure] at h
  · split at h
    · -- the `.needsCreate` branch: pd.frame = { fr with exec := exec }
      simp only [Except.ok.injEq, Signal.needsCreate.injEq] at h
      obtain ⟨_, hpd⟩ := h
      subst hpd; rfl
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp [bind, Except.bind] at h
      | ok f => intro h; simp [bind, Except.bind, pure, Except.pure] at h

/-- `createArm` never emits `.needsCall` (only `.needsCreate`/`.next`). -/
theorem createArm_never_needsCall {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {p : CallParams} {pd : PendingCall} :
    createArm fr exec stack value initOffset initSize salt ≠ .ok (.needsCall p pd) := by
  intro h
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- nonce overflow: .next via resumeAfterCreate
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => simp [bind, Except.bind]
    | ok f => simp [bind, Except.bind, pure, Except.pure]
  · split at h
    · simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => simp [bind, Except.bind]
      | ok f => simp [bind, Except.bind, pure, Except.pure]

/-- `haltOp` never emits `.needsCall`. -/
theorem haltOp_never_needsCall {op : Operation.SystemOp} {exec : ExecutionState}
    {p : CallParams} {pd : PendingCall}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.needsCall p pd) := by
  intro h
  unfold haltOp at h
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · simp at h
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp [bind, Except.bind] at h
      | ok ec =>
        rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
        split at h <;> simp at h
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp [bind, Except.bind] at h
      | ok ec =>
        rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
        split at h <;> simp at h
  · rw [selfdestructOp] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind, pure, Except.pure] at h
      cases hp : exec.stack.pop with
      | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, rw'⟩ := v; rw [hp] at h
        simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge (selfdestructCost _ _) exec with
        | error e => rw [hc] at h; simp [bind, Except.bind] at h
        | ok ec =>
          rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
          split at h <;> simp at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `charge cost` drops gas by at least `cost`. -/
theorem charge_drop_ge {cost : ℕ} {exec exec' : ExecutionState}
    (h : charge cost exec = .ok exec') :
    exec'.gasAvailable.toNat + cost ≤ exec.gasAvailable.toNat := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · rename_i hge
    have hge' : cost ≤ exec.gasAvailable.toNat := Nat.not_lt.mp hge
    injection h with h; subst h
    have hlt : cost < 2 ^ 64 := Nat.lt_of_le_of_lt hge' exec.gasAvailable.toNat_lt
    dsimp only
    rw [toNat_sub_ofNat _ _ hge' hlt]; omega

/-- `createCost ≥ Gcreate = 32000 ≥ 2`. -/
theorem createCost_ge_2 (initSize : UInt256) : 2 ≤ createCost initSize := by
  unfold createCost Gcreate; omega

/-- `create2Cost ≥ Gcreate = 32000 ≥ 2`. -/
theorem create2Cost_ge_2 (initSize : UInt256) : 2 ≤ create2Cost initSize := by
  unfold create2Cost Gcreate; omega

/-! ## `systemOp` / `stepFrame` inversion onto `callArm`

Every `.needsCall` a `systemOp` (hence `stepFrame`) emits is produced by a
`callArm fr fr.exec …` call (the four CALL-family ops differ only in the
operand wiring; all pass `fr.exec` as the working exec). So the `callArm` gas
relations transfer verbatim to `stepFrame`. -/

/-- A `.needsCall` from `systemOp` comes from `callArm` on `fr.exec`. -/
theorem systemOp_needsCall_gas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {p : CallParams} {pd : PendingCall}
    (h : systemOp op fr exec = .ok (.needsCall p pd)) :
    p.gas.toNat + pd.frame.exec.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat := by
  unfold systemOp at h
  cases op with
  | STOP => exact absurd h (haltOp_never_needsCall (by tauto))
  | RETURN => exact absurd h (haltOp_never_needsCall (by tauto))
  | REVERT => exact absurd h (haltOp_never_needsCall (by tauto))
  | SELFDESTRUCT => exact absurd h (haltOp_never_needsCall (by tauto))
  | INVALID => exact absurd h (haltOp_never_needsCall (by tauto))
  | CALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact callArm_needsCall_gas h
  | CALLCODE =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_needsCall_gas h
  | DELEGATECALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_needsCall_gas h
  | STATICCALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_needsCall_gas h
  | CREATE =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · -- chargeMemExpansion >>= charge >>= createArm; createArm never .needsCall
          cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              exact absurd h createArm_never_needsCall
  | CREATE2 =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              exact absurd h createArm_never_needsCall

/-- `callArm` never emits `.needsCreate` (only `.needsCall`/`.next`). -/
theorem callArm_never_needsCreate
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {cp : CreateParams} {pd : PendingCreate} :
    callArm fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission ≠ .ok (.needsCreate cp pd) := by
  intro h
  rw [callArm] at h
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h; simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp [bind, Except.bind] at h
    | ok e1 =>
      rw [he1] at h; simp only [bind, Except.bind] at h
      cases he2 : charge _ e1 with
      | error e => rw [he2] at h; simp [bind, Except.bind] at h
      | ok e2 =>
        rw [he2] at h
        simp only [bind, Except.bind] at h
        split at h <;> · simp only [Except.ok.injEq] at h; exact absurd h (by simp)

/-- `haltOp` never emits `.needsCreate`. -/
theorem haltOp_never_needsCreate {op : Operation.SystemOp} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.needsCreate cp pd) := by
  intro h
  unfold haltOp at h
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · simp at h
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp [bind, Except.bind] at h
      | ok ec =>
        rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
        split at h <;> simp at h
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp [bind, Except.bind] at h
      | ok ec =>
        rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
        split at h <;> simp at h
  · rw [selfdestructOp] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind, pure, Except.pure] at h
      cases hp : exec.stack.pop with
      | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, rw'⟩ := v; rw [hp] at h
        simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge (selfdestructCost _ _) exec with
        | error e => rw [hc] at h; simp [bind, Except.bind] at h
        | ok ec =>
          rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
          split at h <;> simp at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`systemOp` `.needsCreate` inversion (saved gas).** The suspended parent's
saved gas plus `2` does not exceed the pre-step gas: the `createCost`/`
create2Cost` charged before `createArm` covers the `+2` slack (`createArm` itself
charges nothing, so the saved frame keeps the *post-charge* gas). -/
theorem systemOp_needsCreate_savedGas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (h : systemOp op fr exec = .ok (.needsCreate cp pd)) :
    pd.frame.exec.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat := by
  unfold systemOp at h
  cases op with
  | STOP => exact absurd h (haltOp_never_needsCreate (by tauto))
  | RETURN => exact absurd h (haltOp_never_needsCreate (by tauto))
  | REVERT => exact absurd h (haltOp_never_needsCreate (by tauto))
  | SELFDESTRUCT => exact absurd h (haltOp_never_needsCreate (by tauto))
  | INVALID => exact absurd h (haltOp_never_needsCreate (by tauto))
  | CALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact absurd h callArm_never_needsCreate
  | CALLCODE =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact absurd h callArm_never_needsCreate
  | DELEGATECALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact absurd h callArm_never_needsCreate
  | STATICCALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact absurd h callArm_never_needsCreate
  | CREATE =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              have hsaved := createArm_needsCreate_savedGas h
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := createCost_ge_2 is
              rw [hsaved]; omega
  | CREATE2 =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              have hsaved := createArm_needsCreate_savedGas h
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := create2Cost_ge_2 is
              rw [hsaved]; omega

/-- `haltOp` never emits `.next`: its `.ok` outputs are all `.halted`. (Local
restatement of `haltOp_not_next` over the explicit op disjunction.) -/
theorem haltOp_not_next' {op : Operation.SystemOp} {exec exec' : ExecutionState}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.next exec') :=
  haltOp_not_next hh

/-- **`systemOp` `.next` inversion (gas).** A `.next` from `systemOp` strictly
drops the working gas. For the CALL family this is `callArm_next_gas`; for
CREATE/CREATE2 the `createCost`/`create2Cost` charged before `createArm` makes
the (gas-preserving) `createArm` `.next` strict. -/
theorem systemOp_next_gas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {exec' : ExecutionState}
    (h : systemOp op fr exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  unfold systemOp at h
  cases op with
  | STOP => exact absurd h (haltOp_not_next' (by tauto))
  | RETURN => exact absurd h (haltOp_not_next' (by tauto))
  | REVERT => exact absurd h (haltOp_not_next' (by tauto))
  | SELFDESTRUCT => exact absurd h (haltOp_not_next' (by tauto))
  | INVALID => exact absurd h (haltOp_not_next' (by tauto))
  | CALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact callArm_next_gas h
  | CALLCODE =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_next_gas h
  | DELEGATECALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_next_gas h
  | STATICCALL =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact callArm_next_gas h
  | CREATE =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              -- createArm .next: gas ≤ ec.gas; createCost charge makes it < exec.gas
              have hca := createArm_next_gas h
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := createCost_ge_2 is
              omega
  | CREATE2 =>
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [bind, Except.bind, pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp [bind, Except.bind, pure, Except.pure] at h
            | ok ec =>
              rw [hc] at h; simp only [bind, Except.bind, pure, Except.pure] at h
              have hca := createArm_next_gas h
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := create2Cost_ge_2 is
              omega

/-! ## `stepFrame` inversion: bridging the `Signal` to `systemOp`

`stepFrame fr` decodes `(op, arg)`, screens `INVALID`/overflow (both `.halted`),
then maps `dispatch op arg fr fr.exec`. A `.needsCall`/`.needsCreate`/(System)
`.next` signal therefore comes from `dispatch op arg fr fr.exec = .ok (that
signal)` with `op = .System s`, and `dispatch (.System s) … = systemOp s …`.

The non-`System` dispatcher arms only ever emit `.next` (`continueWith`) on
success, so they cannot emit `.needsCall`/`.needsCreate`. We capture that with
`onlyNext`, mirroring `neverHalts`. -/

/-- A `Step` whose every `.ok` output is a `.next`. -/
def onlyNext (s : Step) : Prop := ∀ sig, s = .ok sig → ∃ e, sig = .next e

theorem onlyNext_continueWith (e : ExecutionState) : onlyNext (continueWith e) := by
  intro sig he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨e, he.symm⟩
theorem onlyNext_error (e : ExecutionException) : onlyNext (.error e : Step) := by
  intro sig he; simp at he
theorem onlyNext_throw (e : ExecutionException) : onlyNext (throw e : Step) := by
  intro sig he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem onlyNext_bind_except {α : Type} (m : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, m = .ok a → onlyNext (k a)) : onlyNext (m >>= k) := by
  intro sig he
  cases hm : m with
  | error e => rw [hm] at he; simp [bind, Except.bind] at he
  | ok a => rw [hm] at he; simp only [bind, Except.bind] at he; exact hk a hm sig he
theorem onlyNext_optionBind {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → onlyNext (k a)) :
    onlyNext ((o : Except ExecutionException α) >>= k) := by
  intro sig he
  cases ho : o with
  | none => rw [ho] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
  | some a =>
    rw [ho] at he; simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    exact hk a ho sig he
theorem onlyNext_chargeBind {cost : ℕ} {exec : ExecutionState} {k : ExecutionState → Step}
    (hk : ∀ ec, charge cost exec = .ok ec → onlyNext (k ec)) :
    onlyNext (charge cost exec >>= k) :=
  onlyNext_bind_except _ _ hk
theorem onlyNext_memChargeBind {exec : ExecutionState} {off size : UInt256}
    {k : ExecutionState → Step} (hk : ∀ ec, onlyNext (k ec)) :
    onlyNext (chargeMemExpansion exec off size >>= k) := by
  apply onlyNext_bind_except; intro a _; exact hk a

theorem unOp_onlyNext {f : UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (unOp f exec cost) := by
  rw [unOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
theorem binOp_onlyNext {f : UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (binOp f exec cost) := by
  rw [binOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
theorem ternOp_onlyNext {f : UInt256 → UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (ternOp f exec cost) := by
  rw [ternOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _; exact onlyNext_continueWith _
theorem pushOp_onlyNext {v : ExecutionState → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (pushOp v exec cost) := by
  rw [pushOp]; apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem unStateOp_onlyNext {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec : ExecutionState} :
    onlyNext (unStateOp f cost exec) := by
  rw [unStateOp]; apply onlyNext_optionBind; rintro ⟨s, a⟩ _
  apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem dup_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (dup n exec) := by
  rw [dup]; apply onlyNext_chargeBind; intro ec _
  intro sig he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
theorem swap_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (swap n exec) := by
  rw [swap]; apply onlyNext_chargeBind; intro ec _
  intro sig he
  by_cases hg : List.length (ec.stack.take (n + 1)) = (n + 1)
  · rw [if_pos hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  · rw [if_neg hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem logArm_onlyNext {exec : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256} :
    onlyNext (logArm exec stack offset size topics) := by
  rw [logArm]; apply onlyNext_bind_except; intro _ _
  apply onlyNext_memChargeBind; intro ec
  apply onlyNext_chargeBind; intro ec2 _; exact onlyNext_continueWith _
theorem smsfOp_onlyNext {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState} :
    onlyNext (smsfOp op fr exec) := by
  unfold smsfOp
  cases op with
  | POP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
  | MLOAD =>
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE8 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | SLOAD => exact unStateOp_onlyNext
  | SSTORE =>
    apply onlyNext_bind_except; intro _ _
    by_cases hg : exec.gasAvailable.toNat ≤ Gcallstipend
    · simp only [hg, if_true]; exact onlyNext_throw _
    · simp only [hg, if_false]
      apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
      apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | TLOAD => exact unStateOp_onlyNext
  | TSTORE =>
    apply onlyNext_bind_except; intro _ _
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
  | MSIZE => exact pushOp_onlyNext
  | GAS => exact pushOp_onlyNext
  | JUMP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d⟩ _ sig he
    dsimp only at he
    split at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
    · simp at he
  | JUMPI =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d, c⟩ _ sig he
    dsimp only at he
    split at he
    · split at he
      · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
      · simp at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  | PC => exact pushOp_onlyNext
  | JUMPDEST =>
    apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | MCOPY =>
    apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _

/-- The non-`System` dispatcher arms only emit `.next`. -/
theorem dispatch_onlyNext {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} (hne : ∀ s, op ≠ .System s) :
    onlyNext (dispatch op arg fr exec) := by
  unfold dispatch
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | Smsf s => exact smsfOp_onlyNext
  | Log l => cases l <;>
      (apply onlyNext_optionBind; rintro _ _; exact logArm_onlyNext)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_onlyNext
    | _ =>
      apply onlyNext_chargeBind; intro ec _ sig he
      cases arg <;>
        first
          | (simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩)
          | simp [continueWith, throw, throwThe, MonadExceptOf.throw] at he
  | Dup d => exact dup_onlyNext
  | Swap s => exact swap_onlyNext
  | ArithLogic a => cases a <;>
      first
        | exact binOp_onlyNext | exact unOp_onlyNext | exact ternOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)
  | Env e =>
    cases e <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
           apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
           exact onlyNext_continueWith _)
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c, d⟩ _
           apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
           exact onlyNext_continueWith _)
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _ sig he
           revert he; dsimp only; split
           · intro he; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at he
           · exact (onlyNext_memChargeBind (k := _)
               (fun ec => onlyNext_chargeBind (fun ec2 _ => onlyNext_continueWith _)) sig))
  | Block b =>
    cases b <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, i⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)

/-- Bridge: a non-`.next` `Signal` from a successful `dispatch` forces `op` to be
a `System` op. -/
theorem dispatch_ok_System_of_not_next {op : Operation} {arg : Option (UInt256 × UInt8)}
    {fr : Frame} {exec : ExecutionState} {sig : Signal}
    (hdisp : dispatch op arg fr exec = .ok sig) (hnn : ∀ e, sig ≠ .next e) :
    ∃ s, op = .System s := by
  by_cases hsys : ∃ s, op = .System s
  · exact hsys
  · push_neg at hsys
    obtain ⟨e, he⟩ := dispatch_onlyNext hsys sig hdisp
    exact absurd he (hnn e)

/-- A `.needsCall` from `stepFrame` is a `.needsCall` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCall_systemOp {fr : Frame} {p : CallParams} {pd : PendingCall}
    (h : stepFrame fr = .needsCall p pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCall p pd) := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e => rw [hdisp] at h; exact absurd h (by simp)
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e => exact absurd h (by simp)
        | halted hl => exact absurd h (by simp)
        | needsCreate cp pc => exact absurd h (by simp)
        | needsCall p' pd' =>
          simp only [Signal.needsCall.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨s, rfl⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
          rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `.needsCreate` from `stepFrame` is a `.needsCreate` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCreate_systemOp {fr : Frame} {cp : CreateParams} {pd : PendingCreate}
    (h : stepFrame fr = .needsCreate cp pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCreate cp pd) := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e => rw [hdisp] at h; exact absurd h (by simp)
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e => exact absurd h (by simp)
        | halted hl => exact absurd h (by simp)
        | needsCall p' pd' => exact absurd h (by simp)
        | needsCreate cp' pc' =>
          simp only [Signal.needsCreate.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨s, rfl⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
          rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `System`-op `.next` from `stepFrame`: when the decoded op is a `System` op
and `stepFrame` is `.next exec'`, that `.next` comes from `systemOp s fr fr.exec`. -/
theorem stepFrame_next_systemOp {fr : Frame} {exec' : ExecutionState} {s : Operation.SystemOp}
    (hs : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s)
    (h : stepFrame fr = .next exec') :
    systemOp s fr fr.exec = .ok (.next exec') := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h hs
  obtain ⟨op, arg⟩ := dp
  simp only at h hs
  subst hs
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases hdisp : dispatch (.System s) arg fr fr.exec with
      | error e => rw [hdisp] at h; exact absurd h (by simp)
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | halted hl => exact absurd h (by simp)
        | needsCall p pd => exact absurd h (by simp)
        | needsCreate cp pd => exact absurd h (by simp)
        | next e =>
          simp only [Signal.next.injEq] at h; subst h
          rw [dispatch] at hdisp; exact hdisp

/-! ## The four *sound* `DescentDrops` conjuncts

Conjuncts (3), (4), (5a), (5b) are exactly the per-transition decreases that
`mu_bound` needs, and each follows from the `systemOp`/`stepFrame` inversions
plus the gas arithmetic above. They are stated here in the precise `Prop` shapes
of `DescentDrops` so they can be plugged into a future assembly.

**Conjunct (4') is *not* here, and `descentDrops_holds` is deliberately *not*
assembled** — see the closing note: leanevm's `createArm` does not debit the
parent frame by the forwarded child gas, so (4') is false. -/

open BytecodeLayer

/-- **Conjunct (3).** A `System`-op `.next` fallback strictly drops `totalGas`. -/
theorem descentDrops_conj3
    (fr : Frame) (exec' : ExecutionState) (stack : List Pending)
    (hstep : stepFrame fr = .next exec')
    (hsys : ∃ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s) :
    totalGas stack (.inl { fr with exec := exec' }) < totalGas stack (.inl fr) := by
  obtain ⟨s, hs⟩ := hsys
  have hsop := stepFrame_next_systemOp hs hstep
  have hlt := systemOp_next_gas hsop
  simp only [totalGas, activeGas]
  omega

/-- **Conjunct (4).** A `.needsCall` descent into a code child: child gas +
saved parent gas + 2 ≤ pre-step gas. -/
theorem descentDrops_conj4
    (fr : Frame) (params : CallParams) (pending : PendingCall) (child : Frame) (stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inl child) :
    activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hchild : child.exec.gasAvailable = params.gas := beginCall_inl_gas hbc
  simp only [activeGas, Pending.savedGas, Pending.frame]
  rw [hchild]
  exact hgas

/-- **Conjunct (5a).** A `.needsCall` precompile (immediate result): result gas +
saved parent gas + 2 ≤ pre-step gas. -/
theorem descentDrops_conj5a
    (fr : Frame) (params : CallParams) (pending : PendingCall) (result : CallResult) (stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inr result) :
    FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hres : result.gasRemaining.toNat ≤ params.gas.toNat := beginCall_inr_gas hbc
  simp only [FrameResult.gasRemaining, activeGas, Pending.savedGas, Pending.frame]
  omega

/-- **Conjunct (5b).** A `.needsCreate` that fails the guard (zeroed result):
saved parent gas + 2 ≤ pre-step gas. -/
theorem descentDrops_conj5b
    (fr : Frame) (params : CreateParams) (pending : PendingCreate) (stack : List Pending)
    (hstep : stepFrame fr = .needsCreate params pending) :
    Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCreate_systemOp hstep
  have hgas := systemOp_needsCreate_savedGas hsop
  simp only [Pending.savedGas, Pending.frame, activeGas]
  exact hgas

/-! ## ⚠️ The blocking conjunct (4') — `needsCreate` descent

`DescentDrops`'s fourth conjunct (4') requires, for a CREATE/CREATE2 descent
`stepFrame fr = .needsCreate params pending` with `beginCreate params = .ok child`:

  `activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr)`.

This is **false** under the current leanevm semantics. In `createArm`
(`Evm/Semantics/System.lean:73`):

* the suspended parent's frame is saved with the *full* working gas `g`
  (`{ fr with exec := exec }`, line 84 — `createArm` performs **no** charge of
  the forwarded gas), so `Pending.savedGas (.create pending) = g`
  (`createArm_needsCreate_savedGas`);
* the child is forwarded `allButOneSixtyFourth g` (line 112 →
  `beginCreate`'s `gasAvailable := params.gas`, `Create.lean:97`), so
  `activeGas (.inl child) = g - g/64` (`createArm_child_gas`, checked separately).

Hence the LHS is `(g - g/64) + g + 2 = 2·g - g/64 + 2`, while
`activeGas (.inl fr) = g + createCost + memExpansion` (the `createCost ≥ 32000`
charged in `systemOp` *before* `createArm`). For large `g` the LHS exceeds the
RHS by `≈ g`, so (4') cannot hold.

Contrast with CALL: `callArm` charges `gasCap + extraCost` **inside** the arm
(`System.lean:28`) *before* saving the parent, so the parent keeps only
`pre − gasCap − extraCost` and the child gets `≈ gasCap` — no double-counting,
and conjunct (4) (`descentDrops_conj4`) goes through.

The gas *is* reconciled end-to-end by `resumeAfterCreate` (it resets the parent
to `g/64 + childRemaining`, `Create.lean:173`), so the **semantics** is sound;
but the `totalGas` measure used by `mu_bound` double-counts the forwarded
`allButOneSixtyFourth g` during the open CREATE descent, so it transiently
*increases*. Closing (4') therefore requires either:

* patching `createArm` to debit the parent frame by the forwarded child gas
  (mirroring `callArm`), or
* redefining the measure / `DescentDrops` so the CREATE descent obligation does
  not over-count (e.g. measuring the parent's *un-forwarded* gas).

Both are out of scope for a proof-only task, so per the task contract we leave
(4') unproven, do **not** assemble `descentDrops_holds`, and do **not** state the
unconditional `messageCall_never_outOfFuel`. The other four conjuncts (3, 4, 5a,
5b) are fully proven above and remain reusable for whichever fix lands. -/

end BytecodeLayer.Proof

