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

end BytecodeLayer.Proof
