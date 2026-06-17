import BytecodeLayer.Reasoning.NeverOutOfFuel
import BytecodeLayer.Reasoning.StepGas
import BytecodeLayer.Proof.DecodeGas
import BytecodeLayer.Proof.Fuel.PrecompileGas
import BytecodeLayer.Proof.Fuel.DispatchSignalShape

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

/-- **The shared `callArm` parent-charge invariant.** Both gas readouts
(`callArm_needsCall_gas` / `callArm_next_gas`) reach the same post-charge state
`e2 = charge (gasCap + extraCost) e1` and then need the *same* four arithmetic
facts about it. We factor that common block here so each readout finishes in a
handful of lines after its own `split`.

Given the parent charge `charge (gasCap + extraCost) e1 = .ok e2` (with
`gasCap`/`extraCost`/`childGas` the `callArm` let-bindings, here passed
explicitly so the lemma is independent of `callArm`'s syntax):
* `e2`'s gas is `e1`'s gas minus the charge, and the charge fits (`he2eq`/`he2le`);
* the child's forwarded gas plus the `+2` measure slack is dominated by the
  charge (`hslack`, from `childGas_le_of_extraCost`);
* `childGas < 2^64`, so `.ofNat childGas` round-trips (`hcgub`). -/
theorem callArm_charge_inv
    {ca rc : AccountAddress} {value gas : UInt256} {e1 e2 : ExecutionState}
    {extraCost gasCap childGas : ℕ}
    (hextra : extraCost = callExtraCost ca rc value e1.accounts e1.substate)
    (hgcap : gasCap = callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate)
    (hcg : childGas = if value = 0 then gasCap else gasCap + Gcallstipend)
    (he2 : charge (gasCap + extraCost) e1 = .ok e2) :
    e2.gasAvailable.toNat = e1.gasAvailable.toNat - (gasCap + extraCost)
      ∧ gasCap + extraCost ≤ e1.gasAvailable.toNat
      ∧ childGas + 2 ≤ gasCap + extraCost
      ∧ childGas < 2 ^ 64 := by
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
  exact ⟨he2eq, he2le, hslack, hcgub⟩

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
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h
      simp only [] at h
      -- abbreviations as in callArm (computed from e1)
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        -- now `h` is the final `if … then .ok (.needsCall …) else .ok (.next …)`
        obtain ⟨he2eq, he2le, hslack, hcgub⟩ := callArm_charge_inv hextra hgcap hcg he2
        split at h
        · -- needsCall branch
          simp only [Except.ok.injEq, Signal.needsCall.injEq] at h
          obtain ⟨hp, hpd⟩ := h
          -- read off p.gas and pd.frame.exec
          subst hp hpd
          -- p.gas = .ofNat childGas ; pd.frame.exec = e2
          have hmemle : e1.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le he1
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
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h
      simp only [] at h
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        obtain ⟨he2eq, he2le, hslack, hcgub⟩ := callArm_charge_inv hextra hgcap hcg he2
        split at h
        · -- needsCall branch: contradiction
          simp only [Except.ok.injEq] at h
          exact absurd h (by simp)
        · -- next (fallback) branch
          simp only [Except.ok.injEq, Signal.next.injEq] at h
          subst h
          have hmemle : e1.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le he1
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
    · exact absurd hf (by simp)
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
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · -- needsCreate branch: not a `.next`
      simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr


/-- **`createArm` `.needsCreate` inversion (saved gas).** `createArm` performs
**no** charge, so the suspended parent's saved frame keeps the full working
`exec` gas. The forwarded child gas (`allButOneSixtyFourth exec.gas`) is *not*
debited from the parent here; the kind-aware `Pending.savedGas (.create _)`
compensates by withholding that forwarded part from the measure, so conjunct (4')
goes through (see `descentDrops_conj4'`). -/
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
    | error e => intro h; simp at h
    | ok f => intro h; simp at h
  · split at h
    · -- the `.needsCreate` branch: pd.frame = { fr with exec := exec }
      simp only [Except.ok.injEq, Signal.needsCreate.injEq] at h
      obtain ⟨_, hpd⟩ := h
      subst hpd; rfl
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f => intro h; simp at h

/-- **`beginCreate` gas.** When `beginCreate` succeeds, the child frame's gas is
exactly the forwarded `params.gas`. -/
theorem beginCreate_ok_gas {params : CreateParams} {child : Frame}
    (h : beginCreate params = .ok child) :
    child.exec.gasAvailable = params.gas := by
  rw [beginCreate] at h
  simp only [Option.option] at h
  split at h
  · rw [Except.ok.injEq] at h
    subst h; rfl
  · simp at h

/-- **`createArm` `.needsCreate` inversion (child gas).** The child created by a
CREATE/CREATE2 descent is forwarded exactly `allButOneSixtyFourth exec.gas`
(`createArm` does no charge before forwarding). -/
theorem createArm_needsCreate_childGas
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray}
    {cp : CreateParams} {pd : PendingCreate}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.needsCreate cp pd)) :
    cp.gas = .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat) := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f => intro h; simp at h
  · split at h
    · simp only [Except.ok.injEq, Signal.needsCreate.injEq] at h
      obtain ⟨hcp, _⟩ := h
      subst hcp; rfl
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f => intro h; simp at h

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
    | error e => simp
    | ok f => simp
  · split at h
    · simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => simp
      | ok f => simp

/-- A `Step` whose every `.ok` output is a `.halted`. The single source of truth
for the halt ops: STOP/RETURN/REVERT/SELFDESTRUCT/INVALID never produce a
`.next`/`.needsCall`/`.needsCreate` on success. -/
def onlyHalted (s : Step) : Prop := ∀ sig, s = .ok sig → ∃ hl, sig = .halted hl

/-- **The halt-op inversion (single source of truth).** Every `.ok` output of
`haltOp op exec` (for `op` a halt op) is a `.halted`. The three downstream
"`haltOp` never emits …" facts are one-line corollaries. -/
theorem haltOp_onlyHalted {op : Operation.SystemOp} {exec : ExecutionState}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    onlyHalted (haltOp op exec) := by
  intro sig h
  unfold haltOp at h
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp at h
      | ok ec =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        split at h <;> (simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩)
  · rw [returnOrRevertOp] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at h; simp at h
      | ok ec =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        split at h <;> (simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩)
  · rw [selfdestructOp] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind, pure, Except.pure] at h
      cases hp : exec.stack.pop with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, rw'⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge (selfdestructCost _ _) exec with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          split at h <;> (simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩)
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `haltOp` never emits `.needsCall`. -/
theorem haltOp_never_needsCall {op : Operation.SystemOp} {exec : ExecutionState}
    {p : CallParams} {pd : PendingCall}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.needsCall p pd) := fun h => by
  obtain ⟨_, hsig⟩ := haltOp_onlyHalted hh _ h; exact absurd hsig (by simp)

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

/-- **`systemOp` → `callArm` reduction (single shell).** Any `.ok` signal a
CALL-family `systemOp` (CALL/CALLCODE/DELEGATECALL/STATICCALL) emits is exactly
that signal from `callArm fr exec …` on some operand wiring. The CALL static
guard (`value ≠ 0 ∧ ¬canModifyState`) and the `pop7`/`pop6` decode failures are
discharged here, once. The four downstream `systemOp_*` CALL arms reduce to the
matching `callArm_*` inversion via this lemma. -/
theorem systemOp_callArm_reduce {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {sig : Signal}
    (hop : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (h : systemOp op fr exec = .ok sig) :
    ∃ (stack : Stack UInt256)
      (gas caller recipient codeAddress value apparentValue
        inOffset inSize outOffset outSize : UInt256) (permission : Bool),
      callArm fr exec stack gas caller recipient codeAddress value apparentValue
        inOffset inSize outOffset outSize permission = .ok sig := by
  unfold systemOp at h
  rcases hop with rfl | rfl | rfl | rfl
  · -- CALL: pop7, then the StaticModeViolation guard
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      split at h
      · simp at h
      · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩
  · -- CALLCODE: pop7, no guard
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop7 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, val, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩
  · -- DELEGATECALL: pop6
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩
  · -- STATICCALL: pop6
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop6 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, g, t, io, is, oo, os⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩

/-- **`systemOp` → `createArm` reduction (single shell).** Any `.ok` signal a
CREATE/CREATE2 `systemOp` emits is that signal from `createArm fr em …` on the
charged intermediate state `em` (post `chargeMemExpansion` + `createCost`/
`create2Cost`), with `em.gas + 2 ≤ exec.gas` (the create's own cost dominates the
`+2` slack). The `requireStateMod`, `pop3`/`pop4`, `initSize > 49152` and charge
failures are discharged here, once. -/
theorem systemOp_createArm_reduce {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {sig : Signal}
    (hop : op = .CREATE ∨ op = .CREATE2)
    (h : systemOp op fr exec = .ok sig) :
    ∃ (em : ExecutionState) (stack : Stack UInt256) (value initOffset initSize : UInt256)
      (salt : Option ByteArray),
      em.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat ∧
      createArm fr em stack value initOffset initSize salt = .ok sig := by
  unfold systemOp at h
  rcases hop with rfl | rfl
  · -- CREATE
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              refine ⟨ec, s, val, io, is, none, ?_, h⟩
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := createCost_ge_2 is
              omega
  · -- CREATE2
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              refine ⟨ec, s, val, io, is, some <| Evm.UInt256.toByteArray salt, ?_, h⟩
              have hmle : em.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
              have hcc := charge_drop_ge hc
              have h2 := create2Cost_ge_2 is
              omega

/-- A `.needsCall` from `systemOp` comes from `callArm` on `fr.exec`. -/
theorem systemOp_needsCall_gas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {p : CallParams} {pd : PendingCall}
    (h : systemOp op fr exec = .ok (.needsCall p pd)) :
    p.gas.toNat + pd.frame.exec.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h) (haltOp_never_needsCall (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := systemOp_callArm_reduce (by tauto) h
    exact callArm_needsCall_gas hc
  | CREATE | CREATE2 =>
    obtain ⟨_, _, _, _, _, _, _, hcr⟩ := systemOp_createArm_reduce (by tauto) h
    exact absurd hcr createArm_never_needsCall

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
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h; simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h; simp only [] at h
      cases he2 : charge _ e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        split at h <;> · simp only [Except.ok.injEq] at h; exact absurd h (by simp)

/-- `haltOp` never emits `.needsCreate`. -/
theorem haltOp_never_needsCreate {op : Operation.SystemOp} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.needsCreate cp pd) := fun h => by
  obtain ⟨_, hsig⟩ := haltOp_onlyHalted hh _ h; exact absurd hsig (by simp)

/-- **`systemOp` `.needsCreate` inversion (saved gas).** The suspended parent's
saved gas plus `2` does not exceed the pre-step gas: the `createCost`/`
create2Cost` charged before `createArm` covers the `+2` slack (`createArm` itself
charges nothing, so the saved frame keeps the *post-charge* gas). -/
theorem systemOp_needsCreate_savedGas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (h : systemOp op fr exec = .ok (.needsCreate cp pd)) :
    pd.frame.exec.gasAvailable.toNat + 2 ≤ exec.gasAvailable.toNat := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h) (haltOp_never_needsCreate (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := systemOp_callArm_reduce (by tauto) h
    exact absurd hc callArm_never_needsCreate
  | CREATE | CREATE2 =>
    obtain ⟨em, _, _, _, _, _, hle, hcr⟩ := systemOp_createArm_reduce (by tauto) h
    rw [createArm_needsCreate_savedGas hcr]; exact hle

/-- **`systemOp` `.needsCreate` inversion (child gas).** The forwarded child gas
is `allButOneSixtyFourth` of the suspended parent's saved gas (`createArm` does no
charge between saving the parent and forwarding the child). -/
theorem systemOp_needsCreate_childGas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (h : systemOp op fr exec = .ok (.needsCreate cp pd)) :
    cp.gas = .ofNat (allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat) := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h) (haltOp_never_needsCreate (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := systemOp_callArm_reduce (by tauto) h
    exact absurd hc callArm_never_needsCreate
  | CREATE | CREATE2 =>
    obtain ⟨em, _, _, _, _, _, _, hcr⟩ := systemOp_createArm_reduce (by tauto) h
    rw [createArm_needsCreate_childGas hcr, createArm_needsCreate_savedGas hcr]

/-- `haltOp` never emits `.next`: its `.ok` outputs are all `.halted`. (One-line
corollary of the local single-source-of-truth `haltOp_onlyHalted`.) -/
theorem haltOp_not_next' {op : Operation.SystemOp} {exec exec' : ExecutionState}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.next exec') := fun h => by
  obtain ⟨_, hsig⟩ := haltOp_onlyHalted hh _ h; exact absurd hsig (by simp)

/-- **`systemOp` `.next` inversion (gas).** A `.next` from `systemOp` strictly
drops the working gas. For the CALL family this is `callArm_next_gas`; for
CREATE/CREATE2 the `createCost`/`create2Cost` charged before `createArm` makes
the (gas-preserving) `createArm` `.next` strict. -/
theorem systemOp_next_gas {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {exec' : ExecutionState}
    (h : systemOp op fr exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h) (haltOp_not_next' (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := systemOp_callArm_reduce (by tauto) h
    exact callArm_next_gas hc
  | CREATE | CREATE2 =>
    obtain ⟨em, _, _, _, _, _, hle, hcr⟩ := systemOp_createArm_reduce (by tauto) h
    have hca := createArm_next_gas hcr
    omega


/-! ## The five `DescentDrops` conjuncts

Conjuncts (3), (4), (5a), (4'), (5b) are exactly the per-transition decreases
that `mu_bound` needs, and each follows from the `systemOp`/`stepFrame`
inversions plus the gas arithmetic above. They are stated here in the precise
`Prop` shapes of `DescentDrops` and assembled into `descentDrops_holds`, which
discharges the last hypothesis of the general theorem. -/

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
    (fr : Frame) (params : CallParams) (pending : PendingCall) (child : Frame) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inl child) :
    activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hchild : child.exec.gasAvailable = params.gas := beginCall_inl_gas hbc
  simp only [activeGas, Pending.savedGas]
  rw [hchild]
  exact hgas

/-- **Conjunct (5a).** A `.needsCall` precompile (immediate result): result gas +
saved parent gas + 2 ≤ pre-step gas. -/
theorem descentDrops_conj5a
    (fr : Frame) (params : CallParams) (pending : PendingCall) (result : CallResult) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inr result) :
    FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hres : result.gasRemaining.toNat ≤ params.gas.toNat := beginCall_inr_gas hbc
  simp only [FrameResult.gasRemaining, activeGas, Pending.savedGas]
  omega

/-- **Conjunct (5b).** A `.needsCreate` that fails the guard (zeroed result):
saved parent gas + 2 ≤ pre-step gas. -/
theorem descentDrops_conj5b
    (fr : Frame) (params : CreateParams) (pending : PendingCreate) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCreate params pending) :
    Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCreate_systemOp hstep
  have hgas := systemOp_needsCreate_savedGas hsop
  simp only [Pending.savedGas, activeGas]
  have hsub : pending.frame.exec.gasAvailable.toNat
      - allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat
      ≤ pending.frame.exec.gasAvailable.toNat := Nat.sub_le _ _
  omega

/-! ## Conjunct (4') — `needsCreate` descent

For a CREATE/CREATE2 descent `stepFrame fr = .needsCreate params pending` with
`beginCreate params = .ok child`, the kind-aware `Pending.savedGas` makes the
descent conserve the measure (plus the `createCost ≥ 2` slack):

* the suspended parent's frame keeps the full charged gas `g`, so
  `Pending.savedGas (.create pending) = g − allButOneSixtyFourth g`;
* the child is forwarded `allButOneSixtyFourth g`, so
  `activeGas (.inl child) = allButOneSixtyFourth g`.

Hence the LHS is
`allButOneSixtyFourth g + (g − allButOneSixtyFourth g) + 2 = g + 2`, and
`g + 2 ≤ activeGas (.inl fr)` is exactly `systemOp_needsCreate_savedGas` (the
`createCost`/`create2Cost` charged in `systemOp` before `createArm` covers the
`+2`). The forwarded `allButOneSixtyFourth g` is no longer double-counted: the
measure subtracts it from the parent precisely because the child holds it, and
`resumeAfterCreate` returns it on delivery (`mu_bound`'s create-resume case via
`resumeAfterCreate_gas_le_savedGas`). -/

/-- **Conjunct (4').** A `.needsCreate` descent into a code child: child gas +
saved parent gas + 2 ≤ pre-step gas. The child holds `allButOneSixtyFourth g`,
the (kind-aware) saved parent holds `g − allButOneSixtyFourth g`, and the
`createCost` charged before `createArm` covers the `+2`. -/
theorem descentDrops_conj4'
    (fr : Frame) (params : CreateParams) (pending : PendingCreate) (child : Frame) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCreate params pending) (hbcr : beginCreate params = .ok child) :
    activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCreate_systemOp hstep
  have hsaved := systemOp_needsCreate_savedGas hsop
  have hchild := systemOp_needsCreate_childGas hsop
  have hcg : child.exec.gasAvailable = params.gas := beginCreate_ok_gas hbcr
  -- `params.gas = .ofNat (allButOneSixtyFourth pd.gas)`, and the round-trip is exact.
  have habf_le : allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat
      ≤ pending.frame.exec.gasAvailable.toNat := by unfold allButOneSixtyFourth; omega
  have hlt : allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt habf_le pending.frame.exec.gasAvailable.toNat_lt
  have hchildNat : child.exec.gasAvailable.toNat
      = allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat := by
    rw [hcg, hchild, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  simp only [activeGas, Pending.savedGas]
  rw [hchildNat]
  omega

open BytecodeLayer in
/-- **`DescentDrops` discharged.** All five per-transition decrease obligations
hold; the create descent (4') is sound under the kind-aware `Pending.savedGas`. -/
theorem descentDrops_holds : DescentDrops :=
  ⟨descentDrops_conj3, descentDrops_conj4, descentDrops_conj5a,
    descentDrops_conj4', descentDrops_conj5b⟩

open BytecodeLayer in
/-- **General `messageCall` never out-of-fuel — unconditional.** No
`DescentDrops`, no `Frame`/fuel hypothesis: for every `CallParams`, the message
call never returns `OutOfFuel`. -/
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_descentDrops descentDrops_holds p

end BytecodeLayer.Proof

