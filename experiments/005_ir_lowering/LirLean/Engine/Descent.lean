import LirLean.Engine.StepWalk

/-!
# `LirLean.Engine.Descent` — the per-kind CALL/CREATE descent facts (engine level)

The structural facts of the interpreter's two *descents* (`.needsCall` → `beginCall` →
child run → `resumeAfterCall`; `.needsCreate` → `beginCreate` → child run →
`resumeAfterCreate`), extracted verbatim from the former `V2/TieDischarge.lean` monolith (names and namespaces
unchanged; zero IR / zero recorder / zero `SelfPresent`):

* the CALL-site inversions (`callArm_needsCall_inv` / `systemOp_needsCall_inv` /
  `stepFrame_needsCall_inv`) and their CREATE twins (`createArm_needsCreate_inv` /
  `systemOp_needsCreate_inv` / `stepFrame_needsCreate_inv`);
* `beginCall`/`beginCreate` presence + checkpoint threading into the child
  (`beginCall_inl_accounts_present` / `beginCall_inl_checkpoint` /
  `beginCreate_ok_accounts_present` / `beginCreate_ok_checkpoint`);
* the `resumeAfterCreate` accounts/kind facts (`toCreateResult_accounts_eq` /
  `resumeAfterCreate_exec_accounts_present` / `resumeAfterCreate_kind`).

The `DescentKind` interface packaging these per-kind facts uniformly (CALL and CREATE as
its two instances) is appended at the end of this file.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Evm
open GasConstants

/-! ### CALL-site inversion facts (`hcall_acc` / `hcall_kind` / `hcall_self`)

The three structural CALL-site facts supplied to `callPreservesSelf`, all inverting
`stepFrame → systemOp → callArm`'s `.needsCall` arm. In that arm `callArm` builds
`pd.frame := { fr with exec := e2 }` and `cp.accounts := accounts` where `accounts := e1.accounts`
(the post-mem-charge map, `= exec.accounts` since `charge` preserves accounts); `e2`'s execution
environment equals `exec`'s. So all three are universally true. -/

/-- **`callArm` `.needsCall` structural inversion.** The issued child params' accounts equal the
issuing `exec.accounts`, the suspended parent frame keeps `fr`'s `kind`, and its execution
environment equals `exec`'s. -/
theorem callArm_needsCall_inv
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {p : CallParams} {pd : PendingCall}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.needsCall p pd)) :
    p.accounts = exec.accounts ∧ pd.frame.kind = fr.kind
      ∧ pd.frame.exec.executionEnv = exec.executionEnv := by
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
      obtain ⟨he1acc, he1env⟩ := Lir.V2.charge_accounts_env he1
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
        obtain ⟨he2acc, he2env⟩ := Lir.V2.charge_accounts_env he2
        split at h
        · -- needsCall branch
          simp only [Except.ok.injEq, Signal.needsCall.injEq] at h
          obtain ⟨hp, hpd⟩ := h
          subst hp hpd
          refine ⟨?_, rfl, ?_⟩
          · show e1.accounts = exec.accounts; exact he1acc
          · show e2.executionEnv = exec.executionEnv; rw [he2env, he1env]
        · -- next (fallback): not a needsCall
          simp only [Except.ok.injEq] at h; exact absurd h (by simp)

/-- **`systemOp` `.needsCall` structural inversion.** Lifts `callArm_needsCall_inv` through the
CALL-family `systemOp` reduction (the only `.needsCall` source). -/
theorem systemOp_needsCall_inv {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {p : CallParams} {pd : PendingCall}
    (h : systemOp op fr exec = .ok (.needsCall p pd)) :
    p.accounts = exec.accounts ∧ pd.frame.kind = fr.kind
      ∧ pd.frame.exec.executionEnv = exec.executionEnv := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h)
      (BytecodeLayer.System.haltOp_never_needsCall (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      BytecodeLayer.System.systemOp_callArm_reduce (by tauto) h
    exact callArm_needsCall_inv hc
  | CREATE =>
    obtain ⟨_, _, _, _, _, _, _, hcr⟩ :=
      BytecodeLayer.System.systemOp_createArm_reduce (by tauto) h
    exact absurd hcr BytecodeLayer.System.createArm_never_needsCall
  | CREATE2 =>
    obtain ⟨_, _, _, _, _, _, _, hcr⟩ :=
      BytecodeLayer.System.systemOp_createArm_reduce (by tauto) h
    exact absurd hcr BytecodeLayer.System.createArm_never_needsCall

/-- **`stepFrame` `.needsCall` structural inversion (the bundle behind `hcall_acc`/`hcall_kind`/
`hcall_self`).** Via `stepFrame_needsCall_systemOp` then `systemOp_needsCall_inv`. -/
theorem stepFrame_needsCall_inv {fr : Frame} {p : CallParams} {pd : PendingCall}
    (h : stepFrame fr = .needsCall p pd) :
    p.accounts = fr.exec.accounts ∧ pd.frame.kind = fr.kind
      ∧ pd.frame.exec.executionEnv = fr.exec.executionEnv := by
  obtain ⟨s, hs⟩ := BytecodeLayer.Dispatch.stepFrame_needsCall_systemOp h
  exact systemOp_needsCall_inv hs

/-! ### CREATE-site inversion facts (the create twins of the CALL-site facts)

The structural CREATE-site facts inverting `stepFrame → systemOp → createArm`'s `.needsCreate` arm.
In that arm `createArm` builds `pd.frame := { fr with exec := exec }` (same `kind`, same
`exec.accounts`) and `cp.accounts := accountsWithBump := exec.accounts.insert self { … }` (a single
nonce-bump `insert`, so presence at any `a` survives — Brick A). The `exec` here is the post-charge
state (`chargeMemExpansion`/`createCost` are accounts-verbatim), so the facts are stated against the
issuing `fr.exec.accounts`. These are the create analogues of `callArm_needsCall_inv` /
`stepFrame_needsCall_inv`; they replace the old false-universal no-CREATE seam — the CREATE-fault arm
now returns the caller checkpoint (`pd.frame.exec.accounts`), so it preserves presence. -/

/-- **`createArm` `.needsCreate` structural inversion.** The issued child params' accounts retain
presence at any `a` present in the issuing `exec.accounts` (`accountsWithBump` is one `insert`), the
suspended parent frame keeps `fr`'s `kind`, and its running map is exactly `exec.accounts` (the
create-fault checkpoint world the caller resumes into). -/
theorem createArm_needsCreate_inv
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray}
    {cp : CreateParams} {pd : PendingCreate}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.needsCreate cp pd)) :
    (∀ a, Lir.V2.AccPresent a exec.accounts → Lir.V2.AccPresent a cp.accounts)
      ∧ pd.frame.kind = fr.kind ∧ pd.frame.exec.accounts = exec.accounts
      ∧ pd.frame.exec.executionEnv = exec.executionEnv := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- nonce overflow: `.next`, not `.needsCreate`
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f => intro h; simp at h
  · split at h
    · -- the `.needsCreate` branch: `cp.accounts = accountsWithBump`, `pd.frame = { fr with exec := exec }`
      simp only [Except.ok.injEq, Signal.needsCreate.injEq] at h
      obtain ⟨hcp, hpd⟩ := h
      subst hcp hpd
      refine ⟨?_, rfl, rfl, rfl⟩
      intro a ha
      -- `cp.accounts = exec.accounts.insert self { selfAccount with nonce := … }` (single insert).
      exact Lir.V2.accounts_find?_insert_mono _ _ _ _ ha
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f => intro h; simp at h

/-- **`systemOp` `.needsCreate` structural inversion.** Lifts `createArm_needsCreate_inv` through the
CREATE-family `systemOp` reduction (the only `.needsCreate` source), transporting presence back
through the accounts-verbatim `chargeMemExpansion`/create-cost charge. -/
theorem systemOp_needsCreate_inv {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {cp : CreateParams} {pd : PendingCreate}
    (h : systemOp op fr exec = .ok (.needsCreate cp pd)) :
    (∀ a, Lir.V2.AccPresent a exec.accounts → Lir.V2.AccPresent a cp.accounts)
      ∧ pd.frame.kind = fr.kind ∧ pd.frame.exec.accounts = exec.accounts
      ∧ pd.frame.exec.executionEnv = exec.executionEnv := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h)
      (BytecodeLayer.System.haltOp_never_needsCreate (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      BytecodeLayer.System.systemOp_callArm_reduce (by tauto) h
    exact absurd hc BytecodeLayer.System.callArm_never_needsCreate
  | CREATE =>
    -- Unfold `systemOp`'s CREATE arm to expose `createArm fr ec …` on the charged `ec`, tracking
    -- `ec.accounts = exec.accounts` through the accounts-verbatim `chargeMemExpansion`/`createCost`.
    unfold systemOp at h
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
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              have hem : ec.accounts = exec.accounts := by rw [hcacc, hmacc]
              have hemenv : ec.executionEnv = exec.executionEnv := by rw [hcenv, hmenv]
              obtain ⟨hacc, hkind, hpdacc, hpdenv⟩ := createArm_needsCreate_inv h
              refine ⟨fun a ha => hacc a (hem ▸ ha), hkind, by rw [hpdacc, hem],
                by rw [hpdenv, hemenv]⟩
  | CREATE2 =>
    unfold systemOp at h
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
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              have hem : ec.accounts = exec.accounts := by rw [hcacc, hmacc]
              have hemenv : ec.executionEnv = exec.executionEnv := by rw [hcenv, hmenv]
              obtain ⟨hacc, hkind, hpdacc, hpdenv⟩ := createArm_needsCreate_inv h
              refine ⟨fun a ha => hacc a (hem ▸ ha), hkind, by rw [hpdacc, hem],
                by rw [hpdenv, hemenv]⟩

/-- **`stepFrame` `.needsCreate` structural inversion (the create twin of `stepFrame_needsCall_inv`).**
The issued child params keep presence at any `a` present in the issuing `fr.exec.accounts`, the
suspended parent frame keeps `fr`'s `kind`, and its running map is exactly `fr.exec.accounts`. (The
third conjunct is now slack — it fed the removed CREATE-begin-fault arm; `beginCreate` is total.) Via
`stepFrame_needsCreate_systemOp` then `systemOp_needsCreate_inv`. -/
theorem stepFrame_needsCreate_inv {fr : Frame} {cp : CreateParams} {pd : PendingCreate}
    (h : stepFrame fr = .needsCreate cp pd) :
    (∀ a, Lir.V2.AccPresent a fr.exec.accounts → Lir.V2.AccPresent a cp.accounts)
      ∧ pd.frame.kind = fr.kind ∧ pd.frame.exec.accounts = fr.exec.accounts
      ∧ pd.frame.exec.executionEnv = fr.exec.executionEnv := by
  obtain ⟨s, hs⟩ := BytecodeLayer.Dispatch.stepFrame_needsCreate_systemOp h
  exact systemOp_needsCreate_inv hs

end Evm

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps

/-- **`beginCall` threads presence at `a` into the code child.** When a CALL begins as a code child
(`beginCall cp = .inl child`), the child's running `exec.accounts` is `accountsAfterTransfer` — a
credit (recipient) then debit (caller) `insert` chain over `cp.accounts`; each branch is either
verbatim (`none`) or an `insert` (`some`), so presence at any `a` present in `cp.accounts` survives
(Brick A). And the child's kind checkpoint is exactly `cp.accounts` (the `.call ⟨_, cp.accounts, _⟩`
node), present by hypothesis. This is the non-vacuous witness that the child drive run *starts*
present at the caller's address. -/
theorem beginCall_inl_accounts_present (a : Evm.AccountAddress) (cp : Evm.CallParams)
    {child : Evm.Frame} (hbc : Evm.beginCall cp = .inl child)
    (h : AccPresent a cp.accounts) :
    AccPresent a child.exec.accounts := by
  -- Reduce `beginCall` to its `.inl` (Code) arm and read off `child.exec.accounts`.
  unfold Evm.beginCall at hbc
  -- The credit step preserves presence at `a` (none → verbatim, some → insert mono).
  have hcredit : AccPresent a
      (match cp.accounts.find? cp.recipient with
        | none =>
          if cp.value != (0 : UInt256) then
            cp.accounts.insert cp.recipient { (default : Evm.Account) with balance := cp.value }
          else cp.accounts
        | some acc =>
          cp.accounts.insert cp.recipient { acc with balance := acc.balance + cp.value }) := by
    cases hr : cp.accounts.find? cp.recipient with
    | none =>
      simp only [hr]
      by_cases hv : cp.value != (0 : UInt256)
      · rw [if_pos hv]; exact accounts_find?_insert_mono _ _ _ _ h
      · rw [if_neg hv]; exact h
    | some acc => simp only [hr]; exact accounts_find?_insert_mono _ _ _ _ h
  -- The debit step over the credited map likewise preserves presence at `a`.
  set credited :=
    (match cp.accounts.find? cp.recipient with
        | none =>
          if cp.value != (0 : UInt256) then
            cp.accounts.insert cp.recipient { (default : Evm.Account) with balance := cp.value }
          else cp.accounts
        | some acc =>
          cp.accounts.insert cp.recipient { acc with balance := acc.balance + cp.value }) with hcred
  have htransfer : AccPresent a
      (match credited.find? cp.caller with
        | none => credited
        | some acc => credited.insert cp.caller { acc with balance := acc.balance - cp.value }) := by
    cases hc : credited.find? cp.caller with
    | none => simp only [hc]; exact hcredit
    | some acc => simp only [hc]; exact accounts_find?_insert_mono _ _ _ _ hcredit
  -- In the Code arm, `child.exec.accounts = accountsAfterTransfer = the debited map`.
  cases hcs : cp.codeSource with
  | Precompiled p => rw [hcs] at hbc; simp only [Sum.inl.injEq] at hbc; exact absurd hbc (by nofun)
  | Code code =>
    rw [hcs] at hbc
    simp only [Sum.inl.injEq] at hbc
    rw [← hbc]
    -- `child.exec.accounts` is definitionally `accountsAfterTransfer` (the debited map).
    exact htransfer

/-- **`beginCall`'s code child carries `cp.accounts` as its kind checkpoint.** The `.inl` (Code) arm
builds `kind := .call ⟨_, cp.accounts, _⟩`; so the checkpoint that `endCall .revert/.exception` rolls
back to is exactly `cp.accounts`. -/
theorem beginCall_inl_checkpoint (cp : Evm.CallParams) {child : Evm.Frame}
    (hbc : Evm.beginCall cp = .inl child) :
    ∃ created sub, child.kind = .call ⟨created, cp.accounts, sub⟩ := by
  unfold Evm.beginCall at hbc
  cases hcs : cp.codeSource with
  | Precompiled p => rw [hcs] at hbc; simp only [Sum.inl.injEq] at hbc; exact absurd hbc (by nofun)
  | Code code =>
    rw [hcs] at hbc
    simp only [Sum.inl.injEq] at hbc
    exact ⟨cp.createdAccounts, cp.substate, by rw [← hbc]⟩

/-- **`beginCreate` threads presence at `a` into the init-code child.** When a CREATE descends into a
child (`beginCreate params = child`, total), the child's running `exec.accounts` is `accountsWithNew` —
either `params.accounts` verbatim (`none`) or a creator-debit then new-account-credit `insert` chain
(`some`); every branch is verbatim or an `insert`, so presence at any `a` present in `params.accounts`
survives (Brick A). The create twin of `beginCall_inl_accounts_present`. -/
theorem beginCreate_ok_accounts_present (a : Evm.AccountAddress) (params : Evm.CreateParams)
    {child : Evm.Frame} (hbc : Evm.beginCreate params = child)
    (h : AccPresent a params.accounts) :
    AccPresent a child.exec.accounts := by
  rw [Evm.beginCreate] at hbc
  rw [← hbc]
  -- `child.exec.accounts = accountsWithNew = match params.accounts.find? creator with …`
  -- (`beginCreate` is total — no `.error` arm — so the body is unconditional.)
  show AccPresent a
    (match params.accounts.find? params.caller with
      | none => params.accounts
      | some ac =>
        (params.accounts.insert params.caller
          { ac with balance := ac.balance - params.value }).insert _ _)
  cases hcr : params.accounts.find? params.caller with
  | none => simp only [hcr]; exact h
  | some ac =>
    simp only [hcr]
    exact accounts_find?_insert_mono _ _ _ _ (accounts_find?_insert_mono _ _ _ _ h)

/-- **`beginCreate`'s init-code child carries `params.accounts` as its kind checkpoint.** The child's
`kind := .create newAddress ⟨_, params.accounts, _⟩`; so the checkpoint that `endCreate` failure and
the CREATE-fault arm roll back to is exactly `params.accounts`. The create twin of
`beginCall_inl_checkpoint`. -/
theorem beginCreate_ok_checkpoint (params : Evm.CreateParams) {child : Evm.Frame}
    (hbc : Evm.beginCreate params = child) :
    ∃ addr created sub, child.kind = .create addr ⟨created, params.accounts, sub⟩ := by
  rw [Evm.beginCreate] at hbc
  -- `beginCreate` is total — no `.error` arm — so the body is unconditional.
  exact ⟨_, _, _, by rw [← hbc]⟩

/-- `FrameResult`'s two result projections expose the **same** accounts field (`CreateResult extends
CallResult`, so both `.toCallResult.accounts` and `.toCreateResult.accounts` read the inherited
field). -/
theorem toCreateResult_accounts_eq (result : Evm.FrameResult) :
    result.toCreateResult.accounts = result.toCallResult.accounts := by
  cases result with
  | call r => rfl
  | create r => rfl

/-- `resumeAfterCreate` on `.ok` keeps the resumed running map equal to the result's accounts (it
sets `exec.accounts := result.accounts`), so presence at `a` transports from `hresult`. -/
theorem resumeAfterCreate_exec_accounts_present (a : Evm.AccountAddress) (result : Evm.FrameResult)
    (pd : Evm.PendingCreate) (parent : Evm.Frame)
    (hres : Evm.resumeAfterCreate result.toCreateResult pd = .ok parent)
    (hresult : AccPresent a result.toCallResult.accounts) :
    AccPresent a parent.exec.accounts := by
  unfold Evm.resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres
    rw [← hres]
    -- `parent.exec = exec'.replaceStackAndIncrPC …` and `exec'.accounts = result.toCreateResult.accounts`.
    show AccPresent a result.toCreateResult.accounts
    rw [toCreateResult_accounts_eq]; exact hresult

/-- `resumeAfterCreate` on `.ok` rebuilds `pd.frame` with the same `kind` (it touches only `exec`),
so checkpoint presence transports. -/
theorem resumeAfterCreate_kind (result : Evm.FrameResult) (pd : Evm.PendingCreate)
    (parent : Evm.Frame) (hres : Evm.resumeAfterCreate result.toCreateResult pd = .ok parent) :
    parent.kind = pd.frame.kind := by
  unfold Evm.resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres; rw [← hres]

/-- `resumeAfterCreate` on `.ok` rebuilds `pd.frame` with the same `executionEnv` (it touches only
`exec`'s stack/pc/gas/accounts/substate via `replaceStackAndIncrPC` over `pd.frame.exec`), so the
resumed self *address* is the suspended creator's. The create twin of `resumeAfterCall_address`. -/
theorem resumeAfterCreate_execEnv (result : Evm.FrameResult) (pd : Evm.PendingCreate)
    (parent : Evm.Frame) (hres : Evm.resumeAfterCreate result.toCreateResult pd = .ok parent) :
    parent.exec.executionEnv = pd.frame.exec.executionEnv := by
  unfold Evm.resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres; rw [← hres]
    rfl


/-! ### The `DescentKind` interface — CALL and CREATE as ONE descent shape

CALL and CREATE are the same interpreter shape — a *descent*: a `stepFrame` signal
(`.needsCall`/`.needsCreate`), a begin (`beginCall`, child frame ⊕ immediate result;
`beginCreate`, total — always a child), a black-box child `drive` run, and a resume
(`resumeAfterCall`, total; `resumeAfterCreate`, can fault). `DescentKind` packages the
per-kind data + the presence/checkpoint/kind laws proven above, so the descent machinery
(Phase 3.5's first-class CREATE) instantiates ONE interface instead of duplicating the
CALL ecosystem. The `resume` field is `Except`-valued because `resumeAfterCreate` faults;
the CALL instance wraps `resumeAfterCall` in `.ok` (which is why `descentReturns_call_iff`
is a lemma rather than `rfl`).

Organization of existing green lemmas: every law field is `:=`-wired (with 1-line adapters
where the per-kind lemma is *stronger* than the common weakening — the CALL inversion's
equality conclusions stay untouched under their own names). No consumer is re-plumbed:
`Runs.call` and the `callPreservesSelf` chain keep consuming `CallReturns`;
`DescentReturns createDescent` has no consumer yet by design. -/

/-- A descent kind: the data of one CALL-family interpreter descent
(signal → begin → child run → resume) together with the account-presence /
checkpoint / kind laws every kind satisfies. -/
structure DescentKind where
  /-- descent parameters (`CallParams` / `CreateParams`). -/
  Params : Type
  /-- the suspended parent (`PendingCall` / `PendingCreate`). -/
  Pending : Type
  /-- the descent's result (`CallResult` / `CreateResult`). -/
  Result : Type
  /-- the `stepFrame` signal announcing the descent (`.needsCall` / `.needsCreate`). -/
  signal : Params → Pending → Evm.Signal
  /-- descend into a child frame, or resolve immediately —
  `beginCall` / (`.inl ∘ beginCreate`, total post-RLP). -/
  descend : Params → Evm.Frame ⊕ Result
  /-- resume the suspended parent — `(.ok ∘ resumeAfterCall ·)` (total) /
  `resumeAfterCreate` (can fault), hence `Except`-valued at the common shape. -/
  resume : Result → Pending → Except Evm.ExecutionException Evm.Frame
  /-- project the child run's `FrameResult` (`.toCallResult` / `.toCreateResult`). -/
  toResult : Evm.FrameResult → Result
  /-- the descent's gas seed (`CallParams.gas` / `CreateParams.gas`). -/
  gasOf : Params → UInt64
  /-- the suspended parent frame (`PendingCall.frame` / `PendingCreate.frame`). -/
  pendingFrame : Pending → Evm.Frame
  /-- the accounts issued to the descent (`CallParams.accounts` / `CreateParams.accounts`). -/
  paramsAccounts : Params → Evm.AccountMap
  /-- the result's world accounts (`CallResult.accounts` / `CreateResult.accounts`). -/
  resultAccounts : Result → Evm.AccountMap
  /-- the suspended parent keeps the issuing frame's `kind`. -/
  needs_kind : ∀ {fr : Evm.Frame} {p : Params} {pd : Pending},
    Evm.stepFrame fr = signal p pd → (pendingFrame pd).kind = fr.kind
  /-- presence at any `a` transports from the issuing frame's running map into the
  issued `paramsAccounts`. -/
  needs_accPresent : ∀ {fr : Evm.Frame} {p : Params} {pd : Pending},
    Evm.stepFrame fr = signal p pd →
      ∀ a, AccPresent a fr.exec.accounts → AccPresent a (paramsAccounts p)
  /-- a code descent threads presence at any `a` into the child's running map. -/
  descend_present : ∀ {p : Params} {child : Evm.Frame},
    descend p = .inl child →
      ∀ a, AccPresent a (paramsAccounts p) → AccPresent a child.exec.accounts
  /-- a code descent pins the child's kind checkpoint to the issued `paramsAccounts`
  (stated as presence transport into the checkpoint accounts, the common weakening of
  `beginCall_inl_checkpoint` / `beginCreate_ok_checkpoint`). -/
  descend_checkpoint : ∀ {p : Params} {child : Evm.Frame},
    descend p = .inl child →
      ∀ a, AccPresent a (paramsAccounts p) →
        (match child.kind with
         | .call ck => AccPresent a ck.accounts
         | .create _ ck => AccPresent a ck.accounts)
  /-- a successful resume takes the result's accounts as the resumed running map
  (presence transport, the common weakening of `resumeAfterCall_accounts` /
  `resumeAfterCreate_exec_accounts_present`). -/
  resume_accounts : ∀ {r : Result} {pd : Pending} {fr' : Evm.Frame},
    resume r pd = .ok fr' →
      ∀ a, AccPresent a (resultAccounts r) → AccPresent a fr'.exec.accounts

/-- **The CALL descent.** `signal = .needsCall`, `descend = beginCall` (precompile/empty
resolves immediately via `.inr`), `resume = .ok ∘ resumeAfterCall` (total). Laws are the
CALL-site inversion / begin / resume lemmas above, weakened to the common shape (the
stronger equality forms keep their names untouched). -/
def callDescent : DescentKind where
  Params := Evm.CallParams
  Pending := Evm.PendingCall
  Result := Evm.CallResult
  signal := .needsCall
  descend := Evm.beginCall
  resume := fun r pd => .ok (Evm.resumeAfterCall r pd)
  toResult := Evm.FrameResult.toCallResult
  gasOf := Evm.CallParams.gas
  pendingFrame := Evm.PendingCall.frame
  paramsAccounts := Evm.CallParams.accounts
  resultAccounts := Evm.CallResult.accounts
  needs_kind := fun h => (Evm.stepFrame_needsCall_inv h).2.1
  needs_accPresent := fun h a hp => (Evm.stepFrame_needsCall_inv h).1 ▸ hp
  descend_present := fun h a hp => beginCall_inl_accounts_present a _ h hp
  descend_checkpoint := fun h a hp => by
    obtain ⟨created, sub, hk⟩ := beginCall_inl_checkpoint _ h
    rw [hk]; exact hp
  resume_accounts := fun h a hp => by
    injection h with h; rw [← h]; exact hp

/-- **The CREATE descent.** `signal = .needsCreate`, `descend = .inl ∘ beginCreate`
(total post-RLP — no immediate arm), `resume = resumeAfterCreate` (can fault). Laws are
the CREATE-site inversion / begin / resume lemmas above. -/
def createDescent : DescentKind where
  Params := Evm.CreateParams
  Pending := Evm.PendingCreate
  Result := Evm.CreateResult
  signal := .needsCreate
  descend := fun p => .inl (Evm.beginCreate p)
  resume := Evm.resumeAfterCreate
  toResult := Evm.FrameResult.toCreateResult
  gasOf := Evm.CreateParams.gas
  pendingFrame := Evm.PendingCreate.frame
  paramsAccounts := Evm.CreateParams.accounts
  resultAccounts := fun r => r.accounts
  needs_kind := fun h => (Evm.stepFrame_needsCreate_inv h).2.1
  needs_accPresent := fun h a hp => (Evm.stepFrame_needsCreate_inv h).1 a hp
  descend_present := fun h a hp => by
    injection h with h
    exact beginCreate_ok_accounts_present a _ h hp
  descend_checkpoint := fun h a hp => by
    injection h with h
    obtain ⟨addr, created, sub, hk⟩ := beginCreate_ok_checkpoint _ h
    rw [hk]; exact hp
  resume_accounts := fun {r pd fr'} h a hp =>
    resumeAfterCreate_exec_accounts_present a (.create r) pd fr' h hp

/-- **The begin-immediate no-erase law.** A descent resolving immediately (`descend = .inr`)
preserves presence at any `a` from the issued `paramsAccounts` into the immediate result's
accounts. For `callDescent` this is **verbatim the `hprec` seam** (`beginCall`'s precompile
`.inr` arm — the one surviving supplied hypothesis of the `callPreservesSelf` chain, quoted
by `V2/Realisability/RealisabilitySpec.lean`); for `createDescent` it is a theorem
(`createDescent_descendImmediate_trivial` — `beginCreate` never resolves immediately). -/
def DescentKind.DescendImmediateNoErase (k : DescentKind) : Prop :=
  ∀ (p : k.Params) (imm : k.Result), k.descend p = .inr imm →
    ∀ a, AccPresent a (k.paramsAccounts p) → AccPresent a (k.resultAccounts imm)

/-- **CREATE's begin-immediate law is trivial** (the post-RLP-totality analogue of the CALL
seam): `createDescent.descend` is `.inl ∘ beginCreate` — there is no `.inr` arm. -/
theorem createDescent_descendImmediate_trivial :
    createDescent.DescendImmediateNoErase := by
  intro p imm h
  exact absurd h (by simp [createDescent])

/-- **`DescentReturns k`: one returning descent of kind `k`** — the kind-generic shape of
`CallReturns` (`BytecodeLayer/Hoare.lean`): the signal at `frD`, a code descent into
`child`, the child's black-box terminating `drive` run, and a successful resume at `frR`.
`DescentReturns callDescent` IS `CallReturns` (`descentReturns_call_iff`);
`DescentReturns createDescent` is the CREATE analogue (no consumer yet by design —
Phase 3.5 instantiates it). -/
def DescentReturns (k : DescentKind) (frD frR : Evm.Frame) : Prop :=
  ∃ (p : k.Params) (pd : k.Pending) (child : Evm.Frame) (childRes : Evm.FrameResult),
      Evm.stepFrame frD = k.signal p pd
    ∧ k.descend p = .inl child
    ∧ drive (seedFuel (k.gasOf p)) [] (running child) = .ok childRes
    ∧ k.resume (k.toResult childRes) pd = .ok frR

/-- **Erasure: the CALL instance of `DescentReturns` is exactly `CallReturns`.** Conjuncts
1–3 are definitional (`EntersAsCode` is an abbrev for `beginCall p = .inl child`); conjunct 4
differs only by the `.ok` wrapper the uniform `Except`-valued `resume` forces on the total
CALL side (`Except.ok` injectivity + symmetry). -/
theorem descentReturns_call_iff (frD frR : Evm.Frame) :
    DescentReturns callDescent frD frR ↔ CallReturns frD frR := by
  constructor
  · rintro ⟨p, pd, child, childRes, hsig, hdesc, hdrive, hres⟩
    injection hres with hres
    exact ⟨p, pd, child, childRes, hsig, hdesc, hdrive, hres.symm⟩
  · rintro ⟨p, pd, child, childRes, hsig, henters, hdrive, hres⟩
    exact ⟨p, pd, child, childRes, hsig, henters, hdrive, by rw [hres]; rfl⟩

end Lir.V2

