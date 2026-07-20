import Evm
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Semantics.Gas
import BytecodeLayer.Semantics.Precompiles

/-!
# `System`-op semantic facts (CALL / CREATE / Halt / resume machinery)

The reusable, measure-independent facts about the vendored `Evm/` tree's `System`-op machinery
(`callArm`/`createArm`/`systemOp`/`haltOp`/`beginCall`/`beginCreate`/
`resumeAfterCall`/`resumeAfterCreate`). They belong with the System semantics
they are about, well below the fuel-measure layer in the import DAG.

This file gathers:

* **The CALL rule** (`stepFrame_call` and its `callerCharged`/`callChildParams`/
  `callPending` building blocks): a real `CALL` instruction — through the public
  `callArm` — and the `drive` `.needsCall` arm that turns it into a *reflexive*
  child `messageCall` (the real engine computation, never an oracle). Restricted
  to the value-free, zero-memory CALL shape so the only quantitative gas content
  is the 63/64 `callGasCap`.
* **The `beginCall` entry characterization** (`beginCall_code`, with
  `codeAccounts`/`codeEnv`/`codeFrame`): pins the initial code-call `Frame`; the
  single bridge that unfolds `beginCall`.
* **Gas accessors + resume/halt facts** (`FrameResult.gasRemaining`, the
  `resumeAfter*` gas bounds, the `haltOp`/`gasOf`/`neverHalts` shape lemmas,
  `beginCall_inl_gas`, `endFrame_gasRemaining_le`).
* **The `systemOp`/`callArm`/`createArm` descent/fallback inversions** that read
  off the gas relations each `Signal` arm forces.

These are low-level internal bricks (they mention `Frame`, `pending`, `Signal`,
gas caps); they exist only so the fuel argument and external-call capstone can
reason past `System` ops without exposing frames or fuel in exported statements.
-/

namespace BytecodeLayer.System
open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer.UInt64
open BytecodeLayer.Gas
open BytecodeLayer.Precompiles

/-- `0` is the least `UInt256` (its `toBitVec` is `0`, below every BitVec). The
balance/value guard in `callArm` for the value-free case is `0 ≤ balance`, which
this discharges unconditionally. -/
theorem UInt256.zero_le (x : UInt256) : (0 : UInt256) ≤ x := by
  show (0 : UInt256).toBitVec ≤ x.toBitVec
  rw [show (0 : UInt256).toBitVec = 0 from rfl, BitVec.le_def]
  simp

/-- The execution state of the caller frame **after** `callArm` charges the call
cost (`callGasCap + callExtraCost`), for the value-free zero-memory shape. This
is the `exec` carried into the suspended `PendingCall`. The mem-expansion charge
is `0` (size `0`), so only the call charge is subtracted. -/
def callerCharged (exec : ExecutionState) (toAddr gasv : UInt256) : ExecutionState :=
  { exec with
      gasAvailable := exec.gasAvailable - UInt64.ofNat
        (callGasCap (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0 gasv
            exec.accounts exec.gasAvailable exec.substate
          + callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
              exec.accounts exec.substate) }

/-- The child `CallParams` a value-free zero-memory `CALL` to `toAddr` produces:
the **reflexive** message call. `codeSource = toExecute accounts toAddr` reads the
callee's real code from the (post-charge) account map; `gas` is the 63/64-capped
`callGasCap`; `depth` is bumped. This is the child `messageCall` argument — no
oracle. -/
def callChildParams (fr : Frame) (toAddr gasv : UInt256) : CallParams :=
  let v := callerCharged fr.exec toAddr gasv
  { blobVersionedHashes := v.executionEnv.blobVersionedHashes
    createdAccounts := v.createdAccounts
    genesisBlockHeader := v.genesisBlockHeader
    blocks := v.blocks
    accounts := fr.exec.accounts
    originalAccounts := v.originalAccounts
    substate := (v.addAccessedAccount (AccountAddress.ofUInt256 toAddr)).substate
    caller := AccountAddress.ofUInt256 (UInt256.ofNat fr.exec.executionEnv.address)
    origin := v.executionEnv.origin
    recipient := AccountAddress.ofUInt256 toAddr
    codeSource := toExecute fr.exec.accounts (AccountAddress.ofUInt256 toAddr)
    gas := UInt64.ofNat
      (callGasCap (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0 gasv
        fr.exec.accounts fr.exec.gasAvailable fr.exec.substate)
    gasPrice := UInt256.ofNat v.executionEnv.gasPrice
    value := 0
    apparentValue := 0
    calldata := v.memory.readWithPadding (UInt256.toNat 0) (UInt256.toNat 0)
    depth := fr.exec.executionEnv.depth + 1
    blockHeader := v.executionEnv.blockHeader
    chainId := v.executionEnv.chainId
    canModifyState := fr.exec.executionEnv.canModifyState }

/-- The suspended parent frame after a value-free zero-memory `CALL`: the caller
frame with its charged exec, an empty residual operand stack (all 7 args popped),
and zero in/out memory windows. -/
def callPending (fr : Frame) (toAddr gasv : UInt256) : PendingCall :=
  { frame := { kind := fr.kind, validJumps := fr.validJumps, exec := callerCharged fr.exec toAddr gasv }
    stack := []
    callerAccounts := fr.exec.accounts
    value := 0
    inOffset := UInt256.toUInt64 0
    inSize := UInt256.toUInt64 0
    outOffset := UInt256.toUInt64 0
    outSize := UInt256.toUInt64 0 }

-- `hsz`/`hmod` are part of the documented CALL premise set (stack non-overflow,
-- state-modifying context) but are vacuous for the exact 7-element, value-0 shape,
-- so they go unused in the proof; kept in the signature for faithfulness.
set_option linter.unusedVariables false in
/-- **The CALL rule** (value-free, zero-memory, state-modifying). At a pc that
decodes to `CALL`, with the 7 args `[gas, toAddr, 0,0,0,0,0]` on the stack (gas on
top, value=0), `depth < 1024`, state-modifying context, and enough gas to cover
`callExtraCost`, `stepFrame` emits `.needsCall (callChildParams …) (callPending …)`.
The child params' `codeSource` is `toExecute accounts toAddr` — the **real**
callee code — so the driver's `.needsCall` arm runs the genuine child
`messageCall`, not an oracle. -/
theorem stepFrame_call (fr : Frame) (gasv toAddr : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .CALL, .none))
    (hstk : fr.exec.stack = gasv :: toAddr :: 0 :: 0 :: 0 :: 0 :: 0 :: [])
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hdepth : fr.exec.executionEnv.depth < 1024)
    (hgas : callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
        fr.exec.accounts fr.exec.substate ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .needsCall (callChildParams fr toAddr gasv) (callPending fr toAddr gasv) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.System .CALL)
      + stackPushCount (.System .CALL) > 1024) := by
    rw [hstk] at hsz
    simp only [show stackPopCount (.System .CALL) = 7 from rfl,
               show stackPushCount (.System .CALL) = 1 from rfl, hstk, Stack.size]
    simp only [List.length] at hsz ⊢
    omega
  rw [if_neg hov]
  dsimp only [dispatch, systemOp]
  rw [hstk]
  dsimp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift, Option.option,
    bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp)]
  unfold callArm
  dsimp only [memoryExpansionWords?, bind, Except.bind, pure, Except.pure]
  simp only [show (((0:UInt256))==0) = true from rfl, if_true, Option.bind_some]
  rw [show (Cₘ fr.exec.activeWords - Cₘ fr.exec.activeWords) = 0 from by omega]
  unfold charge
  rw [if_neg (by simp)]
  dsimp only
  -- `gasAvailable - UInt64.ofNat 0 = gasAvailable`
  rw [show fr.exec.gasAvailable - UInt64.ofNat 0 = fr.exec.gasAvailable from by
        simp]
  -- discharge the call-charge gas guard: callGasCap + extraCost ≤ gasAvailable
  have hcap : callGasCap (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0 gasv
      fr.exec.accounts fr.exec.gasAvailable fr.exec.substate
      + callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
          fr.exec.accounts fr.exec.substate ≤ fr.exec.gasAvailable.toNat := by
    unfold callGasCap
    rw [if_pos hgas]
    have hmin : min (allButOneSixtyFourth (fr.exec.gasAvailable.toNat
        - callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
            fr.exec.accounts fr.exec.substate)) gasv.toNat
        ≤ fr.exec.gasAvailable.toNat
          - callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
              fr.exec.accounts fr.exec.substate := by
      apply le_trans (min_le_left _ _)
      unfold allButOneSixtyFourth; omega
    omega
  rw [if_neg (by
    rw [not_lt]
    -- goal: callGasCap + extraCost ≤ gasAvailable.toNat  (as UInt64 compare via toNat)
    exact hcap)]
  dsimp only
  -- depth/balance guard: 0 ≤ balance ∧ depth < 1024
  rw [if_pos ⟨UInt256.zero_le _, hdepth⟩]
  rfl

/-! ## `beginCall` entry characterization for code calls

`beginCall` (`Evm/Semantics/Call.lean`) decides what running a `CallParams` produces *before* code
execution: a precompile result, or — for a `.Code` call — the initial `Frame` the
driver descends into. This pins that initial frame as named definitions
(`codeEnv`, `codeAccounts`, `codeFrame`) and proves `beginCall` equals it
(`beginCall_code`) for any `.Code` call. It is the **single bridge** that unfolds
`beginCall`. -/

/-- The account map after `beginCall`'s value credit (to the recipient) and debit
(from the caller) — mirrors `beginCall`'s `accountsAfterTransfer`. -/
def codeAccounts (params : CallParams) : AccountMap :=
  let accountsAfterCredit :=
    match params.accounts.find? params.recipient with
      | none =>
        if params.value != (0 : UInt256) then
          params.accounts.insert params.recipient { (default : Account) with balance := params.value }
        else
          params.accounts
      | some acc =>
        params.accounts.insert params.recipient { acc with balance := acc.balance + params.value }
  match accountsAfterCredit.find? params.caller with
    | none => accountsAfterCredit
    | some acc =>
      accountsAfterCredit.insert params.caller { acc with balance := acc.balance - params.value }

/-- The execution env `beginCall` builds for a `.Code code` call. -/
def codeEnv (params : CallParams) (code : ByteArray) : ExecutionEnv :=
  { address := params.recipient
    origin    := params.origin
    gasPrice  := params.gasPrice.toNat
    calldata  := params.calldata
    caller    := params.caller
    value  := params.apparentValue
    depth     := params.depth
    canModifyState      := params.canModifyState
    code      := code
    blockHeader := params.blockHeader
    blobVersionedHashes := params.blobVersionedHashes
    chainId   := params.chainId }

/-- The initial frame `beginCall` produces for a `.Code code` call. -/
def codeFrame (params : CallParams) (code : ByteArray) : Frame :=
  { kind := .call ⟨params.createdAccounts, params.accounts, params.substate⟩
    validJumps := validJumpDests code 0
    exec :=
      { (default : ExecutionState) with
          accounts := codeAccounts params
          originalAccounts := params.originalAccounts
          executionEnv := codeEnv params code
          substate := params.substate
          createdAccounts := params.createdAccounts
          gasAvailable := params.gas
          blocks := params.blocks
          genesisBlockHeader := params.genesisBlockHeader } }

/-- `p`'s call enters as code, starting at frame `fr` (as opposed to resolving
immediately to a precompile/empty result). -/
abbrev EntersAsCode (p : CallParams) (fr : Frame) : Prop := beginCall p = .inl fr

/-- **`beginCall` on a code call.** For any `params` whose code source is
`.Code code`, `beginCall` returns `.inl (codeFrame params code)` — the driver
descends into the initial frame, i.e. `EntersAsCode params (codeFrame params
code)`. The one place `beginCall` is unfolded. -/
theorem beginCall_code (params : CallParams) (code : ByteArray)
    (hc : params.codeSource = .Code code) :
    EntersAsCode params (codeFrame params code) := by
  unfold EntersAsCode
  unfold beginCall codeFrame codeEnv codeAccounts
  rw [hc]
  rfl


/-! ## Gas accessor (finished-frame result) -/

/-- The gas a finished frame result still carries. -/
def FrameResult.gasRemaining : FrameResult → ℕ
  | .call r   => r.gasRemaining.toNat
  | .create r => r.gasRemaining.toNat

/-! ## Obligation 2 — halting: `endFrame` never carries more gas than the frame

A halting step's result keeps at most the frame's available gas. `endCall` /
`endCreate` set `gasRemaining` to either `0`, a `revert`-carried gas, or the
halt's `exec.gasAvailable` (possibly minus a deposit). We bound the gas carried
by every `FrameHalt` reachable from `stepFrame` by the frame's pre-step gas. -/

theorem ite_le {c : Prop} [Decidable c] {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    (if c then a else b) ≤ m := by split <;> assumption

/-- The gas a `FrameHalt` carries. -/
def FrameHalt.gasOf : FrameHalt → ℕ
  | .success exec _    => exec.gasAvailable.toNat
  | .revert g _        => g.toNat
  | .exception _       => 0

theorem charge_gasOf_le {cost : ℕ} {exec exec' : ExecutionState}
    (h : charge cost exec = .ok exec') :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le h

theorem chargeMem_gasOf_le {exec exec' : ExecutionState} {off size : UInt256}
    (h : chargeMemExpansion exec off size = .ok exec') :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le h

/-- `returnOrRevertOp` halts with gas ≤ the input frame gas. -/
theorem returnOrRevertOp_gasOf_le {op : Operation.SystemOp} {exec : ExecutionState} {halt : FrameHalt}
    (h : returnOrRevertOp op exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  rw [returnOrRevertOp] at h
  cases hp : exec.stack.pop2 with
  | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨s, off, size⟩ := v; rw [hp] at h
    simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hm : chargeMemExpansion exec off size with
    | error e => rw [hm] at h; simp at h
    | ok ec =>
      rw [hm] at h
      have hle : ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasOf_le hm
      simp only [pure, Except.pure] at h
      split at h <;>
        · simp only [Except.ok.injEq, Signal.halted.injEq] at h
          subst h
          simp only [FrameHalt.gasOf, gasNat_replaceStackAndIncrPC]
          exact hle

/-- `selfdestructOp` halts with gas ≤ the input frame gas. -/
theorem selfdestructOp_gasOf_le {exec : ExecutionState} {halt : FrameHalt}
    (h : selfdestructOp exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  rw [selfdestructOp] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp [bind, Except.bind] at h
  | ok _ =>
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hp : exec.stack.pop with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, rw'⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hc : charge (selfdestructCost _ _) exec with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h
        have hle : ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_gasOf_le hc
        simp only [] at h
        -- the result is `.halted (.success (exec'.replaceStackAndIncrPC stack) .empty)`
        -- where exec' is ec with only account/substate fields changed (gas preserved).
        split at h <;>
          · simp only [Except.ok.injEq, Signal.halted.injEq] at h
            subst h
            simp only [FrameHalt.gasOf, gasNat_replaceStackAndIncrPC]
            exact hle

/-- `haltOp` halts with gas ≤ the input frame gas. -/
theorem haltOp_gasOf_le {op : Operation.SystemOp} {exec : ExecutionState} {halt : FrameHalt}
    (h : haltOp op exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  unfold haltOp at h
  cases op with
  | STOP =>
    simp only [Except.ok.injEq, Signal.halted.injEq] at h
    subst h; simp only [FrameHalt.gasOf]; omega
  | RETURN => exact returnOrRevertOp_gasOf_le h
  | REVERT => exact returnOrRevertOp_gasOf_le h
  | SELFDESTRUCT => exact selfdestructOp_gasOf_le h
  | INVALID => simp [throw, throwThe, MonadExceptOf.throw] at h
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A `Step` `s` *never halts* if no `.ok (.halted _)` is among its outputs. The
non-`System` dispatcher arms (and the helper combinators that build them) enjoy
this: their `.ok` outputs are all `continueWith` (`.next`) values; `.error`s and
`throw`s are not `.ok`. -/
def neverHalts (s : Step) : Prop := ∀ hl, s ≠ .ok (.halted hl)

theorem neverHalts_continueWith (e : ExecutionState) : neverHalts (continueWith e) := by
  intro hl he; simp [continueWith] at he

theorem neverHalts_error (e : ExecutionException) : neverHalts (.error e : Step) := by
  intro hl he; simp at he

theorem neverHalts_throw (e : ExecutionException) :
    neverHalts (throw e : Step) := by
  intro hl he; simp [throw, throwThe, MonadExceptOf.throw] at he

/-- An `.error`-shaped `Step` is not `.ok (.halted _)`. Closes the throw branches
after `throw`/`bind` are unfolded to `.error`. -/
theorem error_ne_okHalted (e : ExecutionException) (hl : FrameHalt) :
    ¬ ((.error e : Step) = .ok (.halted hl)) := by simp

theorem neverHalts_bind_except {α : Type} (m : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, m = .ok a → neverHalts (k a)) : neverHalts (m >>= k) := by
  intro hl he
  cases hm : m with
  | error e => rw [hm] at he; simp [bind, Except.bind] at he
  | ok a => rw [hm] at he; simp only [bind, Except.bind] at he; exact hk a hm hl he

theorem neverHalts_optionBind {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → neverHalts (k a)) :
    neverHalts ((o : Except ExecutionException α) >>= k) := by
  intro hl he
  cases ho : o with
  | none => rw [ho] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
  | some a =>
    rw [ho] at he; simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    exact hk a ho hl he

/-- A `charge`-then-`k` step never halts if `k` never does. -/
theorem neverHalts_chargeBind {cost : ℕ} {exec : ExecutionState} {k : ExecutionState → Step}
    (hk : ∀ ec, charge cost exec = .ok ec → neverHalts (k ec)) :
    neverHalts (charge cost exec >>= k) :=
  neverHalts_bind_except _ _ hk

/-- A `chargeMemExpansion`-then-`k` step never halts if `k` never does. -/
theorem neverHalts_memChargeBind {exec : ExecutionState} {off size : UInt256}
    {k : ExecutionState → Step} (hk : ∀ ec, neverHalts (k ec)) :
    neverHalts (chargeMemExpansion exec off size >>= k) := by
  apply neverHalts_bind_except; intro a _; exact hk a

theorem unOp_neverHalts {f : UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (unOp f exec cost) := by
  rw [unOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a⟩ _; exact neverHalts_continueWith _

theorem binOp_neverHalts {f : UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (binOp f exec cost) := by
  rw [binOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _; exact neverHalts_continueWith _

theorem ternOp_neverHalts {f : UInt256 → UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (ternOp f exec cost) := by
  rw [ternOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _; exact neverHalts_continueWith _

theorem pushOp_neverHalts {v : ExecutionState → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (pushOp v exec cost) := by
  rw [pushOp]; apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _

theorem unStateOp_neverHalts {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec : ExecutionState} :
    neverHalts (unStateOp f cost exec) := by
  rw [unStateOp]; apply neverHalts_optionBind; rintro ⟨s, a⟩ _
  apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _

theorem dup_neverHalts {n : ℕ} {exec : ExecutionState} : neverHalts (dup n exec) := by
  rw [dup]; apply neverHalts_chargeBind; intro ec _
  unfold neverHalts; intro hl he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp [continueWith] at he

theorem swap_neverHalts {n : ℕ} {exec : ExecutionState} : neverHalts (swap n exec) := by
  rw [swap]; apply neverHalts_chargeBind; intro ec _
  unfold neverHalts; intro hl he
  by_cases hg : List.length (ec.stack.take (n + 1)) = (n + 1)
  · rw [if_pos hg] at he; simp [continueWith] at he
  · rw [if_neg hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he

theorem logArm_neverHalts {exec : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256} :
    neverHalts (logArm exec stack offset size topics) := by
  rw [logArm]; apply neverHalts_bind_except; intro _ _
  apply neverHalts_memChargeBind; intro ec
  apply neverHalts_chargeBind; intro ec2 _; exact neverHalts_continueWith _

theorem smsfOp_neverHalts {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState} :
    neverHalts (smsfOp op fr exec) := by
  unfold smsfOp
  cases op with
  | POP =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, a⟩ _; exact neverHalts_continueWith _
  | MLOAD =>
    apply neverHalts_optionBind; rintro ⟨s, a⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | MSTORE =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | MSTORE8 =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | SLOAD => exact unStateOp_neverHalts
  | SSTORE =>
    apply neverHalts_bind_except; intro _ _
    by_cases hg : exec.gasAvailable.toNat ≤ Gcallstipend
    · simp only [hg, if_true]; exact neverHalts_throw _
    · simp only [hg, if_false]
      apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
      apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _
  | TLOAD => exact unStateOp_neverHalts
  | TSTORE =>
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _; exact neverHalts_continueWith _
  | MSIZE => exact pushOp_neverHalts
  | GAS => exact pushOp_neverHalts
  | JUMP =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, d⟩ _ hl he
    dsimp only at he
    split at he <;> simp [continueWith] at he
  | JUMPI =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, d, c⟩ _ hl he
    dsimp only at he
    split at he
    · split at he <;> simp [continueWith] at he
    · simp [continueWith] at he
  | PC => exact pushOp_neverHalts
  | JUMPDEST =>
    apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _
  | MCOPY =>
    apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _

/-- The non-`System` dispatcher arms never halt. -/
theorem dispatch_neverHalts {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} (hne : ∀ s, op ≠ .System s) :
    neverHalts (dispatch op arg fr exec) := by
  unfold dispatch
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | Smsf s => exact smsfOp_neverHalts
  | Log l => cases l <;>
      (apply neverHalts_optionBind; rintro _ _; exact logArm_neverHalts)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_neverHalts
    | _ =>
      apply neverHalts_chargeBind; intro ec _ hl he
      cases arg <;> simp [continueWith, throw, throwThe, MonadExceptOf.throw] at he
  | Dup d => exact dup_neverHalts
  | Swap s => exact swap_neverHalts
  | ArithLogic a => cases a <;>
      first
        | exact binOp_neverHalts | exact unOp_neverHalts | exact ternOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
           apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _)
  | Env e =>
    cases e <;>
      first
        | exact pushOp_neverHalts | exact unStateOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _
           apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
           exact neverHalts_continueWith _)
        | (apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _ hl he
           revert he; dsimp only; split
           · intro he; simp [bind, Except.bind] at he
           · exact (neverHalts_memChargeBind (k := _)
               (fun ec => neverHalts_chargeBind (fun ec2 _ => neverHalts_continueWith _)) hl))
  | Block b =>
    cases b <;>
      first
        | exact pushOp_neverHalts | exact unStateOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, i⟩ _
           apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _)

/-- `callArm` never halts: its outputs are `.needsCall` or `.next`. -/
theorem callArm_neverHalts {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} :
    neverHalts (callArm fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission) := by
  rw [callArm]
  -- `let some words' := … | throw .OutOfGas` then two charges then an `if`.
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none =>
    intro hl he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some words' =>
    simp only [bind, Except.bind]
    apply neverHalts_chargeBind; intro ec1 _
    apply neverHalts_chargeBind; intro ec2 _
    unfold neverHalts; intro hl he
    split at he <;> simp at he

/-- `createArm` never halts: its outputs are `.needsCreate` or `.next`. -/
theorem createArm_neverHalts {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} :
    neverHalts (createArm fr exec stack value initOffset initSize salt) := by
  rw [createArm]
  -- `resumeAfterCreate r p >>= fun f => pure (.next f.exec)` is the only `.ok`
  -- output in every branch; the continuation yields `.next`, never `.halted`.
  have hk : ∀ (r : CreateResult) (p : PendingCreate),
      neverHalts (resumeAfterCreate r p >>= fun f => (pure (.next f.exec) : Step)) := by
    intro r p
    apply neverHalts_bind_except; intro f _ hl he
    simp [pure, Except.pure] at he
  simp only [bind, Except.bind, pure, Except.pure]
  intro hl he
  split at he
  · exact hk _ _ hl he
  · split at he
    · simp at he
    · exact hk _ _ hl he

/-- `systemOp` halts with gas ≤ the input frame gas. Halt ops go through
`haltOp_gasOf_le`; the CALL/CREATE family never halts. -/
theorem systemOp_gasOf_le {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {halt : FrameHalt} (h : systemOp op fr exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  unfold systemOp at h
  cases op with
  | STOP => exact haltOp_gasOf_le h
  | RETURN => exact haltOp_gasOf_le h
  | REVERT => exact haltOp_gasOf_le h
  | SELFDESTRUCT => exact haltOp_gasOf_le h
  | INVALID => exact haltOp_gasOf_le h
  | CALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, v, io, is, oo, os⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · exact callArm_neverHalts hl he
  | CALLCODE =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, v, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | DELEGATECALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | STATICCALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | CREATE =>
    refine absurd h ?_
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_optionBind; rintro ⟨s, v, io, is⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · revert he
      exact (neverHalts_memChargeBind (k := _)
        (fun ec => neverHalts_chargeBind (fun ec2 _ => createArm_neverHalts)) hl)
  | CREATE2 =>
    refine absurd h ?_
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_optionBind; rintro ⟨s, v, io, is, salt⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · revert he
      exact (neverHalts_memChargeBind (k := _)
        (fun ec => neverHalts_chargeBind (fun ec2 _ => createArm_neverHalts)) hl)

/-- A `.halted` from `stepFrame` carries gas ≤ the frame's pre-step gas. The
halt comes from INVALID/overflow (gas 0), a dispatch `.error` (gas 0), or a
dispatch `.ok (.halted)`. The last forces a `System` halt op (non-System arms
`neverHalt`), bounded by `haltOp_gasOf_le`. -/
theorem stepFrame_halted_gasOf_le {fr : Frame} {halt : FrameHalt}
    (h : stepFrame fr = .halted halt) :
    FrameHalt.gasOf halt ≤ fr.exec.gasAvailable.toNat := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · simp only [Signal.halted.injEq] at h; subst h; simp only [FrameHalt.gasOf]; omega
  · split at h
    · simp only [Signal.halted.injEq] at h; subst h; simp only [FrameHalt.gasOf]; omega
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e =>
        rw [hdisp] at h; simp only [Signal.halted.injEq] at h
        subst h; simp only [FrameHalt.gasOf]; omega
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e => exact absurd h (by simp)
        | needsCall p pc => exact absurd h (by simp)
        | needsCreate p pc => exact absurd h (by simp)
        | halted hl =>
          simp only [Signal.halted.injEq] at h; subst h
          by_cases hsys : ∃ s, op = .System s
          · obtain ⟨s, rfl⟩ := hsys
            rw [dispatch] at hdisp
            exact systemOp_gasOf_le hdisp
          · exact absurd hdisp (dispatch_neverHalts (fun s hc => hsys ⟨s, hc⟩) hl)

/-- **Obligation 2.** `endFrame` of a `stepFrame`-halt keeps gas ≤ the frame gas. -/
theorem endFrame_gasRemaining_le {fr : Frame} {halt : FrameHalt}
    (h : stepFrame fr = .halted halt) :
    FrameResult.gasRemaining (endFrame fr halt) ≤ fr.exec.gasAvailable.toNat := by
  have hb := stepFrame_halted_gasOf_le h
  unfold endFrame
  cases fr.kind with
  | call cp =>
    simp only [FrameResult.gasRemaining]
    cases halt with
    | success exec output =>
      simp only [endCall, FrameHalt.gasOf] at hb ⊢; exact hb
    | revert g output => simp only [endCall, FrameHalt.gasOf] at hb ⊢; exact hb
    | exception e => simp only [endCall, UInt64.toNat_ofNat]; omega
  | create addr cp =>
    simp only [FrameResult.gasRemaining]
    cases halt with
    | success exec output =>
      simp only [endCreate, FrameHalt.gasOf] at hb ⊢
      rw [UInt64.toNat_ofNat']
      refine le_trans (Nat.mod_le _ _) (le_trans ?_ hb)
      exact ite_le (Nat.zero_le _) (Nat.sub_le _ _)
    | revert g output => simp only [endCreate, FrameHalt.gasOf] at hb ⊢; exact hb
    | exception e => simp only [endCreate, UInt64.toNat_ofNat]; omega

/-! ## Obligation 6 — delivery: `resume` does not create gas

`resumeAfterCall` restores the parent's gas to `parentSaved + childRemaining`
(memory writes preserve gas, the stack/pc rewrap preserves gas; UInt64 wrap can
only *lower* the `.toNat`). `resumeAfterCreate` keeps even less (it deducts the
`allButOneSixtyFourth` floor). Either way, the delivered parent's gas `.toNat` is
`≤ savedParent + childRemaining`. -/

theorem writeBytes_gasAvailable (src : ByteArray) (sa : ℕ) (self : MachineState)
    (da len : ℕ) : (writeBytes src sa self da len).gasAvailable = self.gasAvailable := rfl

/-- `toCallResult` preserves `gasRemaining` (matches `FrameResult.gasRemaining`). -/
theorem toCallResult_gasRemaining (r : FrameResult) :
    r.toCallResult.gasRemaining.toNat = FrameResult.gasRemaining r := by
  cases r <;> rfl

/-- `toCreateResult` preserves `gasRemaining` (matches `FrameResult.gasRemaining`). -/
theorem toCreateResult_gasRemaining (r : FrameResult) :
    r.toCreateResult.gasRemaining.toNat = FrameResult.gasRemaining r := by
  cases r <;> rfl

/-- `resumeAfterCall` gives the parent gas `.toNat ≤ savedParent + childRemaining`. -/
theorem resumeAfterCall_gas_le (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.gasAvailable.toNat
      ≤ pd.frame.exec.gasAvailable.toNat + result.gasRemaining.toNat := by
  unfold resumeAfterCall
  simp only [gasNat_replaceStackAndIncrPC]
  -- exec'.gasAvailable = machineWithOutput.gasAvailable + result.gasRemaining,
  -- machineWithOutput = writeBytes … pd.frame.exec.toMachineState …
  show (_ + result.gasRemaining).toNat ≤ _
  rw [UInt64.toNat_add]
  refine le_trans (Nat.mod_le _ _) ?_
  -- writeBytes preserves gas, so the first summand is pd.frame.exec.gasAvailable.toNat
  exact Nat.le_refl _

/-- `resumeAfterCreate` (when it returns a frame) gives parent gas
`.toNat ≤ savedParent + childRemaining`. -/
theorem resumeAfterCreate_gas_le {result : CreateResult} {pd : PendingCreate} {parent : Frame}
    (h : resumeAfterCreate result pd = .ok parent) :
    parent.exec.gasAvailable.toNat
      ≤ pd.frame.exec.gasAvailable.toNat + result.gasRemaining.toNat := by
  unfold resumeAfterCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [gasNat_replaceStackAndIncrPC]
    rw [UInt64.toNat_ofNat']
    refine le_trans (Nat.mod_le _ _) ?_
    -- gas.toNat - allButOneSixtyFourth gas.toNat + gasRemaining.toNat ≤ gas.toNat + gasRemaining.toNat
    have : pd.frame.exec.gasAvailable.toNat - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat
        ≤ pd.frame.exec.gasAvailable.toNat := Nat.sub_le _ _
    omega

/-- The **tight** `resumeAfterCreate` bound, matching the kind-aware
`Pending.savedGas`: the resumed parent's gas is `≤ (saved − allButOneSixtyFourth
saved) + childRemaining`. The forwarded `allButOneSixtyFourth` returns to the
parent on delivery, which is exactly what `savedGas (.create _)` already withheld
from the measure. -/
theorem resumeAfterCreate_gas_le_savedGas {result : CreateResult} {pd : PendingCreate} {parent : Frame}
    (h : resumeAfterCreate result pd = .ok parent) :
    parent.exec.gasAvailable.toNat
      ≤ (pd.frame.exec.gasAvailable.toNat
          - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat)
        + result.gasRemaining.toNat := by
  unfold resumeAfterCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [gasNat_replaceStackAndIncrPC]
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_le _ _

/-! ## Halt-op shape helper -/

/-- `haltOp` never produces `.next`: its `.ok` outputs are all `.halted`. -/
theorem haltOp_not_next {op : Operation.SystemOp} {exec exec' : ExecutionState}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.next exec') := by
  intro he
  unfold haltOp at he
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · simp at he
  · rw [returnOrRevertOp] at he
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at he
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at he; simp at he
      | ok ec =>
        rw [hm] at he; simp only [pure, Except.pure] at he
        split at he <;> simp at he
  · rw [returnOrRevertOp] at he
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at he
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at he; simp at he
      | ok ec =>
        rw [hm] at he; simp only [pure, Except.pure] at he
        split at he <;> simp at he
  · rw [selfdestructOp] at he
    cases hr : requireStateMod exec with
    | error e => rw [hr] at he; simp [bind, Except.bind] at he
    | ok _ =>
      rw [hr] at he; simp only [bind, Except.bind, pure, Except.pure] at he
      cases hp : exec.stack.pop with
      | none => rw [hp] at he; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at he
      | some v =>
        obtain ⟨s, rw'⟩ := v; rw [hp] at he
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at he
        cases hc : charge (selfdestructCost _ _) exec with
        | error e => rw [hc] at he; simp at he
        | ok ec =>
          rw [hc] at he; simp only [] at he
          split at he <;> simp at he
  · simp [throw, throwThe, MonadExceptOf.throw] at he

/-- The gas of the frame `beginCall` produces for a code call is `params.gas`. -/
theorem beginCall_inl_gas {p : CallParams} {fr : Frame} (h : beginCall p = .inl fr) :
    fr.exec.gasAvailable = p.gas := by
  unfold beginCall at h
  cases hcs : p.codeSource with
  | Precompiled pc => rw [hcs] at h; simp at h
  | Code code => rw [hcs] at h; simp only [Sum.inl.injEq] at h; subst h; rfl


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
goes through (see `gasFundsDescent_conj4'`). -/
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

/-- **`beginCreate` gas.** The child frame `beginCreate` produces is forwarded
exactly `params.gas`. (`beginCreate` is now total — no `.ok` hypothesis.) -/
theorem beginCreate_gas {params : CreateParams} :
    (beginCreate params).exec.gasAvailable = params.gas := by
  rw [beginCreate]

-- Axiom guard: the totalised `beginCreate` gas fact stays within the standard kernel.
#print axioms beginCreate_gas

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



end BytecodeLayer.System
