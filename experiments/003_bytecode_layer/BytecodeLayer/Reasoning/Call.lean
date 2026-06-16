import Evm

/-!
# The CALL rule and the `.needsCall` driver descent (proof-internal)

This file characterizes a real `CALL` instruction — through the **public**
`callArm` — and the `drive` `.needsCall` arm that turns it into a *reflexive*
child `messageCall`. These are low-level internal bricks (they mention `Frame`,
`pending`, `Signal`, gas caps); they exist only so the external-call capstone can
reduce `messageCall` past a `CALL` without ever exposing frames or fuel in an
exported statement.

The whole point of the rung: the child call here is the **real** leanevm
`messageCall` computation (`beginCall` + `drive` on the child params), never an
oracle. We restrict to the value-free, zero-memory CALL shape
(`value = inOffset = inSize = outOffset = outSize = 0`) so the only quantitative
gas content is the 63/64 `callGasCap` — which is exactly the content the `∃G₀`
counterexample turns on.
-/

namespace BytecodeLayer
open Evm
open GasConstants

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

set_option maxHeartbeats 4000000 in
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

end BytecodeLayer
