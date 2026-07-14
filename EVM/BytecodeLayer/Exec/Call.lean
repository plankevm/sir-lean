import BytecodeLayer.Exec.Observable
import Evm
import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Dispatch

/-!
# Abstract CALL effects

`CallOracle` exposes the three effects of resuming an external call that execution
clients need: post-call storage, restored gas, and the pushed success word.
`evmCallOracle` is the concrete instance obtained by projecting those fields from
`resumeAfterCall`.
-/

namespace BytecodeLayer.Exec

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## Oracle interface -/

/-- An abstract view of an external call's effect. Its three projections match the
observable parts of `resumeAfterCall`:

* `postStorage result pd addr key` — the storage of account `addr` at `key` in the
  resumed world, through the observable `find?/lookupStorage` lens; for the EVM
  oracle this is `result.accounts`'s lens;
* `restoredGas result pd` — the gas the caller resumes with (`gasAfterReturn`);
* `successWord result pd` — the 0/1 success word the CALL pushes (`x`).

`evmCallOracle` instantiates every field by projection from the resumed frame. -/
structure CallOracle where
  /-- Post-call storage of `addr` at `key`, through the observable lens. -/
  postStorage : CallResult → PendingCall → AccountAddress → Word → Word
  /-- Gas restored to the caller on resume (`gasAfterReturn`). -/
  restoredGas : CallResult → PendingCall → UInt64
  /-- The 0/1 success word the CALL pushes (`x`). -/
  successWord : CallResult → PendingCall → Word

/-! ## Concrete EVM instance

Each field is the corresponding projection of `resumeAfterCall result pd`:

* `postStorage` reads `result.accounts` (the map `resumeAfterCall` writes into
  `exec.accounts`) through the observable `find?/lookupStorage` lens;
* `restoredGas` is `(resumeAfterCall result pd).exec.gasAvailable`, i.e.
  `gasAfterReturn`;
* `successWord` is the word `resumeAfterCall` pushes — the head of
  `(resumeAfterCall result pd).exec.stack` (which is `pd.stack.push x = x ::
  pd.stack`), i.e. `x`.

The definitions are transparent, so equality facts reduce directly. -/

/-- The concrete external-CALL effect, projected from `resumeAfterCall`. -/
def evmCallOracle : CallOracle where
  postStorage := fun result pd addr key =>
    (resumeAfterCall result pd).exec.accounts.find? addr |>.option 0 (·.lookupStorage key)
  restoredGas := fun result pd => (resumeAfterCall result pd).exec.gasAvailable
  successWord := fun result pd =>
    -- the word pushed on top of the suspended stack (the head of the resumed
    -- stack, `pd.stack.push x = x :: pd.stack`) — `resumeAfterCall`'s `x`.
    (resumeAfterCall result pd).exec.stack.head?.getD 0

/-- The CALL success flag pushed by `resumeAfterCall`: `0` on code failure,
insufficient funds, or the call-depth limit; otherwise `1`. -/
def callSuccessFlag (result : CallResult) (pd : PendingCall) : Word :=
  if !result.success
      || (pd.value > (pd.callerAccounts.find? pd.frame.exec.executionEnv.address |>.elim 0 (·.balance)))
      || (pd.frame.exec.executionEnv.depth == 1024) then 0 else 1

/-- Resuming a CALL preserves the suspended caller's code. -/
theorem resumeAfterCall_code (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.executionEnv.code
      = pd.frame.exec.executionEnv.code := rfl

/-- Resuming a CALL preserves the suspended caller's state-modification permission. -/
theorem resumeAfterCall_canModifyState (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.executionEnv.canModifyState
      = pd.frame.exec.executionEnv.canModifyState := rfl

/-- Resuming a CALL preserves the suspended caller's valid jump destinations. -/
theorem resumeAfterCall_validJumps (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).validJumps = pd.frame.validJumps := rfl

/-- Resuming a CALL advances the suspended caller's program counter by one. -/
theorem resumeAfterCall_pc (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.pc = pd.frame.exec.pc + 1 := rfl

/-- Resuming a CALL pushes its success flag on the suspended caller's residual stack. -/
theorem resumeAfterCall_stack (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.stack
      = pd.stack.push (callSuccessFlag result pd) := rfl

/-- The concrete oracle's success word is the flag pushed by `resumeAfterCall`. -/
theorem evmCallOracle_successWord_eq_x (result : CallResult) (pd : PendingCall) :
    evmCallOracle.successWord result pd = callSuccessFlag result pd := rfl

end BytecodeLayer.Exec
