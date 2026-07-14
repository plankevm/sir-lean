import LirLean.Spec.Lowering
import BytecodeLayer.Exec.Frame

/-!
# LirLean — lowered-program boundary adapters

The remaining statements connect a `Runs` execution of `lower prog` to the
top-level `messageCall` result. Frame-local opcode simulations are re-exported for
the IR proofs that consume them.
-/

namespace Lir.Frame
open BytecodeLayer.Exec
open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Maps
open BytecodeLayer.Dispatch
open BytecodeLayer.System

export BytecodeLayer.Exec
  (storageAt call_reflects_lowered create_reflects_lowered selfStorage sim_imm sim_gas sim_add
   sim_lt sim_sload sstoreFrame_storage_self' sstoreFrame_storage_frame' sim_sstore sim_mload
   sim_mstore halt_stop returnWordPost stepFrame_return_word M_zero32_idem
   memExpWords_zero32_covered sim_call sim_create)

/-! ## Top-level preservation discharge (`lower_preserves`, the bridge half)

The discharge turns a `Runs fr₀ last` execution plus the terminator halt into the
observable `messageCall` result, specialized to the two IR terminators.

`lower_preserves_discharge` is the construct-agnostic bridge; `lower_preserves_stop`
/ `lower_preserves_ret` are the two terminator instances, supplying the halt from
`halt_stop` / `stepFrame_return_word`. -/

/-- **The boundary discharge.** A top-level call entering the lowered code as code
(`EntersAsCode`) whose assembled `Runs fr₀ last` reaches a halting `last`
(`stepFrame last = .halted halt`) delivers the caller's halt result as
`messageCall`. This is `messageCall_runs` applied at the IR/lowering boundary; it
crosses regardless of how many `Runs.call` (external CALL) nodes the assembled run
contains (multi-call composition is `messageCall_runs_calls`). -/
theorem lower_preserves_discharge (prog : Program) (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (_hcode : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin hruns hhalt

/-- **`Term.stop` preservation.** When the assembled `Runs` lands on a `STOP` frame
`last`, the discharge pins `messageCall` to `last`'s success
`endFrame`. The halt is `halt_stop`. -/
theorem lower_preserves_stop (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .STOP, .none))
    (hstk   : last.exec.stack.size ≤ 1024) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success last.exec .empty))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (halt_stop last hdec hstk)

/-- **`Term.ret` preservation** (word return window). When the assembled `Runs`
lands on a `RETURN` frame `last` with `0 :: 32 :: rest` and the `[0, 32)` window already
active (`hmem`, the post-`MSTORE(0,…)` shape), the discharge pins
`messageCall` to `last`'s success `endFrame`, returning the 32-byte window. The halt is
`stepFrame_return_word`. -/
theorem lower_preserves_ret (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (rest : Stack Word)
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .RETURN, .none))
    (hstk   : last.exec.stack = (0 : Word) :: (32 : Word) :: rest)
    (hsz    : last.exec.stack.size ≤ 1024)
    (hmem   : memoryExpansionWords? last.exec.activeWords (0 : Word) (32 : Word)
                = some last.exec.activeWords) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success (returnWordPost last.exec rest)
        (last.exec.memory.readWithPadding (0 : Word).toNat (32 : Word).toNat)))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (stepFrame_return_word last rest hdec hstk hsz hmem)

end Lir.Frame

-- Build-enforced axiom-cleanliness guard for the memory value-channel simulation
-- bricks: both MSTORE/MLOAD arms depend only on `[propext, Classical.choice, Quot.sound]`.
