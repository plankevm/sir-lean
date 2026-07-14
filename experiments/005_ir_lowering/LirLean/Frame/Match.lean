import BytecodeLayer.Exec.Call
import BytecodeLayer.Exec.Create
import BytecodeLayer.Exec.CallRealises
import LirLean.Decode.LoweringLemmas
import LirLean.Decode.Layout
import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Exec.Frame

/-!
# LirLean — frame-local simulation and boundary lemmas

This module collects **atomic, frame-local simulation lemmas**. Each shows that an
EVM `Runs` segment implements one lowered construct, discharging straight to the
corresponding opcode rule. It also contains the CALL/CREATE oracle reflexivity
lemmas and the top-level `messageCall` boundary discharge.

The lemmas are deliberately stated using only the frame facts they consume: local
decode, stack shape, gas bounds, and observable storage. This keeps them reusable
by the current `Corr`-based simulation without carrying a second IR state or a
parallel invariant.
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

`lower_preserves` (`docs/ir-design.md` §6.3) closes the simulation under the IR run
and crosses the single boundary bridge `messageCall_runs`. The program-global
*assembly* of the `Runs fr₀ last` is separate; the **discharge** —
turning an assembled `Runs` + the terminator halt into the observable
`messageCall` result — is fully provable now and proved here. It is the exact half
that consumes A's `messageCall_runs`, specialised to the two IR terminators.

`lower_preserves_discharge` is the construct-agnostic bridge; `lower_preserves_stop`
/ `lower_preserves_ret` are the two terminator instances, supplying the halt from
`halt_stop` / `stepFrame_return_word`. The single-call worked program assembles its `Runs` and
applies the matching one. -/

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
