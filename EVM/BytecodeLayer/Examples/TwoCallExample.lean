import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence

/-!
# Worked two-CALL composition example — the acceptance test for intermediary calls

`messageCall_runs` (and its named multi-call alias `messageCall_runs_calls`) is the
single boundary bridge, and it accepts a `Runs fr₀ last` carrying **any number** of
returning external CALLs. The single-call instantiation lives in
`CallerProgExample.lean`. This file is the acceptance test for the *defect Track C
identified*: that **intermediary** CALLs — calls that return into more code rather
than halting the program — compose.

The worked shape is exactly Track C's:

```
  fr₀  --prefix Runs-->  callFr₁
       --Runs.call (CallReturns₁)-->  resumeFr₁     -- first external CALL returns
       --middle Runs (opcode steps)-->  callFr₂     -- code runs BETWEEN the two calls
       --Runs.call (CallReturns₂)-->  resumeFr₂     -- second external CALL returns
       --suffix Runs-->  last                        -- more code
       --halts (stepFrame last = .halted halt)
```

The whole caller execution is assembled into **one** `Runs fr₀ last` value by
`Runs.trans` gluing two `Runs.call` nodes around a middle run, and then crossed by
the single bridge in one shot. Crucially neither intermediary call has any halt
requirement of its own: the first call returns into `middle`, the second returns
into `suffix`, and only the final `last` halts. All fuel reconciliation across both
`call` nodes is internal to `Runs.drive_reconcile`; there is no numeric side
condition.

The per-piece facts (`hpre`, `hcall₁`, `hmiddle`, `hcall₂`, `hpost`, `hhalt`) are
honest structural hypotheses — each is a genuine `Runs` / `CallReturns` value built
with the real constructors, exactly what a concrete program supplies (the
single-call worked instance `CallerProgExample.caller_callReturns` is precisely such
a `CallReturns` witness, and the prefix there a real glued `Runs`). This theorem is
therefore the composition API Track C calls: hand it the two call witnesses and the
runs between them, get the `messageCall` result.
-/

namespace BytecodeLayer.Examples
open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.System

/-! ## The two-CALL `Runs` (the composition shape, with no bridge yet)

`twoCall_runs` is the structural heart: it glues the six pieces into a single
`Runs fr₀ last`. This is the value Track C builds; it makes the
`prefix · call₁ · middle · call₂ · suffix` interleaving explicit and shows the two
`call` nodes need nothing between them but ordinary opcode steps. -/

/-- **Two returning CALLs, composed into one `Runs`.** Glue a prefix run, a first
returning external CALL (`hcall₁`), a middle run of opcode steps, a second returning
external CALL (`hcall₂`), and a suffix run into a single `Runs fr₀ last`. Neither
intermediary CALL halts: the first returns into `middle`, the second into `suffix`.
Built purely from `Runs.call` / `Runs.trans` — the regular-language shape `(step |
call)*` realized for two calls. -/
theorem twoCall_runs
    {fr₀ callFr₁ resumeFr₁ callFr₂ resumeFr₂ last : Frame}
    (hpre    : Runs fr₀ callFr₁)
    (hcall₁  : CallReturns callFr₁ resumeFr₁)
    (hmiddle : Runs resumeFr₁ callFr₂)
    (hcall₂  : CallReturns callFr₂ resumeFr₂)
    (hpost   : Runs resumeFr₂ last) :
    Runs fr₀ last :=
  hpre.trans (Runs.call hcall₁ (hmiddle.trans (Runs.call hcall₂ hpost)))

/-! ## Crossing the single bridge with two CALLs -/

/-- **The two-CALL acceptance test.** A caller that enters as code and whose
execution is a prefix run, a returning CALL, a middle run, a second returning CALL,
and a suffix run to a halting `last`, delivers the caller's halt result as
`messageCall p` — with **no per-call halt requirement and no numeric fuel side
condition**. This is the defect-C acceptance test: two external calls with code
between them compose, and the *intermediary* first call (which returns into the
middle code rather than halting) is handled by the same single bridge.

The proof is: build the one `Runs fr₀ last` with `twoCall_runs` (two `Runs.call`
nodes glued by `Runs.trans`), then cross `messageCall_runs_calls` once. -/
theorem twoCall_messageCall (p : CallParams)
    {fr₀ callFr₁ resumeFr₁ callFr₂ resumeFr₂ last : Frame} {halt : FrameHalt}
    (hbegin  : EntersAsCode p fr₀)
    (hpre    : Runs fr₀ callFr₁)
    (hcall₁  : CallReturns callFr₁ resumeFr₁)
    (hmiddle : Runs resumeFr₁ callFr₂)
    (hcall₂  : CallReturns callFr₂ resumeFr₂)
    (hpost   : Runs resumeFr₂ last)
    (hhalt   : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs_calls p hbegin
    (twoCall_runs hpre hcall₁ hmiddle hcall₂ hpost)
    hhalt

/-- **The two-CALL acceptance test, observable level.** The same two-CALL
composition, lifted to the named `Outcome.completedWith`: if the caller's halt
result is a success leaving `v` at cell `(a, k)`, the top-level
`Outcome.ofCall (messageCall p)` `completedWith` `v` there. The composition API
Track C exposes to its observable specs. -/
theorem twoCall_completedWith (p : CallParams)
    {fr₀ callFr₁ resumeFr₁ callFr₂ resumeFr₂ last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin  : EntersAsCode p fr₀)
    (hpre    : Runs fr₀ callFr₁)
    (hcall₁  : CallReturns callFr₁ resumeFr₁)
    (hmiddle : Runs resumeFr₁ callFr₂)
    (hcall₂  : CallReturns callFr₂ resumeFr₂)
    (hpost   : Runs resumeFr₂ last)
    (hhalt   : stepFrame last = Signal.halted halt)
    (hsucc   : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell   : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  messageCall_calls_completedWith p a k v hbegin
    (twoCall_runs hpre hcall₁ hmiddle hcall₂ hpost)
    hhalt hsucc hcell

end BytecodeLayer.Examples
