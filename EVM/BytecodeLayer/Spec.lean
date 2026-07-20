import BytecodeLayer.Programs
import BytecodeLayer.Observables
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.Behaves
import BytecodeLayer.Hoare.Sequence
import BytecodeLayer.Hoare.OutcomeBridge
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Hoare.GasMonotone
import BytecodeLayer.Examples.ConcreteSpecs

/-!
# Spec — the audit surface of the Hoare program-logic layer

**This is the file to read for the program-logic layer.** It collects the
*general*, program-agnostic results: the program-logic rules a user composes to
verify their own bytecode, and the sound external-CALL sequencing rule. Each is
re-exported here with a high-level docstring; the proofs live in `Hoare/`.

This is one of the library's two export surfaces. The other is the `Exec/`
engine layer (recording interpreter, cyclic simulation, witness checks —
aggregated by `Exec.lean`, plus the `Asm/` assembler geometry), consumed by
`experiments/005_ir_lowering` (LirLean). The *conformance flagship* surface
(`lower_conforms*` and its disclosed seams) lives on the LirLean side, in
`experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean` —
`Exec/` holds the supporting engine machinery, not the flagship statements.

Scope note: the per-program storage/observable results (`stopProgram` …
`callerProg`) are **worked examples** that exercise these rules, not general specs;
they now live in `Examples/ConcreteSpecs.lean`, off this surface.

Altitude ruling (settled): the program-logic rules below are **frame-level** —
they mention `Runs`/`Frame`/`stepFrame`, not pure observables. That is intended:
this bytecode layer *is* the low-level layer, and its reusable theorems are
exactly the frame-level rules a user instantiates. The observables-only
exported-surface standard binds the higher, experiment-style surfaces, not this
one (the carve-out is recorded in AGENTS.md, "Reviewer standard"). The fully
observable-level export here is `messageCall_calls_completedWith`.
-/

namespace BytecodeLayer
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open BytecodeLayer.Interpreter
open BytecodeLayer.System

/-! ## Program-logic rules (general over all programs)

The reusable bricks for verifying a straight-line block: a sequencing rule, the
per-opcode `Runs` rules, and the bridge that crosses the `messageCall` boundary.
A user instantiates these on their own bytecode (see `Examples/` for worked
instantiations). They are general over every program; only the *premises*
(decode, gas, stack shape) pin them to a concrete program. -/

/-- **The sequencing rule.** Compose a block `fr → mid` with the block that
follows it `mid → fr'` into one block `fr → fr'`. A program's `Runs` is built by
gluing the per-opcode `Runs` rules (and returning CALL/CREATE nodes) with this,
never by exhibiting an execution trace. -/
theorem Runs.trans {fr mid fr' : Frame}
    (h₁ : Runs fr mid) (h₂ : Runs mid fr') : Runs fr fr' :=
  Hoare.Runs.trans h₁ h₂

/-- **Gas monotonicity of `Runs`
(`experiments/005_ir_lowering/docs/ir-design-v2.md` §3.4).** Across any flat
`Runs fr last` — opcode steps, returning external CALLs (`.call` nodes) and returning
CREATEs (`.create` nodes) in any order — the machine's remaining gas does not increase:
`last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat`. The `.call`/`.create` cases
are the 63/64 net-debit (a returning call cannot raise the caller's gas), discharged from
the never-OutOfFuel descent machinery with **no hypothesis** beyond what
`Runs.call`/`Runs.create` carry.
This is the structural fact that makes the monotone-gas-read law hold across calls. -/
theorem Runs.gasAvailable_le {fr last : Frame} (h : Runs fr last) :
    last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat :=
  Hoare.Runs.gasAvailable_le h

/-- **The `messageCall` boundary bridge.** A code call whose entry frame `fr₀`
(`EntersAsCode p fr₀`) `Runs` to a frame that halts yields the caller's halt
result as `messageCall p` — **no numeric fuel side condition**. From here up,
statements are observable-only. -/
theorem messageCall_runs {fr₀ last : Frame} {halt : FrameHalt} (p : CallParams)
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  Hoare.messageCall_runs p hbegin h hhalt

/-- **The PUSH1 rule.** From a frame decoding to `PUSH1 imm` with gas and stack
room, one step `Runs` to `pushFrame fr imm` (`imm` pushed, pc + 2, `Gverylow`
charged). -/
theorem runs_push1 (fr : Frame) (imm : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH1, some (imm, 1)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrame fr imm) :=
  Hoare.runs_push1 fr imm hdec hgas hstk

/-- **The general PUSH rule (any width).** From a frame decoding to `PUSH<w> imm`
(any push opcode other than `PUSH0`) with gas and stack room, one step `Runs` to
`pushFrameW fr imm w` (`imm` pushed, pc + `w+1`, `Gverylow` charged). Covers the
multi-byte gas/address pushes (PUSH3, PUSH4, …) that `runs_push1` cannot. -/
theorem runs_push (fr : Frame) (op : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : op ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push op, some (imm, w)))
    (hpop : stackPopCount (.Push op) = 0)
    (hpush : stackPushCount (.Push op) = 1)
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr imm w) :=
  Hoare.runs_push fr op imm w hp0 hdec hpop hpush hgas hstk

/-- **The SSTORE rule (effect).** From a frame decoding to `SSTORE` with
`key :: newValue :: rest` on the stack, in a state-modifying context with enough
gas, one step `Runs` to `sstoreFrame fr key newValue rest`. The framing of this
write is `sstoreFrame_storage_self` / `sstoreFrame_storage_frame`. -/
theorem runs_sstore (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key newValue ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (sstoreFrame fr key newValue rest) :=
  Hoare.runs_sstore fr key newValue rest hdec hstk hsz hmod hstip hcost

/-- **SSTORE effect.** After `sstoreFrame` (writing a *non-zero* `newValue`),
reading the self account's storage at `key` returns `newValue`. -/
theorem sstoreFrame_storage_self (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (hnz : newValue ≠ 0) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? fr.exec.executionEnv.address
      |>.option 0 (·.lookupStorage key)) = newValue :=
  Hoare.sstoreFrame_storage_self fr key newValue rest acc hself hnz

/-- **SSTORE framing.** After `sstoreFrame`, reading **any other** cell `(a', k')`
— a different account, or the same account at a different slot — returns exactly
what `fr` held there: the write touches only `(self, key)`. -/
theorem sstoreFrame_storage_frame (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (hnz : newValue ≠ 0)
    (a' : AccountAddress) (k' : UInt256)
    (hframe : a' ≠ fr.exec.executionEnv.address ∨ k' ≠ key) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? a' |>.option 0 (·.lookupStorage k'))
      = (fr.exec.accounts.find? a' |>.option 0 (·.lookupStorage k')) :=
  Hoare.sstoreFrame_storage_frame fr key newValue rest acc hself hnz a' k' hframe

/-- **The ADD rule.** From a frame decoding to `ADD` with `a :: b :: rest` on the
stack, enough gas (`Gverylow`) and stack room, one step `Runs` to `addFrame fr a b
rest` (top = `a + b`). -/
theorem runs_add (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest) :=
  Hoare.runs_add fr a b rest hdec hstk hsz hgas

/-- **The LT rule.** From a frame decoding to `LT` with `a :: b :: rest` on the
stack, enough gas (`Gverylow`) and stack room, one step `Runs` to `ltFrame fr a b
rest` (top = `UInt256.lt a b`, the boolean-as-word `a < b`). -/
theorem runs_lt (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (ltFrame fr a b rest) :=
  Hoare.runs_lt fr a b rest hdec hstk hsz hgas

/-- **The SLOAD rule.** From a frame decoding to `SLOAD` with `key :: rest` on the
stack and enough gas (`sloadCost warm`), one step `Runs` to `sloadFrame fr key rest`
(top = the self account's stored value at `key`). The pushed value is exposed
through the same storage lens by `sloadFrame_storage_self`. -/
theorem runs_sload (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (sloadFrame fr key rest) :=
  Hoare.runs_sload fr key rest hdec hstk hsz hgas

/-- **SLOAD read companion** (mirrors `sstoreFrame_storage_self`). The value SLOAD
pushes — the head of `sloadFrame`'s resulting stack — is exactly the self account's
stored value at `key`, read through the same `find?/lookupStorage` lens. -/
theorem sloadFrame_storage_self (fr : Frame) (key : UInt256) (rest : Stack UInt256) :
    (sloadFrame fr key rest).exec.stack.head?
      = some (fr.exec.accounts.find? fr.exec.executionEnv.address
          |>.option 0 (·.lookupStorage key)) :=
  Hoare.sloadFrame_storage_self fr key rest

/-- **The GAS rule.** From a frame decoding to `GAS` with enough gas (`Gbase`) and
stack room, one step `Runs` to `gasFrame fr` (top = `ofUInt64` of the *post-charge*
`gasAvailable`). -/
theorem runs_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr) :=
  Hoare.runs_gas fr hdec hsz hgas

/-! ## The general external-call rule (over both caller and callee programs)

The sound, program-agnostic external-call rule. It is **general over both the
caller and the callee program**, and unlike a forwarding hypothesis it assumes
nothing about the conclusion:

* the **callee is consumed as a black-box terminating run** — any `drive` of the
  child params to `.ok childRes`, no oracle on what it computes (this is the
  payload of a `Runs.call` / `CallReturns` node; a returning CREATE's init child
  is likewise the black-box payload of a `Runs.create` / `CreateReturns` node);
* the **caller is described by its actual `Runs` trace** through every CALL and
  CREATE: a single `Runs fr₀ last` interleaving `Runs.step` (opcode steps),
  `Runs.call` (returning external CALLs) and `Runs.create` (returning CREATEs)
  in any order, to a halting `last` — structural facts
  about how the caller bytecode executes, *not* an assumed forwarding;
* gas stays first-class but needs **no numeric side condition** — the rule
  discharges the fuel bound internally.

There is **one** boundary bridge, `messageCall_runs` (above): because external
CALLs are `Runs.call` nodes (and returning CREATEs `Runs.create` nodes), it already
accepts a caller trace with **any number**
of returning calls and creates. `messageCall_runs_calls` re-states it as the explicit
multi-call composition guarantee, and `messageCall_calls_completedWith` lifts it to
the named `Outcome.completedWith`. A worked single-call instantiation on
`callerProg`/`calleeProg` is `Examples.messageCall_callerProg_storageAt`; a worked
two-call program is `Examples.twoCallProg_runs`. -/

/-- **`CallReturns callFr resumeFr`.** Re-exported from
`BytecodeLayer.Hoare`. Bundles the four call-facts of the external
CALL: `callFr` issues a CALL (`stepFrame callFr = .needsCall cp pending`) whose
child enters as code (`EntersAsCode cp child`) and runs to completion
(`drive (seedFuel cp.gas) [] (running child) = .ok childRes`), pinning the resumed
parent frame to `resumeFr = resumeAfterCall childRes.toCallResult pending`. It is
the payload of the `Runs.call` constructor. See `BytecodeLayer.Hoare.CallReturns`. -/
abbrev CallReturns := Hoare.CallReturns

/-- **`CreateReturns createFr resumeFr`.** Re-exported from
`BytecodeLayer.Hoare`; the CREATE twin of `CallReturns`. Bundles the three
create-facts of a CREATE/CREATE2 that returns *and successfully resumes*: `createFr`
issues a CREATE (`stepFrame createFr = .needsCreate cp pending`), the init child —
the total `beginCreate cp`, no code/precompile split — runs to completion
(`drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes`), and the
63/64 retention guard passes, pinning the resumed parent frame
(`resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr`). It is the
payload of the `Runs.create` constructor. See `BytecodeLayer.Hoare.CreateReturns`. -/
abbrev CreateReturns := Hoare.CreateReturns

/-- **Multi-call composition.** Re-exported from `BytecodeLayer.Hoare.CallSequence`.
A caller that enters as code and whose single `Runs fr₀ last` interleaves **any
number of returning external CALLs** (`Runs.call` / `CallReturns` nodes) **and
returning CREATEs** (`Runs.create` / `CreateReturns` nodes) with
opcode steps, ending at a halting `last`, delivers the caller's halt result as
`messageCall p` — no assumed forwarding, **no per-call halt requirement, and no
numeric fuel side condition**. This is the general "≥N calls compose" guarantee
the IR lowering composes against; the caller builds `h` with `Runs.call` /
`Runs.create` / `Runs.step` / `Runs.trans`. -/
theorem messageCall_runs_calls (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  Hoare.messageCall_runs_calls p hbegin h hhalt

/-- **The general external-CALL rule at the observable level.** Re-exported from
`BytecodeLayer.Hoare.CallSequence`. The same honest hypotheses as
`messageCall_runs_calls` (a single multi-call/multi-create `Runs fr₀ last` to a
halting `last`),
plus the caller's halt result being a success leaving `v` at cell `(a, k)`, yield
the named `Outcome.completedWith` on `Outcome.ofCall (messageCall p)`. This is the
sound, general external-call rule for the spec surface — no assumed forwarding. -/
theorem messageCall_calls_completedWith (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin : EntersAsCode p fr₀)
    (h      : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt)
    (hsucc  : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell  : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  Hoare.messageCall_calls_completedWith p a k v
    hbegin h hhalt hsucc hcell

end BytecodeLayer
