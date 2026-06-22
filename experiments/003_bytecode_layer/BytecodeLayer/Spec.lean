import BytecodeLayer.Programs
import BytecodeLayer.Observables
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.Behaves
import BytecodeLayer.Hoare.Sequence
import BytecodeLayer.Hoare.OutcomeBridge
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Examples.ConcreteSpecs

/-!
# Spec — the audit surface of experiment 003

**This is the file to read.** It collects the *general*, program-agnostic results
of the formalization: the program-logic rules a user composes to verify their own
bytecode, and the sound external-CALL sequencing rule. Each is re-exported here
with a high-level docstring; the proofs live in `Hoare/`.

Scope note: the per-program storage/observable results (`stopProgram` …
`callerProg`) are **worked examples** that exercise these rules, not general specs;
they now live in `Examples/ConcreteSpecs.lean`, off this surface.

Altitude caveat (flagged for the lead): the program-logic rules below are
**frame-level** — they mention `Runs`/`Frame`/`stepFrame`, not pure observables.
This is in tension with the experiment's "observables-only exported surface"
standard. They are surfaced here because they *are* the reusable theorems a user
instantiates; the only fully observable-level export is
`messageCall_call_completedWith`. To reconcile.
-/

namespace BytecodeLayer
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open BytecodeLayer.Interpreter

/-! ## Program-logic rules (general over all programs)

The reusable bricks for verifying a straight-line block: a sequencing rule, the
per-opcode `Runs` rules, and the bridge that crosses the `messageCall` boundary.
A user instantiates these on their own bytecode (see `Examples/` for worked
instantiations). They are general over every program; only the *premises*
(decode, gas, stack shape) pin them to a concrete program. -/

/-- **The sequencing rule.** Compose a block `fr → mid` (`m` steps) with the block
that follows it `mid → fr'` (`n` steps) into one block `fr → fr'` (`m + n` steps).
A program's `Runs` is built by gluing the per-opcode `Runs` rules with this, never
by exhibiting an execution trace. -/
theorem Runs.trans {m n : ℕ} {fr mid fr' : Frame}
    (h₁ : Runs m fr mid) (h₂ : Runs n mid fr') : Runs (m + n) fr fr' :=
  Hoare.Runs.trans h₁ h₂

/-- **The `messageCall` boundary bridge.** A code call whose entry frame `fr₀`
(`beginCall p = .inl fr₀`) `Runs` to a frame that halts yields the caller's halt
result as `messageCall p`, under the numeric fuel bound `n + 2 ≤ seedFuel p.gas`.
From here up, statements are observable-only. -/
theorem messageCall_runs {n : ℕ} (p : CallParams) (fr₀ last : Frame)
    (hbegin : beginCall p = .inl fr₀)
    (h : Runs n fr₀ last)
    (halt : FrameHalt) (hhalt : stepFrame last = Signal.halted halt)
    (hfuel : n + 2 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  Hoare.messageCall_runs p fr₀ last hbegin h halt hhalt hfuel

/-- **The PUSH1 rule.** From a frame decoding to `PUSH1 imm` with gas and stack
room, one step `Runs` to `pushFrame fr imm` (`imm` pushed, pc + 2, `Gverylow`
charged). -/
theorem runs_push1 (fr : Frame) (imm : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH1, some (imm, 1)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs 1 fr (pushFrame fr imm) :=
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
    Runs 1 fr (pushFrameW fr imm w) :=
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
    Runs 1 fr (sstoreFrame fr key newValue rest) :=
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

/-! ## The general external-call rule (over both caller and callee programs)

The sound, program-agnostic external-call sequencing rule. It is **general over
both the caller and the callee program**, and unlike a forwarding hypothesis it
assumes nothing about the conclusion:

* the **callee is consumed as a black-box terminating run** — any `drive` of the
  child params to `.ok childRes`, no oracle on what it computes;
* the **caller is described by its actual `Runs` traces** through the CALL: an
  honest prefix run `fr₀ ⇝ callFr` to the CALL site, the CALL step itself, and a
  suffix run from the resumed frame to a halt site — structural facts about how the
  caller bytecode executes, *not* an assumed forwarding of the child's observable;
* gas stays first-class through the single numeric side condition
  `seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas`.

`messageCall_call_runs` lands the raw `messageCall p = .ok (… endFrame last halt)`;
`messageCall_call_completedWith` lifts it to the named `Outcome.completedWith`.
A worked instantiation on `callerProg`/`calleeProg` is
`Examples.messageCall_callerProg_storageAt`. -/

/-- **The general external-CALL sequencing rule.** Re-exported from
`BytecodeLayer.Hoare.CallSequence`. A caller that `Runs` from its entry frame to a
CALL site, issues a CALL whose child terminates (black box), then `Runs` from the
resumed frame to a halt site, produces the caller's halt result as `messageCall p`.
General over both programs; no assumed forwarding — see the section note. -/
theorem messageCall_call_runs {n₁ n₂ : ℕ}
    (p cp : CallParams) (fr₀ callFr child last : Frame)
    (childRes : FrameResult) (pending : PendingCall) (halt : FrameHalt)
    (hbegin   : beginCall p = .inl fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcall    : stepFrame callFr = .needsCall cp pending)
    (hcbegin  : beginCall cp = .inl child)
    (hchild   : drive (seedFuel cp.gas) [] (.inl child) = .ok childRes)
    (hpost    : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last)
    (hhalt    : stepFrame last = .halted halt)
    (hfuel    : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  Hoare.messageCall_call_runs p cp fr₀ callFr child last childRes pending halt
    hbegin hpre hcall hcbegin hchild hpost hhalt hfuel

/-- **The general external-CALL rule at the observable level.** Re-exported from
`BytecodeLayer.Hoare.CallSequence`. The same honest hypotheses as
`messageCall_call_runs`, plus the caller's halt result being a success leaving `v`
at cell `(a, k)`, yield the named `Outcome.completedWith` on
`Outcome.ofCall (messageCall p)`. This is the sound, general external-call rule for
the spec surface — no assumed forwarding. -/
theorem messageCall_call_completedWith {n₁ n₂ : ℕ}
    (p cp : CallParams) (fr₀ callFr child last : Frame)
    (childRes : FrameResult) (pending : PendingCall) (halt : FrameHalt)
    (a : AccountAddress) (k v : UInt256)
    (hbegin   : beginCall p = .inl fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcall    : stepFrame callFr = .needsCall cp pending)
    (hcbegin  : beginCall cp = .inl child)
    (hchild   : drive (seedFuel cp.gas) [] (.inl child) = .ok childRes)
    (hpost    : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last)
    (hhalt    : stepFrame last = .halted halt)
    (hfuel    : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas)
    (hsucc    : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell    : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  Hoare.messageCall_call_completedWith p cp fr₀ callFr child last childRes pending halt a k v
    hbegin hpre hcall hcbegin hchild hpost hhalt hfuel hsucc hcell

end BytecodeLayer
