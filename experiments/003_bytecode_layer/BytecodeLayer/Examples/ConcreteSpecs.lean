import BytecodeLayer.Programs
import BytecodeLayer.Observables
import BytecodeLayer.ExternalCall
import BytecodeLayer.Examples.ProgramExamples
import BytecodeLayer.Examples.CallerProgExample
import BytecodeLayer.Examples.TwoCallExample
import BytecodeLayer.Examples.BranchExample

/-!
# Concrete per-program results — worked examples, not general specs

These are the **per-program** `messageCall` observations for the handwritten
contracts of `Programs.lean`, observed through `Observables.lean`. They are
*examples* that exercise the general engine (`Semantics/` + `Hoare/`): each one is
a result about a single specific program, not a statement quantified over all
programs.

The general, program-agnostic content lives on the audit surface `Spec.lean`
(the sequencing rule `Runs.trans`, the opcode rules, the `messageCall` bridge, and
the multi-call composition rule `messageCall_runs_calls` /
`messageCall_calls_completedWith`).
These concrete results delegate to the proofs in `ProgramExamples.lean` (the
`*'` lemmas, composed from the opcode rules) and — for the external call — to the
**compositional** `CallerProgExample.lean` (which crosses `messageCall_runs` over a
`Runs.call` node),
with the forced-`∃G₀` counterexample from `ExternalCall.lean`.

Two groups:
* **Call-free programs** (`stopProgram` … `seqProgram`): the success/output and
  storage left by straight-line bytecode; gas appears only as the program's exact
  cost, stated as a plain `≤` hypothesis.
* **External call** (`callerParams`): a program that `CALL`s another contract.
  Here gas becomes genuinely observable (the 63/64 cap), so the storage result
  holds only above a gas floor — `messageCall_call_storageAt` states the floor and
  `call_counterexample` proves it cannot be dropped.
-/

namespace BytecodeLayer.Examples
open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

/-! ## The call-free spine -/

/-- A message call into the single-`STOP` program (`stopProgram`) succeeds with
empty output, for *any* call parameters whose code is `stopProgram` — no gas floor
required (STOP charges nothing). Stated purely in observables. -/
theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok Observables.ok :=
  messageCall_stop_observe' p hc

/-- A message call into `PUSH1 0x05 ; STOP` (`pushStopProgram`) succeeds with empty
output for every `p` with `3 ≤ p.gas` — the program's exact gas cost, stated as a
plain hypothesis rather than an `∃G₀`. -/
theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok Observables.ok :=
  messageCall_pushStop_observe' p hc hg

/-- **First persistent effect.** A message call into `PUSH1 5 ; PUSH1 7 ; SSTORE ;
STOP` (`sstoreProgram`) in `addrA` succeeds and leaves `addrA`'s storage cell `7`
holding `5`, for every `g` with `22106 ≤ g` (`= 3 + 3 + 22100`, the cold
first-write SSTORE cost). Observables-only. -/
theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok (Observables.ok, 5) :=
  messageCall_sstore_storageAt' g hg

/-- **A sequence of charging instructions.** A message call into
`PUSH;PUSH;SSTORE;PUSH;PUSH;SSTORE;STOP` (`seqProgram`) in `addrA` leaves cell `7`
holding `5` and cell `9` holding `11`, for every `g` with `44212 ≤ g`
(`= 2 × 22106`). Two distinct storage observables off one run. -/
theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok (Observables.ok, 5, 11) :=
  messageCall_seq_storageAt' g hg

/-! ## External call

`callerParams` runs `callerProg`, which `CALL`s `calleeProg` (living at
`addrCallee`). `calleeProg` is `PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP` — it writes the
value `5` to its own storage slot `7`. The observable is that cell,
`storageAt addrCallee 7`, read off the caller's returned account map. The sub-call
is run for real (leanevm's own `beginCall`/`drive` on the callee's actual code —
no oracle, no assumption). -/

/-- **The `∃G₀` external-call theorem.** There is a gas floor `G₀` such that for
every `g ≥ G₀`, the top-level message call into the caller (which forwards a real
`CALL` to the callee) leaves the callee's storage cell `(addrCallee, 7)` holding
`5`: with enough gas, the child clears the 63/64 `callGasCap`, its `SSTORE`
commits. The `∃G₀` is *forced*, not cosmetic — see `call_counterexample`.

The witness `G₀ = 30000` and the proof come from the **compositional**
`messageCall_callerProg_storageAt` (the single `messageCall_runs` bridge
instantiated on `callerProg`/`calleeProg`), not a monolithic opcode chain. -/
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 :=
  ⟨30000, fun g hg => messageCall_callerProg_storageAt g hg⟩

/-- **The executable counterexample that forces the `∃G₀`.** At the modest gas
`g = 24000`, the *same* observable is `0`: the 63/64 cap starves the callee
(`childGas 24000 = 21045 < 22106`), its `SSTORE` out-of-gases and rolls back —
**yet the top-level call still completes cleanly** (the caller is handed flag `0`
and `STOP`s, no top-level `OutOfGas`). Read against `messageCall_call_storageAt`,
this shows no gas-floor-free statement ("completes ⇒ cell is 5") can hold. -/
theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0 :=
  ExternalCall.call_counterexample

end BytecodeLayer.Examples
