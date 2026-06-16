import BytecodeLayer.Programs
import BytecodeLayer.Observables
import BytecodeLayer.Reasoning.Behaves
import BytecodeLayer.Proof.CallFree
import BytecodeLayer.Proof.Sequence
import BytecodeLayer.Proof.ExternalCall
import BytecodeLayer.Proof.ExternalCallGen
import BytecodeLayer.Proof.Straightline
import BytecodeLayer.Proof.CallFreePrograms

/-!
# Spec — the audit surface of experiment 003

**This is the file to read.** Each theorem states the result of running one of
the example programs from `Programs.lean` as a `messageCall`, observed through
`Observables.lean` (`success`/`output`, and chosen storage cells). No `Frame`,
pc, stack, gas counter, or fuel appears in any statement.

Scope note: these are results about **specific handwritten programs**, not yet
general statements over all programs. The reusable, program-agnostic content is
the engine in `Reasoning/`; these theorems are worked examples that exercise it.

The proofs live in `Proof/`, out of sight: each theorem delegates to a lemma of
the same name in `BytecodeLayer.Proof`. Every theorem's `#print axioms` is
`[propext, Classical.choice, Quot.sound]`.

Two groups:
* **Call-free programs** (`stopProgram` … `seqProgram`): the success/output and
  storage left by straight-line bytecode; gas appears only as the program's exact
  cost, stated as a plain `≤` hypothesis.
* **External call** (`callerParams`): a program that `CALL`s another contract.
  Here gas becomes genuinely observable (the 63/64 cap), so the storage result
  holds only above a gas floor — `messageCall_call_storageAt` states the floor and
  `call_counterexample` proves it cannot be dropped.
-/

namespace BytecodeLayer
open Evm

/-! ## M1 — the call-free spine -/

/-- A message call into the single-`STOP` program (`stopProgram`) succeeds with
empty output, for *any* call parameters whose code is `stopProgram` — no gas floor
required (STOP charges nothing). Stated purely in observables. -/
theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok Observables.ok :=
  Proof.messageCall_stop_observe' p hc

/-- A message call into `PUSH1 0x05 ; STOP` (`pushStopProgram`) succeeds with empty
output for every `p` with `3 ≤ p.gas` — the program's exact gas cost, stated as a
plain hypothesis rather than an `∃G₀`. -/
theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok Observables.ok :=
  Proof.messageCall_pushStop_observe' p hc hg

/-- **First persistent effect.** A message call into `PUSH1 5 ; PUSH1 7 ; SSTORE ;
STOP` (`sstoreProgram`) in `addrA` succeeds and leaves `addrA`'s storage cell `7`
holding `5`, for every `g` with `22106 ≤ g` (`= 3 + 3 + 22100`, the cold
first-write SSTORE cost). Observables-only. -/
theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok (Observables.ok, 5) :=
  Proof.messageCall_sstore_storageAt' g hg

/-- **A sequence of charging instructions.** A message call into
`PUSH;PUSH;SSTORE;PUSH;PUSH;SSTORE;STOP` (`seqProgram`) in `addrA` leaves cell `7`
holding `5` and cell `9` holding `11`, for every `g` with `44212 ≤ g`
(`= 2 × 22106`). Two distinct storage observables off one run. -/
theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok (Observables.ok, 5, 11) :=
  Proof.messageCall_seq_storageAt' g hg

/-! ## External call

`callerParams` runs `callerProg`, which `CALL`s `calleeProg` (living at
`addrCallee`). `calleeProg` is `PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP` — it writes the
value `5` to its own storage slot `7` (the slot and value are arbitrary choices of
this example program; we observe slot `7` precisely because that is where this
callee writes). The observable is that cell, `storageAt addrCallee 7`, read off the
caller's returned account map.

The sub-call is run for real (leanevm's own `beginCall`/`drive` on the callee's
actual code — no oracle, no assumption), so these theorems are about a genuine
nested execution.
-/

/-- **The `∃G₀` external-call theorem.** There is a gas floor `G₀` such that for
every `g ≥ G₀`, the top-level message call into the caller (which forwards a real
`CALL` to the callee) leaves the callee's storage cell `(addrCallee, 7)` holding
`5`: with enough gas, the child clears the 63/64 `callGasCap`, its `SSTORE`
commits.

This is now re-derived as an **instance of the general rung-2 theorem**
`behaves_call` (below): the callee `calleeProg` is supplied through its own
`Behaves`, and the caller through a `CallerForwards` witness; the general theorem
produces the `∃G₀` `Behaves`, which is specialized back to the fixed
`callerParams g` world here. The `∃G₀` is *forced*, not cosmetic — see
`call_counterexample`. -/
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 :=
  Proof.messageCall_call_storageAt_via_behaves_call

/-- **The executable counterexample that forces the `∃G₀`.** At the modest gas
`g = 24000`, the *same* observable is `0`: the 63/64 cap starves the callee
(`childGas 24000 = 21045 < 22106`), its `SSTORE` out-of-gases and rolls back —
**yet the top-level call still completes cleanly** (the caller is handed flag `0`
and `STOP`s, no top-level `OutOfGas`). Read against `messageCall_call_storageAt`,
this shows no gas-floor-free statement ("completes ⇒ cell is 5") can hold. -/
theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0 :=
  Proof.call_counterexample

/-! **Reflexivity is intrinsic here, not a separate axiom.** `messageCall_call_storageAt`
already runs the child through the genuine `beginCall`/`drive` (no oracle
hypothesis), so its truth *is* the statement that the sub-call is a real message
call. The standalone witness that the exact CALL-produced child params, run on
their own, commit `5` is `Proof.messageCall_child_reflexive` — it is kept in the
proof layer because its statement necessarily names the internal caller frame
(`Proof.callerCalled`), which has no place on the frame-free audit surface. -/

/-! ## Rung 2 — the general external-call theorem (general, over both programs)

The external call generalized over **both** programs. For ANY callee characterized
by its **own** `Behaves` (under a callee precondition `calleePre`), a caller that
forwards a `CALL` to it `Behaves` with the **same** `completedWith a k v` named
outcome, above a gas floor `G₀` — the floor being exactly the `∃G₀` the 63/64
`callGasCap` forces. The callee is a black box (consumed only through its
`Behaves`); the caller supplies a per-entry `CallerForwards` witness packaging the
caller-specific facts the engine cannot know generically (which child params the
`CALL` produces, that they run `calleeCode` and clear `calleePre`, and that a
completed child's cell is forwarded to the top level).

Honest-statement note: `Behaves` quantifies over **all** worlds running
`callerCode`, but a caller only forwards to *this* callee when the world actually
places `calleeCode` at the called address; in an adversarial world the call fails
and the cell is untouched. So the theorem carries a **caller precondition**
`callerPre` (conjoined with the gas floor) that pins the world enough for
forwarding to hold — gas stays first-class, the world constraint is visible, never
swept away. The concrete `messageCall_call_storageAt` above is the instance with
`callerPre := ∃ g, p = callerParams g`. -/

/-- **Rung 2: `behaves_call`.** For any callee given by its own
`Behaves calleePre calleeCode (completedWith … a k v)`, any caller with a per-entry
`CallerForwards` witness `Behaves` with the **same** `completedWith a k v`, above
the gas floor `G₀`. The callee `Behaves` is a genuine hypothesis (black-box), the
`∃G₀` is the 63/64 `callGasCap` floor carried in `pre`, and the conclusion is the
named `Outcome` — never a raw `.ok`. -/
theorem behaves_call
    (callerCode calleeCode : ByteArray)
    (callerPre calleePre : World → Prop)
    (a : AccountAddress) (k v : UInt256) (G₀ : ℕ)
    (hcallee : Behaves calleePre calleeCode (fun o => Outcome.completedWith o a k v))
    (W : ∀ p : World, p.codeSource = .Code callerCode → callerPre p → G₀ ≤ p.gas.toNat →
        Proof.CallerForwards calleeCode calleePre a k v p) :
    Behaves (fun p => callerPre p ∧ G₀ ≤ p.gas.toNat) callerCode
      (fun o => Outcome.completedWith o a k v) :=
  Proof.behaves_call callerCode calleeCode callerPre calleePre a k v G₀ hcallee W

end BytecodeLayer
