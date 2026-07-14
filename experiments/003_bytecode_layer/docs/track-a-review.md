# Track A review — the flat-EVM `Runs` reasoning layer (exp003)

*Specs-first review for the project lead. Read-only on code. Every code reference
links to the current source; the load-bearing definitions and statements are quoted
verbatim. Proof bodies are deliberately omitted — at most a one-line strategy.*

---

## TL;DR

Track A turns philogy's **flat** `EVMLean` (`drive`) into a reusable, compositional
reasoning layer. The single design move — making an external **CALL a constructor of
the `Runs` relation** — collapses a brittle 5-hypothesis "one call only" bridge into
ordinary regular-language composition: a multi-call program is now one `Runs` value
built with `Runs.trans`/`Runs.call`, crossed by **one** boundary bridge. The headline
result is [`messageCall_runs_calls`](../../../EVM/BytecodeLayer/Spec.lean#L221) (re-exporting the
proof [`Hoare.messageCall_runs_calls`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L175)):
a caller whose `Runs fr₀ last` interleaves **any number** of returning CALLs with
opcode steps, ending at a halt, delivers `messageCall p` — *no per-call halt
requirement and no numeric fuel side condition*. The layer also gains the opcode rules
(`runs_push`/`runs_sstore`/`runs_add`/`runs_lt`/`runs_sload`/`runs_gas`) and a
CFG combinator ([`runs_branch`](../../../EVM/BytecodeLayer/Hoare.lean#L408) + the JUMP/JUMPI/JUMPDEST
rules) that Track C's lowering consumes.

**Status (reported, not re-run):** build green at **1130 jobs**; the layer is
**axiom-clean** — every new theorem depends only on `propext`/`Classical.choice`/`Quot.sound`,
with no `sorry`/`admit`/`axiom` and no `native_decide`/`ofReduceBool`/`bv_decide`
(PLAN.md log, [PLAN.md#L239](../PLAN.md#L239)). I independently confirmed: zero
`sorry`/`admit`/`native_decide`/`bv_decide` in `BytecodeLayer/` source (the three grep
hits are the strings inside docstrings claiming axiom-cleanliness).

---

## 1. Goal & context

The experiment ([`currentplan.md`](../../../currentplan.md), repo root) builds toward a
**verified IR → EVM bytecode compiler**, on top of *two* EVM semantics that are meant to
**converge**: the **flat** `EVMLean` (one tail-recursive `drive` over a shared pending
stack, one fuel counter — Track A's base) and the **nested** `EVMYulLean` (`Θ/Ξ` mutual
recursion — Track B). Flat is implementation-faithful and terminates trivially, but
*compositionality must be earned as theorems*; nested is compositional by construction.
Track A is the **flat side** of that bake-off: it recovers procedure-call-style
compositional reasoning as theorems over `drive`.

The driving defect Track A exists to fix (recorded in `currentplan.md`): exp003's old
sequencing rule was *one frame → one call → one frame that halts*. It composed only with
suffixes that *eventually halt*, so it could not express an **intermediary** call — a
program that calls, continues, and calls again. Track C confirmed this is fatal for
multi-call lowering. Track A's answer is §6.1 below.

The **end goal** (`currentplan.md` "END GOAL", [EXPERIMENT-REPORT.md](../../../EXPERIMENT-REPORT.md)):
a shared `EVMSemantics` interface both semantics instantiate with the *same* theorems.
The Track-A surface theorems that are candidates for that interface are flagged in §7.

---

## 2. The abstraction stack (bottom → top)

The layer is four strata. Lower strata mention `Frame`/`drive`/fuel (internal bricks);
the top stratum is the `messageCall`/`Outcome` boundary.

| Layer | File | Job |
|---|---|---|
| **L0 — vendored flat semantics** | `EVMLean/Evm/Semantics/Interpreter.lean` ([`drive`](../EVMLean/Evm/Semantics/Interpreter.lean#L36), [`messageCall`](../EVMLean/Evm/Semantics/Interpreter.lean#L84), [`seedFuel`](../EVMLean/Evm/Semantics/Interpreter.lean#L82), [`endFrame`](../EVMLean/Evm/Semantics/Interpreter.lean#L8)); [`beginCall`](../EVMLean/Evm/Semantics/Call.lean#L18), [`resumeAfterCall`](../EVMLean/Evm/Semantics/Call.lean#L122) | The trusted trampoline. One `drive (fuel) (stack) (Frame ⊕ FrameResult)`. |
| **L1 — interpreter `drive` lemmas** | [`Semantics/Interpreter/Drive.lean`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean), [`DescentEq.lean`](../../../EVM/BytecodeLayer/Semantics/Interpreter/DescentEq.lean), [`Measure.lean`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Measure.lean), [`NeverOutOfFuel.lean`](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean) | The `drive` rewrite vocabulary, fuel monotonicity, call-descent reconciliation, and the unconditional never-out-of-fuel theorem. |
| **L2 — `Runs` + opcode/CFG rules** | [`Hoare.lean`](../../../EVM/BytecodeLayer/Hoare.lean) | The index-free `Runs` relation (`refl`/`step`/`call`), `Runs.trans`, every `runs_*` opcode rule, the `runs_branch` combinator, and SSTORE framing. |
| **L3 — boundary bridges** | [`Hoare/CallSequence.lean`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean), re-exported on [`Spec.lean`](../../../EVM/BytecodeLayer/Spec.lean) | `Runs.drive_reconcile`, `messageCall_runs`, `messageCall_runs_calls`, `messageCall_calls_completedWith` — the only observable-level exports. |
| **examples** | [`TwoCallExample.lean`](../../../EVM/BytecodeLayer/Examples/TwoCallExample.lean), [`BranchExample.lean`](../../../EVM/BytecodeLayer/Examples/BranchExample.lean), [`ArithStorageExample.lean`](../../../EVM/BytecodeLayer/Examples/ArithStorageExample.lean) | Acceptance tests for multi-call, branching, and the arithmetic/storage rules. |

**Dependency spine to the headline.** `messageCall_runs_calls`
→ [`messageCall_runs`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L132)
→ [`Runs.drive_reconcile`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L75)
+ [`messageCall_never_outOfFuel`](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158)
+ [`messageCall_eq_drive`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L75)
+ [`drive_halt`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L56).
`Runs.drive_reconcile` in turn rests on three L1 bricks, one per `Runs` constructor:
[`drive_eq_of_both_ne_oof`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L42) (refl),
[`drive_stepsTo`](../../../EVM/BytecodeLayer/Hoare.lean#L68)/[`drive_step`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L45) (step),
and [`drive_descend_eq`](../../../EVM/BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L154) + [`drive_fuel_mono`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L187) + [`driveG_needsCall_code`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L115) (call).

---

## 3. The specs that matter

### 3.1 The `Runs` relation and its composition (L2)

`Runs` is the reflexive-transitive closure of single opcode steps, **extended with an
external-CALL link**. It carries no step index — the index was dropped once every fuel
obligation was discharged by never-out-of-fuel reconciliation instead of a numeric bound.

```lean
-- BytecodeLayer/Hoare.lean#L114
inductive Runs : Frame → Frame → Prop where
  | refl (fr : Frame) : Runs fr fr
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') :
      Runs fr fr'
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
```

The atom of `step` is [`StepsTo`](../../../EVM/BytecodeLayer/Hoare.lean#L52) ("one non-halting
`stepFrame` advances `exec`"). The payload of `call` is `CallReturns`, which bundles the
*entire returning external call as one link* — CALL step, child entering as code, the
child's black-box terminating `drive`, and the resumed parent frame:

```lean
-- BytecodeLayer/Hoare.lean#L91
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending
```

Composition is the **sequencing rule** — gluing any two blocks (including ones with call
nodes) end to end:

```lean
-- BytecodeLayer/Hoare.lean#L129  (re-exported BytecodeLayer/Spec.lean#L50)
theorem Runs.trans {fr mid fr' : Frame}
    (h₁ : Runs fr mid) (h₂ : Runs mid fr') : Runs fr fr'
```
*Strategy: induction on `h₁`, re-applying the matching constructor in each case.*

### 3.2 The reconciliation invariant (L3, the engine)

Because `Runs` has no step index, the bridge cannot phrase a numeric fuel bound. The
replacement is an *index-free* invariant: any two terminating runs along a `Runs` path
agree.

```lean
-- BytecodeLayer/Hoare/CallSequence.lean#L75
theorem Runs.drive_reconcile {fr last : Frame} (h : Runs fr last) :
    ∀ {a b : ℕ},
      drive a [] (running fr) ≠ .error .OutOfFuel →
      drive b [] (running last) ≠ .error .OutOfFuel →
      drive a [] (running fr) = drive b [] (running last)
```
*Strategy: induction on the `Runs` derivation. `refl` reconciles by `drive_eq_of_both_ne_oof`;
`step` peels one `drive` step (`drive_stepsTo`); `call` splices the whole returning child
run into the path via `drive_descend_eq` (lifted to the path's fuel with `drive_fuel_mono`).*
The crucial point for the design argument: **the `call` case is already in this induction**
— multi-call composition required *no new proof obligation*.

### 3.3 The headline bridges (L3)

The single boundary bridge — `Runs` to a halt becomes a `messageCall` result, no fuel
side condition:

```lean
-- BytecodeLayer/Hoare/CallSequence.lean#L132  (re-exported BytecodeLayer/Spec.lean#L58)
theorem messageCall_runs (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))
```
*Strategy: the halt site delivers in 2 fuel (`drive_halt`); the seeded run avoids
`OutOfFuel` (`messageCall_never_outOfFuel`); `Runs.drive_reconcile` equates the two.*

The **headline** multi-call guarantee is *definitionally the same theorem*, renamed so
callers cite the multi-call contract:

```lean
-- BytecodeLayer/Hoare/CallSequence.lean#L175  (re-exported BytecodeLayer/Spec.lean#L221)
theorem messageCall_runs_calls (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin h hhalt
```

The only fully observable-level export lifts that to the named outcome predicate
[`Outcome.completedWith`](../../../EVM/BytecodeLayer/Observables.lean#L100):

```lean
-- BytecodeLayer/Hoare/CallSequence.lean#L210  (re-exported BytecodeLayer/Spec.lean#L234)
theorem messageCall_calls_completedWith (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin : EntersAsCode p fr₀)
    (h      : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt)
    (hsucc  : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell  : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v
```

### 3.4 The opcode rules (L2)

Each rule is a one-step `Runs` to a *named post-frame transformer* (so the next rule
consumes it and `Runs.trans` threads symbolic state without ever naming a trace), under
purely semantic preconditions (decode, gas, stack shape). Representative pair:

```lean
-- BytecodeLayer/Hoare.lean#L241  (ADD)
theorem runs_add (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest)
```

The full opcode roster (all re-exported on `Spec.lean`):
[`runs_push1`](../../../EVM/BytecodeLayer/Hoare.lean#L173)/[`runs_push`](../../../EVM/BytecodeLayer/Hoare.lean#L185),
[`runs_sstore`](../../../EVM/BytecodeLayer/Hoare.lean#L197),
[`runs_add`](../../../EVM/BytecodeLayer/Hoare.lean#L241),
[`runs_lt`](../../../EVM/BytecodeLayer/Hoare.lean#L252),
[`runs_sload`](../../../EVM/BytecodeLayer/Hoare.lean#L264),
[`runs_gas`](../../../EVM/BytecodeLayer/Hoare.lean#L276).
SSTORE and SLOAD additionally carry **observable storage lenses**:
[`sstoreFrame_storage_self`](../../../EVM/BytecodeLayer/Hoare.lean#L446) (effect),
[`sstoreFrame_storage_frame`](../../../EVM/BytecodeLayer/Hoare.lean#L466) (frame — only `(self,key)`
is touched), and [`sloadFrame_storage_self`](../../../EVM/BytecodeLayer/Hoare.lean#L287) (the pushed
word read through the same `find?/lookupStorage` lens Track C's `Match` uses). These connect
the symbolic post-frames to the IR-level storage cell. *All seven `runs_*` proofs are
`Runs.single ∘ stepsTo_of_next ∘ stepFrame_*` one-liners; the lens proofs are `rfl`/`simp`.*

### 3.5 The CFG combinator (L2) — see §6.2 for the design argument

JUMP/JUMPI lift the same way ([`runs_jump`](../../../EVM/BytecodeLayer/Hoare.lean#L328),
[`runs_jumpi_taken`](../../../EVM/BytecodeLayer/Hoare.lean#L341),
[`runs_jumpi_fallthrough`](../../../EVM/BytecodeLayer/Hoare.lean#L357),
[`runs_jumpdest`](../../../EVM/BytecodeLayer/Hoare.lean#L374)), differing only in that the post-frame
moves `pc` to a resolved destination. The reasoning helper for a conditional is:

```lean
-- BytecodeLayer/Hoare.lean#L408
theorem runs_branch {fr fr' : Frame} {dest cond : UInt256} {rest : Stack UInt256}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Ghigh ≤ fr.exec.gasAvailable.toNat)
    (branch :
      (∃ new_pc, cond ≠ 0 ∧ fr.get_dest dest = some new_pc
        ∧ Runs (jumpFrame fr GasConstants.Ghigh new_pc rest) fr')
      ∨ (cond = 0 ∧ Runs (jumpiFallthroughFrame fr rest) fr')) :
    Runs fr fr'
```
*Strategy: `rcases` on the caller's `branch` disjunction; each arm is `runs_jumpi_* |>.trans`
the supplied continuation.*

---

## 4. Hypotheses & modeling

**World model.** State is a [`Frame`](../EVMLean/Evm/Semantics/Frame.lean) (an
`ExecutionState` plus `kind`/`validJumps`); a call is described by [`CallParams`](../EVMLean/Evm/Semantics/Params.lean#L8)
and a [`CallResult`](../EVMLean/Evm/Semantics/Params.lean#L30); execution is the flat
[`drive`](../EVMLean/Evm/Semantics/Interpreter.lean#L36) trampoline. Observables are the
three-way [`Outcome`](../../../EVM/BytecodeLayer/Observables.lean#L72) (completed/reverted/exception),
with [`completedWith`](../../../EVM/BytecodeLayer/Observables.lean#L100) as the storage-cell predicate.

**Hypotheses carried by the headline `messageCall_runs_calls`** — three, all honest and
structural, *none* smuggling the conclusion:
- `hbegin : EntersAsCode p fr₀` — i.e. [`beginCall p = .inl fr₀`](../../../EVM/BytecodeLayer/Semantics/System.lean#L237): the call enters as EVM code with entry frame `fr₀`. A side condition on the *entry*, not the result.
- `h : Runs fr₀ last` — the caller's actual execution trace, built by the constructors. This is structural: it says *how the bytecode steps*, derived from decode/gas/stack facts via the `runs_*` rules — it is **not** an assumed "the call forwards/returns X".
- `hhalt : stepFrame last = Signal.halted halt` — the final frame halts.

**What is notably *absent* and why it matters (the load-bearing improvement):** there is
**no numeric fuel side condition** (discharged internally by `messageCall_never_outOfFuel`
+ `drive_reconcile`) and **no per-call halt requirement**. Intermediary calls return into
more code; each is just a `.call` node spliced by the reconciliation induction. The CALLEE
is consumed as a **black box** — `CallReturns` only requires *some* terminating `drive` of
the child to `.ok childRes`, with no oracle on what it computes. This is what makes the
rule *sound* rather than a forwarding assumption.

**The honest-but-large hypothesis to be aware of:** `Runs fr₀ last` itself can be a deep
term (one `.call` node per external call, plus one `.step` per opcode). It is large, but it
is *exactly the execution* and is assembled mechanically by the caller from `runs_*` lemmas
and `Runs.trans` — it does not quantify over an abstract trace variable or assume anything
about outputs. So it is load-bearing structure, not a smell.

---

## 5. Results taxonomy

**Headline / mainline.**
[`messageCall_runs_calls`](../../../EVM/BytecodeLayer/Spec.lean#L221) (multi-call composition) and
its observable lift [`messageCall_calls_completedWith`](../../../EVM/BytecodeLayer/Spec.lean#L234).
[`messageCall_runs`](../../../EVM/BytecodeLayer/Spec.lean#L58) is the single underlying bridge.

**Supporting bricks (load-bearing scaffolding).**
- L3 engine: [`Runs.drive_reconcile`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L75), [`drive_eq_of_both_ne_oof`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L42), [`completedWith_of_ok`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L192).
- L2: [`Runs.trans`](../../../EVM/BytecodeLayer/Hoare.lean#L129), [`Runs.single`](../../../EVM/BytecodeLayer/Hoare.lean#L138), the seven `runs_*` opcode rules, the four CFG rules + `runs_branch`, the three storage lenses.
- L1: [`messageCall_never_outOfFuel`](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158) (unconditional — see below), [`drive_fuel_mono`](../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L187), [`drive_descend_eq`](../../../EVM/BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L154), the `drive_*`/`driveG_*` rewrite vocabulary, and the `stepFrame_*` characterizations the `runs_*` rules wrap.

**Examples / demos (acceptance tests; nothing in the headline chain depends on them, but
all three are wired into the default build via [`ConcreteSpecs.lean`](../../../EVM/BytecodeLayer/Examples/ConcreteSpecs.lean#L6) so they are continuously type-checked).**
- [`TwoCallExample`](../../../EVM/BytecodeLayer/Examples/TwoCallExample.lean#L62): [`twoCall_runs`](../../../EVM/BytecodeLayer/Examples/TwoCallExample.lean#L62) glues `prefix · call₁ · middle · call₂ · suffix` into one `Runs`, and [`twoCall_messageCall`](../../../EVM/BytecodeLayer/Examples/TwoCallExample.lean#L84) crosses the bridge once — the **acceptance test for the intermediary-call defect** (neither call halts; only `last` does).
- [`BranchExample`](../../../EVM/BytecodeLayer/Examples/BranchExample.lean#L70): [`branchRuns`](../../../EVM/BytecodeLayer/Examples/BranchExample.lean#L70) composes both arms of a `JUMPI` for an *arbitrary* runtime `cond` via `runs_branch`.
- [`ArithStorageExample`](../../../EVM/BytecodeLayer/Examples/ArithStorageExample.lean#L50): [`arithStorageRuns`](../../../EVM/BytecodeLayer/Examples/ArithStorageExample.lean#L50) threads `ADD ; LT ; GAS ; SLOAD` through `Runs.trans` (incl. the GAS→SLOAD coupling and a cold-slot `Gcoldsload = 2100` charge).

**Smells / weak proofs.** None of consequence. The examples use small `omega`/`rfl`
discharges over concrete hardcoded programs (e.g. `branchProgram = #[0x57,0x00,0x00,0x5b,0x00]`,
gas floors `11`/`2200`) — these are hardcoded *witnesses*, isolated leaves, and notably
**avoid `native_decide`** (the frames carry an explicit `validJumps := #[3]` precisely so
`get_dest` reduces in the kernel rather than through the opaque `partial def
validJumpDests`). No cranked `maxHeartbeats`, no `decide` on big terms. The general
`runs_*`/bridge proofs are short. The whole layer is axiom-clean per §TL;DR.

**Note on `messageCall_never_outOfFuel`** — it is **unconditional** ([NeverOutOfFuel.lean#L158](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158)): no `gasFundsDescent` hypothesis, no fuel/`Frame` in the statement. It is discharged by `gasFundsDescent_holds` (the five per-transition gas-decrease conjuncts) fed to the general measure theorem. This is what lets the bridge drop its fuel side condition — a genuine improvement, not a hypothesis shuffle.

---

## 6. The two design arguments

### 6.1 Why `call` is a `Runs` constructor (and why this makes multi-call work)

**The prior pain.** exp003's earlier bridge, `messageCall_call_runs`, was a *bespoke
five-hypothesis sequence*: a prefix `Runs`, then exactly **one** `CallReturns`, then a
suffix `Runs` that **halts**. Structurally it could express only *one* call sandwiched
between a prefix and a halting suffix. The fatal limitation: an **intermediary** call —
one that returns into *more code that itself contains another call* — could not be
expressed, because the rule's single call slot was already spent and the suffix had to
halt. A CALL was a `Signal.needsCall`, *not* a `Runs` link, so `Runs.trans` could not glue
it. Track C's multi-call lowering hit exactly this wall (`currentplan.md` orchestration log).

**The fix and why it is the right one.** Promote the returning call to a *link in the
relation itself*: bundle its four facts as [`CallReturns`](../../../EVM/BytecodeLayer/Hoare.lean#L91)
and add it as the [`Runs.call`](../../../EVM/BytecodeLayer/Hoare.lean#L114) constructor. Now `Runs`
is the closure of `refl`/`step`/`call` — precisely the **regular language `(step | call)*`**.
A program with N calls is one `Runs` value, assembled by `Runs.trans` gluing `Runs.call`
nodes around opcode runs ([`twoCall_runs`](../../../EVM/BytecodeLayer/Examples/TwoCallExample.lean#L62)
is the worked two-call witness). The payoff that makes this *clearly* the correct approach:
**multi-call composition needed no new proof.** `Runs.drive_reconcile` inducts over the
`Runs` derivation and *already has a `call` case* that splices a returning child run; so
[`messageCall_runs_calls`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L175) is *definitionally*
[`messageCall_runs`](../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L132). The N-call guarantee
fell out for free the moment the closure was the right shape.

**Alternatives considered, and why they lose.**
1. *Keep the bespoke per-call bridge and add a 2-call, 3-call, … variant.* Combinatorial
   explosion; every new program shape needs a new hand-rolled lemma with its own fuel
   bookkeeping. The single-call bridge's halting-suffix requirement makes intermediary
   calls *inexpressible*, not just inconvenient — no amount of variants recovers them
   cleanly.
2. *Reshape `drive` into a nested form* so a child call is a genuine subterm (the Track B
   design). This abandons the flat base's chief virtues (trivial termination, single fuel,
   implementation fidelity) and amounts to switching semantics — which is exactly Track B's
   separate bake-off, not a fix for the flat layer. It would also re-litigate the trusted
   semantics rather than build a *reasoning layer* over it.
3. *Generalize the bridge to take an explicit `List CallReturns` (a trace of calls).* This
   re-introduces the very "name the trace" pain the `Runs` relation was built to abolish:
   the calls would have to be threaded by hand and reconciled with the opcode steps
   between them. The constructor approach hides the trace *inside the proof term*.

Making CALL a `Runs` link is the minimal change that (a) stays on the flat base, (b) reuses
the existing reconciliation induction unchanged, and (c) yields the regular-language algebra
where composition is just `trans`.

### 6.2 Why the CFG / control-flow combinator design

**The shape.** A conditional branch is *not* given an invariant theory. Instead
[`runs_branch`](../../../EVM/BytecodeLayer/Hoare.lean#L408) is a thin combinator: the caller
**case-splits on the runtime value of the branch condition**, supplies for the selected
side the `Runs` that continues from there (taken: from the jump-destination frame;
fall-through: from `pc+1`), and `runs_branch` drops that into `Runs.trans` after the
matching `runs_jumpi_*` step. The disjunction is *the caller's*, so the helper is usable
both when the condition is statically known and when it is only known to be one of two
cases ([`branchRuns`](../../../EVM/BytecodeLayer/Examples/BranchExample.lean#L70) runs it for an
arbitrary `cond`). JUMPDEST is handled as an ordinary no-op step
([`runs_jumpdest`](../../../EVM/BytecodeLayer/Hoare.lean#L374)): a taken jump simply `trans`-steps
past its landing pad. **Loops are deferred**, deliberately: a back-edge is *just another
`runs_jump` to an earlier pc, glued by `Runs.trans`* — and because gas strictly decreases
each iteration (and `drive` terminates / never out-of-fuel), any finite execution is
already a finite `Runs`. So loops need no fixed-point/invariant machinery at this layer;
finiteness comes from gas.

**What it buys.** Branch reasoning composes *exactly like straight-line code* — the same
`Runs`/`Runs.trans` algebra, no new relation, no special-casing in the bridge (the bridge
never sees control flow; it only sees `Runs … last`). Track C's branch lowering threads
`runs_branch` the same way it threads `runs_add`. The CFG rules reuse the opcode-rule
template verbatim (one-step `Runs` to a post-frame), so they cost almost nothing.

**Alternatives considered, and why this one was chosen.**
1. *A Hoare-style invariant/while theory for loops now.* Premature and heavyweight:
   gas-bounded EVM execution is always finite, so a `Runs`-as-finite-trace already covers
   every terminating loop via back-edge `trans`. An invariant theory would add machinery
   the current consumers (Track C, no unbounded loops yet) do not need, and would couple
   the layer to a fixed-point discipline before the IR demands it. It can be layered on top
   later *without* disturbing `runs_branch`.
2. *Bake the case-split into the combinator* (make `runs_branch` decide the condition
   itself, e.g. by `decide`). That fails when the condition is symbolic/runtime-unknown —
   the common case for real branches and for gas-dependent branches (the Q2 gas-introspection
   goal). Exposing the disjunction to the caller keeps the combinator honest under symbolic
   conditions.
3. *Per-program bespoke branch lemmas* (as the calls once were). Same explosion problem as
   §6.1; `runs_branch` is the program-agnostic generalization.

The combinator is the smallest design that makes branches first-class `Runs` citizens,
stays sound under symbolic conditions, and leaves room for both gas-introspection (the
condition can be a `GAS`-derived word) and an eventual loop-invariant layer.

---

## 7. Rough edges, open questions, and the convergence handoff

- **Altitude caveat (self-flagged in [Spec.lean#L23](../../../EVM/BytecodeLayer/Spec.lean#L23)).** The
  program-logic rules on the spec surface (`Runs.trans`, the `runs_*` rules, `messageCall_runs`)
  are **frame-level** — they mention `Runs`/`Frame`/`stepFrame`, not pure observables. Only
  [`messageCall_calls_completedWith`](../../../EVM/BytecodeLayer/Spec.lean#L234) is fully
  observable-level. Per project memory this frame-level surface is acceptable for exp003 (the
  low-level layer), but it is the tension to resolve before Phase-2 export.
- **Modeling limits read from the specs.** SSTORE effect lens requires `newValue ≠ 0`
  ([Hoare.lean#L449](../../../EVM/BytecodeLayer/Hoare.lean#L449)) and the self account present; SLOAD's
  warm/cold flag is a literal `accessedStorageKeys.contains` premise. No RETURN-data rule yet
  (the bridge takes halts generically via `hhalt`, and `completedReturning` exists, but there
  is no `runs_return`). `CREATE` is not yet a second descent constructor (backlog). Reentrancy
  / value-transfer interaction is deferred.
- **Candidates for the shared `EVMSemantics` interface (Phase 2a).** The signatures Track B's
  nested surface should converge on are
  [`messageCall_runs_calls`](../../../EVM/BytecodeLayer/Spec.lean#L221) (the ≥N-call composition
  contract), [`messageCall_calls_completedWith`](../../../EVM/BytecodeLayer/Spec.lean#L234) (observable
  external-call rule), and [`messageCall_never_outOfFuel`](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158)
  (Track B's B2 is the nested analogue). If both semantics prove these same statements, they
  are interchangeable for IR reasoning — exactly the bake-off `currentplan.md` END-GOAL wants.
- **Next steps already queued** (`currentplan.md`): merge A → base (unblocks Track C's C3),
  then gas-introspection first-class, `CREATE` constructor, and symbolic worlds + gas-ledger
  to scale past concrete `find?`/`decide`.
