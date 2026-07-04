# Recorder model note — ungated `recordCall` and the `rest.isEmpty` gate

Date: 2026-07-03. Branch `p3/recorder`, commit `82e7453`. Files: `LirLean/Spec/Recorder.lean`,
`LirLean/V2/RealisabilitySpec.lean`. Companion to `docs/gas-decision.md` (the recorder is the
log-producer that decision feeds the oracles from) and `docs/target-architecture-2026-07-02.md` §3/§12.

## The finding

The recording interpreter `driveLog` (`Spec/Recorder.lean`) mirrors `drive` branch-for-branch and
records three kinds of introspection point into the `RunLog`: each top-level `GAS` read's post-charge
word, each top-level `SLOAD`'s warmth charge, and each top-level returning external CALL's
`(result, pending)` (via `recordCall`). Per the recorder's own docstrings, all three are meant to
record **only the top-level program's own** points — a descended callee's contract is a single
black box whose internal gas reads / sloads / calls are its own frame's business, not the log's.

The gas and sload records honored this: they gate on `stack.isEmpty` (the running frame is the
top-level one). The returning-CALL record did **NOT** — `recordCall` was invoked **UNGATED** in
`driveLog`'s `.call` delivery branch, so it also recorded a descended callee's inner returning CALLs.
This contradicted:

- its own docstrings ("the top-level program's own returning external CALLs, in program order");
- the sibling gas/sload `stack.isEmpty` gates;
- the intended log model that `docs/gas-decision.md` and the flagship's `realisedCall` oracle assume.

Symptom in the proof surface: R7e (`recorderCoupled_call`) could only be stated with a single-call
`hone` hypothesis, and even then the record count had a "1 + child call count" asymmetry — the
recorder was not faithful when the top-level call's callee itself called.

## The fix

Gate the returning-CALL record on the resumed **pending stack** being empty (`rest.isEmpty`), at both
call sites in the delivery branch:

```lean
(if rest.isEmpty then recordCall pending result callAcc else callAcc)
```

`rest.isEmpty` is the returning-CALL analogue of `stack.isEmpty`: it holds exactly when the CALL that
is returning is the top-level program's own (it resumes onto an empty pending stack). A descended
callee's inner CALLs resume on a nonempty `rest` and are now black-boxed **structurally** — the gate
fails regardless of how many times the child calls. `recordCall` itself is unchanged; only its two
invocation sites are gated. Default `lake build` stays sorry-free; `Nightly` stays green (its sorry
set is the prior set minus R7e).

## Consequence

R7e (`recorderCoupled_call`) now holds **UNCONDITIONALLY** — the `hone` hypothesis was dropped and
the statement is otherwise unchanged — via a new recorder-composition lemma `driveLog_frame_nonempty`:
a nonempty bottom stack makes every gate fail, so an inline child records nothing and threads the
accumulator through unchanged; this is fuel-reconciled with the black-box child run (`drive_fuel_mono`)
and peeled by `driveLog_acc_hom`. Axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

`realisedCall` is therefore faithful even when the top-level call's callee itself calls, which
**unblocks the R3' multi-call generalization**: R3' now generalizes the *consumption* of a record
stream that is already faithful per-record.

Note the two distinct uses of "one call":

- The `rest.isEmpty` gate is about **descent depth** (top-level vs. descended callee). It fully
  resolves R7e, unconditionally, and is orthogonal to how many calls the top-level program makes.
- The `hone : log.calls.length ≤ 1` premises on R3 / R10a / the flagships are about **multiple
  top-level calls** — `callOracleOf` reads only the head `CallRecord`, so the log-fed call oracle is
  currently correct only for single-top-level-CALL programs. These are untouched by this fix; lifting
  them (calls as a consumed stream) is the R3' decision, which now builds on the corrected recorder.

## Decision rationale — Option B (gate the recorder) over the Nightly-only stopgap

Two ways to make R7e provable were on the table:

- **Nightly-only stopgap (rejected).** Leave `recordCall` ungated and carry the mismatch as extra
  hypotheses in the Nightly sorry-lib — an `hone`/single-call premise on R7e (and downstream on R3'),
  absorbing the "1 + child call count" asymmetry into supplied debt. This keeps the model bug and
  pushes it onto the theorem statements: exactly the diseased "supplied-hypothesis debt" the
  `2026-07-02` audit and `docs/gas-decision.md` warned against (a hypothesis that papers over an
  unfaithful definition rather than fixing it). It also would not unblock R3' cleanly — a stream
  consumer cannot be built on a per-record-unfaithful recorder.

- **Option B — gate the recorder (chosen).** Fix the definition so it matches its docstrings and the
  gas/sload gates. The correction lives entirely in the model (`Spec/Recorder.lean`), costs one
  `rest.isEmpty` guard, strengthens R7e to unconditional, and leaves the flagship statements cleaner
  (one fewer supplied premise). Consistent with the project's "fix the definition, don't supply a
  hypothesis around it" stance and with `Runs.call`'s existing child black-boxing.

(In the R7e docstring this resolution is labeled "resolution (A)"; that is the same fix — the (A)/(B)
labels come from different local enumerations. Both refer to gating `recordCall` on `rest.isEmpty`.)
