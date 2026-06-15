# Bytecode-first: discussion record and proposed direction

*Recorded 2026-06-11, mid-session, while the gas-erasure proof agent was still
running. This document is the handoff: it captures the session's findings, the
strategic discussion between Eduardo and the agent, the proposed pivot, and how
to finish the in-flight work. It partially supersedes
[lowering-v2-plan.md](../archive/lowering-v2-plan.md): the v2 *statement shape* survives;
the plan's later phases are replaced by the direction below.*

## 1. Session state (experiment 001, "lowering v2")

Done and building (`lake build` green, no sorries):

| Artifact | Content |
|---|---|
| `ToyExternalCall/IR.lean` | **The spec**: gasless, oracle-free IR semantics (`Gasless.*`). Gas counter is dead; calls execute real callee bytecode by invoking `EVM.call` on a *full tank* (gas := max, so the 63/64 cap never binds and the callee gets exactly the requested gas). Shared syntax/state defs at top. |
| `ToyExternalCall/Metered.lean` | The v1 gas-exact semantics, demoted to an internal proof artifact ("the proof's gas ledger"). Oracle machinery lives here; `evmCallOracle` = `EVM.call` itself. |
| `ToyExternalCall/CallSound.lean` | `evmCallOracle_sound : CallOracleSound evmCallOracle` — **`EVM.call` frame insensitivity, proved** (89 lines, pure defeq bridging: `if_congr` + structure eta). Corollary `lowering_exact`: the metered lowering theorem with **zero semantic assumptions** (only the `hsize` representability bound). |
| `ToyExternalCall/{Bytecode,EVMLemmas,Preservation}.lean` | Unchanged from v1 (deliberate reuse). |

**Update (same day, later): v2 is COMPLETE.** `GasErasure.lean` (860 lines,
`run_erasure` proved) and `Correctness.lean` (`load`, `lowering_correct`,
`Observables`, `lowering_observables`) landed; full `lake build` green, zero
sorries, all exported theorems on standard axioms only. The honest results
doc exists: `experiments/001_toy_external_call/docs/results-v2.md` (read it —
it records the rough edges and the verdict). `handoff.md` updated. The only
possibly-unfinished piece is `Validation.lean` (`#eval` non-vacuity harness,
delegated to a background agent — if absent or broken, it is optional
evidence, not part of the proof artifact). §7 below is therefore done except
where it concerns Validation; the next session starts directly at the pivot
(§4, vendoring first).

## 2. Findings that drove the discussion (load-bearing, keep these)

1. **`CALL` is a gas-consulting opcode.** Even with no `GAS` opcode in the IR,
   gas is semantically observable through calls, twice over: the forwarded
   amount is `min(g, ⌊63/64·remaining⌋)` (reads the counter via `Cgascap`), and
   a callee that runs out of gas does **not** abort the caller — it returns
   flag 0 and the caller continues on a different branch.
   **Counterexample** killing the tempting statement
   `result ≠ OutOfGass → result = IR.run` (and its disjunctive variant
   `∀G, OOG ∨ equal`): fund the bytecode modestly; at a call with gas argument
   `g`, the cap binds, the callee OOGs internally, flag 0 is stored, the run
   `STOP`s cleanly — a successful execution different from the IR's (which
   forwarded the full `g`, callee succeeded, flag 1), with no `OutOfGass`
   anywhere. Hence the exported form must be `∃ G₀, ∀ G ≥ G₀` ("sufficiently
   funded ⇒ the cap never binds"), not "didn't visibly OOG ⇒ equal".
2. **For the call-free fragment** the conditional statement *is* true and has a
   ledger-free proof: walk the simulation; at each gas check, either it passes,
   or the whole result is `OutOfGass`, contradicting the hypothesis — vacuity
   propagation, zero arithmetic. The quantitative content of the gas story
   lives **only at call sites**.
3. **The metered semantics is reuse-driven, not necessary** (Eduardo's
   "cut-elimination" point, conceded). It exists because v1's 1700 lines of
   chunk lemmas are stated against it; a greenfield proof could use vacuity
   propagation everywhere + local arithmetic at `CALL` and skip the ledger.
4. **Lockstep artifacts are disposable internals.** Fuel-per-lowered-opcode,
   the metered cost schedule, and the chunk-by-chunk `injectFrame` simulation
   are all tied to the current bijective, non-optimizing lowering and will
   break under an optimizing compiler. The *exported statement* (∃G₀ on gas,
   observables, eventually ∃-quantified fuel) mentions none of them — it is the
   stable contract; internals get rearchitected per lowering.
5. **Fuel debt.** Removing fuel from exported statements needs a
   fuel-monotonicity theorem about EVMYulLean's whole stack (`Θ`/`Ξ`/`X`):
   more fuel only turns `OutOfFuel` into the stable result. Provable,
   substantial, not yet attempted. (Callee `OutOfFuel` propagates as a hard
   error, not flag 0 — verified in the fork — so monotonicity is the right
   shape.)
6. **`EVM.call` is frame-insensitive** — proved, cheaply (`CallSound.lean`).
   The "reflexive calls" design (IR call = literally `EVM.call`) reduced what
   was an *assumption* in v1 to a ten-line defeq proof, and is strictly
   stronger than both comparators: vyper-hol pays a state-translation cheat
   (B5) at this exact boundary; Verity doesn't execute calls at all (interface
   assumptions per call site).

## 3. The strategic critique (Eduardo)

The toy IR is, by construction, a bijective re-notation of straight-line EVM
bytecode: its instructions are opcodes, its state is `EVM.State`, its semantics
mirrors `EVM.X` action-for-action. The entire lowering proof is therefore a
natural-transformation/bijection argument — real work, but spent proving that
the same thing equals itself in two notations. The *durable* value produced was
never the IR: it was (a) the lemma layer over `EVM.X` (EVMYulLean proves zero
theorems about its own execution), and (b) the findings in §2. Continuing to
grow this IR (control flow, more ops) means continuing to pay low-level costs
for an artifact that is not the real target. Meanwhile the reviewer feedback
(Philip) stands: specs must not be low-level.

## 4. The proposed pivot: bytecode-first, then straight to SIR

Drop the intermediate toy-IR ladder. Invest in the bytecode layer once, then
make Plank SIR the *first* IR we formalize — an IR with a genuine abstraction
gap (CFG, locals, structured operations) where compiler correctness is a real
theorem, not a bijection.

1. **Vendor EVMYulLean, EVM-only.** Fork honestly, in-tree; discard the Yul
   side (we lower straight to bytecode; Yul buys nothing). Keep the
   ethereum/tests conformance harness alive — it is the empirical backing for
   "this semantics is the real EVM"; vendoring without it converts an
   executable spec into an unvalidated model. Maintain `DIVERGENCES.md`
   (existing deltas: exposed `Z`/`H`/`W`, list-based `ByteArray.get?`/
   `extract'`, pure `zeroes`). We gain the freedom to refactor definitions for
   provability (e.g. factor `EVM.call`, restate `X` as a step relation with a
   proved equivalence) instead of working around them.
2. **Build the missing reasoning layer over the bytecode semantics.** This is
   the layer EVMYulLean lacks and Verifereum has (its Hoare-style relational
   framework was flagged in our docs audit as its main architectural advantage
   — use it as the reference design). Contents, demand-driven (see risk §6.2):
   the existing `EVMLemmas` material (decode-at-prefix, per-opcode step/X
   lemmas), sequencing/composition combinators, `JUMP`/`JUMPI` + `D_J`
   reasoning, a loop rule, frame/call rules built on `evmCallOracle_sound`,
   and the gas-refinement pattern (∃G₀; vacuity propagation away from calls,
   local cap arithmetic at calls).
3. **Move the theorem boundary from `EVM.X` to `Θ`/`Ξ` (message-call), and
   state everything in observables.** This is the architectural answer to
   "stop reasoning about injectFrame": `injectFrame` exists *only because* the
   current boundary is mid-frame, where pc/stack/code are live. At the
   message-call boundary a frame is born fresh (pc 0, empty stack, code from
   the account map) and dies at halt, so the natural statement is

   > for every message call to the contract, executing the compiled code under
   > `Θ` yields the same observables (success, returndata, storage/account
   > changes, logs) as the SIR semantics, for all sufficiently large gas,

   with no frame fields anywhere. Mid-frame relations don't vanish — they
   become *proof-internal* to the reasoning layer (rule premises/conclusions),
   never appearing in exported statements.
4. **Formalize Plank SIR against that layer.** SIR keeps a high-level state
   (locals environment, CFG position — no pc, no machine stack, no gas);
   relations to bytecode use per-layer encoding + coupling invariant +
   boundary projection (the Verity pattern), with the §2 gas/fuel treatment.

## 5. What carries over from experiments 001/v2

* `EVMLemmas.lean` — wholesale (it was always the reusable layer).
* `CallSound.lean` — frame insensitivity of `EVM.call` is needed by any call
  rule at any layer.
* The gas-erasure arithmetic (L-monotonicity, cap bounds, `∃G₀` bookkeeping)
  — the pattern recurs at every layer that erases gas; the lemmas port.
* The findings/proof patterns docs (`findings.md`: list-first encodings, defeq
  bridging over record-commutation, if_pos/if_neg guard alignment, standalone
  evaluation equations, position-generalized chunk lemmas).
* The exported statement *shape* (∃G₀ gas refinement; observables; fuel
  pending monotonicity) — designed this session, survives the pivot verbatim.
* The toy IR itself: **retire after v2 closes.** It was scaffolding
  ("teaching IR" per the original pilot plan) and it taught what it was built
  to teach, including that `CALL` forces the gas story (§2.1) — that was the
  pilot plan's stated reason to include calls early.

## 6. Risks and honest caveats

1. **Control flow lands all at once.** Skipping intermediate IRs means the
   first SIR proof takes on `JUMP`/`D_J`, a CFG, and Plank's stack scheduler
   together. Mitigation: the reasoning layer's jump/loop rules get developed
   and tested against small handwritten bytecode *before* SIR consumes them
   (cheap, no IR needed — this is what "good theorems about bytecode" means
   concretely).
2. **"A well-theorem'd bytecode layer" is open-ended.** Scope discipline:
   build rules demand-driven from the SIR proof's needs, not speculatively.
3. **`X` is a fueled function, not a step relation.** Hoare/simulation-style
   rules compose better over a small-step relation; consider defining one and
   proving it equivalent to `X` once (a vendoring-enabled refactor).
4. **Fuel monotonicity** (§2.5) becomes load-bearing at the Θ boundary
   (callee executions are fuel-bounded); schedule it as real work, not a
   footnote.
5. **Gas refunds/substate observability** at the transaction boundary still
   needs a decision (refund counters feed end-of-transaction accounting).
6. The §2.1 constraint is permanent: any gas-free SIR spec must forward
   exactly `g` at calls and export `∃G₀` statements. No higher layer escapes
   it.

## 7. Closing out v2 (instructions for the next session)

1. Wait for / collect `GasErasure.lean` (background agent). Verify:
   `lake build ToyExternalCall.GasErasure`, no sorries, axiom check.
2. Write `Correctness.lean` per §1: compose `lowering_exact` (CallSound) with
   `run_erasure`; the composition is mechanical — rewrite the metered run via
   `run_erasure`'s equation inside `lowering_exact`'s RHS at gas `.ofNat G`,
   `Except.map` of `.ok` reduces, done. Add `Observables`
   (accounts/substate/output) + corollary; `#eval` cross-check both semantics
   on `[inputLoad 0 0, add 1 (local 0) (const 5)]`-style programs (fund the
   EVM side generously: first local touch pays ~2.1M gas for expansion to
   `localBase`); `#print axioms`.
3. Write `experiments/001_toy_external_call/docs/results-v2.md` — honest:
   what was proved, the §2 findings as first-class results, where the design
   fell short of the hope (metered ledger retained for reuse not necessity;
   fuel still in the statement; injectFrame still in the strong form;
   lockstep internals disposable), and the §4 pivot as the recommendation.
   Update `handoff.md` to point at it; mark `spec.md` as describing v1+v2.
4. Then start the pivot: vendoring is the first concrete task (lowering-v2-plan
   §7 has the checklist).

## 8. Open decisions (for Philip)

1. Sign off on retiring the toy IR after v2 closes, and on bytecode-first.
2. Vendoring: EVM-only fork in-tree, conformance tests kept — any reason to
   keep tracking upstream instead (expected hardfork updates)?
3. Theorem boundary at `Θ` (message call): are the observables
   success/returndata/storage/logs the right contract-level interface for
   Plank? Refund counters in or out?
4. Does SIR need `gas()`/`gasleft()`? If yes, a cost-model fragment must be
   planned (it breaks the gas-free spec for those programs).
5. Reasoning-layer style: Hoare-triple-like rules (Verifereum-style) vs
   simulation combinators — preference may follow from who writes SIR proofs
   later.
