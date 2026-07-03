# Cyclic CFG via drive-indexed forward simulation (retire `CFGAcyclic` + discharge the ties)

**Goal.** Make `lower_conforms` general over **cyclic** CFGs (loops) AND discharge the
per-cursor §7 ties (`StmtTies`/`TermTies`) from the bytecode run — in **one** construction.
These are the same node: build the IR run by **following the finite, clean-halting bytecode
execution** instead of constructing it statically.

## Why this is one node, not two
- `CFGAcyclic` is used in **exactly one place**: `irRun_exists`/`runFrom_exists`
  (`V2/IRRun.lean`) — building the IR `RunFrom` by recursion on a control-flow block-rank.
  Back-edges have no smaller-rank successor ⇒ no static measure ⇒ can't build the run.
- The lowering simulation `sim_cfg` (`LowerConforms.lean`) inducts on the **given** finite
  IR derivation `hrun : RunFrom …` and is **already cycle-agnostic**. The per-block bricks
  (`sim_stmts_block`, `sim_term_*`, the `Corr` boundary invariant) don't mention acyclicity.
- The bytecode run `driveLog`/`runWithLog` (`V2/RunLog.lean`) is **fuel-recursive and finite**;
  `totalGas`-descent (the never-OOF proof) is the well-founded measure. So: induct on the
  bytecode run, build the IR `RunFrom` as we go, read the realised ties off the actual frames.

## The honest scope — CLEAN HALT only (not OOG)
"Never out of fuel" ≠ "terminates cleanly": with `seedFuel p.gas`, `driveLog` reaches an
EVM conclusion — clean halt (`.halted`, STOP/RETURN) **or** out-of-gas. The IR is **gas-free**
(no OOG counterpart). So:
- bytecode **clean-halts** ⇒ IR exits at the same data condition ⇒ finite, matches;
- bytecode **OOGs mid-loop** ⇒ IR has no counterpart ⇒ **out of scope** (no final world).
The theorem is **conditioned on `runWithLog` reaching a clean `.halted` outcome**. This is NOT
a new restriction: today's gas-envelope ties (`chargeOf … ≤ gasAvailable` per cursor) already
encode "enough gas here, no OOG" — clean-halt and tie-discharge are the same hypothesis two ways.
(Return *value* stays out of scope too — `result` is the value-free `.stopped` boundary, as now.)

## The construction — statement-granular, NOT per-opcode
The invariant lives **only at IR-cursor boundaries** (block entries + statement boundaries where
`stack = []` and `Corr` holds). Between boundaries we **reuse** the existing per-statement
segments (`sim_assign`/`sim_sstore_stmt`/`sim_call_stmt`, each "one IR stmt ↔ one multi-opcode
`Runs`") and the per-terminator `sim_term_*`. The non-optimizing lowering gives each statement a
fixed segment ⇒ boundaries line up. Lockstep is a PROOF technique here (earned by the structural
lowering); the §7 *statement* stays observation-based (would survive an optimizing lowering).

## F0 de-risk verdict (done) — GREEN
Read of `RunLog.lean`/`IRRun.lean`/`Law.lean`/`LowerConforms.lean` confirms feasibility:
- **Measure = `totalGas`** (`Interpreter/Measure.lean`), strictly **descends per block** (every
  block runs ≥ a `JUMPDEST`, cost ≥ 1) and across CALL sub-runs (`gasFundsDescent_*`,
  `resumeAfterCall_gas_le`) — already proved for the never-OOF result (`driveLog_gas_inv`;
  *note 2026-07-03: that recorder-side lemma was deleted in Phase 2 with RunLog's
  gas-monotonicity section — the exp003 descent lemmas named here survive*). This,
  not the trace length, is what bounds the IR run (a gas-free loop with no `GAS` read isn't
  trace-bounded). 
- **`RunFrom.det`/`RunStmts.det`/`EvalStmt.det` exist** (`V2/Law.lean`) — but they give
  *uniqueness*, not existence. **Existence is the work** (the loop has no static measure). The IR
  is built FORWARD one block at a time (always possible, like `runFrom_exists`'s per-block body,
  needs `RunDefinable` operand-definability); the **bytecode's `totalGas` descent is the recursion
  measure** and fixes which successor each branch takes. Determinism is only used to reconcile the
  constructed run with `sim_cfg`'s world equation if needed.
- **`sim_cfg` is confirmed cycle-agnostic** (inducts on the given `RunFrom`, no `CFGAcyclic`).
- **Adequacy** `driveLog_drive`/`runWithLog_drive`/`runWithLog_messageCall` exist; `realisedCall`
  is `rfl` (`realisedCall_eq_evmV2`). Clean-halt = `runWithLog … = some log` (OOG/stuck ⇒ `none`).

## RE-SCOPE (per Eduardo) — cyclic `RunFrom` FIRST, tie-discharge LATER
Eduardo's actual worry is **acyclic-only** (loops); the supplied ties can be "charged later". So
the FIRST deliverable is narrower and very achievable: **construct the IR `RunFrom` from the
clean-halting bytecode (drop `CFGAcyclic`/`RunDefinable`-as-static), feed the EXISTING `sim_cfg`
with the ties STILL supplied.** That removes the loop restriction by itself. Discharging the ties
in the same `totalGas` walk is the follow-on unification (F3+), not blocking.

### `DriveCorr` (boundary invariant) and the construction
```
-- at a block-entry frame (stack []), the bytecode frame is Corr-aligned with the IR cursor,
-- and the frame's remaining run clean-halts (its totalGas is the recursion measure).
DriveCorr prog log … st fr L  :=  Corr prog … st fr L 0  ∧  <fr's driveLog suffix clean-halts>
```
Cyclic `irRun_exists` (the target): by **well-founded recursion on `totalGas` of `fr`**, from
`DriveCorr` at `L`: run the IR block forward (`RunStmts b.stmts` + terminator via the per-block
forward step), run the bytecode to the successor boundary (`sim_stmts_block`+`sim_term_*`
FORWARD), whose `totalGas` is strictly smaller ⇒ IH gives `RunFrom` from the successor ⇒ prepend.
Base: bytecode `.halted` ⇒ IR `RunFrom.stop`/`.ret`. Yields `∃ O, RunFrom prog (realisedCall log
self) st (realisedGas log) L O`. Then the EXISTING `sim_cfg` + supplied ties ⇒ cyclic
`lower_conforms` (no `CFGAcyclic`).

## Phases (DAG; always green; `main` untouched)
- **F0 Scope+invariant.** Read `driveLog`/`runWithLog`/`endFrame`/`totalGas` (`V2/RunLog.lean`),
  `irRun_exists`/`runFrom_exists`/`RunDefinable` (`V2/IRRun.lean`), `sim_cfg` + the per-block
  bricks (`LowerConforms.lean`). Define **`DriveCorr`** — the boundary invariant relating a
  `driveLog` state (at a block-entry frame, stack `[]`) to an IR cursor `(L, st)`: `Corr` at
  `(L,0)` + the realised accumulators so far = the IR trace consumed so far. State the clean-halt
  hypothesis precisely (the `.halted` terminal of `driveLog`).
- **F1 Per-block drive step.** From `DriveCorr` at block `L`'s entry, `driveLog` reaches the next
  block boundary (successor entry, or a `.halted`) in finitely many fuel steps, AND the IR takes
  one `RunFrom`-block step (`RunStmts b.stmts` + terminator) — reusing `sim_stmts_block` +
  `sim_term_*` **in reverse** (we have the bytecode segment from `driveLog`; produce the matching
  IR step + re-establish `DriveCorr` at the successor). Read the per-cursor ties off the frames
  here (this is where `StmtTies`/`TermTies` get **discharged**, not supplied).
- **F2 The drive recursion.** Strong induction on the `driveLog` fuel / `totalGas` measure:
  glue the F1 block-steps into a full IR `RunFrom prog … L O` whose `O.world` = the clean-halt
  frame's world. The back-edge (JUMP to a visited block) is fine — the measure is bytecode fuel,
  which strictly descends regardless of CFG cycles. The CALL black-box consumes a sub-run of
  `driveLog` fuel (the child); handle via the existing `CallReturns`/`resumeAfterCall` boundary.
- **F3 Assemble `lower_conforms_cyclic`.** Replace `irRun_exists` (drop `CFGAcyclic`/`RunDefinable`)
  with the F2 construction; the ties are now discharged (drop `hstmtties`/`htermties` as supplied
  — they're produced by F1). New headline: `runWithLog` clean-halts ⇒ `∃ O, O.world =
  (observe self log.observable).world`, **general over cyclic CFG, no supplied ties** (only
  structural `WellFormedLowered` + the clean-halt hypothesis + def-graph `AcyclicWellFormed`).
- **F4 Concrete close + cruft.** Instantiate on a worked LOOPING program (and `workedCall`) end to
  end; retire the now-subsumed acyclic-specific lemmas if dead; docs + memory.

## Risk / open questions
1. **Reverse direction of the per-block bricks.** `sim_*` are stated IR→bytecode (given the IR
   step, produce `Runs`). F1 needs bytecode→IR (given the `driveLog` segment, produce the IR step
   + ties). The bytecode segment is deterministic (`drive` is a function), so the IR step is
   recoverable — but this may need the bricks restated as an iff / a `driveLog`-segment lemma, or
   a determinism bridge (`RunFrom.det` exists). Scope in F0/F1.
2. **Matching `driveLog`'s gas/call accumulators to `realisedGas`/`realisedCall`.** The ties read
   per-cursor values; confirm they equal the `log` projections at each boundary (adequacy lemmas
   `driveLog_drive`/`runWithLog_drive` already relate `driveLog` to `drive`).
3. **CALL sub-run fuel.** The child `driveLog` burns fuel; the parent boundary resumes via
   `resumeAfterCall`. Ensure the measure descends across the whole call.
4. **Clean-halt detection.** Pin the `.halted`-terminal hypothesis on `log` (vs OOG/stuck) and
   thread it as the F2 base case.
