# Track C — local plan (High-level IR → EVM bytecode, lowering preserved)

Worktree: `../evm-semantics-wt/ir-lowering` · Branch: `exp005-ir` · Base: `exp003-fuel-layer-cleanup`
Master index: repo-root `currentplan.md`.

## Goal
Define an *interesting* high-level IR, lower it to EVM bytecode, and prove the
lowering preserves semantics — reusing exp003's reasoning layer (`Runs` + boundary
bridges). The IR's job is to exercise the three primitives we actually need:
**storage arithmetic, external calls, and branching**. Branching is what makes
**gas introspection** reasoning meaningful (a `GAS`-dependent branch).

## Starting material
- exp002 `experiments/002_ssa_cfg/SirLean/` — an existing SSA/CFG IR
  (`IR.lean`, `SmallStep.lean`, `Eval.lean`, `Spec.lean`, `Proof.lean`, `SCCP.lean`,
  `State.lean`). Reuse/extend it, but ENSURE branches and external calls are
  first-class (the previous IR may lack one or both).
- exp003 `experiments/003_bytecode_layer/` — the bytecode reasoning layer and its
  `Runs`/`messageCall_runs` API. Track C is its first real consumer.

## Milestones
- [x] **C1** Define the IR: storage arithmetic + external calls + branching.
  Decide build-on-exp002 vs fresh. Write a design doc (`docs/ir-design.md`).
  → DONE: fresh `LirLean` IR + design doc + compiling skeleton (no `sorry`).
- [ ] **C2** Lowering IR → EVM bytecode (decode-compatible with exp003).
- [ ] **C3** Prove lowering preserves semantics via exp003's `Runs` machinery.
- [ ] **C4** Acceptance check: does exp003 sequencing suffice for **multi-call** IR
  programs? If NOT, write the precise requirement here and flag Track A
  (`exp003-runs-call`) — this is the A↔C feedback edge.

## Agent brief (durable — re-spawn from this verbatim)
> Work ONLY in `/Users/eduardo/workspace/evm-semantics-wt/ir-lowering`, branch
> `exp005-ir`, dir `experiments/005_ir_lowering`. Do **Milestone C1 only** this run
> (design + skeleton, no heavy proofs yet), then stop and report. First STUDY
> exp002's `SirLean/` and exp003's `Runs`/boundary-bridge API; decide extend-vs-fresh
> with reasons. Produce `docs/ir-design.md` (IR grammar: storage read/write +
> arithmetic, CALL, conditional branch; small-step or denotational semantics choice;
> how it lowers to exp003-decodable bytecode; how gas introspection appears) and a
> compiling Lean skeleton (`lakefile.lean` requiring what it needs; IR datatype +
> stubbed lowering signature — types only, no `sorry`-backed theorems). Append dated
> progress to this PLAN.md; commit on this branch; do not touch other tracks.
> Report the design decision + skeleton build status.

## Progress log
- 2026-06-22: Track seeded. Awaiting C1 agent.
- 2026-06-22 (C1): Studied exp002 `SirLean/` and exp003's `Runs`/boundary-bridge
  API. **Decision: fresh IR (`LirLean/`), not an extension of `SirLean`.** Reasons
  (full version in `docs/ir-design.md` §1): `SirLean.Word = UInt32` vs EVM
  `UInt256`; `SirLean.World = Word → Word` is disconnected from the EVM
  account/storage model the preservation proof must target; `SirLean` has **no
  external CALL** and **no gas/gas-introspection**; its SSA/dominance/`refs_valid`
  + `SCCP` scaffolding (>80 KB) is dead weight for lowering. We keep only exp002's
  *structural idea* (a CFG of basic blocks with branch terminators).
- 2026-06-22 (C1): Wrote `docs/ir-design.md` — IR grammar (Tmp/Label/Expr/Stmt/
  Term/Block/Program with first-class `sload`/`sstore`/`add`/`lt`, `Stmt.call`,
  `Term.branch`, and `Expr.gas` introspection); small-step + gas-aware semantics
  choice (rationale: mirror exp003's `Runs` for a simulation proof); two-pass
  lowering to `Evm.decode`-compatible bytecode (per-block `JUMPDEST`, fixed-width
  `PUSH4` destinations → prefix-sum offset table); call→`Runs`/`CallReturns`
  mapping; preservation statement *shape* (per-step `Match` simulation +
  top-level `messageCall_runs`/`_call_runs` discharge).
- 2026-06-22 (C1): **⚠ C4 surfaced early (flag for Track A).** Reading
  `Hoare/CallSequence.lean`: `messageCall_call_runs` is hard-wired to exactly ONE
  `CallReturns` between a prefix and suffix `Runs`. A `Runs` link is one
  *non-halting* `stepFrame` (`Signal.next`); a CALL is `Signal.needsCall`, so it is
  NOT a `StepsTo` link and cannot be glued in by `Runs.trans`. Therefore a
  ≥2-call IR program (`prefix → call → middle → call → suffix → halt`) is
  inexpressible with the current bridge. Track C's multi-call lowering (C3/C4) is
  blocked on Track A's planned `Runs.call` constructor (A1–A3). Single-call
  lowering can proceed against the current API now. (Detail in `ir-design.md` §5.)
- 2026-06-22 (C1): Wrote the compiling Lean skeleton — `lakefile.lean` (requires
  exp003's `bytecode_layer`, transitively `evm`/Mathlib), `lean-toolchain`
  (v4.30.0, matching exp003), `LirLean/IR.lean` (the IR datatypes),
  `LirLean/Lowering.lean` (`lower : Program → ByteArray` with a concrete,
  `sorry`-free two-pass body — correctness deferred to C2). No theorems stated, so
  nothing is `sorry`/`axiom`-backed. `lake build` status recorded on commit.
