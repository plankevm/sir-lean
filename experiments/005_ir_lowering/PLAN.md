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
- [ ] **C1** Define the IR: storage arithmetic + external calls + branching.
  Decide build-on-exp002 vs fresh. Write a design doc (`docs/ir-design.md`).
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
