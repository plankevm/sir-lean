# Spec Feedback Response - 2026-07-09

## Addressed

- Moved byte encoders out of spec lowering. `offsetBytesBE` and `wordBytesBE` now live in [Words.lean](../../LirLean/Util/Words.lean#L8), while [Lowering.lean](../../LirLean/Spec/Lowering.lean#L2) imports that utility and keeps `emitImm`/`emitDest` at the lowering surface.

- Made `emitStmt` easier to scan. The CALL and CREATE emissions in [Lowering.lean](../../LirLean/Spec/Lowering.lean#L116) are now split by stack phase and result handling, with only local comments for EVM stack order and whether the returned word is stored or popped.

- Restored semantic orientation comments where the stripped spec was hard to read. [EvalStmt](../../LirLean/Spec/Semantics.lean#L45) now explains stream consumption, [RunFrom](../../LirLean/Spec/Semantics.lean#L97) explains why leftovers are hidden, [RunFromLeft](../../LirLean/Spec/Semantics.lean#L142) explains why it exists, and [RunFromAll](../../LirLean/Spec/Semantics.lean#L187) states exact stream consumption.

- Stopped using `Trace` in spec-facing signatures. [Semantics.lean](../../LirLean/Spec/Semantics.lean#L19) keeps `GasOracle` as the public name and leaves `Trace` only as a compatibility alias; [WellFormed.lean](../../LirLean/Spec/WellFormed.lean#L20) now quantifies over `GasOracle`.

- Added local orientation for `StmtDefinableG`. [WellFormed.lean](../../LirLean/Spec/WellFormed.lean#L11) now says what statement readiness means for gas, calls, and creates.

- Checked the blank-space failure mode after edits. The adjacent-empty-line scan over `LirLean/Spec/*.lean` reported no consecutive blank lines.

## Deferred

- The `matExpr`/`matLoc`/`matFold` rfl simp lemmas remain in [Lowering.lean](../../LirLean/Spec/Lowering.lean#L87). They are named proof-interface lemmas used across decode/materialisation/lowering proofs, and moving them safely requires a coordinated import split rather than a spec-only cleanup.

- The long proof-only block in [WellFormed.lean](../../LirLean/Spec/WellFormed.lean#L105) was not moved in this pass. It exports `matCache_unfold`, `matCache_remat`, `matCache_slot`, and related fold facts consumed by the lowering and realisability cone. A safe split should introduce a proof-only module, move the fold lemmas there, and update downstream imports in one build-backed pass.

- A complete deletion of the `Trace` alias was deferred. Spec signatures now use `GasOracle`, but downstream proof files still refer to `Trace`; removing the alias would be a broad mechanical rename outside the requested safe pass.

- A theorem-boundary simplification of `EvalStmt`, `RunFrom`, `RunFromLeft`, or `RunFromAll` was deferred. Their current stream-threaded shapes are consumed by determinism, exact-consumption, and realisability statements, so this pass only made the existing boundary readable.

## WellFormed Review

The public `IRWellFormed` fields still have active consumers. `RunDefinableG` supplies run-position local availability, `DefsConsistent` ties def-sites to allocation, `CFGClosed` keeps jump targets present and in range, `DefEnvOrdered` gives the fold recursion order, and `slotAddr` bounds spill-slot addresses. The scalar budgets `codeFits` and `stackFits` remain outside `IRWellFormed` and are used to derive layout and stack-room obligations.

The more artificial-looking state-scoped cluster is real but less settled. `invalStep`, `DefsSoundS`, `StepScopedS`, and `RevalidatesPerBlock` are consumed by the WIP realisability machinery, so they were kept. They should be reviewed as a separate design pass because deleting them is not local to the spec file.

## Checks

- `cd experiments/005_ir_lowering && lake build LirLean`
- `cd experiments/005_ir_lowering && lake build WIP`
- `rg -n "\b(sorry|admit|axiom)\b" experiments/005_ir_lowering/LirLean/Spec experiments/005_ir_lowering/LirLean/Util/Words.lean`
- `rg -n "\bTrace\b" experiments/005_ir_lowering/LirLean/Spec`
- `rg -n "offsetBytesBE|wordBytesBE" experiments/005_ir_lowering/LirLean experiments/005_ir_lowering/LirLean.lean`
- Adjacent-empty-line scan over `experiments/005_ir_lowering/LirLean/Spec/*.lean`
