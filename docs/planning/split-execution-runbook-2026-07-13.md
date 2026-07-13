# Split execution runbook — Phase 0 → B → A (2026-07-13)

Executable runbook for an autonomous green-gated agent (box). Covers the clean split +
consolidate-under-EVM milestone. **Phase C (assembler) is OUT OF SCOPE for this run** — it is a
supervised follow-up. Design context: `split-and-assembler-plan-2026-07-13.md`,
`exp005-ir-vs-generic-classification.md` (the cut-lines), `consolidate-under-evm-plan-2026-07-13.md`.

## Non-negotiable discipline

1. **Green-gate every step.** A "step" is one coherent move (one file migrated, one file split,
   one rename). After each step run the FULL gate (below). If green → commit + push. If not green
   after reasonable effort → `git checkout -- .` / `git reset --hard` to the last good commit and
   move on; log the skip in the outcome doc. NEVER leave the tree broken.
2. **Never touch flagship STATEMENTS.** `Lir.lower_conforms`, `lower_conforms_exact`,
   `lower_conforms_gasfree` signatures are frozen. Proof bodies may move; statements may not change.
3. **Axiom-clean or revert.** Every gate includes the axiom check; all three flagships must remain
   exactly `[propext, Classical.choice, Quot.sound]`. Any `sorryAx` or extra axiom → revert the step.
4. **One commit per step**, message `split: <what>` (Phase 0/B) or `fold: <what>` (Phase A).
   `git push origin <branch>` after each commit so results are durable continuously.
5. **No proof shortcuts.** No `sorry`, no `admit`, no axiom-adding. Pure relocation/rename/split —
   proof bodies move intact. If a move needs real new proof work, it's out of scope: skip + log.

## The gate (run from repo root)

Pre-fold (Phases 0, B — packages still separate):
```bash
set -e
( cd experiments/003_bytecode_layer && lake build )
( cd experiments/005_ir_lowering && lake build && lake build WIP )
cat > /tmp/ax.lean <<'EOF'
import LirLean.Realisability.RealisabilitySpec
#print axioms Lir.lower_conforms
#print axioms Lir.lower_conforms_exact
#print axioms Lir.lower_conforms_gasfree
EOF
cp /tmp/ax.lean experiments/005_ir_lowering/AxAudit.lean
( cd experiments/005_ir_lowering && lake env lean AxAudit.lean )   # expect the 3 standard-trio lines
rm -f experiments/005_ir_lowering/AxAudit.lean
```
Post-fold (Phase A — exp003 gone, BytecodeLayer now a lib of the evm package):
```bash
( cd EVM && lake build Evm && lake build Conform && lake build BytecodeLayer )
( cd experiments/005_ir_lowering && lake build && lake build WIP && <axiom check as above> )
```
Green = all builds succeed AND the three `#print axioms` lines are exactly
`[propext, Classical.choice, Quot.sound]`.

## Branch

Work on `refactor/split-five-file-surface`, created off the current `refactor/fold-bytecode-layer`
tip (which already carries these plan docs). Push it to `origin`.

---

## Phase 0 — Scrub `Lir` from the exp003 engine

Six files under `experiments/003_bytecode_layer/BytecodeLayer/Hoare/` declare IR namespaces:
`AccountMap.lean` (`namespace Lir`), `Descent.lean`, `CleanHalt.lean`, `DriveMono.lean`,
`StepWalk.lean` (`namespace Lir` + many `open Lir (...)`), `MemAlgebra.lean` (`namespace
LirLean.MemAlgebra`). Their symbols (`AccPresent`, `accMono_of_accounts_eq`,
`accounts_find?_insert_mono`, `SelfAt`, mem-algebra lemmas) are EVM-generic.

Steps (green-gate each):
1. Rename `namespace Lir` → `namespace BytecodeLayer.Hoare.AccountMap` (or the owning module's
   `BytecodeLayer.Hoare.*`) in `AccountMap.lean`; update the `open Lir (...)` / `Lir.<sym>` sites in
   `StepWalk.lean`, `Descent.lean` and the ~15 exp005 files that reference these symbols.
2. Same for `Descent.lean`, `CleanHalt.lean`, `DriveMono.lean`, `StepWalk.lean`.
3. `MemAlgebra.lean`: `namespace LirLean.MemAlgebra` → `namespace BytecodeLayer.Hoare.MemAlgebra`;
   sweep references (see `MaterialiseRuns.lean`, `SimTerm.lean`).
4. Verify `grep -rn 'Lir\|LirLean' experiments/003_bytecode_layer --include='*.lean'` returns ZERO.

Pure namespace/reference rename — proof bodies untouched. Commit `split: scrub Lir from exp003 engine`.

---

## Phase B — Split the EVM-generic mass down into the five-file surface

Build the surface INSIDE `experiments/003_bytecode_layer/BytecodeLayer/`:
`Exec.lean`, `Exec/Recorder.lean`, `Exec/Invariants.lean`, `Exec/CyclicSim.lean`. (Asm.lean is
Phase C — not this run.) Cluster → file mapping and per-file cut-lines are in
`exp005-ir-vs-generic-classification.md` (§"clusters" and §"MIXED modules").

### B0 — Precursor: hoist shared aliases (do FIRST)
`Observable`, `CallStream`, `CreateStream`, `GasOracle`/`Trace`, `World := Word → Word` are defined
in `LirLean/Spec/Semantics.lean` but are structurally EVM-generic. Move them into a new
`BytecodeLayer/Exec/Observable.lean` (or `Exec.lean`), re-export/alias from exp005 so existing
`Lir.*` references still resolve. Gate. Commit `split: hoist observable/stream aliases to exp003`.
Nothing else migrates cleanly until this lands.

### B1 — Whole-file clean migrations (13 files, do before B2)
Each: move the file from `experiments/005_ir_lowering/LirLean/...` to the right
`experiments/003_bytecode_layer/BytecodeLayer/...` surface location, move its IR-free support defs
with it, fix imports on both sides, re-export if exp005 still needs the names. One commit per file.
Files (target file in parens):
- `Frame/StorageErase` (Invariants or Exec) — pure storage-map, calibration C
- `Frame/Call`, `Frame/Create` (Exec) — CALL/CREATE effect oracles
- `Drive/CallPreservesSelf` (Invariants) — self-presence invariant
- `RecorderLemmas` (Recorder), `CallRealises` (Exec/Recorder)
- `Realisability/CheckedStep`, `Realisability/SegmentedEval` (Recorder) — checked-twin evaluators
- `Materialise/MatDecLower` (Exec/Asm-adjacent; put in Exec for now), `Materialise/CleanHaltExtract` (Exec)
- `Spec/Seams` (Invariants), `Words` (Exec or a small util in evm), `Spec/Recorder` (Recorder; dominantly generic)

### B2 — Mixed-file splits (14 files) — real surgery, do in order, skip-and-log if a split won't close
For each, extract the generic part to the surface file, leave the thin IR adapter in exp005. Cut-lines
(from the classification doc):
- `Realisability/Machinery` → generic `RecorderCoupled`+boundary engine (Recorder) | IR adapter
  (`matRunsC`/`termTies'`/`callRealises`) stays. **Highest value — do first.**
- `Materialise/MaterialiseRuns` → `StashRuns`/`mload_covered`/mem-expansion + `MemRealises`/
  `StorageAgree` (Exec) | `evalExpr_obs_irrel` stays
- `Materialise/StashTail` → `mstoreFrame_*`/`stash_tail_runs` (Exec) | `stash_tail_sload` stays
- `Materialise/MaterialiseGas` → `subCharges_*`/`charge_binOpPost_gas` (Exec) | `chargeExpr` fold stays
- `Drive/SelfPresent` → `SelfPresent`+gas/sload alignment+presence (Invariants) | `sloadRealises_charge_of_witness` stays
- `Frame/Match` → `sim_*`/`*_reflects_lowered`/`sstoreFrame_*` (Exec) | `lower_preserves_*` stays
- `Sim/SimTerm` → `result*_endFrame_success` (Exec) | `sim_term_*`/`pcOf_*` stays
- `Realisability/WitnessParams` → `callsCodeOk`/`entryCallsCodeOk`/precompile stubs/`RunLog.cleanb`
  (Recorder/Invariants) | `ex*` witness stays
- `Decode/*` (Modellable, DecodeLower, BoundaryReach, JumpValid, SegAligned, BoundaryCursor):
  **DEFER the geometry cut to Phase C (assembler)** — do NOT split Decode/ in this run beyond moving
  `Decode/Modellable`'s already-generic `Frame`/`Step` theory (its `ModellableStep` payload) to
  Invariants, leaving the `AtReachableBoundary = lower prog` tether behind. The rest of `Decode/` is
  the assembler's re-indexing job and stays put for now.

If any B2 split cannot be made green without new proof work, revert it and log "B2 <file>: deferred
to Phase C (needs re-indexing)" — do not force it.

---

## Phase A — Fold exp003 (with the surface) into EVM

Only after B is as complete as it will get and green.
1. Move `experiments/003_bytecode_layer/BytecodeLayer/` → `EVM/BytecodeLayer/`.
2. `EVM/lakefile.lean`: add `lean_lib «BytecodeLayer» where globs := #[.andSubmodules \`BytecodeLayer]`.
3. Delete `experiments/003_bytecode_layer/{lakefile.lean,lake-manifest.json,lean-toolchain}`; leave a
   stub `README.md` pointing to `EVM/BytecodeLayer/`.
4. `experiments/005_ir_lowering/lakefile.lean`: `require bytecode_layer from "../003_bytecode_layer"`
   → `require evm from "../../EVM"`. Refresh exp005 `lake-manifest.json`.
5. Post-fold gate (above). Commit `fold: dissolve exp003 into EVM/BytecodeLayer`. Push.

---

## Finish

Write `docs/review/split-outcome-2026-07-13.md`: what landed per phase, the B2 deferrals, final gate
output (both cones + the 3 axiom lines verbatim), and the file/namespace structure after. Confirm the
branch is pushed. Stop — do not start Phase C.
