# Exec report — Track B, Phase 2 gas-law removal (`exec/phase2-gaslaw`)

Executed 2026-07-02 per `docs/execution-plan-2026-07-02.md` (Track B) and
`docs/gas-decision.md`. Baseline HEAD `6980831`, 1164 jobs; result 1161 jobs, green,
zero sorry, headlines axiom-clean.

## What was deleted

**Files** (`git rm`):

- `LirLean/V2/Mono.lean` (70 decls) — the two-read gas-monotonicity milestone: the guard
  bytecode/frames (`guard_*`, `gf*`, `q0..q6`), `gReads_*`, `toNat_ofUInt64`,
  `LoweredRunHasObsMono`, `lower_preserves_obs_mono`.
- `LirLean/V2/Oracle.lean` (9 decls) — the law-first gas-oracle interface:
  `GasRealises`, `GasRealises.monotoneGas`, `toNat_gasReadOf`, the guard theorems —
  **except** `gasReadOf` and `FramesRun`, which are live (see Relocation).
- `LirLean/V2/HonestGasTie.lean` (8 decls) — the retired-universal regression witnesses:
  `gasRealises_universal_unsatisfiable`, `sloadRealises_universal_unsatisfiable`,
  `new_sloadLogAligned_two_read_satisfiable`, `sload_tie_vacuity_resolved`,
  `spilled_gas_value_tie_realisable`, and the gas analogues. These are **lost from the
  build cone** (plan FLAG 4, brief-sanctioned); they survive in git history and in the
  Lesson paragraph of `docs/gas-decision.md`. None appeared in Track A's audit-guard
  list; no surviving `.lean` code referenced them.

**Sections**:

- `LirLean/V2/RunLog.lean` — the whole gas-monotonicity section (pre-edit lines
  379–609): `geToNat`, `bound_mono`, `driveLog_gas_inv`, `realisedGas_monotone`, plus
  `#print axioms realisedGas_monotone` and the module-docstring / guard-comment prose
  about the law. `import LirLean.V2.Oracle` (the one dead import) dropped.
- `LirLean/V2/Law.lean` — narrowed to determinism: deleted §1–§2
  (`Trace.gasMonotone`, `MonotoneGas`, `gasMonotone_pair`, `lt_eq_zero_of_toNat_le`);
  kept the four `.det` (`EvalStmt.det`, `RunStmts.det`, `RunFrom.det`, `IRRun.det`);
  docstring rewritten with a pointer to `docs/gas-decision.md`.
- `LirLean.lean` (root) — dropped the Mono/Oracle/HonestGasTie imports + comment pairs;
  updated the Law and CallRealises comments.

## The relocation (plan FLAG 1)

`Lir.V2.gasReadOf` and `Lir.V2.FramesRun` are consumed **in code** by
`V2/TieDischarge.lean` (`gasRecord_eq_gasReadOf`, `gasReadOf_gasFrame_eq_obs`,
`GasLogAligned`, `SloadLogAligned`, `FramesRun.snoc`/`.snoc_seed`), which is untouchable
this wave. They were relocated byte-identically (same fully-qualified names) into
`LirLean/V2/RunLog.lean` — the unique Track-B-owned file inside TieDischarge's import
cone — under a `-- RELOCATED from V2/Oracle.lean (Phase 2)` note.

## Kept import (plan FLAG 2)

`import BytecodeLayer.Hoare.GasMonotone` in RunLog.lean is **live**, not dead:
`DriveSim.lean:201` uses `Runs.gasAvailable_le` in code, and with Mono/Oracle gone this
import is the only path bringing that module into DriveSim's cone. A NOTE comment marks
it in RunLog.lean.

## DEVIATION from the plan: root gains `import LirLean.V2.TieDischarge`

The plan's Step 3 deleted the HonestGasTie import block without replacement. But
`HonestGasTie.lean:1` (`import LirLean.V2.TieDischarge`) was the **only** path from the
`LirLean` root to TieDischarge — the file holding the headlines
(`lower_conforms_cyclic_tiefree`/`_assembled`, `callPreservesSelf_modGuards`). The first
post-deletion build succeeded at 1160 jobs with those constants **absent from the
default target** (caught by the Step-6 scratch axiom check: unknown constants).
Fix: one direct `import LirLean.V2.TieDischarge` in the root (commented), restoring the
cone. Result: 1161 jobs, all 10 baseline decls present and clean.

## Verification evidence

- `lake build`: `Build completed successfully (1161 jobs).` (baseline 1164; −3 modules)
- Zero `sorry` in the edited files; no sorry warnings in the build log.
- Scratch axiom check (`lake env lean` on a `/tmp` file, `import LirLean` + 10
  `#print axioms`) — output matches the pre-deletion baseline verbatim:

```
'Lir.V2.lower_conforms_cyclic_assembled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.lower_conforms_cyclic_tiefree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.callPreservesSelf_modGuards' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.driveLog_drive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.runWithLog_drive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.runWithLog_messageCall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.observe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.gasReadOf_gasFrame_eq_obs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.V2.FramesRun.snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Residual-reference grep over the deleted decl names: comment-only hits
  (CallRealises.lean:9/32/88 — Wave-4 list below — and Law.lean's own deletion-record
  docstring).
- Untouched per constraints: `V2/TieDischarge.lean`, the `DriveCorrPlus` accumulator
  params, `realisedGas`/`realisedCall`/`callOracleOf`/`observe`/`runWithLog` (all intact
  in RunLog.lean).

## Wave-4 stale-comment worklist (unowned files, NOT edited this wave)

Prose references to deleted decls that survive:

- `V2/TieDischarge.lean:7, 57–68, 137–144, 204–210` — `Oracle.GasRealises` /
  `V2/Oracle.lean` mentions (file untouchable this wave).
- `V2/CallRealises.lean:9, 32, 88` — `GasRealises.monotoneGas`.
- `MaterialiseRuns.lean:552` — "…`Lir.V2.GasRealises` (`V2/Oracle.lean`)…".
- `MaterialiseRuns.lean:530` — mentions `V2/HonestGasTie.lean` +
  `sloadRealises_universal_unsatisfiable` (now deleted).
- `SimStmt.lean:133` — `GasRealises` (Phase-B retirement prose).
- `DefsSound.lean:125` — `guardIR` (Mono decl) prose.
- `LowerDecode.lean:1064`, `StashTail.lean:311` — mention `gasReadOf` /
  `gasReadOf_gasFrame_eq_obs`; those decls still exist (RunLog / TieDischarge), pointer
  prose only — fine.
- `MaterialiseRuns.lean:510` + `SimStmt.lean:883` reference the *kept* `Lir.GasRealises`
  (`MaterialiseRuns.lean:553`) — fine.
- Docs mentioning the deleted witnesses (`headline-transitive-chain.md`, memory notes)
  are the lead's Wave-4 doc-sync concern.
