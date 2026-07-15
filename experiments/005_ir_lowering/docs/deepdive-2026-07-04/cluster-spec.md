# Deep-dive: the `Spec/` cluster (2026-07-04)

Scope: the six reviewer-facing DEFINITION modules under `LirLean/Spec/`. Read-only
audit; every claim cites `file:line`. Classification default is "incremental-toward-X",
never "dead", unless a replacement is named with evidence.

The cluster is NOT a tight altitude band. `IR`/`Semantics`/`Lowering` are L0 base
(import only `Evm` + `Spec/IR`); `Recorder` and `Seams` sit HIGH in the DAG (they
import Drive/Engine machinery) but live in `Spec/` because they are reviewer-facing
surface. `Conformance` is a deliberate tombstone stub.

---

## 1. Per-file sections

### `LirLean/Spec/IR.lean`
Purpose: the datatypes-only high-level IR (C1 deliverable, `docs/ir-design.md` §1–2).
Values are `Evm.UInt256` so IR and bytecode share the word type. Register machine over
named locals, CFG of basic blocks. **Zero CREATE node** (confirmed: `Stmt` = assign /
sstore / call only, :77–86) — CREATE is prepared scaffolding elsewhere (`Create.lean`),
not in the IR surface.

| decl | kind | role | callers |
|---|---|---|---|
| `Word` (:25) | abbrev | shared-infra (the single IR value type = `UInt256`) | 525 refs repo-wide |
| `Tmp` (:28) | structure | shared-infra (register name) | 316 refs |
| `Label` (:33) | structure | shared-infra (block index) | 202 refs |
| `CallSpec` (:43) | structure | shared-infra (CALL payload: callee/gasFwd/resultTmp) | 14 refs (Stmt.call, EvalStmt.call, emitStmt.call) |
| `Expr` (:54) | inductive | shared-infra (imm/tmp/add/lt/sload/gas/**slot**) | 211 refs |
| `Stmt` (:77) | inductive | shared-infra (assign/sstore/call) | 93 refs |
| `Term` (:89) | inductive | shared-infra (ret/stop/jump/branch) | 30 refs |
| `Block` (:103) | structure | shared-infra | 196 refs |
| `Program` (:109) | structure | shared-infra (blocks + entry) | 230 refs |

Note `Expr.slot` (:73): the generic spill-load marker; `Lir.evalExpr (.slot _) = none`
(Semantics :130). Today produced by `defsOf`/`allocate` only for the three spilled
channels (gas/sload/call-result); it is the uniform-spill mechanism's IR half. Not
dead — load-bearing for the value channel.

### `LirLean/Spec/Semantics.lean`
Purpose: the **v2 gas-free observable IR machine** (`docs/ir-design-v2.md` §3–4,
`ir-design-v3.md` §7–8). `IRState = {locals, world}`, no gas/pc. Big-step relation
threading two head-consumed streams — the gas `Trace` and the `CallStream`. This is the
IR side of the whole conformance statement (`RunFrom` is the flagship's conclusion
relation).

| decl | kind | role | callers |
|---|---|---|---|
| `World` (:44) | abbrev | shared-infra (`Word → Word` storage lens) | 2 explicit `Lir.World` refs; used pervasively via `IRState.world`/`Observable.world` |
| `IRState` (:48) | structure | shared-infra (the machine state) | 87 refs |
| `HaltResult` (:55) | inductive | shared-infra (stopped/returned) | 8 refs (Observable, observe) |
| `GasOracle` (:73) | abbrev | shared-infra (`List Word` gas stream) | 3 explicit + via `Trace` alias |
| `Trace` (:78) | abbrev | shared-infra (working alias of `GasOracle`) | 53 refs (all `T : Trace` signatures) |
| `CallStream` (:99) | abbrev | shared-infra (`List (World×Word)`, foundation call-stream, 1c77c07) | 67 refs |
| `IRState.setLocal` (:104) | def | shared-infra | 17 refs |
| `IRState.setStorage` (:108) | def | shared-infra | 6 refs |
| `evalExpr` (:123) | def | shared-infra (gas-free expr eval; `.slot`→none, `.gas`→obs) | 151 refs |
| `blockAt` (:139) | def | shared-infra (v2-local block accessor) | used internally by `RunFrom` (:233,241,247,257,266) and `RealisabilitySpec` `ClosedCFG`/`RunFromAll`; v2 twin of `Program.blockAt` (SmallStep :123) kept local so Semantics depends only on IR |
| `EvalStmt` (:164) | inductive | shared-infra (one-stmt step; call pops `CallStream` head) | 74 refs |
| `RunStmts` (:198) | inductive | shared-infra (stmt-list closure) | 72 refs |
| `Observable` (:210) | structure | shared-infra (final world + halt) | 29 refs |
| `RunFrom` (:228) | inductive | terminal-for-flagship (the CFG driver; flagship conclusion is `∃ O, RunFrom … ∧ Conforms`) | 137 refs |
| `IRRun` (:275) | def | incremental-toward top-level IR run (`ir-design-v2.md` §4 entry wrapper) | 6 refs |

### `LirLean/Spec/Lowering.lean`
Purpose: `lower : Program → ByteArray` = `encode ∘ emit (allocate prog)`
(`docs/ir-design.md` §4, `uniform-spill-alloc-plan.md`). Executable byte emission only;
no semantics theorem here (that is C3). Factored into **policy** (`allocate`/`Loc`/`Alloc`),
**mechanism** (`emit`/`materialise*`/`emitStmt`/`emitTerm`/`offsetTable`), **backend**
(`encode`). **emitStmt emits opcodes for assign/sstore/call only — no CREATE opcode ever**
(:178–200), confirming the structural CREATE exclusion.

| decl | kind | role | callers |
|---|---|---|---|
| `Byte.{stop..ret}` (:46–61, 16 defs) | def | shared-infra (opcode byte table) | all 16 used 7–43× each (verified) |
| `offsetBytesBE` (:67) | def | shared-infra (BE 4-byte dest encode) | 34 refs |
| `wordBytesBE` (:72) | def | shared-infra (BE 32-byte PUSH32) | 30 refs |
| `Loc` (:92) | inductive | incremental-toward Phase-B/C/D alloc (`SoundAlloc` floor) | 1 ref: `LoweringLemmas.lean:84` (`toDef_locOfExpr`) |
| `Alloc` (:101) | abbrev | incremental-toward `∀ SoundAlloc` headline (Phase D, not landed) | `emit` (:311), `allocate` (:275), `LoweringLemmas:89/93` |
| `Loc.toDef` (:105) | def | incremental (policy→defs bridge) | `Alloc.toDefs`; `LoweringLemmas:84` |
| `Alloc.toDefs` (:111) | def | shared-infra (`emit` consumes alloc through this) | `emit` (:312), `LoweringLemmas:89/93` |
| `emitImm` (:128) | def | shared-infra | 185 refs |
| `slotOf` (:132) | def | shared-infra (spill slot = t.id*32) | 149 refs |
| `emitDest` (:135) | def | shared-infra | 57 refs |
| `materialiseExpr` (:140) | def | shared-infra (recompute-on-use push seq) | 294 refs |
| `materialise` (:157) | def | shared-infra | 171 refs |
| `recomputeFuel` (:162) | def | shared-infra | 441 refs |
| `emitStmt` (:178) | def | shared-infra (per-stmt bytes; slot-stash def-site) | 172 refs |
| `emitTerm` (:214) | def | shared-infra (ret stashes to mem[0], RETURN(0,32)) | 108 refs |
| `defsOf` (:247) | def | shared-infra (program-global def env; routes gas/sload/call-result to `Expr.slot`) | 617 refs |
| `locOfExpr` (:269) | def | incremental (Phase-A policy classifier) | 4 refs (`allocate`, `LoweringLemmas:84/85/96`) |
| `allocate` (:275) | def | shared-infra (Phase-A default policy) | 29 refs |
| `emitBlockBody` (:284) | def | shared-infra | 69 refs |
| `blockLen` (:290) | def | shared-infra | 18 refs |
| `offsetTable` (:295) | def | shared-infra (two-pass offset table) | 233 refs |
| `emit` (:311) | def | shared-infra (alloc-driven byte assembly mechanism) | `lower` (:323), `DecodeLower:52/55` |
| `encode` (:318) | def | shared-infra (ByteArray backend) | `lower` (:323), `DecodeLower:59/62` |
| `lower` (:323) | def | terminal-for-flagship (`lower prog` is the flagship's subject) | 279 refs |

The `Loc`/`Alloc`/`Loc.toDef`/`locOfExpr` policy layer bottoms out at ONE keystone,
`LoweringLemmas.allocate_toDefs` (via `toDef_locOfExpr`), which proves
`(allocate prog).toDefs = defsOf prog` — the Phase-A "no behaviour change" bridge feeding
`emit_allocate_eq_flatBytes` → `lower_eq_flatBytes` (`DecodeLower:52–62`). This is
low-usage but load-bearing: it is exactly the seam that lets Phase D swap in a
`∀ SoundAlloc` without touching the byte layer. Not dead; incremental toward Phase D.

### `LirLean/Spec/Recorder.lean`
Purpose: the **instrumented recording interpreter** `runWithLog` (`ir-design-v3.md` §8,
regime (i)). A `Type`-valued parallel copy of `drive` (`driveLog`) so the realised
oracles are honest FUNCTIONS (`Prop` cannot eliminate into `Type`). Records top-level GAS
reads, SLOAD warmth-charges, and returning external CALLs; projects to
`realisedGas`/`realisedSload`/`realisedCall`; `observe` bridges bytecode `FrameResult` →
IR `Observable`. Imports `CallRealises` + `Hoare.GasMonotone` (the latter is a LIVE
import for `Runs.gasAvailable_le` in DriveSim — see the file's own note :2–5), so it sits
HIGH in the DAG despite being in `Spec/`.

| decl | kind | role | callers |
|---|---|---|---|
| `gasReadOf` (:65) | def | shared-infra (gas-read↔frame bridge) | 27 refs (SelfPresent tie-discharge) |
| `FramesRun` (:70) | def | shared-infra (Runs-chain over gas frames) | 28 refs |
| `CallRecord` (:85) | structure | shared-infra (per-CALL recorded datum) | 32 refs |
| `RunLog` (:100) | structure | shared-infra (the introspection log; flagship arg) | 39 refs |
| `RunAcc` (:113) | def | **genuinely-superseded** (see candidates §3) | 0 refs (docstring only :154) |
| `isGasOp` (:122) | def | shared-infra (GAS-step gate) | 11 refs |
| `isSloadOp` (:135) | def | shared-infra (SLOAD-step gate) | 9 refs |
| `sloadWarmthOf` (:144) | def | shared-infra (recorded sloadCost warm) | 25 refs |
| `recordCall` (:172) | def | shared-infra (delivery-branch record append) | 16 refs |
| `driveLog` (:186) | def | terminal-for-flagship (the recording driver) | 86 refs |
| `runWithLog` (:262) | def | terminal-for-flagship (top-level recorder) | 65 refs |
| `realisedGas` (:279) | def | terminal-for-flagship (flagship's `T := realisedGas log`) | 20 refs |
| `realisedSload` (:285) | def | incremental-toward sload-tie (per-cursor alignment deferred, parallel to GAS) | 1 ref (`SelfPresent:233` docstring) |
| `callStreamOf` (:292) | def | shared-infra (CallRecord list → CallStream) | 9 refs |
| `realisedCall` (:300) | def | terminal-for-flagship (flagship's `C := realisedCall log self`) | 33 refs |
| `resultStorageAt` (:330) | def | shared-infra (FrameResult storage lens) | 13 refs |
| `observe` (:340) | def | terminal-for-flagship (bytecode→IR observable; used by `Conforms`) | 69 refs |
| `observe_result` (:347) | theorem | shared-infra (observe.result unfold, `rfl`) | 2 refs |

### `LirLean/Spec/Seams.lean`
Purpose: the tracked-debt **seam register** (`docs/headline-transitive-chain.md` §3).
Definitional forwarders (`:=`) of the real seam decls, re-exported under `Lir.Spec` so the
debt is named/typed/drift-proof. Asserts nothing new. Imported ONLY by `Audit.lean`.

| decl | kind | role | callers |
|---|---|---|---|
| `SelfPresent` (:38) | def | terminal-for-audit (forwarder of `Lir.SelfPresent`) | register entry; no non-Seam ref |
| `CallPreservesSelf` (:47) | def | terminal-for-audit (forwarder of `Lir.CallPreservesSelf`) | used in `callPreservesSelf_of_precompiles` type |
| `PrecompilesPreservePresence` (:59) | def | terminal-for-audit (the `hprec` seam shape) | used in `callPreservesSelf_of_precompiles` type |
| `callPreservesSelf_of_precompiles` (:68) | theorem | terminal-for-audit (drift-proof binding; axiom-checked) | `Audit.lean:60/62` (`#print axioms`) |
| `CallsCode` (:81) | def | terminal-for-audit (forwarder of `Interpreter.CallsCode`) | register entry; no non-Seam ref |
| `CleanHaltsNonException` (:93) | def | terminal-for-audit (forwarder of `Lir.CleanHaltsNonException`) | register entry; no non-Seam ref |

`SelfPresent`/`CallsCode`/`CleanHaltsNonException` have no in-code consumers outside the
file, but they are the deliberate reviewer-surface register (the four irreducible seams);
their VALUE is being named/typed/drift-proof. Not dead — this is exactly the "seam
register" role. `callPreservesSelf_of_precompiles` is the sole one with a live consumer
(the Audit axiom check) and it forces `PrecompilesPreservePresence`/`CallPreservesSelf` to
stay definitionally aligned with the real hypothesis.

### `LirLean/Spec/Conformance.lean`
Purpose: **deliberate tombstone stub** (no decls). The old vacuous cyclic-headline surface
(`lower_conforms_cyclic_assembled`, `RealisabilityObligations`) was DELETED 2026-07-03
because the supplied `StmtTies`/`TermTies` were unsatisfiable. Kept in the build cone via
`LirLean.lean:50` so the canonical conformance path resolves to this honest notice rather
than a missing module. NOT dead — deliberate per grounding + `final-audit-2026-07-03.md`.

---

## 2. Internal sub-DAG + entry/exit edges

Intra-cluster import edges (only these exist between Spec files):
```
Spec/IR  ──imported-by──►  Spec/Semantics   (Semantics imports IR)
Spec/IR  ──imported-by──►  Spec/Lowering    (Lowering imports IR)
```
`Recorder`, `Seams`, `Conformance` do NOT import any other `Spec/` file directly; they
reach `Semantics`'s types (`CallStream`/`Observable`/`GasOracle`) only transitively.

Altitude (three tiers, not one cluster):
- L0 base: `IR` → `Semantics`, `Lowering` (Evm-only + IR).
- High-DAG surface: `Recorder` (imports `CallRealises`, `Hoare.GasMonotone`),
  `Seams` (imports `Drive/CallPreservesSelf`, `Decode/Modellable`, `BytecodeLayer/Hoare/CleanHalt`).
- Tombstone: `Conformance` (imports nothing).

Entry edges (who imports each, from outside `Spec/`):
| module | direct importers |
|---|---|
| `Spec.IR` | `SmallStep`, `Call`, `Create`; root `LirLean.lean:9` |
| `Spec.Semantics` | `Lir.Law`, `DefsSound`; root :10 |
| `Spec.Lowering` | `LoweringLemmas` |
| `Spec.Recorder` | `RecorderLemmas` |
| `Spec.Seams` | `Audit`; root :49 |
| `Spec.Conformance` | none (kept live via root :50) |

Exit edges (what the cluster reaches into other clusters):
- `Recorder` → `Frame/Call`, `Frame/Create`, and exp003
  `Frame`/`drive`/`CallResult`/`stepFrame`/`beginCall`/`beginCreate`.
- `Seams` → `Lir.SelfPresent`, `Lir.CallPreservesSelf`, `Lir.callPreservesSelf_modGuards`,
  `Lir.AccPresent`, `Interpreter.CallsCode`, `Lir.CleanHaltsNonException`.
- `IR`/`Semantics`/`Lowering` → `Evm` only.

Terminal consumption by the flagship (`RealisabilitySpec.lean`, WIP lib):
`RunFrom`, `lower`, `observe`, `realisedGas`, `realisedCall`, `runWithLog`, `driveLog`,
`RunLog` all feed `Conforms` (:155) and `lower_conforms` (:3705). `Conforms` compares BOTH
`observe`'s world AND result (foundation full-observable change 4628201).

---

## 3. SIMPLIFICATION CANDIDATES (defensible only)

1. **`Recorder.RunAcc` (:113) — genuinely superseded / unused type alias.**
   `def RunAcc : Type := List Word × List Nat × List CallRecord`. Repo-wide grep finds
   ZERO uses as a type: `driveLog` (:186) threads three SEPARATE args (`gasAcc`,
   `sloadAcc`, `callAcc`) and returns the spelled-out tuple `FrameResult × List Word ×
   List Nat × List CallRecord`; `runWithLog` (:262) destructures the same spelled-out
   tuple. The only reference is a stale docstring (:154 "a `RunAcc = (gas, calls)`
   accumulator") that is itself out of date (it says 2-tuple; the real accumulator is a
   3-tuple). Evidence for "superseded": the accumulator was refactored from a bundled type
   to three positional args, and `RunAcc` was left behind. Low-risk removal, but
   **needs confirmation** it is not reserved for a planned bundling refactor.

2. **Docstring drift in `recordCall`/`driveLog`/`RunAcc` comments** (not code): several
   comments still say "`(gas, calls)`" 2-tuple (Recorder :154, :157) after the SLOAD warmth
   channel was added (the former RunLog had a dedicated SLOAD warmth field). Documentation-only; flag
   for a sweep, not a deletion.

No other deletion is defensible. In particular the low-usage `Loc`/`Alloc`/`Loc.toDef`/
`locOfExpr` policy layer and `realisedSload`/`isSloadOp`/`sloadWarmthOf` sload channel are
INCREMENTAL toward landed goals (Phase-D `∀ SoundAlloc`; the deferred sload per-cursor
tie), not dead — each has a live keystone consumer (`allocate_toDefs`; the SelfPresent
sload adequacy) even where import-graph reach is thin. `Seams` forwarders with no code
consumer are the intended reviewer register. `Conformance` is a deliberate tombstone.
