# LirLean file/module restructuring plan

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Date: 2026-07-04. Read-only design synthesis (no `.lean` touched). Reconciles
`docs/lirlean-reorg-plan.md` with the 2026-07-04 deep dives, **correcting the reorg-plan
where the deep dives show it assumed decls/files that turned out shared or live**.

Scope of truth: the tree has **51 `*.lean` files** today (not 44 — the reorg-plan's "26
top-level" predates `StorageErase.lean` and does not count `Spec/Engine/Lir.Drive`). Layout:
27 top-level + `Spec/` (6) + `Engine/` (8) + `` (7, incl. `RealisabilitySpec`) + `Drive/`
(3). The default `LirLean` lib is sorry-free; the one-file `WIP` lib
(`lakefile.lean:31-32`, rooted at `LirLean.RealisabilitySpec`) is the sole sorry-carrier.

> **P8 status note (2026-07-08).** This plan predates the P8 well-formedness reshaping. Any
> statement below that treats `Acyclic.lean`, `MatFueled`, `AcyclicWellFormed`, or
> `wellFormedLowered_of_acyclic` as live R9/flagship infrastructure is superseded:
> `IRWellFormed.defEnvOrdered` plus `codeFits`/`stackFits` now rebuilds the internal
> `WellLowered` adapter, while the residual rank/fuel definitions wait for P9 deletion.

---

## 0. Headline corrections to `docs/lirlean-reorg-plan.md`

The reorg-plan is directionally right (flat → role-directories) but four of its groupings are
wrong per the deep dives, and its central "acyclic drop shrinks `Conformance/` to nothing"
premise is false:

1. **`Conformance/ = {LowerConforms, DefsSound, CleanHaltExtract, RecorderLemmas, Acyclic}` is
   mis-clustered.** Of those five, only `LowerConforms` + `Acyclic` are true CFG-assembly (L5).
   - `DefsSound` is the value-channel "Layer B3" (imports `LoweringLemmas` + `Spec.Semantics`;
     imported by `MaterialiseRuns`, `Call`) → belongs in **`Materialise/`**, not assembly.
   - `CleanHaltExtract` is the clean-halt→gas/mem envelope PRODUCER, upstream of
     `MaterialiseCleanHalt` which imports it (`CleanHaltExtract → MatDecLower`;
     `MaterialiseCleanHalt → CleanHaltExtract`) → belongs in **`Materialise/`**.
   - `RecorderLemmas` imports only `Spec/Recorder` and feeds `Drive/SelfPresent` + the drive
     spine (`RecorderLemmas.lean:117,143` etc.) → belongs in **``** (recorder proof
     companions of the spine), not assembly.
2. **`Sim/ = {SmallStep, Match, SimStmt, SimStmts, SimTerm, Call, Create}` conflates two
   altitudes.** `SmallStep/Match/Call/Create` (+ the omitted `StorageErase`) are the exp003-bound
   **frame-local / v1-brick** sublayer (cluster-v1bricks); `SimStmt/SimStmts/SimTerm` are the v2
   **per-block `Corr` simulation** (cluster-sim). Split into `Frame/` and `Sim/`.
3. **"Acyclic + LowerConforms are slated to be dropped, so `Conformance/` shrinks to nothing" is
   still wrong, but for the P8 reason.** `LowerConforms`'s `sim_cfg`, `SimTermStep`,
   `WellFormedLowered`, and `CallRealises` are shared infra. `Acyclic.lean` is no longer the live
   R9 witness route; it is residual generic-`defs` fuel/rank support that P9 deletes after the
   old fuel materialisation stack is removed. Only the **dead acyclic capstone decl**
   `Lir.lower_conforms` (`LowerConforms.lean:1188`, ~63 LOC) is droppable in this phase — that is a
   decl deletion, not a file deletion. **No whole simulation layer disappears from the
   acyclic-vs-cyclic conclusion.**
4. **The reorg-plan omits two moves the deep dives call for:** `DriveSim.lean` is a
   drive-layer file misfiled directly under `` (00-proof-plan §1 note) → move to `Drive/`;
   and the 3874-LOC `RealisabilitySpec.lean` should be split (below).
5. **`Create.lean` placement:** the reorg-plan says "stays under `Sim/` (or a `Create/`)". Do
   NOT make a premature `Create/` dir — `Create.lean` is the field-for-field twin of `Call.lean`
   (00-create-status §1), so it lives beside it in **`Frame/`**. First-class CREATE, when it lands,
   adds arms to existing files (IR/Semantics/Lowering/Match/Recorder) + reuses the `DescentKind`
   scaffold already in `BytecodeLayer/Hoare/Descent.lean:421-567` — it does not want its own directory.

---

## 1. Proposed directory tree (every file placed, one-line rationale)

`LirLean/` becomes `Audit.lean` + ten role directories. Rationale = altitude band (L0–L7 from
00-proof-plan §1) + feature role.

```
LirLean/
  Audit.lean                         -- L7 axiom-guard net; imported LAST (LirLean.lean:53)

  Spec/                              -- reviewer-facing surface (NB: not one altitude — see note)
    IR.lean                          -- L0 base: IR datatypes (no CREATE node, IR.lean:77-86)
    Semantics.lean                   -- L0 base: v2 gas-free observable machine (RunFrom, :228)
    Lowering.lean                    -- L0 base: lower = encode∘emit∘allocate (:323)
    Recorder.lean                    -- HIGH-DAG surface: recording interpreter (imports CallRealises)
    Seams.lean                       -- HIGH-DAG surface: tracked-debt seam register (imported only by Audit)
    Conformance.lean                 -- tombstone stub (kept live via LirLean.lean:50)

  Engine/                           -- L1 IR-agnostic EVM theory; SLATED TO GRADUATE to exp003
    AccountMap.lean                  -- account-presence RBMap prims (self-flags RELOCATE, :26)
    StepWalk.lean                    -- per-opcode .next accMono dispatch walk (Brick C)
    Descent.lean                     -- CALL/CREATE descent inversions + DescentKind CREATE scaffold
    DriveMono.lean                   -- Brick D: presence monotone across drive
    Charges.lean                     -- subCharges fold algebra (gas channel)
    MemAlgebra.lean                  -- MSTORE/MLOAD slot value-channel crux lemmas
    CleanHalt.lean                   -- clean-halt scope predicates (9-file consumer)
    DriveRuns.lean                   -- reverse drive→Runs construction (already exp003-namespaced)

  Decode/                           -- L2 bytes <-> IR positions + control-flow validity
    LoweringLemmas.lean              -- allocate_toDefs Phase-A bridge (:91); defsOf_ne_gas/sload
    DecodeLower.lean                 -- decode round-trips over lower prog
    Layout.lean                     -- byte offsets of segments
    DecodeAnchors.lean              -- decode lands at expected IR positions ("Layer A")
    JumpValid.lean                  -- SegAligned tower #1 (True predicate) + reach-end transport
    NoCreateBytes.lean              -- SegAligned tower #2 (notCreate) — dedup target (see S-D)
    BoundaryReach.lean              -- SegAligned tower #3 (IsLoweringOp) — R6 geometry feeder

  Frame/                            -- L3a exp003-bound frame-local / v1-brick sublayer
    SmallStep.lean                  -- v1 reference small-step (mostly superseded-for-flagship)
    Match.lean                      -- pcOf + storage lens + sim_* frame bricks (LIVE) + dead Match struct
    Call.lean                       -- CALL oracle projections (evmCallOracle LIVE; applyCall dead)
    Create.lean                     -- CREATE oracle scaffold (twin of Call; incremental, keep)
    StorageErase.lean               -- RBMap erase read-back for zero-write SSTORE (LIVE)

  Materialise/                      -- L3b spill/recompute value channel + clean-halt envelope
    DefsSound.lean                  -- B3: def-env soundness (defsOf_ne_gas/sload consumers)
    MaterialiseGas.lean             -- B2: gas charge bookkeeping (load-bearing for gas-free proof too)
    MaterialiseRuns.lean            -- B1 linchpin: materialise_runs total over Expr (:771)
    MatDecLower.lean                -- MatSeg operand-decode path
    CleanHaltExtract.lean           -- clean-halt -> gas/mem envelope producer (§4 next_*_of_cleanHalt)
    MaterialiseCleanHalt.lean       -- clean-halt gas fold (imports CleanHaltExtract)
    StashTail.lean                  -- stash-tail gas/sload; stash_tail_runs_covered (Phase-C leaf)

  Sim/                              -- L4 per-block gas-aware Corr simulation
    SimStmt.lean                    -- per-statement Corr arms (hosts sim_call_stmt)
    SimStmts.lean                   -- stmt-list block form ("Layer D")
    SimTerm.lean                    -- terminator arms ("Layer E")

  CfgSim/                           -- L5 CFG simulation (world-channel walk)
    LowerDecode.lean                -- discharge per-cursor decode hyps over lower prog
    LowerConforms.lean              -- sim_cfg / SimTermStep / WellFormedLowered / CallRealises (LIVE)
    Acyclic.lean                    -- legacy generic-defs fuel/rank support (P9 deletion target)

                                 -- L6 gas-free IR spine
    Law.lean                        -- IR-run determinism ladder
    IRRun.lean                      -- IR-run existence + definability fold (acyclic half superseded)
    Call.lean                       -- worked external-call anti-vacuity example
    CallRealises.lean               -- call/create entry realisation bridges
    Modellable.lean                 -- ModellableStep producer (no-CREATE structural discharge)
    RecorderLemmas.lean             -- recorder proof companions (MOVED from top-level)
    Drive/                          -- L6 cyclic interpreter-drive walk
      DriveSim.lean                 -- cyclic-CFG drive (F1-F3) (MOVED from )
      SelfPresent.lean              -- SSTORE-presence world invariant + gas/sload alignment machinery
      CallPreservesSelf.lean        -- SelfPresent forward-closed along Runs -> hprec seam
      Headline.lean                 -- DriveCorrPlus salvage carrier (retained for R0 reshape)
    Flagship/                       -- L7 the WIP flagship, split 4 ways (WIP lib only)
      Surface.lean                  -- §1-§4 defs/coupling/ties/exact-consumption (sorry-free)
      Machinery.lean                -- §5 R0b-R11 obligation proofs (carries R3/R6/R10a sorries)
      Witness.lean                  -- §6a exProg + R9 anti-vacuity (sorry-free)
      RealisabilitySpec.lean        -- §6b conforms_of_worldeq + flagships + R12 (WIP root; sorries)
```

Net: `Audit.lean` + 10 role directories (`Spec/ Engine/ Decode/ Frame/ Materialise/ Sim/
CfgSim/  Drive/ Flagship/`); 51 files → 54 (the +3 is the RealisabilitySpec split,
which halves the worst file). `Engine/` stays a clean self-contained directory precisely so it can
lift to exp003 unchanged on the import axis.

**Note on `Spec/` altitude honesty (correcting reorg-plan's "the definitions" label):**
`Spec/{IR,Semantics,Lowering}` are true L0 (import only `Evm`+`Spec/IR`); `Spec/Recorder` and
`Spec/Seams` sit HIGH in the DAG (Recorder imports `CallRealises`+`Hoare.GasMonotone`; Seams
imports `Drive/CallPreservesSelf`+`Decode/Modellable`+`BytecodeLayer/Hoare/CleanHalt`). They live in `Spec/` for
the **reviewer-surface role**, not because they are base — keep them there but the directory README
should state this so no one reads `Spec/` as a pure altitude floor. `Spec/Conformance` is a
deliberate tombstone (`Spec/Conformance.lean:1-24`), not dead.

---

## 2. RealisabilitySpec split boundaries (the 3874-LOC file)

The §-structure and line ranges are machine-verified in cluster-flagship. Split along the existing
§ boundaries; the exit edges between §-blocks are narrow, so this is a **pure relocation** (no
proof change). Dependency order Surface → {Machinery, Witness} → RealisabilitySpec(root):

| new file | source lines | content | sorries | ~LOC |
|---|---|---|---|---|
| `Flagship/Surface.lean` | §1 :114-564, §2 :566-647, §3 :649-948, §4 :950-1040 | all REAL defs/structures: `entryState`, `Conforms` (:155), `WellLowered` (:477), `PrecompileAssumptions` (:550), `RecorderCoupled` (:599), `DriveCorrLog` (:629), `StmtTies'`/`TermTies'`, `RunFromLeft`/`RunFromAll` + 2 PROVED adequacy lemmas | none | ~930 |
| `Flagship/Machinery.lean` | §5 :1042-2958 | R0b (`defsSoundS_preserved_step`), R2, R3 (`callRealises_of_recorded` SORRY :1385), R5, R6 walk (`atReachableBoundaryVJ_*` SORRIES :2343/2351/2380/2383), R7 edge family, R8 | R3, R6 (4 tokens) | ~1916 |
| `Flagship/Witness.lean` | §6a :2959-3623 | `exProg` (:2975) + ~20 private witness lemmas + R9 (`wellLowered_exProg` :3585, `wellLowered_check_exists` :3603) | none | ~664 |
| `Flagship/RealisabilitySpec.lean` (WIP root) | §6b :3624-3865, §7 :3867-3873 | R10a (SORRY :3634), R10b, `conforms_of_worldeq` (:3661 CLOSED), the flagship `lower_conforms` (:3705) + `_exact` + `_gasfree` (SORRIES), `realisedGas_nil_of_noGasReads`, R12a/b | R10a, R11×3, R12a | ~240 |

Boundary evidence: §6a `exProg` block is self-contained — its only exits to the rest are `exProg`
itself and `wellLowered_exProg`/`wellLowered_check_exists` (cluster-flagship S1); everything else in
it is `private`. §5 imports the R6-geometry names from `BoundaryReach` and the R7 machinery — those
imports move with `Machinery.lean`. The four flagship theorems + `conforms_of_worldeq` are the only
things that must see all three lower files, so they stay in the root.

**Optional finer split (defer):** `Machinery.lean` at ~1900 LOC is still large; the R6 geometry
block (`emptyProg`/`not_runs_atReachableBoundary`/`AtReachableBoundaryVJ`/`runs_atReachableBoundary`,
:2214-2472, the only part that imports `BoundaryReach`) could later peel into
`Flagship/Boundary.lean`. Not now — do it only if the R6 leaf lands and the block stabilizes.

**Cost to flag:** the module name `RealisabilitySpec` is cited across `docs/`. Keeping it as the
aggregator module (physically under `Flagship/`) preserves the name but changes its module path
to `LirLean.Flagship.RealisabilitySpec` — one-line `lakefile.lean:32` edit + a docs sweep. If
doc drift is unacceptable, keep the root at `RealisabilitySpec.lean` (no lakefile change) and put
only `Surface/Machinery/Witness` under `Flagship/`; the tree is slightly less tidy but zero doc
churn. Recommend the former (full `Flagship/`) — the legibility win dominates a mechanical rename.

---

## 3. Acyclic-vs-cyclic reconciliation (what the eval concludes for the tree)

The honest headline is `Lir.lower_conforms` (`RealisabilitySpec.lean:3705`). The acyclic path
is dead legacy; the cyclic tie-supplied path is live-but-superseded (the vacuous route the flagship
refuses to cite, `:3730-3736`). **This removes decls, not files:**

- **Delete (dead, zero callers):** `Lir.lower_conforms` capstone (`LowerConforms.lean:1188`, ~63
  LOC) — and, only together with it, `runWithLog_messageCall` (`RecorderLemmas.lean:143`, its sole
  caller is that capstone). `LowerConforms.lean` and `RecorderLemmas.lean` both survive (their other
  decls are live).
- **Superseded content inside a live file (delete the acyclic half only):** `IRRun.lean`
  `CFGAcyclic`/`TermRankLt`/`Term.succs`/`runFrom_exists*`/`irRun_exists*` (~150 LOC, retired by
  DriveSim's `totalGas` measure, `DriveSim.lean:17,54`). KEEP the definability fold
  (`StmtDefinable`/`StmtsDefinable`/`stmtPost`/`stmtsPost`/`runStmts_exists`) — still load-bearing
  for the DriveSim per-block bricks and it inspired `StmtDefinableG`.
- **Needs-confirmation, do NOT cut in the reorg:** the DriveSim vacuous route
  (`lower_conforms_cyclic'` :666 + `driveStep_of_block` + the `RunDefinable` path). The *measure*
  infra (`totalGas_succ_lt`, `DriveCorr`, `drive_step_block_*`) is the reshape skeleton the missing
  `runFrom_of_driveCorrLog` reuses — keep. `Acyclic.lean` is no longer an R9 live path; keep it
  only until P9 deletes the residual fuel stack.

Consequence for the reorg: `CfgSim/` is a real, populated directory (`LowerDecode`,
`LowerConforms`, `Acyclic`), NOT the empty shell the reorg-plan predicted.

---

## 4. Engine graduation + CREATE reconciliation

**Engine → exp003 (separate, last).** `Engine/` already imports only exp003 (`Evm`,
`BytecodeLayer.*`) — clean on the import axis. The blocker is **namespace leakage**: 5/8 files sit
in `Lir` (`AccountMap`, `StepWalk`, `Descent`, `DriveMono`, `CleanHalt`); `DriveRuns`
(`BytecodeLayer.Interpreter`) and the `Evm`-namespaced inversions are graduation-ready;
`AccountMap.lean:26/55/68` already carries `-- RELOCATE to exp003`. Graduation is a renamespace +
physical move to `003_bytecode_layer/`, changing every downstream engine import to
`import BytecodeLayer.Hoare.*`. Because it touches ~every Drive
file's import block, **do it as its own PR AFTER the LirLean-internal reorg settles** — never
interleave the two churns. Keep `Engine/` a self-contained directory in the meantime so the move is
a clean `git mv` of the whole folder.

**CREATE going live (future feature, no premature directory).** Today `Create.lean` (Frame/) and
the `DescentKind` block (`BytecodeLayer/Hoare/Descent.lean:421-567`) are green scaffolding; the IR surface has
zero CREATE node (`Spec/IR.lean:77-86`, `Spec/Lowering.lean:178-200`). When first-class CREATE
lands (00-create-status §6) it **adds arms to existing files** — `Stmt.create` in `Spec/IR`, a
`.create` arm in `Spec/Semantics` + `IRRun` + `Spec/Lowering.emitStmt`, a `create_reflects_lowered`
in `Frame/Match` (twin of `call_reflects_lowered`, `Match.lean:519`), a recorder arm in
`Spec/Recorder`/`RecorderLemmas` — plus it **retires** `Decode/NoCreateBytes` + the `NotCreate`
clause rather than extending them. The restructure must therefore **not** invent a `Create/` dir:
CREATE is a cross-cutting arm-addition, and its scaffold belongs beside its CALL twin (`Frame/`) and
in `Engine/` (the `DescentKind` unification). The one restructure implication: keep `Frame/Call.lean`
and `Frame/Create.lean` adjacent, and keep `Decode/NoCreateBytes.lean` a separate file so it can be
cleanly retired later.

---

## 5. Import-churn & sequencing plan

The governing constraint (reorg-plan step 3, confirmed): a directory move rewrites the `import` line
in every downstream file, so it collides head-on with any in-flight proof branch. The flagship
(`RealisabilitySpec`, 11 open sorries) is under active development and imports `Drive.Headline` +
`Acyclic` + `BoundaryReach`, so blind moves would rewrite its import block mid-proof. Order the work
so the noisy moves happen in a quiet window and the flagship-internal work happens at a leaf-landing
checkpoint.

**Phase A — dead-decl deletions (do FIRST; small, no cross-file import churn).** Remove corpses
before moving anything so you don't relocate dead code:
- `Lir.lower_conforms` capstone + `runWithLog_messageCall` (§3).
- `IRRun` acyclic half (§3).
- Zero-ref orphans: `SmallStep.IRConf` (:69), `SmallStep.Program.stmtAt` (:127),
  `Recorder.RunAcc` (:113), `MaterialiseGas.chargeOf_imm_const` (:141),
  `LowerDecode.assign_sload_sub_key` (:68), `SelfPresent.realisedCall_projection` (:55).
- Confirm-then-delete: `LowerConforms.entry_storageAgree_codeFrame` (:1089) — verify the flagship
  supplies entry `w0` differently before cutting.
- Each deletion is local to one file's decl list; no importer changes. Rebuild green + `WIP` after.

**Phase B — the directory reorg (the big atomic churn; QUIET WINDOW only).** In one commit, when no
proof branch is open against the default cone:
1. `git mv` every file into its role directory per §1; move `DriveSim.lean` → `Drive/`.
2. Rewrite every `import LirLean.X` → `import LirLean.<Dir>.X` repo-wide, and update the grouped
   root `LirLean.lean` (its 40-odd imports) + `Audit.lean`'s 6 imports.
3. `lake build` (default: green + sorry-free) then `lake build WIP`.
This is the reorg-plan's step 1-2, unchanged, but now with the corrected mapping.

**Phase C — RealisabilitySpec split (flagship-track, WIP-internal, at a leaf checkpoint).** Split
per §2. This touches ONLY the `WIP` lib (nothing in the default cone imports `RealisabilitySpec`),
so it does NOT collide with Phase B and can be done by the flagship owner independently — ideally
right after an R-leaf lands, when the § boundaries are momentarily stable. One `lakefile.lean:32`
edit if the module is renamed.

**Phase D — SegAligned dedup (independent proof refactor, anytime).** Collapse the three towers
(`Decode/JumpValid` `SegAligned` :78, `Decode/NoCreateBytes` `SegAlignedSafe` :50,
`Decode/BoundaryReach` `SegAlignedLowering` :135) into one predicate-parameterized `SegAlignedP P`;
the emit-ladders are line-identical bar one predicate arg. `SegAlignedLowering` is strictly stronger
than `SegAlignedSafe` (every `IsLoweringOp` op is non-CREATE), so `NoCreateBytes` can fold into
`BoundaryReach` after flipping the current `BoundaryReach → NoCreateBytes` import. This is orthogonal
to the moves; sequence it whenever, but easiest AFTER Phase B so the files are already in `Decode/`.

**Phase E — Engine graduation to exp003 (LAST; cross-repo).** §4. Renamespace + move the whole
`Engine/` folder to exp003; rewrite downstream imports. Biggest cross-boundary churn — do it alone.

Rationale for the order: A shrinks the surface before B moves it; B is the one unavoidable
mass-rewrite and must be atomic + quiet; C is WIP-isolated and rides the flagship's own cadence; D
and E are independent refactors best done after the tree is in its new shape.

---

## 6. Honest note: legibility-only vs real reduction

**Legibility-only (pure `git mv` + import rewrite, ZERO LOC removed) — the bulk of this plan:**
- The entire directory reorg (Phase B) and the DriveSim relocation. It makes 51 files navigable by
  altitude/role but removes nothing. Value is real (a reviewer can find the value channel, the
  frame bricks, the flagship) but it is *not* a size reduction.
- The RealisabilitySpec split (Phase C). Same 3874 LOC, now in 4 files of ~930/1900/660/240. Halves
  the worst offender and isolates the sorry-carriers from the sorry-free surface/witness — a large
  legibility win, zero content reduction.

**Real reduction (content actually removed):**
- SegAligned dedup (Phase D): ~1400 → ~600 LOC, the single biggest real shrink (~800 LOC). This is
  the lever the DAG doc already names; it is a proof refactor, not a move.
- Phase A dead-decl deletions: capstone (~63) + `messageCall` bridge + `IRRun` acyclic half (~150)
  + the six zero-ref orphans. A few hundred LOC total — real but modest.
- (Confirm-first, potentially large) `jump_landing_of_cleanHalt`/`branch_landing_of_cleanHalt`
  (`LowerDecode.lean:486,769`, ~410 LOC combined): vestigial `Plus`-thread scaffolding whose
  functionality the flagship re-derives inline (`RealisabilitySpec ~:1741-1899`). Green +
  axiom-guarded; **do not delete blind** — only if the flagship commits to NOT factoring the landing
  walk back out. If confirmed dead, this is the second-largest real reduction after the towers.

**Relocation-out (removes LOC from *this* package, not from the world):**
- Engine graduation (Phase E): ~3200 LOC leaves LirLean for exp003. Real for this package's size,
  but it is a move, gated on renamespacing.

**Explicitly NOT reductions (guard against the shallow pass):** deleting `Acyclic.lean`,
`LowerConforms.lean`, `Create.lean`, `Spec/Conformance.lean`, `Drive/Headline.lean`, the DriveSim
measure infra, or the `DescentKind` scaffold. Each looks droppable by import-graph reach but is live
(R9 witness / cyclic default headline), scaffold for a settled roadmap item (CREATE / R0 reshape),
or a deliberate tombstone. The "delete the acyclic path and drop ~6k LOC" hope is not real: the L4
sim engine is shared by the cyclic flagship via `sim_cfg` (00-proof-plan §1 honest note). The genuine
size wins are the SegAligned dedup and Engine's departure — everything else in this plan is
legibility.
