# exp005 LirLean — SIMPLIFICATION + RESTRUCTURE + CREATE roadmap

Date: 2026-07-04. **Actionable companion to `docs/deepdive-2026-07-04/00-proof-plan.md`
(the DAG doc).** The DAG doc says *what the proof is trying to be*; this doc says *what to
do to the tree and in what order*. Every move cites `file:line`; every move carries a KIND,
a LOC/file impact, a RISK, and a GATE. Read-only synthesis of the eval + deepdive docs; no
`.lean` touched in producing it.

> **P8 status note (2026-07-08).** The Acyclic/MatFueled route described below is no longer live
> P8 infrastructure. `IRWellFormed.defEnvOrdered` plus `codeFits`/`stackFits` rebuilds the
> internal `WellLowered` adapter; the residual rank/fuel definitions are P9 deletion targets.
>
> **P9 status note (2026-07-08).** Those residual targets have been deleted: `Expr.slot`,
> `materialiseExpr`, `materialise`, `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, and
> `NoSlotSource` are no longer current APIs.

Baseline: **51 `*.lean` files, 25 518 LOC** (`find LirLean -name '*.lean' | wc -l` = 51,
`cat | wc -l` = 25518). Default `LirLean` lib is sorry-free; the one-file `WIP` lib
(`lakefile.lean:31-32`, rooted at `LirLean.V2.RealisabilitySpec`) is the sole sorry-carrier
(11 open sorry bodies).

**KIND legend:** `dead-removal` (decl has zero live callers) · `de-dup` (collapse genuine
duplication) · `split` (relocate content into more files, 0 LOC removed) · `relocate`
(move file/decl, 0 LOC removed from the world) · `feature` (CREATE, adds LOC).

**GATE legend:** `now` (no dependency, do anytime) · `quiet-tree` (mass import-rewrite; only
in a window with no open proof branch against the default cone) · `leaf-checkpoint`
(WIP-internal; do right after an R-leaf lands when § boundaries are stable) · `delete-together`
(a stranded feeder dies with its sole consumer) · `confirm-first` (one verification before
cutting) · `needs-lead-decision` (roadmap fork, not a mechanical call) · `after-<X>` (ordering
dependency).

---

## 0. The one-paragraph honest verdict

The **biggest real LOC reduction** is the SegAligned tower de-dup (~700 LOC, ungated). The
**biggest legibility win** is splitting the 3874-line `RealisabilitySpec.lean`. Everything else
that *looks* deletable by import-graph reach is live (R9 witness, cyclic default headline),
scaffold toward a settled roadmap item (CREATE, R0 reshape), or a deliberate tombstone. The
"delete the acyclic path and drop ~6k LOC" hope is **not real** — the L4 sim engine is shared by
the cyclic flagship via `sim_cfg` (`LowerConforms.lean:970`). Genuine size wins:
SegAligned de-dup + a few hundred LOC of true dead decls + (confirm-first) the landing-lemma pair.
CREATE is *added* work, planned first-class, not a deletion.

---

## 1. Ranked table of concrete moves

Ranked by **(value × do-now-ability)**. "LOC" is content removed (negative) or added (positive);
`0` means a pure move/split.

### Tier 1 — do now, low risk, default build, no roadmap dependency

| # | Move | Kind | LOC | Files | Risk | Gate |
|---|---|---|---|---|---|---|
| 1 | **Collapse the 3× SegAligned tower** into one `SegAlignedP (P)` inductive + `.mono`. `SegAligned` (`JumpValid.lean:78`), `SegAlignedSafe` (`NoCreateBytes.lean:50`), `SegAlignedLowering` (`BoundaryReach.lean:135`) are the same inductive differing only by a per-head predicate; the whole ladder (`segAligned_emitStmt` `JumpValid.lean:243` ≡ `segAlignedSafe_emitStmt` `NoCreateBytes.lean:243` ≡ `segAlignedLowering_emitStmt` `BoundaryReach.lean:282`) is re-proven line-for-line bar one `(by decide)`. Prove once at the tightest predicate `IsLoweringOp` (`BoundaryReach.lean:126-129`), derive the other two by `.mono`. | de-dup | **−700 to −730** | 0 (or −1) | LOW-MED | now |
| 2 | **Split `RealisabilitySpec.lean` (3874 LOC)** 4 ways along existing § boundaries: `Surface` (§1-4 :114-1040, sorry-free), `Machinery` (§5 :1042-2958, holds R3/R6 sorries), `Witness` (§6a exProg+R9 :2959-3623, sorry-free), root (§6b :3624-3865, holds R10a/R11/R12a). exProg block is self-contained (exits only `exProg` + `wellLowered_exProg`/`_check_exists`). | split | 0 | +3 | LOW | leaf-checkpoint |
| 3 | **Delete dead acyclic capstone** `Lir.lower_conforms` (`LowerConforms.lean:1188`, ~63 LOC, zero code callers — the one apparent caller `RealisabilitySpec.lean:3864` resolves to the *flagship* `Lir.V2.lower_conforms` inside `namespace Lir.V2`) **+ its sole exclusive feeder** `runWithLog_messageCall` (`RecorderLemmas.lean:143`, ~20 LOC). Both host files survive. | dead-removal | **−85** | 0 | LOW | delete-together |
| 4 | **Delete confirmed zero-ref orphans:** `SmallStep.IRConf` (`SmallStep.lean:69`) + `SmallStep.Program.stmtAt` (`SmallStep.lean:127`) (genuinely dead, only own def lines); `assign_sload_sub_key` (`LowerDecode.lean:68`, never-wired twin of used `sstore_sub_*`); `chargeOf_imm_const` (`MaterialiseGas.lean:141`, = `chargeOf_imm`); `realisedCall_projection` (`SelfPresent.lean:55`, body is literally `realisedCall_cons self hc`, flagship uses `realisedCall_cons` directly at RS:2856). | dead-removal | **−40 to −60** | LOW | now |
| 5 | **Delete `Recorder.RunAcc`** (`Spec/Recorder.lean:113`) — `List Word × List Nat × List CallRecord` with ZERO uses as a type repo-wide (`driveLog` threads three separate args); only a stale docstring (:154) references it, and that docstring is itself wrong (says 2-tuple). | dead-removal | ~−4 | LOW | confirm-first (not reserved for a planned re-bundling) |

**Tier-1 total addressable now: ~900–1000 LOC removed + the worst file halved**, none of it
touching the open-sorry surface.

### Tier 2 — medium LOC, one confirmation each

| # | Move | Kind | LOC | Risk | Gate |
|---|---|---|---|---|---|
| 6 | **Delete `IRRun.lean` acyclic-CFG half** — `CFGAcyclic` (:225), `TermRankLt` (:205), `Term.succs` (:212), `runFrom_exists*` (:139/149/292), `irRun_exists*` (:162/174/341); retired by DriveSim's dynamic `totalGas` measure (`DriveSim.lean:17,54`), all 11 `CFGAcyclic` grep hits are DriveSim docstrings. **KEEP** the definability fold (`StmtDefinable`/`stmtsPost`/`stmtPost`/`runStmts_exists`) — still cited by DriveSim per-block bricks, inspired `StmtDefinableG`. | dead-removal | −150 | LOW | confirm-first (delete acyclic half only) |
| 7 | **Delete `jump_landing_of_cleanHalt` / `branch_landing_of_cleanHalt`** (`LowerDecode.lean:486,769`, ~410 LOC combined) — vestigial `Plus`-thread scaffolding (Plus deleted 2026-07-03); flagship re-derives the landing walk inline (`RealisabilitySpec ~:1741-1899`). Green + axiom-guarded (Audit.lean). Second-largest real reduction if confirmed. | dead-removal | −410 | MED | confirm-first (flagship will NOT factor the landing walk back out) |
| 8 | **Confirm-then-delete `entry_storageAgree_codeFrame`** (`LowerConforms.lean:1089`) — `entry_corr` takes `hstore` as a hypothesis rather than using this canonical `w0` choice; orphaned. RS:626 names `entry_corr` (its caller) as intended flagship R7 entry machinery. | dead-removal | ~−20 | MED | confirm-first (not the flagship's intended R7 entry-world supply) |

### Tier 3 — largest potential deletion, ROADMAP decision (not dead code)

| # | Move | Kind | LOC | Risk | Gate |
|---|---|---|---|---|---|
| 9 | **`Drive/Headline.lean` (~200, entirely unreferenced) + `SelfPresent.lean` §3-§4 `GasLogAligned`/`SloadLogAligned` (~230)** — header designates them "retained salvage" for the R0 reshape; the coupled run-producer `runFrom_of_driveCorrLog` (the flagship's single blocker) may or may not reuse them. Single largest deletion, but deleting salvage the reshape needs would re-open closed work. | dead-removal | −430 | HIGH uncertainty | needs-lead-decision (does the R-series gas/sload alignment channel survive the drive reshape?) |
| 10 | **Prune v1 IR-semantics decls superseded by V2 twins** — `Match.lean` `evalExpr` (:89), `IRState` (:49), `IRHalt` (:60), `setLocal` (:101), `bindCallResult` (:110), the **Match STRUCTURE** (:125, never instantiated — `.storage_eq`/`Match.mk`/`: Match` grep empty; replaced by `Corr` `SimStmt.lean:103`), `lower_preserves_discharge/stop/ret` (:550/562/577, zero callers). Each has a live `V2.*` twin in `Spec/Semantics.lean`. **Files stay** (sim_* bricks + oracles are live). | dead-removal | −100 to −150 | MED | needs-lead-decision (v1-reference-layer scoping; confirm Law/Call anti-vacuity artifacts don't need v1) |

### Tier 4 — legibility-only reorg (0 LOC; the bulk of the "restructure")

| # | Move | Kind | LOC | Files | Risk | Gate |
|---|---|---|---|---|---|---|
| 11 | **Flat → role-directory reorg** per restructure-plan §1: `Audit.lean` + 10 dirs (`Spec/ Engine/ Decode/ Frame/ Materialise/ Sim/ Assembly/ V2/ V2/Drive/ V2/Flagship/`). Corrects 4 reorg-plan mis-groupings: `DefsSound`+`CleanHaltExtract` → `Materialise/`; `RecorderLemmas` → `V2/`; split `Sim/` into `Frame/` (SmallStep/Match/Call/Create/StorageErase) vs `Sim/` (SimStmt/SimStmts/SimTerm); place `StorageErase` (reorg-plan omitted it). | relocate | 0 | 51→54 | MED (mass import rewrite) | quiet-tree, after-Tier-1-deletions |
| 12 | **Move `V2/DriveSim.lean` → `V2/Drive/DriveSim.lean`** — a drive-layer file misfiled under `V2/`; updates importers `Drive/Headline`, `Audit`, `LirLean.lean:44`. | relocate | 0 | 0 | LOW | with #11 |

### Tier 5 — zero-LOC hygiene / cross-repo

| # | Move | Kind | LOC | Risk | Gate |
|---|---|---|---|---|---|
| 13 | **Engine/ graduation to exp003** — 5/8 files sit in `Lir.V2` despite being IR-agnostic (`AccountMap.lean:26/55/68` self-flags `-- RELOCATE to exp003`); import-clean already (only `Evm`/`BytecodeLayer.*`). Renamespace + `git mv` whole folder; rewrite every downstream `import LirLean.Engine.*`. | relocate | −3200 from *this package* (moves, not removed) | MED-HIGH (cross-repo, touches every V2/Drive import block) | needs-lead-decision + after-#11, its own PR |

---

## 2. CREATE — first-class planned work (a `feature`, not a deletion)

The lead wants CREATE built. It mirrors CALL step-for-step (the CALL ecosystem is the template:
`Spec/IR.CallSpec` → `V2.EvalStmt.call` → `emitStmt .call` → `Call.evmCallOracle` →
`Match.call_reflects_lowered` → `V2/CallRealises` → recorder `recordCall` → `Modellable`
clause-1). What already exists: the whole exp003 reference layer for **both** kinds
(`contractAddressBytes` exp003:Create.lean:22 with the salt branch; `beginCreate` total :64;
`resumeAfterCreate` :189; `createArm` System.lean:73; the engine/`DescentKind` create layer
Descent.lean:502) **and** the exp005 oracle twin (`Create.lean` `CreateOracle` :64 /
`createAddrOrZero` :75 / `evmCreateOracle` :99 / `evmCreateOracle_addressWord_eq` :107, green, in
the build cone `LirLean.lean:22`, consumed by nobody). What is absent: the IR-surface-and-up
mirror, **and** a genuine exp003 `Runs`-level bridge.

### 2.1 The load-bearing surprise (gates everything)

`grep -rn "CreateReturns\|Runs.create"` across **both** experiments is **empty**. exp003 `Runs`
(`Hoare.lean:120-123`) has only `| call (hcall : CallReturns …)`; `runs_of_drive_ok`
(`Engine/DriveRuns.lean:283`) is *predicated* on `NoCreate`/`ModellableStep` precisely because
"`.needsCreate` … `Runs` cannot model" (`DriveRuns.lean:27`). So CREATE is not merely absent from
the IR — it is *actively excluded from the `Runs` abstraction the flagship's conclusion rides*.
Step 0 is a real exp003 edit with exp005-wide ripple and is the item most likely to blow the
estimate.

### 2.2 Ordered build (bottom-up, proof-first, each step green on the last)

| Step | Where | Add | Gate / risk |
|---|---|---|---|
| **0** | exp003 `Hoare.lean` + `Engine/DriveRuns.lean` | `CreateReturns` (twin of `CallReturns` :91; must carry the `.ok` witness of the 63/64 guard since `resumeAfterCreate` is `Except`-typed); `Runs.create` constructor + arms in every `Runs` recursion (`Runs.trans` :129, `gasAvailable_le` ladder, `cleanHalts`, DriveSim measure); **de-`NoCreate`** `runs_of_drive_ok` (delete the side condition, build a `Runs.create` node via `endFrame_create_accPresent` DriveMono.lean:87). | **needs-lead-decision** (exp003 owner must accept a `Runs.create` node) — R1, the load-bearing unknown. |
| **1** | `Spec/IR.lean` | `CreateSpec` (mirror `CallSpec` :43) + `Stmt.create` (mirror :85). Carry `value/initOffset/initSize : Tmp`, `salt : Option Tmp` **from day one** (CREATE2 delta), `resultTmp : Option Tmp`. `Expr.slot` (:73) already exists for the pushed address. | Widest blast radius — a new `Stmt` constructor breaks every exhaustive match (Semantics, Lowering, SmallStep, MaterialiseRuns, the 3 SegAligned emit-ladders, SimStmt arms). |
| **2** | `Spec/Semantics.lean` | `EvalStmt.create` (mirror `.call` :187-195); pops a stream head `(world', addrW)`, sets `world`, binds `addrW` at `resultTmp`. | **needs-lead-decision** (R2, the stream fork — see 2.3). |
| **3** | `SmallStep.lean` | `IRState.applyCreate` (twin of `Call.IRState.applyCall` :158) + `.create` arm in the v1 line. | Low priority (v1 superseded-for-flagship) but needed to keep v1 compiling. |
| **4** | `Spec/Lowering.lean` | `Byte.create := 0xf0`, `Byte.create2 := 0xf5` (:46-61); `emitStmt .create` arm (mirror `.call` :191-200); `defsOf` create-result stash arm (:254 twin). | `defsOf` create arm forces re-proving `allocate_toDefs` (`LoweringLemmas.lean:91`, the Phase-A keystone). |
| **5** | `Match.lean` | `sim_create` (= `Runs.create hc rest` — **unstatable without Step 0b**); `create_reflects_lowered` (twin of :519). | R3 — **NOT `rfl`-clean**: `evmCreateOracle.postStorage` reads `result.accounts` directly (Create.lean:100-101), not through `Except`-typed `resumeAfterCreate`; budget a short unfold through the 63/64 guard + `replaceStackAndIncrPC`. |
| **6** | `V2/CreateRealises.lean` (new) + `Spec/Recorder.lean` | `evmV2CreateEntry` (twin of `evmV2CallEntry` :59); `createRealises_bridge` (twin :85); un-drop `recordCall`'s `\| .create _ => callAcc` (:172); create accumulator in `driveLog` (:186, gated on `rest.isEmpty`); `realisedCreate` projection. | Stream model per R2. |
| **7** | `V2/Modellable.lean` + `Decode/NoCreateBytes.lean` | **RETIRE the exclusion** (a *subtraction*): weaken/delete `NotCreate` (`Modellable.lean:194`, `notCreate_of_atReachableBoundary` :25, wired at RS:1255/3677); add `0xf0`/`0xf5` to `IsLoweringOp` (`BoundaryReach.lean:126-129`). | **after-#1** (SegAligned de-dup) — add CREATE to `IsLoweringOp` **once** in the merged tower instead of maintaining a CREATE-permitting `SegAlignedSafe`. |
| **8** | `V2/RealisabilitySpec.lean` | `Conforms` (:155) + `WellLowered` (:477) shapes unchanged; add a create-cursor sibling to the R3 call tie (RS:2856) and admit CREATE boundary heads in R6 (`atReachableBoundaryVJ_*`, RS:2343-2383); extend the exProg witness (RS:2975) to exercise CREATE **last** (avoid adding sorry pressure to the 11-open flagship). | The deepest exp005 proof: a create `Corr`-re-establishment lemma (analogue of the 28-hyp `sim_call_stmt` SimStmt.lean:576) — CREATE's init-code memory window `MachineState.M … initOffset initSize` (exp003:Create.lean:207) is **nonzero**, unlike CALL's zero-window first cut, so `memAgree`/`slot_windows_disjoint` must carve out the init window. |

### 2.3 The two design forks to settle before coding

- **R2 — stream model.** Element type is identical `(World × Word)` for CALL and CREATE, but
  they interleave positionally. Minimal mirror = a parallel `CreateStream` (positionally *wrong*
  for `CALL;CREATE;CALL`); correct = **one merged descent stream** `List (World × Word ×
  DescentKind)` replacing `CallStream` (00-create-status §5), which reshapes the settled
  `CallStream` (commit 1c77c07) and changes `EvalStmt`/`RunStmts`/`RunFrom` signatures
  (74/72/137 refs). **Decide before Step 2.**
- **R4 — the 63/64 retention guard** makes `CreateReturns` partial (`resumeAfterCreate` can
  `throw .OutOfGas`, exp003:Create.lean:200 — no CALL analogue). Either carry the `.ok` witness in
  the bundle or add an "enough gas retained" seam — likely a `PrecompileAssumptions`-style entry
  (RS:550).

### 2.4 CREATE2 delta (cheap by construction)

Zero oracle change (`createAddrOrZero` kind-agnostic), zero reference work (`contractAddressBytes`
already branches on salt; CREATE2's `L_A` is *unconditionally* total per create-crosscheck.md:169-170
— **less** totality plumbing than CREATE). Delta ≈ **one `emitStmt` sub-arm** (materialise `saltTmp`,
emit `0xf5`) + adding `0xf5` to `IsLoweringOp`. Requires `salt : Option Tmp` carried from Step 1.

### 2.5 Structural implication for the reorg

CREATE is a **cross-cutting arm-addition, NOT a new directory.** `Create.lean` lives beside its
twin in `Frame/`; the `DescentKind` scaffold stays in `Engine/Descent.lean:421-567`. Keep
`Decode/NoCreateBytes.lean` a *separate* file so Step 7 can retire it cleanly. Keep the empty-init
first cut (`Create.lean:31`: offset=length=value=0) for the initial landing — it is load-bearing
for *soundness* (collapses the init OOG/REVERT/EIP-170/3541/deposit surface), not just scope;
relaxing it is a separate follow-on with its own precondition surface (create-crosscheck.md GO
guardrails).

---

## 3. Recommended sequencing (safe now vs deferred)

Governing constraint: a **directory move rewrites the `import` line in every downstream file**, so
it collides head-on with any in-flight proof branch. The flagship (`RealisabilitySpec`, 11 open
sorries) is under active development and imports `Drive/Headline`+`Acyclic`+`BoundaryReach`, so
blind moves would rewrite its import block mid-proof. Order the work so noisy moves happen in a
quiet window and flagship-internal work happens at a leaf checkpoint.

**Phase A — dead-decl deletions (do FIRST; local, no import churn).**
Tier-1 #3, #4, #5 + Tier-2 #6 (confirm), #7 (confirm), #8 (confirm). Remove corpses *before*
moving anything so you don't relocate dead code. Each deletion is local to one file's decl list;
rebuild green + `WIP` after each.

**Phase B — the directory reorg (Tier-4 #11 + #12; QUIET WINDOW only).** One atomic commit when no
proof branch is open against the default cone: `git mv` per restructure-plan §1, move
`DriveSim.lean` → `V2/Drive/`, rewrite every `import LirLean.X`, update root `LirLean.lean`
(~40 imports) + `Audit.lean` (6 imports). `lake build` (default green + sorry-free) then
`lake build WIP`.

**Phase C — RealisabilitySpec split (Tier-1 #2; WIP-internal, leaf checkpoint).** Touches ONLY the
`WIP` lib (nothing in the default cone imports `RealisabilitySpec`), so it does not collide with
Phase B and rides the flagship owner's cadence — ideally right after an R-leaf lands when the §
boundaries are stable. One `lakefile.lean:32` edit if the module is renamed.

**Phase D — SegAligned de-dup (Tier-1 #1; independent proof refactor).** Orthogonal to the moves;
easiest **after Phase B** so the files are already in `Decode/`. Biggest real LOC win.

**Phase E — CREATE (§2; the feature track).** Runs on its own branch. Step 0 (exp003) needs the
lead/exp003-owner decision first. Step 7 must come **after Phase D** (add `0xf0`/`0xf5` to the
merged `IsLoweringOp` tower once). The stream fork (R2) and the 63/64 seam (R4) settled before
Step 2.

**Phase F — Engine graduation (Tier-5 #13; LAST, cross-repo).** Renamespace + move the whole
`Engine/` folder to exp003; its own PR, never interleaved with B.

**Phase G — Tier-3 gated deletions (#9, #10).** Only after the lead settles whether the R-series
gas/sload alignment channel (#9) survives the drive reshape and whether the v1 reference layer
(#10) is in scope. Do NOT touch before those calls.

Rationale: A shrinks the surface before B moves it; B is the one unavoidable mass-rewrite and must
be atomic + quiet; C is WIP-isolated; D is an independent refactor; E and F are feature/relocation
tracks; G waits on roadmap decisions.

---

## 4. Explicit "do NOT touch" list

These look droppable by import-graph reach but are live, intentional scaffold, or a deliberate
tombstone. A shallow "unused ⇒ dead" pass will wrongly flag every one of them.

**Deliberate infra / tombstones (keep as-is):**
- `Spec/Conformance.lean` (`:1-24`) — tombstone stub, ZERO decls, kept live via `LirLean.lean:50`
  so the canonical conformance path resolves to an honest notice.
- `Spec/Seams.lean` forwarders `SelfPresent` (:38) / `CallsCode` (:81) /
  `CleanHaltsNonException` (:93) — no code consumers by design; the typed seam register that
  names/drift-proofs the debt, consumed by `Audit.lean`.
- `Audit.lean` — 8 `#guard_msgs in #print axioms` guards; ZERO decls; imported LAST
  (`LirLean.lean:53`).
- `GasRealises` / `SloadRealises` (`MaterialiseRuns.lean:536,557`) — RETIRED universals kept as
  regression witnesses of the unsatisfiability lesson that motivated the spill pivot; correct move
  is *relocation* out of the B1 spine, not deletion.
- The PROVED refutations `not_defsSound_stale` (RS:3166), `not_runs_atReachableBoundary` (:2232),
  `emptyProg` — anti-vacuity evidence justifying live side conditions.

**Incremental scaffold toward OPEN leaves / settled roadmap (keep):**
- `Create.lean` + the `DescentKind` block (`Engine/Descent.lean:421-567`) — first-class CREATE
  scaffold (§2); `Create.lean` is the field-for-field twin of the load-bearing `Call.lean`.
- `Loc`/`Alloc`/`Loc.toDef`/`locOfExpr` (`Spec/Lowering.lean:92-111,269`) — low-usage but
  load-bearing via the keystone `allocate_toDefs` (`LoweringLemmas.lean:91`); incremental toward
  Phase-D `∀ SoundAlloc`.
- `realisedSload` (`Spec/Recorder.lean:285`) + `isSloadOp`/`sloadWarmthOf` — the SLOAD value
  channel parallel to the live GAS channel; alignment deferred by design (SelfPresent.lean:233).
- `BoundaryReach` `decode_reachable_boundary_loweringOp` (:415) — decode-level twin of the used
  byte-level lemma; header marks the consuming induction pending (R6).
- `callRealises_bridge` (`CallRealises.lean:85`) — incremental toward R3.
- `stash_tail_runs_covered` (`StashTail.lean:256`) — planned-feature leaf (Phase-C cached-SLOAD
  reuse, named at SimStmt.lean:1076).
- The CALL/CREATE inversion helpers `callArm_needsCall_inv` / `systemOp_needsCall_inv` (+ CREATE
  twins) — incremental bricks of the load-bearing `stepFrame_needsCall_inv`.

**Live shared infra (NOT acyclic-only — do NOT delete with "the acyclic path"):**
- `Acyclic.lean` — entirely LIVE via the flagship exProg/R9 witness
  (RS:3294/3304/3311/3366); its own header (:41-43) "unreferenced in the default build" is STALE.
- `LowerConforms.lean` `sim_cfg` (:970), `SimTermStep` (:96), `WellFormedLowered`, `CallRealises`
  — shared by the default-build cyclic `lower_conforms_cyclic` (`DriveSim.lean:648`) AND the
  flagship. Only the dead capstone decl (#3) drops; the file stays.
- DriveSim measure infra (`totalGas_succ_lt`, `DriveCorr`, `driveStep_of_block`,
  `drive_step_block_*`) — the reshape skeleton `runFrom_of_driveCorrLog` reuses. `lower_conforms_cyclic'`
  (`DriveSim.lean:666`) alone is safely removable, but confirm the block templates first.
- `CleanHaltExtract` `next_*_of_cleanHalt` family — called directly inside the flagship
  (RS:1415…2600) and upstream of SimStmt via MaterialiseCleanHalt; not acyclic-only.
- `Modellable.lean` `lower_modellable` (applied RS:1255) — fully live terminal-for-flagship.

**Genuine duplication that is INTENTIONAL (do not naively dedup):**
- The covered-slot MLOAD zero-expansion argument between `MaterialiseRuns.lean:896-940` and
  `MaterialiseCleanHalt.lean:122-177` — deliberate B1/B2 anti-cycle.
- `chargeOf` mirroring `materialiseExpr` opcode-for-opcode — the intentional B1/B2 gas split.
- `CallRealisesS` (RS:406) vs `Lir.CallRealises` (`LowerConforms.lean:261`) — NAMED Phase-3 debt
  gated on R0b; cross-file, not now.
- The ~30 frame-accessor `@[simp]` families (`sstoreFrame_*`/`popFrame_*` SimStmt;
  `jumpFrame_*`/`jumpdestFrame_*`/`jumpiFallthroughFrame_*` SimTerm) — distinct post-frame
  constructors, each load-bearing.
- `sim_call_stmt` (`SimStmt.lean:576`) 28-hyp shape lemma — genuine irreducible shape lemma; every
  hyp consumed, full `Corr` (incl. memAgree) re-established. Only cosmetic bundling possible.

**Needs-confirmation before touching (do NOT cut blind):**
- `MemAlgebra.mload_after_mstore` (:459, superseded by `mstore_reads_back` :713?) and the
  `resumeAfterCall_mload` crux (:85) + feeders (:58,:69) — superseded OR not-yet-wired.
- `decode_at_stmt_head_{nonpush,push}` / `decode_at_offset_push` (DecodeAnchors :195/215/257) —
  likely superseded by the MatSeg operand-decode path, but their nonpush twins are live and they
  form a symmetric completeness API.
- `sim_stmts` alias (`SimStmts.lean:132`, zero callers, pure alias of `sim_stmts_drop`) — docstring
  bills it as the plan-facing headline restatement.

---

## 5. Legibility-only vs real reduction (honest accounting)

**Real reduction (content removed):**
- SegAligned de-dup (#1): **~700–730 LOC** — the single biggest real shrink.
- Phase-A dead-decl deletions (#3,#4,#5,#6): capstone + `messageCall` + IRRun acyclic half + orphans
  ≈ **~300 LOC**.
- (Confirm-first) landing-lemma pair (#7): **~410 LOC** — second-largest if confirmed dead.
- (Gated) Tier-3 (#9,#10): up to **~580 LOC**, needs-lead-decision.

**Legibility-only (0 LOC removed):**
- The directory reorg (#11,#12) — makes 51 files navigable by altitude/role, removes nothing.
- The RealisabilitySpec split (#2) — same 3874 LOC in 4 files (~930/1900/660/240), isolates the
  sorry-carriers from the sorry-free surface/witness. Large legibility win, zero content reduction.

**Relocation-out (leaves this package, not the world):**
- Engine graduation (#13): ~3200 LOC moves to exp003. Real for *this package's* size, but a move.

**Added (the feature):**
- CREATE (§2) + CREATE2 — a net *increase*, planned first-class.

The "delete the acyclic path → drop ~6k LOC" hope is NOT real: the L4 sim engine is shared by the
cyclic flagship via `sim_cfg`. The genuine size wins are SegAligned + the dead decls + (confirmed)
the landing pair; everything else in the restructure is legibility or relocation.
