# Fleet audit 2026-07-04 — Cluster: Engine + V2 spine + Drive

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


> **P9 status note (2026-07-08).** This audit is historical where it discusses
> `Acyclic.lean`, `MatFueled`, `Expr.slot`, `materialiseExpr`, `recomputeFuel`, or
> `NoSlotSource`; those legacy routes/APIs have been deleted or superseded by
> `IRWellFormed` plus `codeFits`/`stackFits`.

Scope: the IR-agnostic EVM reasoning **BytecodeLayer/Hoare/**, the gas-free frame-free **V2 spine**, and the
cyclic-CFG **Drive** layer. 17 files. No `.lean` file was modified.

## 1. File table

| File | LOC | One-line purpose | Key exports | Layer | Verdict | Simplification note |
|---|---|---|---|---|---|---|
| `BytecodeLayer/Hoare/AccountMap.lean` | 145 | Pure `Evm.AccountMap` non-emptiness + `AccPresent`/`AccMono` presence prims | `AccPresent`, `AccMono`, `find?_some_ne_empty`, `accMono_*` | Engine-reusable | load-bearing | Clean leaf; exp003-ready as-is |
| `BytecodeLayer/Hoare/StepWalk.lean` | 1336 | The ONE per-opcode `.next` dispatch walk: env-equality + account presence mono | `stepFrame_next_accMono`, `stepFrame_next_self`, `stepFrame_next_execEnvAddr`, `stepFrame_halted_success_accMono` | Engine-reusable | load-bearing | Biggest file in cluster; pure opcode induction — no split needed, but the single load-bearing frame-level export is `stepFrame_next_*` |
| `BytecodeLayer/Hoare/Descent.lean` | 570 | CALL/CREATE descent structural facts + `DescentKind` interface | `DescentKind`, `callDescent`, `createDescent`, `*_needsCall/Create_inv`, `beginCall_inl_*` | Engine-reusable | load-bearing | `DescentKind` uniform packaging is nice; CREATE arms are dead-scope for IR (lowering emits no CREATE) but reusable for exp003 |
| `BytecodeLayer/Hoare/DriveMono.lean` | 294 | Account presence monotone across a whole `drive` run (Brick D) | `DrivePresent`, `drive_accounts_find_mono`, `endFrame_*_accPresent` | Engine-reusable | load-bearing | Sole consumer is `CallPreservesSelf`; clean |
| `BytecodeLayer/Hoare/Sequence.lean` (charge fold section) | integrated | `subCharges` snoc/append fold algebra | `subCharges_snoc`, `subCharges_append` | Engine-reusable | support | The two lemmas now live beside `subCharges`; sole downstream consumer is `MaterialiseGas` |
| `BytecodeLayer/Hoare/MemAlgebra.lean` | 996 | EVM memory read/write/slot-window algebra (mstore/mload/copySlice) | `mstore_mload_disjoint`, `mstore_preserves_slot`, `readWithPadding_*`, `writeWord_*` | Engine-reusable | load-bearing | Large but self-contained byte-array/memory theory; ideal exp003 graduate |
| `BytecodeLayer/Hoare/CleanHalt.lean` | 103 | Clean-halt scope predicates `CleanHalts` / `CleanHaltsNonException` + forward closure | `CleanHalts`, `CleanHaltsNonException`, `cleanHaltsNonException_forward` | Engine-reusable | load-bearing | Sits upstream of BOTH proof stacks; keep as leaf |
| `BytecodeLayer/Hoare/DriveRuns.lean` | 369 | Reconstruct halting `Runs` from a clean-terminating `drive` (reverse of `Runs→drive`) | `runs_of_drive_ok`, `ModellableStep`, `drive_descend_lt`, `child_terminates` | Engine-reusable | load-bearing | The `drive→Runs` bridge feeding Lir.Modellable + DriveSim |
| `Law.lean` | 172 | Frame-free IR-run **determinism** (EvalStmt→RunStmts→RunFrom→IRRun) | `EvalStmt.det`, `RunStmts.det`, `RunFrom.det`, `IRRun.det` | V2-spine | load-bearing | Frame-free bottom; gas-monotone law already deleted. Minimal |
| `IRRun.lean` | 371 | Frame-free IR-run **existence** (call-free/gas-free, acyclic via `CFGAcyclic`) | `irRun_exists`, `runFrom_exists`, `CFGAcyclic`, `RunDefinable`, `*_exists_*` | V2-spine | support | `CFGAcyclic` acyclic-rank construction is SUPERSEDED by DriveSim's `totalGas` measure. Existence-half is parked scaffolding; candidate to prune once flagship stops needing existence |
| `Decode/Modellable.lean` | 483 | Discharge `ModellableStep` over `lower prog` (no-CREATE structural + `CallsCode` residual) | `modellable_of_runs`, `ModellableStep` (re-exp), `NotCreate`, `CallsCode`, `AtReachableBoundary` | V2-spine | load-bearing | Turns a raw supplied universal into a proved producing lemma; genuinely load-bearing seam reducer |
| `Call.lean` | 145 | Worked single external `Stmt.call` example (consumed CallStream head) | `callBlock`, `callIR`, `call_IRRun`, `call_IRRun_unique` | V2-spine | support | A worked *example*, not a general lemma. Recently reworked for CallStream. Illustrative — could move to a `demos/` cluster |
| `CallRealises.lean` | 146 | Call/create realisability bridges: abstract stream entries = lowered observables | `callRealises_bridge`, `createRealises_bridge` | V2-spine | load-bearing | The entry projections live with their recorder consumers in `Spec/Recorder.lean` |
| `DriveSim.lean` | 743 | Cyclic-CFG forward sim: `totalGas`-measured drive recursion → `lower_conforms_cyclic` | `DriveCorr`, `drive_step_block_{stop,ret,jump,branch}`, `DriveStep`, `runFrom_of_driveCorr`, `lower_conforms_cyclic'` | Drive-cyclic | support (parked) | The cyclic spine's F1–F3. Green + axiom-clean, but its capstone `lower_conforms_cyclic'` is NOT invoked by the flagship (only Headline+Audit import it); it is the roadmap's intended run-producer. **Imports LowerConforms — see gate §3** |
| `Drive/SelfPresent.lean` | 437 | Recorder/IR value-channel discharges (CALL/GAS/SLOAD align) + `SelfPresent` | `SelfPresent`, `accounts_ne_empty_of_selfPresent`, `resumeAfterCall_self_of_accounts`, `GasLogAligned`, `SloadLogAligned`, `gasRealises_obs_of_witness` | Drive-cyclic | load-bearing | `SelfPresent` + `accounts_ne_empty_of_selfPresent` are actively used by the flagship. Mixed bag (§1–§5 of old monolith) — the GAS/SLOAD alignment half may be parked |
| `Drive/CallPreservesSelf.lean` | 258 | `SelfPresent` forward-closed along `Runs`; reduces to lone `hprec` seam | `CallPreservesSelf`, `stepPreservesSelf`, `callPreservesSelf`, `selfPresent_runs`, `selfPresent_runs_of_call` | Drive-cyclic | load-bearing | `selfPresent_runs_of_call` actively used by flagship + surfaced through `Spec/Seams.lean` |
| `Drive/Headline.lean` | 298 | `DriveCorrPlus` alignment/presence carrier + §7/§8 value/gas channels | `DriveCorrPlus`, `driveCorrPlus_sload_value*`, `GasReach`, `GasCursorClass`, `FramesRun.snoc_seed` | Drive-cyclic | vestigial (parked) | Own header: §9/§10 headlines DELETED as vacuous; carrier "RETAINED as green machinery... currently unreferenced". Flagship replaced `DriveCorrPlus` with its own `DriveCorrLog`. Strongest deletion/quarantine candidate in cluster |

## 2. Dependency sub-DAG (within cluster)

```
BytecodeLayer/Hoare/AccountMap ──> BytecodeLayer/Hoare/StepWalk ──> BytecodeLayer/Hoare/Descent ──> BytecodeLayer/Hoare/DriveMono
                             │                                      │
BytecodeLayer/Hoare/CleanHalt (leaf, feeds BOTH stacks)                         │
BytecodeLayer/Hoare/MemAlgebra (leaf)                                           │
BytecodeLayer/Hoare/Sequence (shared charge fold)                              │
BytecodeLayer/Hoare/DriveRuns (uses CallSequence) ──┐                          │
                                       │                          │
Spec.Semantics ─> Law ─> IRRun ──┤                          │
                     └─────> Call ─> CallRealises            │
                                       │                          │
   BytecodeLayer/Hoare/DriveRuns + NoCreateBytes ─> Decode/Modellable ─┐           │
                                       │              │           │
   LowerConforms (ACYCLIC STACK) ──────┴──────────────┴─> DriveSim
                                                              │
   RecorderLemmas+MaterialiseRuns+AccountMap ─> Drive/SelfPresent
                                                              │
                              SelfPresent + DriveMono ─> Drive/CallPreservesSelf
                                                              │
                              DriveSim + CallPreservesSelf ─> Drive/Headline
                                                              │
                                    (all of the above) ─> RealisabilitySpec  [WIP flagship, sole sorry-carrier]
```

Two internal chains: (a) the **Engine opcode tower** `AccountMap→StepWalk→Descent→DriveMono`
(pure, IR-free); (b) the **V2 frame-free spine** `Law→IRRun`/`Call→CallRealises`. The **Drive**
files fan these together with the recorder into the flagship. `BytecodeLayer/Hoare/CleanHalt`, `MemAlgebra`,
`Charges` are independent leaves.

## 3. THE DRIVESIM→LOWERCONFORMS GATE

**What DriveSim borrows.** `DriveSim.lean:1` imports `LirLean.LowerConforms`. Auditing every
LowerConforms-origin identifier DriveSim actually invokes as a proof term, only **two names
originate in `LowerConforms.lean` itself**:

- **`sim_cfg`** (`LowerConforms.lean:970`) — used at `DriveSim.lean:648` (also referenced 607/610/619/622/635/647). This is the CFG world-equation extractor: **induction on a *given* `Lir.RunFrom`**, consuming `SimStmtStep`/`SimTermStep` ties + `Corr` + `CleanHaltsNonException`, producing `Runs fr last ∧ … world = O.world`. Its own docstring calls it **cycle-agnostic** — it walks a supplied run and does no termination/acyclicity reasoning.
- **`SimTermStep`** (`LowerConforms.lean:96`) — the per-terminator tie structure, appears in the signature of `lower_conforms_cyclic`/`'` (`DriveSim.lean:57,639,681`).

**Everything else DriveSim uses is transitive, not from `LowerConforms.lean`:** `Corr`
(`SimStmt.lean:103`), `sim_stmts_block` (`SimStmts.lean:149`), `corr_at_jumpdest_landing`
(`SimTerm.lean:498`), `sim_term_halt_stop/ret`, `sim_term_edge_jump/branch` (`SimTerm.lean`).
These reach DriveSim through `LowerConforms → LowerDecode → {SimStmt, SimStmts, SimTerm}`.

**Crucially, DriveSim does NOT use `lower_conforms` (the acyclic capstone, `LowerConforms.lean:1188`),
nor `WellFormedLowered`, nor `entry_corr`.** Those are exactly what `Acyclic.lean` consumes. So the
lead's target (delete `Acyclic` + `LowerConforms`) does **not** require any acyclic-capstone logic
to survive for DriveSim — only `sim_cfg` + `SimTermStep`.

**Rewiring size: SMALL–MEDIUM.** Extract `sim_cfg` + `SimTermStep` (and the tiny `codeFrame_*`
helpers at `LowerConforms.lean:1057–1089` if DriveSim's callers need them — DriveSim itself does not)
into a new leaf module, e.g. `LirLean/SimCFG.lean`, importing `LowerDecode` (which already
transitively supplies `Corr`, `sim_stmts_block`, `corr_at_jumpdest_landing`, `sim_term_*` and
`CleanHaltsNonException`). `sim_cfg`'s body depends only on `sim_stmts_block`, `SimTermStep.halt/.edge`,
and `cleanHaltsNonException_forward` — all available at that altitude, with **no reference to the
acyclic capstone**. Then repoint `DriveSim.lean:1` at the new module. This is a mechanical
lift-and-shift of ~one structure + one theorem; the acyclic `lower_conforms` and `Acyclic.lean` can
then be deleted independently. Estimate: **medium** only because `LowerConforms.lean` is 1260 lines
and the extraction must carry the `SimStmtStep`/`SimTermStep` framing docstrings cleanly; the proof
logic move itself is small and low-risk.

## 4. "V2" vs "Drive" vs "Engine" naming clarification

The three names are **altitude layers**, not feature groups:

- **`Engine/`** = *IR-agnostic, frame-level EVM reasoning*. Zero IR, zero recorder, zero
  `SelfPresent` (every header states this verbatim). It is pure exp003-style theory about
  `stepFrame`/`drive`/`Runs`/memory/account-maps. It was extracted verbatim from the former
  `TieDischarge.lean` monolith and is **explicitly slated to graduate to exp003** ("exp003
  promotion is post-Phase-3", `AccountMap.lean` header). **Assessment: yes, it is a clean reusable
  sublayer** — self-describing headers, no upward (IR) dependencies, all axiom-clean. The only
  friction points are `Descent.lean`'s CREATE arms (dead-scope for the CREATE-free IR but reusable
  for exp003). Nothing in `Engine/` imports anything from
  ``, confirming the layering is genuinely one-directional and graduation-ready.

- **``** (Law, IRRun, Call, CallRealises, Modellable, DriveSim) = the *gas-free IR semantics
  spine*. `V2` is the "design-v3" IR model. Its **frame-free floor** (`Law`, `IRRun`, `Call`) imports
  only `Spec.Semantics`/`Machine`/`IR`/`Evm` — no `Frame`, no `Runs`. The **bytecode-coupled** V2
  files (`CallRealises`, `Modellable`, `DriveSim`) then bridge that spine to the interpreter.

- **`Drive/`** = the *cyclic bytecode-drive simulation + its recorder-fed channel discharges*.
  This is **not** a separate semantics; it is the layer that walks the actual bytecode `drive`
  recursion (`DriveCorr`/`DriveCorrPlus` boundary invariants) and discharges the value/gas/self
  channels from the recording. So: **V2 = the IR spine; Drive = the interpreter-drive walk that
  simulates that spine.** The naming confusion is understandable because `DriveSim.lean` lives
  directly under `` (not `Drive/`) despite being the drive layer's engine — it is the shared
  cyclic-construction core that both `Drive/Headline` and `Audit` sit on. A cleaner name would put
  `DriveSim.lean` under `Drive/` (e.g. `Drive/Sim.lean`) so the whole cyclic-drive layer is one
  directory, leaving `` for the frame-free-plus-realisability spine.

## 5. SIMPLIFICATION OPPORTUNITIES (ranked)

1. **Unblock the Acyclic/LowerConforms deletion (the gate).** Lift `sim_cfg` + `SimTermStep` out of
   `LowerConforms.lean` into a new `SimCFG.lean` importing `LowerDecode`; repoint `DriveSim.lean:1`.
   This is the single change that frees the lead to delete `Acyclic` + the `lower_conforms` acyclic
   capstone. Small–medium, low-risk (§3).

2. **Quarantine or delete `Drive/Headline.lean`.** Its own header says the headlines were removed
   as vacuous and the `DriveCorrPlus` carrier + §7/§8 lemmas are "RETAINED... currently unreferenced
   in the default build." The flagship replaced `DriveCorrPlus` with its own `DriveCorrLog`
   (`RealisabilitySpec.lean:629`) and references `DriveCorrPlus`/`lower_conforms_cyclic_assembled`
   only in roadmap comments (lines 25, 612, 3730). If the R0 reshape will genuinely reuse the §7/§8
   value/gas lemmas, keep only those and drop the `DriveCorrPlus` carrier; otherwise delete the file.

3. **Prune `IRRun.lean`'s acyclic existence machinery.** `CFGAcyclic`/`runFrom_exists`/
   `irRun_exists` build IR runs by a *static* block-rank that DriveSim's `totalGas` measure
   supersedes (DriveSim header: "`CFGAcyclic` retired"). Determine whether the flagship still needs
   the existence half at all; if the run-producer is now `runFrom_of_driveCorr`, IRRun's existence
   theorems are parked scaffolding.

4. **Rename for layer clarity.** Move `DriveSim.lean` under `Drive/` so the cyclic-drive layer is
   one directory; this resolves the V2-vs-Drive confusion (§4).

5. **LANDED:** the two charge-fold lemmas were folded into `BytecodeLayer/Hoare/Sequence.lean`,
   beside the `subCharges` definition they characterize.

6. **Graduate `Engine/` to exp003 when ready.** `MemAlgebra`, `AccountMap`, `StepWalk`, `Descent`,
   `DriveMono`, `CleanHalt`, `DriveRuns` form a clean IR-agnostic sublayer with no upward deps —
   the promotion the headers already anticipate.
