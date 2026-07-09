# Fleet audit 2026-07-04 — Cluster: Engine + V2 spine + Drive

> **P9 status note (2026-07-08).** This audit is historical where it discusses
> `Acyclic.lean`, `MatFueled`, `Expr.slot`, `materialiseExpr`, `recomputeFuel`, or
> `NoSlotSource`; those legacy routes/APIs have been deleted or superseded by
> `IRWellFormed` plus `codeFits`/`stackFits`.

Scope: the IR-agnostic EVM reasoning **Engine/**, the gas-free frame-free **V2 spine**, and the
cyclic-CFG **V2/Drive** layer. 17 files. No `.lean` file was modified.

## 1. File table

| File | LOC | One-line purpose | Key exports | Layer | Verdict | Simplification note |
|---|---|---|---|---|---|---|
| `Engine/AccountMap.lean` | 145 | Pure `Evm.AccountMap` non-emptiness + `AccPresent`/`AccMono` presence prims | `AccPresent`, `AccMono`, `find?_some_ne_empty`, `accMono_*` | Engine-reusable | load-bearing | Clean leaf; exp003-ready as-is |
| `Engine/StepWalk.lean` | 1336 | The ONE per-opcode `.next` dispatch walk: env-equality + account presence mono | `stepFrame_next_accMono`, `stepFrame_next_self`, `stepFrame_next_execEnvAddr`, `stepFrame_halted_success_accMono` | Engine-reusable | load-bearing | Biggest file in cluster; pure opcode induction — no split needed, but the single load-bearing frame-level export is `stepFrame_next_*` |
| `Engine/Descent.lean` | 570 | CALL/CREATE descent structural facts + `DescentKind` interface | `DescentKind`, `callDescent`, `createDescent`, `*_needsCall/Create_inv`, `beginCall_inl_*` | Engine-reusable | load-bearing | `DescentKind` uniform packaging is nice; CREATE arms are dead-scope for IR (lowering emits no CREATE) but reusable for exp003 |
| `Engine/DriveMono.lean` | 294 | Account presence monotone across a whole `drive` run (Brick D) | `DrivePresent`, `drive_accounts_find_mono`, `endFrame_*_accPresent` | Engine-reusable | load-bearing | Sole consumer is `CallPreservesSelf`; clean |
| `Engine/Charges.lean` | 32 | `subCharges` snoc/append fold algebra | `subCharges_snoc`, `subCharges_append` | Engine-reusable | support | Trivial 2-lemma module; sole consumer `MaterialiseGas`. Could be inlined but harmless |
| `Engine/MemAlgebra.lean` | 996 | EVM memory read/write/slot-window algebra (mstore/mload/copySlice) | `mstore_mload_disjoint`, `mstore_preserves_slot`, `readWithPadding_*`, `writeWord_*` | Engine-reusable | load-bearing | Large but self-contained byte-array/memory theory; ideal exp003 graduate |
| `Engine/CleanHalt.lean` | 103 | Clean-halt scope predicates `CleanHalts` / `CleanHaltsNonException` + forward closure | `CleanHalts`, `CleanHaltsNonException`, `cleanHaltsNonException_forward` | Engine-reusable | load-bearing | Sits upstream of BOTH proof stacks; keep as leaf |
| `Engine/DriveRuns.lean` | 369 | Reconstruct halting `Runs` from a clean-terminating `drive` (reverse of `Runs→drive`) | `runs_of_drive_ok`, `ModellableStep`, `drive_descend_lt`, `child_terminates` | Engine-reusable | load-bearing | The `drive→Runs` bridge feeding V2.Modellable + DriveSim |
| `V2/Law.lean` | 172 | Frame-free IR-run **determinism** (EvalStmt→RunStmts→RunFrom→IRRun) | `EvalStmt.det`, `RunStmts.det`, `RunFrom.det`, `IRRun.det` | V2-spine | load-bearing | Frame-free bottom; gas-monotone law already deleted. Minimal |
| `V2/IRRun.lean` | 371 | Frame-free IR-run **existence** (call-free/gas-free, acyclic via `CFGAcyclic`) | `irRun_exists`, `runFrom_exists`, `CFGAcyclic`, `RunDefinable`, `*_exists_*` | V2-spine | support | `CFGAcyclic` acyclic-rank construction is SUPERSEDED by DriveSim's `totalGas` measure. Existence-half is parked scaffolding; candidate to prune once flagship stops needing existence |
| `V2/Modellable.lean` | 483 | Discharge `ModellableStep` over `lower prog` (no-CREATE structural + `CallsCode` residual) | `lower_modellable`, `ModellableStep` (re-exp), `NotCreate`, `CallsCode`, `AtReachableBoundary` | V2-spine | load-bearing | Turns a raw supplied universal into a proved producing lemma; genuinely load-bearing seam reducer |
| `V2/Call.lean` | 145 | Worked single external `Stmt.call` example (consumed CallStream head) | `callBlock`, `callIR`, `call_IRRun`, `call_IRRun_unique` | V2-spine | support | A worked *example*, not a general lemma. Recently reworked for CallStream. Illustrative — could move to a `demos/` cluster |
| `V2/CallRealises.lean` | 110 | Call realisability bridge: abstract CallStream entry = lowered CALL observable | `evmV2CallEntry`, `callRealises_bridge` | V2-spine | load-bearing | `evmV2CallEntry` consumed by SimStmt + Recorder + SelfPresent; the call-side analogue of the retired gas `Oracle` |
| `V2/DriveSim.lean` | 743 | Cyclic-CFG forward sim: `totalGas`-measured drive recursion → `lower_conforms_cyclic` | `DriveCorr`, `drive_step_block_{stop,ret,jump,branch}`, `DriveStep`, `runFrom_of_driveCorr`, `lower_conforms_cyclic'` | Drive-cyclic | support (parked) | The cyclic spine's F1–F3. Green + axiom-clean, but its capstone `lower_conforms_cyclic'` is NOT invoked by the flagship (only Headline+Audit import it); it is the roadmap's intended run-producer. **Imports LowerConforms — see gate §3** |
| `V2/Drive/SelfPresent.lean` | 437 | Recorder/IR value-channel discharges (CALL/GAS/SLOAD align) + `SelfPresent` | `SelfPresent`, `accounts_ne_empty_of_selfPresent`, `resumeAfterCall_self_of_accounts`, `GasLogAligned`, `SloadLogAligned`, `gasRealises_obs_of_witness` | Drive-cyclic | load-bearing | `SelfPresent` + `accounts_ne_empty_of_selfPresent` are actively used by the flagship. Mixed bag (§1–§5 of old monolith) — the GAS/SLOAD alignment half may be parked |
| `V2/Drive/CallPreservesSelf.lean` | 258 | `SelfPresent` forward-closed along `Runs`; reduces to lone `hprec` seam | `CallPreservesSelf`, `stepPreservesSelf`, `callPreservesSelf`, `selfPresent_runs`, `selfPresent_runs_of_call` | Drive-cyclic | load-bearing | `selfPresent_runs_of_call` actively used by flagship + surfaced through `Spec/Seams.lean` |
| `V2/Drive/Headline.lean` | 298 | `DriveCorrPlus` alignment/presence carrier + §7/§8 value/gas channels | `DriveCorrPlus`, `driveCorrPlus_sload_value*`, `GasReach`, `GasCursorClass`, `FramesRun.snoc_seed` | Drive-cyclic | vestigial (parked) | Own header: §9/§10 headlines DELETED as vacuous; carrier "RETAINED as green machinery... currently unreferenced". Flagship replaced `DriveCorrPlus` with its own `DriveCorrLog`. Strongest deletion/quarantine candidate in cluster |

## 2. Dependency sub-DAG (within cluster)

```
Engine/AccountMap ──> Engine/StepWalk ──> Engine/Descent ──> Engine/DriveMono
                             │                                      │
Engine/CleanHalt (leaf, feeds BOTH stacks)                         │
Engine/MemAlgebra (leaf)                                           │
Engine/Charges  (leaf)                                            │
Engine/DriveRuns (uses CallSequence) ──┐                          │
                                       │                          │
Spec.Semantics ─> V2/Law ─> V2/IRRun ──┤                          │
                     └─────> V2/Call ─> V2/CallRealises            │
                                       │                          │
   Engine/DriveRuns + NoCreateBytes ─> V2/Modellable ─┐           │
                                       │              │           │
   LowerConforms (ACYCLIC STACK) ──────┴──────────────┴─> V2/DriveSim
                                                              │
   RecorderLemmas+MaterialiseRuns+AccountMap ─> V2/Drive/SelfPresent
                                                              │
                              SelfPresent + DriveMono ─> V2/Drive/CallPreservesSelf
                                                              │
                              DriveSim + CallPreservesSelf ─> V2/Drive/Headline
                                                              │
                                    (all of the above) ─> V2/RealisabilitySpec  [WIP flagship, sole sorry-carrier]
```

Two internal chains: (a) the **Engine opcode tower** `AccountMap→StepWalk→Descent→DriveMono`
(pure, IR-free); (b) the **V2 frame-free spine** `Law→IRRun`/`Call→CallRealises`. The **Drive**
files fan these together with the recorder into the flagship. `Engine/CleanHalt`, `MemAlgebra`,
`Charges` are independent leaves.

## 3. THE DRIVESIM→LOWERCONFORMS GATE

**What DriveSim borrows.** `DriveSim.lean:1` imports `LirLean.LowerConforms`. Auditing every
LowerConforms-origin identifier DriveSim actually invokes as a proof term, only **two names
originate in `LowerConforms.lean` itself**:

- **`sim_cfg`** (`LowerConforms.lean:970`) — used at `DriveSim.lean:648` (also referenced 607/610/619/622/635/647). This is the CFG world-equation extractor: **induction on a *given* `V2.RunFrom`**, consuming `SimStmtStep`/`SimTermStep` ties + `Corr` + `CleanHaltsNonException`, producing `Runs fr last ∧ … world = O.world`. Its own docstring calls it **cycle-agnostic** — it walks a supplied run and does no termination/acyclicity reasoning.
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
into a new leaf module, e.g. `LirLean/V2/SimCFG.lean`, importing `LowerDecode` (which already
transitively supplies `Corr`, `sim_stmts_block`, `corr_at_jumpdest_landing`, `sim_term_*` and
`CleanHaltsNonException`). `sim_cfg`'s body depends only on `sim_stmts_block`, `SimTermStep.halt/.edge`,
and `cleanHaltsNonException_forward` — all available at that altitude, with **no reference to the
acyclic capstone**. Then repoint `DriveSim.lean:1` at the new module. This is a mechanical
lift-and-shift of ~one structure + one theorem; the acyclic `lower_conforms` and `Acyclic.lean` can
then be deleted independently. Estimate: **medium** only because `LowerConforms.lean` is 1260 lines
and the extraction must carry the `SimStmtStep`/`SimTermStep` framing docstrings cleanly; the proof
logic move itself is small and low-risk.

## 4. "V2" vs "V2/Drive" vs "Engine" naming clarification

The three names are **altitude layers**, not feature groups:

- **`Engine/`** = *IR-agnostic, frame-level EVM reasoning*. Zero IR, zero recorder, zero
  `SelfPresent` (every header states this verbatim). It is pure exp003-style theory about
  `stepFrame`/`drive`/`Runs`/memory/account-maps. It was extracted verbatim from the former
  `V2/TieDischarge.lean` monolith and is **explicitly slated to graduate to exp003** ("exp003
  promotion is post-Phase-3", `AccountMap.lean` header). **Assessment: yes, it is a clean reusable
  sublayer** — self-describing headers, no upward (IR) dependencies, all axiom-clean. The only
  friction points are `Descent.lean`'s CREATE arms (dead-scope for the CREATE-free IR but reusable
  for exp003) and `Charges.lean` being a 2-lemma stub. Nothing in `Engine/` imports anything from
  `V2/`, confirming the layering is genuinely one-directional and graduation-ready.

- **`V2/`** (Law, IRRun, Call, CallRealises, Modellable, DriveSim) = the *gas-free IR semantics
  spine*. `V2` is the "design-v3" IR model. Its **frame-free floor** (`Law`, `IRRun`, `Call`) imports
  only `Spec.Semantics`/`Machine`/`IR`/`Evm` — no `Frame`, no `Runs`. The **bytecode-coupled** V2
  files (`CallRealises`, `Modellable`, `DriveSim`) then bridge that spine to the interpreter.

- **`V2/Drive/`** = the *cyclic bytecode-drive simulation + its recorder-fed channel discharges*.
  This is **not** a separate semantics; it is the layer that walks the actual bytecode `drive`
  recursion (`DriveCorr`/`DriveCorrPlus` boundary invariants) and discharges the value/gas/self
  channels from the recording. So: **V2 = the IR spine; V2/Drive = the interpreter-drive walk that
  simulates that spine.** The naming confusion is understandable because `DriveSim.lean` lives
  directly under `V2/` (not `V2/Drive/`) despite being the drive layer's engine — it is the shared
  cyclic-construction core that both `V2/Drive/Headline` and `Audit` sit on. A cleaner name would put
  `DriveSim.lean` under `V2/Drive/` (e.g. `V2/Drive/Sim.lean`) so the whole cyclic-drive layer is one
  directory, leaving `V2/` for the frame-free-plus-realisability spine.

## 5. SIMPLIFICATION OPPORTUNITIES (ranked)

1. **Unblock the Acyclic/LowerConforms deletion (the gate).** Lift `sim_cfg` + `SimTermStep` out of
   `LowerConforms.lean` into a new `V2/SimCFG.lean` importing `LowerDecode`; repoint `DriveSim.lean:1`.
   This is the single change that frees the lead to delete `Acyclic` + the `lower_conforms` acyclic
   capstone. Small–medium, low-risk (§3).

2. **Quarantine or delete `V2/Drive/Headline.lean`.** Its own header says the headlines were removed
   as vacuous and the `DriveCorrPlus` carrier + §7/§8 lemmas are "RETAINED... currently unreferenced
   in the default build." The flagship replaced `DriveCorrPlus` with its own `DriveCorrLog`
   (`RealisabilitySpec.lean:629`) and references `DriveCorrPlus`/`lower_conforms_cyclic_assembled`
   only in roadmap comments (lines 25, 612, 3730). If the R0 reshape will genuinely reuse the §7/§8
   value/gas lemmas, keep only those and drop the `DriveCorrPlus` carrier; otherwise delete the file.

3. **Prune `V2/IRRun.lean`'s acyclic existence machinery.** `CFGAcyclic`/`runFrom_exists`/
   `irRun_exists` build IR runs by a *static* block-rank that DriveSim's `totalGas` measure
   supersedes (DriveSim header: "`CFGAcyclic` retired"). Determine whether the flagship still needs
   the existence half at all; if the run-producer is now `runFrom_of_driveCorr`, IRRun's existence
   theorems are parked scaffolding.

4. **Rename for layer clarity.** Move `DriveSim.lean` under `V2/Drive/` so the cyclic-drive layer is
   one directory; this resolves the V2-vs-V2/Drive confusion (§4).

5. **Fold `Engine/Charges.lean` (2 lemmas, 32 LOC) into `MaterialiseGas` or a shared `Engine` prelude**
   — its own module earns little. Low priority / cosmetic.

6. **Graduate `Engine/` to exp003 when ready.** `MemAlgebra`, `AccountMap`, `StepWalk`, `Descent`,
   `DriveMono`, `CleanHalt`, `DriveRuns` form a clean IR-agnostic sublayer with no upward deps —
   the promotion the headers already anticipate.
