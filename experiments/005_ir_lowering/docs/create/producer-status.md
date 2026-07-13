# `runFrom_of_driveCorrLog` (R11) — STATUS / handoff

Date: 2026-07-05. Worktree: `.worktrees/producer`. Branch: `exp005-producer`.
Toolchain: `leanprover/lean4:v4.30.0`. Base: `main` HEAD `46e47f3`.
Skeleton: `LirLean/Realisability/Producer.lean` (WIP lib only).

Read alongside `docs/create/producer-plan.md` (the full proof plan),
`docs/create/STATUS.md` (the CREATE-build handoff — same R11 gate),
`docs/target-architecture-2026-07-02.md`, and the verbatim blocker at
`RealisabilitySpec.lean:224-248`.

## Headline — DID THE FLAGSHIP CLOSE? NO.

The terminal milestone `lower_conforms` (R11) has **NOT** closed. The coupled
run-producer `runFrom_of_driveCorrLog` (`Producer.lean:707`) is still `sorry`:
its assembly rests on the P3a/P3b/P4 recursion and 4 of the 5 `simStmt_coupled_*`
sim arms, none of which can close honestly today (see BLOCKED, below). No
mergeable flagship commit exists. What landed this run is real, green, tracked
progress on the leaf-most seeds — not the headline.

## Build state at HEAD (`14c73c2`) — verified this run

| Lib | Command | Result | Sorries |
|-----|---------|--------|---------|
| default `LirLean` | `lake build` | green, **1172 jobs, SORRY-FREE** | 0 |
| `WIP` (flagship) | `lake build WIP` | green, **1173 jobs** | 21 (tracked) |

- Default cone verified sorry-free: **0** `declaration uses sorry` warnings in the
  `lake build` log; **no** default-cone module imports `LirLean.Realisability`
  (grep-confirmed). The debt is quarantined to the WIP cone.
- WIP tracked-sorry ledger (21 = 12 pre-existing base + 9 open Producer leaves):
  - `RealisabilitySpec.lean` — 6: `:134` (StmtTies'), `:247`/`:281`/`:318`
    (the three flagship blockers), `:329` (gasfree companion), `:344`
    (`exProg_satisfies_hypotheses`).
  - `Machinery.lean` — 6: `:405` (R3 Piece B `callRealises_of_recorded` `fr0`),
    `:1381`/`:1389`/`:1418`/`:1421` (R6 pure-engine geometry bricks, DEFAULT-target),
    `:1454` (R6 CREATE edge `atReachableBoundaryVJ_create`).
  - `Producer.lean` — 9: gas `:468`, sload `:490`, sstore `:514`, call `:543`,
    P3a `:591`, P3b `:621`, P4 `:644`, P5 `:660`, R11 `:707`.

## Approach (induction measure + invariant bundle) — from `producer-plan.md`

- **Measure**: dynamic bytecode `totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat`,
  strictly descending per block via the leading `JUMPDEST`'s `Gjumpdest = 1` charge
  (`totalGas_succ_lt`); well-founded even for cyclic CFGs — the same measure F2 uses.
- **Invariant bundle carried across the step** = `DriveCorrLog prog sloadChg log self
  st fr L gS sS cS` (`Surface.lean:559`) PLUS the new positional bridge
  `StreamsAligned self log gS cS T C D` (`Producer.lean:74`). `DriveCorrLog` bundles
  `Corr` at `(L,0)`, `CleanHaltsNonException`, block `present`, `SelfPresent`,
  `addrPin`/`kindPin`, and the load-bearing `coupled : RecorderCoupled log fr gS sS cS`
  (the un-consumed recorder suffixes). `StreamsAligned` pins the IR streams to the
  realised image of those suffixes: `T = gS`, `C = callStreamOf cS self`,
  `D = createStreamOf log.creates self` (create pinned WHOLE). This is what turns the
  entry `realisedGas`/`realisedCall`/`realisedCreate` into the per-block head-consumption
  the IR `RunFrom` performs.
- **Why it is NOT assembly over citable leaves** (two verbatim reasons,
  `RealisabilitySpec.lean:231-237`): (a) the only in-tree run-producer
  `lower_conforms_cyclic'` needs an UNCONDITIONAL all-frames `SimStmtStep`, which the
  reshaped `StmtTies'` cannot supply (its arms conclude only under the `RecorderCoupled`
  antecedent — the coupling-free path is exactly the vacuity the reshape kills); so the
  producer runs its OWN coupled walk. (b) R6 `runs_atReachableBoundary` cannot produce
  `hrb` alone — its B2 side condition `(flatBytes prog).length ≤ 2^32` has no producer
  from `WellFormedLowered`; threaded as the honest seam `hsize`.

## Sub-lemmas CLOSED (green, committed) — genuinely sorry-free

| Lemma (loc) | Commit | Note |
|-------------|--------|------|
| `streamsAligned_entry` (P1a, `:137`) | `c38bb70` | near-`rfl` (`⟨rfl,rfl,rfl⟩`) |
| `driveCorrLog_entry` (P1b, `:167`) | `448d321` | entry coupled boundary; assembly of `corr_at_jumpdest_landing` + `cleanHalts_of_runWithLog` + `entry_present` + `selfPresent_codeFrame` + `recorderCoupled_entry`. Statement CORRECTED: returns the POST-`JUMPDEST` landing `fr₀'` + `Runs fr₀ fr₀'` (the codeFrame `pc=0` cannot meet `Corr.pc_eq = offsetTable+1`). |
| `simStmt_coupled_assignPure` (P2-assignPure, `:399`) | `4f52e8` (`4f52e83fd3f3f7a049159a5bfddca27e23457862`) | simplest arm; `sim_assign` pure + R7d; new private helpers `evalExpr_reads_bound` + `defsSound_setLocal_recomputable` (both real, no sorry). |
| `createResolves_reachable` (P6, `:667`) | `14c73c2` | trivial once the create-resolves seam is a hypothesis (`fun fr' hr => hseam fr' ⟨fr₀,hbegin,hr⟩`). |

Also REAL/no-sorry in the skeleton (definitions + helpers, not obligations):
`StreamsAligned`, `RunFromCoupled`, `DriveLogStep`, `CoupledAdvance`, `CoupledBlockRun`.

## Sub-lemmas BLOCKED — and exactly why

### `simStmt_coupled_sstore` (`:514`) — missing machinery, not a citable assembly
Coupling-transport across the multi-step SSTORE `Runs` is absent. To produce
`RecorderCoupled log fr' gS sS cS` at the post-SSTORE frame (`Producer.lean:123`) one
must fold a per-step NON-recording transport across
`materialise value ++ materialise key ++ [SSTORE]`. In-tree there are ONLY single-step
edges (`Machinery.lean:1546/1671/1709/1997`) and they are the wrong tool:
`recorderCoupled_step_other` needs `isGasOp fr = false` AND `isSloadOp fr = false`, but
`isGasOp`/`isSloadOp` (`Recorder.lean:131/144`) are pure DECODE predicates and
`materialise` emits GAS/SLOAD opcodes for recomputable operands
(`MatDecLower.lean:29/134/287/326`), so at intra-materialise GAS/SLOAD frames
`isGasOp = true` while the recorder records nothing (nonempty stack). A non-recording
GAS/SLOAD-at-nonempty-stack edge does not exist (R7b/R7c consume a head, empty-stack
only), the Runs-level fold does not exist, and the required per-frame materialise decode
geometry is explicitly deferred/unbuilt (`Machinery.lean:1993-1996`) and overlaps the
sorried DEFAULT-target R6 engine bricks (`Machinery.lean:1381/1389/1418/1421`) outside
this track. Building these is substantial new machinery (partly in default-target files)
that would itself need sorries → any close now is a forbidden sorry-scaffold.
Secondary: `sim_sstore_stmt`/`_lowered` require a whole-envelope `SstoreRealises fr kw vw
acc` with a FIXED `acc` over all frames (`SimStmt.lean:319/347`, `LowerDecode.lean:139`)
— the unsatisfiable conjunct; R4 (`Machinery.lean:416`) is only per-frame; re-plumb is
declared out of scope (`Machinery.lean:413-415`), inlinable in WIP but moot given the
primary blocker.

### `simStmt_coupled_gas` (`:468`) — FALSE as stated
Its conclusion `CoupledAdvance` forces the STRONG `Corr` at intra-block cursor `pc+1`
(`Producer.lean:121`), whose `defsSound` field is strong `DefsSound prog (st.setLocal t
obs0)`. On `exProg` block 1's loop-exit iteration this post-state is exactly `staleSt`
(`Witness.lean:214`), and `not_defsSound_stale` (`Witness.lean:229`, a PROVED theorem)
establishes `¬ DefsSound exProg staleSt`. The needed define-before-use clause (`StepScoped`'s
`.gas` live-scope conjunct, `DefsSound.lean:583-585`) that `sim_assign_gas_lowered`
requires (`LowerDecode.lean:721 → DefsSound.lean:345`) was deliberately dropped from
`StepScopedS` (`Surface.lean:291-295`), which is all the `StmtTies'` gas arm provides
(`Surface.lean:694`), and it is NOT derivable (`Corr.defsSound` does not pin the
`NonRecomputable` gas target's binding). This is the documented, NOT-YET-DONE Phase-3 R0
reshape: `Machinery.lean:69-90` says the current `Corr.defsSound` cannot traverse a
rebinding loop and that mid-block `Corr` must be swapped to `DefsSoundS`
(`Surface.lean:269`) with strong `DefsSound` re-established only at block boundaries.
Fixing it requires restating `CoupledAdvance` (`Producer.lean:114-124`) and the whole
`simStmt_coupled_*` family + `CoupledBlockRun` boundary (`Producer.lean:551`) with a
`DefsSoundS`-scoped mid-block `Corr` carrying the `invalStep` set — a **skeleton-wide
design change / lead decision**, not a within-lemma proof. Closing it would require
fake-closing (statement weakening or false-hypothesis vacuity), which the rules forbid.

### `simStmt_coupled_sload` (`:490`) — downstream of the same R0 reshape
Same `CoupledAdvance` strong-`Corr`-at-`pc+1` obstruction as `simStmt_coupled_gas` for
its rebinding target, plus the intra-`materialise` SLOAD decode/transport machinery the
sstore arm is missing. Not independently closeable.

### `simStmt_coupled_call` (`:543`) — genuine STOP-and-report (R3 Piece B)
Rests on R3 Piece B `callRealises_of_recorded` (`Machinery.lean:384/405`, `sorry`, no
in-tree producer): the `materialise` CALL-argument-push run driver (~200 lines) has no
producer, and the `resumeAfterCall` frame-pin is a DEFAULT-target bytecode-layer lemma
outside this track's edit surface (design decision D3 in `producer-plan.md`).

## Producer assembly status — still OPEN

`runFrom_of_driveCorrLog` (`:707`) requires:
- **P4** `runFrom_of_driveCorrLog_rec` (`:644`, the strong-`totalGas` recursion) →
- **P3b** `driveLogStep_of_block` (`:621`) → **P3a** `simStmts_coupled_block` (`:591`) →
- the **four blocked sim arms**: gas (`:468`), sload (`:490`), sstore (`:514`),
  call (`:543`).
- **P5** `boundaryWalk_of_wl` (`:660`) additionally awaits the `hsize`-seam decision
  (D1) + the 3 DEFAULT-target R6 engine bricks.

Only the entry seeds (P1a/P1b), one statement arm (assignPure), and P6 are ready. The
recursion and 4/5 sim arms remain, so honest assembly is impossible without
fake-closing.

## Exact next proof to attempt + design decisions the lead MUST make

The critical path is NOT a proof — it is a **design decision** (target-architecture
Phase-3 R0). Before any of gas/sload (and cleanly for P3a/P4) can close, the lead must
decide the mid-block `Corr` scoping:

- **D0 (blocking) — swap mid-block `Corr` to `DefsSoundS`.** Restate `CoupledAdvance`
  (`Producer.lean:114-124`), the whole `simStmt_coupled_*` family, and the
  `CoupledBlockRun` boundary (`:551`) with a `DefsSoundS`-scoped mid-block `Corr`
  carrying the `invalStep` set; re-establish strong `DefsSound` only at block boundaries
  (`Machinery.lean:69-90`). This is what makes `simStmt_coupled_gas` TRUE. Until this
  lands, that arm is false-as-stated.
- **D1 — the `hsize` (2^32) seam** (P5): add a `WellLowered.sizeBound` field
  (decidable, checker-dischargeable — recommended) OR keep it a flagship seam.
- **D2 — the create-resolves seam `hcr`** (P6): add a `createResolves` face to
  `PrecompileAssumptions` so R11 needs no extra hypothesis.
- **D3 — R3 Piece B ownership**: decide whether the `materialise` CALL-arg-push driver
  and `resumeAfterCall` pin land in the DEFAULT exp005 target (out of this track) or are
  threaded as pins. Gates `simStmt_coupled_call`, hence CALL non-vacuity.

After D0, the honest first proof to attempt is `simStmt_coupled_gas` under the
`DefsSoundS` restatement (it fires R1 `gas_suffix_head_realised` — green — +
`sim_assign_gas_lowered` + R7b, all in-tree once the strong-`Corr` obstruction is gone),
then `simStmt_coupled_sload` as its twin, then the intra-`materialise` decode/transport
machinery that sstore/sload/call all share.

## Branch / commit range / mergeable prefix

- Branch `exp005-producer`, **5 commits** ahead of base `46e47f3`:
  `0b83355` (skeleton), `c38bb70`, `448d321`, `4f52e83`, `14c73c2`.
- **Mergeable green prefix: the ENTIRE branch through HEAD `14c73c2`.** Default `LirLean`
  is green + sorry-free at HEAD; WIP is green carrying only tracked debt (21 sorries).
  Every closed sub-lemma was committed green and is genuinely sorry-free. No push
  performed (per rules).
