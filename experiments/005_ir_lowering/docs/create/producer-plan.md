# The coupled run-producer `runFrom_of_driveCorrLog` — proof plan

Date: 2026-07-05. Worktree `.worktrees/producer`, branch `exp005-producer`.
Skeleton: `LirLean/Realisability/Producer.lean` (WIP lib; `lake build WIP` green;
default `LirLean` stays green + sorry-free).

This is the terminal R11 obligation of the whole experiment: the coupled run-producer the
flagship `lower_conforms` (`RealisabilitySpec.lean:240-248`) and its
`lower_conforms_exact`/`lower_conforms_gasfree` siblings `obtain`. It is documented verbatim
at `RealisabilitySpec.lean:224-248` as "THE BLOCKER (Route-A, NOT a citable leaf)".

## 0. Why it is NOT assembly over citable leaves (the two verbatim reasons)

* **(a) unconditional `SimStmtStep` is unsatisfiable under the reshape.** The only in-tree
  run-producer `lower_conforms_cyclic'` (`Drive/DriveSim.lean:672`) consumes an
  ALL-FRAMES, coupling-free `SimStmtStep` (`Sim/SimStmts.lean:66`): for ANY `EvalStmt` at any
  `Corr` frame it must yield a `Runs` re-establishing `Corr`. The reshaped `StmtTies'`
  (`Surface.lean:640`) concludes its arms ONLY under the load-bearing `RecorderCoupled`
  antecedent (target-architecture §3). The coupling-free path is exactly the vacuity the
  reshape exists to kill (header lessons 1–3). So the producer CANNOT factor through
  `SimStmtStep`/`DriveStep`/`runFrom_of_driveCorr`. It runs its OWN walk carrying
  `DriveCorrLog` (which BUNDLES `RecorderCoupled`) and fires the Layer-C sim bricks ONLY at
  the coupled walk frames — the `simStmt_coupled_*` family (§2 of the skeleton).
* **(b) R6 `runs_atReachableBoundary` cannot supply `hrb` alone.** Its B2 side condition
  `(flatBytes prog).length ≤ 2 ^ 32` (`Machinery.lean:1509`) has NO producer from `hwl` — no
  `WellFormedLowered` field asserts it, only per-cursor bounds. It is threaded as an explicit
  honest seam `hsize`. R6 additionally carries three pure-engine geometry `sorry` bricks in
  DEFAULT-target files (outside this track's edit surface).

## 1. Induction measure + invariant bundle + base/step

* **Measure**: the dynamic bytecode `totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat`
  (`driveCorr_measure`), which strictly descends per block (`totalGas_succ_lt`, via the
  leading `JUMPDEST`'s `Gjumpdest = 1` charge). Well-founded regardless of CFG cycles — the
  same measure F2 uses; loops are fine.
* **Invariant bundle carried across the step** = `DriveCorrLog prog sloadChg log self st fr L
  gS sS cS` (`Surface.lean:559`) PLUS `StreamsAligned self log gS cS T C D` (new, §0 of the
  skeleton). `DriveCorrLog` bundles: `Corr` at `(L,0)`; `CleanHaltsNonException`; block
  `present`; `SelfPresent`; `addrPin`/`kindPin`; and `coupled : RecorderCoupled log fr gS sS
  cS` (the un-consumed recorder suffixes). `StreamsAligned` is the positional bridge: at every
  coupled boundary the IR streams `(T,C,D)` are exactly the realised image of the suffixes —
  `T = gS`, `C = callStreamOf cS self`, `D = createStreamOf log.creates self` (create pinned
  WHOLE; the walk consumes no create until Step 8's `createSuffix` twin). This is what turns
  the whole `realisedGas`/`realisedCall`/`realisedCreate` at entry into the per-block
  head-consumption the IR `RunFrom` performs.
* **Step** (`driveLogStep_of_block`, P3b): at a coupled boundary run the block statements via
  the COUPLED block walk `simStmts_coupled_block` (P3a, which folds the per-statement
  `simStmt_coupled_*` steps — each firing the matching `StmtTies'` arm with the coupling
  available and advancing the coupling suffix by exactly one R7 edge, consuming exactly the
  aligned stream head), then dispatch on `b.term` via `TermTies'`:
  - `stop`/`ret` → HALT: package `RunFromCoupled` (the terminal world+result equation +
    IR `RunFrom`) from the terminator world brick + the live `observe`-result inverse;
  - `jump`/`branch` → EDGE: the `jumpdestFrame fj` successor re-establishing `DriveCorrLog`
    at `succ` (coupling transported UNCHANGED across the JUMPDEST/JUMP/JUMPI edge —
    `recorderCoupled_stepsTo_other`; alignment unchanged), the strict `totalGas` descent, and
    the IR continuation (`RunFrom.jump`/`.branch*`).
* **Base case** = the halt disjunct of `DriveLogStep`: `RunFromCoupled` directly.
* **Recursion** (`runFrom_of_driveCorrLog_rec`, P4): strong induction on `totalGas`; halt =
  base, edge = recurse at the smaller successor + prepend via the IR continuation and
  `Runs.trans` (lifting the successor's bytecode halt terminal back to `fr`). Structural mirror
  of `runFrom_of_driveCorr` (F2).
* **Top** (`runFrom_of_driveCorrLog`, R11): entry seed (P1a/P1b) → P4 → the packaged
  existential; `hcr` from P6; the ties per boundary from R10a/R10b (`stmtTies'_of_runWithLog`
  / `termTies'_of_runWithLog`).

## 2. How the two documented gaps are legitimately supplied

* **(a) the unconditional-`SimStmtStep` gap** is supplied by REPLACING it, not discharging it:
  the coupled block walk `simStmts_coupled_block` never asks for a coupling-free per-statement
  step. Every per-statement step (`simStmt_coupled_{assignPure,gas,sload,sstore,call}`) fires
  its sim brick UNDER the `RecorderCoupled` antecedent that `StmtTies'` requires and that the
  walk invariant supplies. Legitimate: no statement weakening, no false hypothesis — the
  coupling is a genuine invariant established at entry (`recorderCoupled_entry`) and preserved
  by the R7 edges.
* **(b) the 2^32 bound** is a NEW HONEST SEAM, not a derivation. It is a real
  well-formedness fact of every emitted program (offsets are 4-byte `PUSH4`, so real programs
  fit the 32-bit address space — the same bound the per-cursor `WellFormedLowered.bound_*`
  fields assert), but it is not entailed by the current `hwl`. Decision (see §4): add a
  `sizeBound` field to `WellLowered`/`WellFormedLowered`, OR thread `hsize` as a flagship seam.
  The skeleton threads it explicitly (`hsize`) so the producer is honest today.

## 3. Sub-lemma ledger (see the skeleton for exact statements)

Ranked leaf-most / most tractable first. `now` = closeable with in-tree green bricks;
`hard` = substantial new proof; `blocked-on-decision` = needs a lead decision or a
default-target (out-of-track) brick.

1. `streamsAligned_entry` — now (near-`rfl`).
2. `createResolves_reachable` (P6) — trivial from the seam, but the SEAM WIRING is a decision
   → blocked-on-decision.
3. `driveCorrLog_entry` (P1b) — now (assembly of `entry_corr`, `cleanHalts_of_runWithLog`,
   `ClosedCFG.entry_present`, `selfPresent_codeFrame`, `recorderCoupled_entry`).
4. `simStmt_coupled_assignPure` — now (simplest arm; `sim_assign` pure + R7d).
5. `simStmt_coupled_sstore` — hard (needs R4 `sstoreRealises_at_frame` + `sim_sstore_stmt`).
6. `simStmt_coupled_gas` — hard (R1 `gas_suffix_head_realised` + gas sim brick + R7b).
7. `simStmt_coupled_sload` — hard (sload sim brick + R7c).
8. `simStmt_coupled_call` — hard, Piece-B-gated (R3 `callRealises_of_recorded` is `sorry`;
   the `materialise` CALL-arg-push driver has no in-tree producer; `resumeAfterCall` frame-pins
   may be a DEFAULT-target lemma → STOP-and-report).
9. `simStmts_coupled_block` (P3a) — hard (folds 4–8; self/addr/kind transport via
   `selfPresent_runs`/`runs_kind`).
10. `driveLogStep_of_block` (P3b) — hard (assembles P3a + terminator bricks + `DriveCorrLog`
    re-establishment; the halt arms extend `drive_step_block_*` to the RESULT channel).
11. `runFrom_of_driveCorrLog_rec` (P4) — hard (structural mirror of `runFrom_of_driveCorr`).
12. `boundaryWalk_of_wl` (P5, `hrb`) — blocked-on-decision (the `hsize` seam decision + three
    default-target engine bricks).
13. `runFrom_of_driveCorrLog` (R11) — hard (top-level assembly; closes once 1–12 land).

## 4. Open decisions for the lead

* **D1 — the `hsize` (2^32) seam.** Add a `WellLowered.sizeBound`/`WellFormedLowered` field
  (checker-dischargeable, R9), OR keep it a flagship seam. The producer currently threads it
  explicitly. Recommendation: a `WellLowered` field (it is a static, decidable program fact).
* **D2 — the create-resolves seam `hcr`.** `CreateResolves` is a genuine runtime residual
  (`Decode/Modellable.lean:413`), NOT structural. The flagship's `PrecompileAssumptions` currently
  has `noErase` + `callsCode` but no create-resolves face. Decision: add a `createResolves`
  field (`∀ fr', ReachableFrom params fr' → CreateResolves fr'`) to `PrecompileAssumptions`
  (the honest boundary structure) so `runFrom_of_driveCorrLog` needs no extra hypothesis. For
  the CALL flagship on create-free programs it is vacuous; the CREATE flagship needs it live.
* **D3 — R3 Piece B ownership.** The `materialise` CALL-arg-push run driver (~200 lines) and
  any `resumeAfterCall` bytecode-layer computation lemma: decide whether the latter lands in
  the DEFAULT exp005 target (out of this track) or is threaded as a pin. This gates
  `simStmt_coupled_call`, hence CALL non-vacuity.
* **D4 — wiring into the flagship.** Once P1–P6 land, replace the `sorry` blocker at
  `RealisabilitySpec.lean:247`/`:281` with `runFrom_of_driveCorrLog` (+ the R10 tie
  producers), threading D1/D2's fields. The output shape already matches the `obtain` verbatim.
