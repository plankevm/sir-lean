# P5 + P6 — the forward-from-real-run tie discharge (the tie-free headline)

> **SUPERSEDED (2026-07-03):** plan of record is `target-architecture-2026-07-02.md` + `execution-plan-2026-07-02.md`; the gas-law apparatus (Mono/Oracle/HonestGasTie) was deleted in Phase 2. The premise below that the §7 ties are "SUPPLIED-but-satisfiable" was later **refuted** — the supplied ties are unsatisfiable as stated (see the target-architecture doc); the realisability rebuild lives in `LirLean/RealisabilitySpec.lean` (R0–R12, non-default `Nightly` lib).
>
> **P9 status note (2026-07-08):** legacy value-channel names below (`Expr.slot`,
> `materialiseExpr`, `materialise`, `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`,
> `NoSlotSource`) are historical; current lowering uses the fold-based `Loc`/`matCache`
> channel.

**Status: planning (read-only recon done 2026-06-28, branch `ir-convergence`, baseline green +
axiom-clean `[propext, Classical.choice, Quot.sound]`).**

This plan turns the conformance headlines TIE-FREE. Today `Lir.lower_conforms`,
`Lir.lower_conforms_acyclic_cfg`, `Lir.lower_conforms_cyclic` / `lower_conforms_cyclic'` are
non-vacuous and sound but conditioned on SUPPLIED-but-satisfiable per-cursor §7 ties. **P5**
PRODUCES every such tie from the actual `lower prog` execution + the recording interpreter
(`runWithLog`/`driveLog`); **P6** assembles the tie-free headline.

It consumes two leaves landing in parallel (plan for their results, do not re-prove):

* **P2** — `ModellableStep` over `lower prog` (`BytecodeLayer.Interpreter.ModellableStep`,
  `DriveRuns.lean:150`): every `Runs`-reachable frame of a `lower prog` run issues a code CALL
  or a halt (never CREATE, never precompile-CALL). Removes the `hmodel` supplied hyp under
  `cleanHalts_of_runWithLog` (`DriveSim.lean:128`).
* **P3** — `SelfPresent`-forward across `Runs` *including the call resume*: a `SelfPresent fr`
  +`Runs fr fr'` ⇒ `SelfPresent fr'` lemma that survives the `Runs.call` black-box resume node.
  Feeds SSTORE presence through the whole walk (the §5 docstring's reason (b)).

---

## 0. Coordinates — where everything lives

| Thing | File:line |
|---|---|
| Headline (general) `lower_conforms` | `LirLean/LowerConforms.lean:1227` |
| Headline (acyclic CFG) `lower_conforms_acyclic_cfg` | `LirLean/Acyclic.lean:339` |
| Headline (cyclic) `lower_conforms_cyclic` / `'` | `LirLean/DriveSim.lean:606` / `:646` |
| `StmtTies` / `TermTies` (the supplied bundles) | `LowerConforms.lean:1312` / `:1391` |
| `CallRealises` (the §7 CALL tie) | `LowerConforms.lean:284` |
| `Corr` boundary invariant | `LirLean/SimStmt.lean:101` |
| `SimStmtStep` / `SimTermStep` | builders `LowerConforms.lean:421` / `:856`; consumers `sim_cfg` `:980` |
| `DriveCorr` / `CleanHalts` / `DriveStep` | `DriveSim.lean:82` / `:75` / `:443` |
| `drive_step_block_{stop,ret,jump,branch}` | `DriveSim.lean:209` / `:235` / `:281` / `:364` |
| `runFrom_of_driveCorr` (F2) | `DriveSim.lean:569` |
| `DriveCorrPlus` + `driveCorrPlus_entry` | `LirLean/TieDischarge.lean:544` / `:563` |
| Alignment substrate `GasLogAligned`/`SloadLogAligned` + step lemmas | `TieDischarge.lean:146` / `:313` |
| Selection lemmas `gasRealises_obs_of_witness`/`sloadRealises_charge_of_witness` | `TieDischarge.lean:251` / `:373` |
| `SelfPresent` + `selfPresent_matRuns` + `selfPresent_codeFrame` | `TieDischarge.lean:408` / `:464` / `:484` |
| Stash-tail forward lemmas | `LirLean/StashTail.lean` (`stash_tail_runs` `:156`, `_covered` `:256`, `stash_tail_gas` `:320`) |
| `materialise_runs` / `MatRuns` (clauses incl. `.accounts`) | `LirLean/MaterialiseRuns.lean:767` / `:335` |
| Recorder `driveLog`/`runWithLog`/projections | `LirLean/RunLog.lean` |
| `runs_of_drive_ok` (drive→Runs reverse) | `DriveRuns.lean:300` |
| `Runs` inductive (`.refl`/`.step`/`.call`), `linear_to_halt`, `gasAvailable_le` | `experiments/003_bytecode_layer/BytecodeLayer/Hoare.lean:114` / `:219` |

---

## 1. Inventory — the exact remaining supplied ties

These are the ties P5 must produce. Each is tagged with the producer lemma/walk-step and its
P2/P3 dependency. (Gas `hstash` is already DISCHARGED via `sim_assign_gas_lowered`/`stash_tail_gas`
— **not** in this list; the gas tie reduced to the *positional value* `ob = ofUInt64 (gas − Gbase)`,
which P5 must still position-select.)

### 1a. Statement-level (`StmtTies`, `LowerConforms.lean:1312`)

| # | Tie (field) | Statement (abbreviated) | P5 producer | Dep |
|---|---|---|---|---|
| S1 | sload stash run (`StmtTies` arm 2, `:1323`) | `∃ endFr, Runs fr0 endFr ∧ endFr.memory = (fr0.mstore (slotOf t) w).memory ∧ … ∧ stack = []` | `stash_tail_runs_covered` (covered slot) / `stash_tail_runs`, **constructed** inside the walk's sload-cursor step | P3 (SelfPresent through the materialise prefix `materialise k`) |
| S2 | sload value tie (`:1329`) | `Lir.evalExpr st0 0 (.sload k) = some w` and `w` = recorded warmth-tied loaded value | walk: the realised SLOAD output; warmth via `sloadRealises_charge_of_witness` | — (value from IR step) |
| S3 | gas positional value (`:1356`) | `ob = ofUInt64 (fr0.gas − Gbase)` | walk: the realised GAS read via `gasRealises_obs_of_witness` | — |
| S4 | gas runtime envelopes (`:1360`) | `Gbase ≤ gas`, `3 ≤ gasFrame gas`, the memExpansion witness + 2 MSTORE bounds | walk: descending-gas facts (`Runs.gasAvailable_le`) + coverage | — |
| S5 | sstore gas/stack envelopes + `SstoreRealises` + `vw ≠ 0` (`:1375`) | `(charge value).sum + (charge key).sum ≤ gas` … `∃ acc, SstoreRealises fr0 kw vw acc` ∧ `vw ≠ 0` | gas via `Runs.gasAvailable_le`; presence via `sstorePresence_of_self`; `vw≠0` from IR step inversion (see §4 risk) | **P3** (SelfPresent at the SSTORE frame `frk`) |
| S6 | call `htail` + structural CALL trace (`CallRealises`, `:1386`/`LowerConforms.lean:284`) | the realised `(result,pd)`, `o = evmV2CallOracle …`, arg-push `Runs`, `CallReturns`, resume pins, Route-B tail | `o=…` via `realisedCall_projection`; arg run + `CallReturns` from the walk's CALL-boundary; tail via `stash_tail_runs` | **P3** (SelfPresent across `Runs.call` resume) |
| S7 | assign post-state realisability (`:1314`) | rematerialised assign: `MemRealises prog st0' fr0` + scoping | walk: `MemRealises` transported across empty emit (`Runs.refl`) | — |

### 1b. Terminator-level (`TermTies`, `LowerConforms.lean:1391`)

| # | Tie | Statement | P5 producer | Dep |
|---|---|---|---|---|
| T1 | `stop` frame facts (`hstop`) | `self = addr` ∧ `∃ cp, kind = .call cp` ∧ `accounts ≠ ∅` | walk: frame pins from `Corr` + `SelfPresent` (`accounts ≠ ∅` from presence) | **P3** |
| T2 | `ret` value-channel (`hretties`) | `self=addr`, `∃ vw, locals t = some vw`, charge envelopes, the RETURN-site `hret` | walk + IR step value; gas via descent | **P3** (RETURN frame presence) |
| T3 | `jump` gas envelopes (`hjump`) | `3 ≤ gas`, `Gmid ≤ …`, `Gjumpdest ≤ …` at the landing | walk: `Runs.gasAvailable_le` descent + `Gjumpdest` margin | — |
| T4 | `branch` cond-materialise + gas (`hbranch`) | `∃ frc, MatRuns … cond cw frT frc ∧ <6 gas bounds>` | `materialise_runs` (constructed) + descent | — |

### 1c. Drive-level (cyclic, `DriveSim.lean`) — the `hjump`/`hbranch` edge bundles + entry

| # | Tie | Where | P5 producer | Dep |
|---|---|---|---|---|
| D1 | entry `CleanHalts fr₀` | `lower_conforms_cyclic` `hclean` (`:611`) | `cleanHalts_of_runWithLog` | **P2** (`hmodel`) |
| D2 | per-boundary `hjump` edge bundle (`drive_step_block_jump` `hjump`, `:296`) | `lower_conforms_cyclic'` `:672` | walk: the `JUMPDEST`-landing data, same shape as T3 + presence | — |
| D3 | per-boundary `hbranch` edge bundle (`:378`) | `lower_conforms_cyclic'` `:687` | walk: cond-materialise + `JUMPI` landing, same shape as T4 | — |
| D4 | entry `Corr` (`hentry`) | `lower_conforms_cyclic` `:610` | `entry_corr` (`LowerConforms.lean:1141`) — already a builder; canonical `w₀` choice | — |

**Note.** The cyclic edge bundles (D2/D3) and the `SimTermStep` edge bundles (T3/T4) are
THE SAME DATA in two shapes (`drive_step_block_*`'s `hjump` is `sim_term_edge_jump`'s internals,
per `DriveSim.lean:280` docstring). P5 produces them once at the boundary and feeds both consumers.

---

## 2. The DAG — sub-lemmas in dependency order

The spine is a single walk-induction that strengthens the drive recursion's boundary invariant
from `DriveCorr` to `DriveCorrPlus` (`TieDischarge.lean:544`), threading the alignment witnesses
(`GasLogAligned`/`SloadLogAligned`) and `SelfPresent` block-by-block, and **at each block step**
emitting (a) the per-cursor STASH/structural ties and (b) the per-cursor OBSERVATION (value/warmth)
ties via the selection lemmas. The assembled `SimStmtStep`/`SimTermStep` feed the existing
`sim_cfg`/cyclic machinery for P6.

`driveCorrPlus_entry` (`:563`) is proven. **The open piece is preservation through the block step.**

Difficulty legend: **M** = mechanical (mirror an existing `drive_step_block_*` / `selfPresent_*`);
**N** = genuinely new; **R** = risk-bearing (see §4).

### Tier 0 — leaves consumed (assumed landing)

* **P2** `modellableStep_lower : ∀ prog fr, Runs (codeFrame …) fr → ModellableStep fr` — discharges
  D1's `hmodel`. **(leaf, not P5)**
* **P3** `selfPresent_runs : SelfPresent fr → Runs fr fr' → SelfPresent fr'` — the `Runs`-closure
  of `SelfPresent`, **including the `Runs.call` resume node**. Per-op bricks exist
  (`selfPresent_addFrame`/…/`selfPresent_pushFrameW`, `TieDischarge.lean:428–445`) and
  `selfPresent_matRuns` (`:464`) covers a materialise sub-run via `MatRuns.accounts`. The new
  content is the `.step`/`.call` induction over the raw `Runs` inductive (`Hoare.lean:114`), where
  the `.call` arm must show the resume frame `resumeFr = resumeAfterCall result pd` keeps the self
  account present (the child commits its account map back; for a `lower prog` self-call the self
  account survives — world-wellformedness of the realised `CallResult`). **(leaf, not P5; R: the
  call-child account commit is the genuinely new fact, see §4.)**

### Tier 1 — alignment step lemmas through ONE op (mostly banked)

These advance `GasLogAligned`/`SloadLogAligned` in lockstep with one bytecode step. Already proven:

* `gasLogAligned_step_gas` (`TieDischarge.lean:177`) — **M, DONE**
* `gasLogAligned_step_norecord` (`:198`) — **M, DONE**
* `sloadLogAligned_step_sload` (`:327`) — **M, DONE**
* `sloadLogAligned_step_norecord` (`:342`) — **M, DONE**
* `FramesRun.snoc` (`:155`) — **M, DONE**

**New, Tier 1:**

* **L1.1 `gasLogAligned_matRuns`** — *N(small)*.
  `GasLogAligned gasAcc gasFrs → MatRuns defs sloadChg fuel e w fr fr' →`
  `∃ gasFrs', GasLogAligned (gasAcc ++ <gas reads in e>) gasFrs' ∧ gasFrs'.getLast? threads to fr'`.
  Consumes: the materialise sub-run's GAS sites (an `e` may materialise a `.gas` only at a spilled
  def-site, which in the spilled regime is NOT inside `materialise` — gas is read once at the stash;
  so for the materialise *prefix* of an sstore/branch operand there are **no** top-level GAS reads,
  making this the no-record composite). Produces: alignment preserved across the sub-run.
  **In the spilled model this collapses to `gasLogAligned_step_norecord` iterated** — there are no
  GAS/SLOAD ops *inside* `materialise` (they are stashed at def-sites). Risk: verify `materialiseExpr`
  of a `.slot`/`.tmp`/`.add`/`.lt` truly contains no `GAS`/`SLOAD` byte (it does not — `materialise`
  of a spilled tmp is `PUSH slot; MLOAD`). **Low risk once verified.**
* **L1.2 `sloadLogAligned_matRuns`** — twin of L1.1. *N(small)*. Same collapse argument.

### Tier 2 — the `DriveCorrPlus` preservation walk-step (THE CENTERPIECE)

Decomposed by terminator shape, then by channel. Each mirrors the corresponding
`drive_step_block_*` (`DriveSim.lean:209/235/281/364`) but threads `DriveCorrPlus` instead of
`DriveCorr` and EMITS the per-cursor ties consumed by `SimStmtStep`/`SimTermStep`.

**The shared statement-walk core (consumed by all four shapes):**

* **L2.0 `driveCorrPlus_run_stmts`** — *N, the heart, R*.
  ```
  DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
  blockAt prog L = some b →
  -- the IR block run (from RunDefinable.stmts / runStmts_exists):
  RunStmts prog o st T b.stmts st' T' →
  ∃ frT gasAcc' gasFrs' sloadAcc' sloadFrs',
      Runs fr frT
    ∧ Corr prog sloadChg obs st' frT L b.stmts.length
    ∧ SelfPresent frT
    ∧ GasLogAligned gasAcc' gasFrs' ∧ SloadLogAligned sloadAcc' sloadFrs'
    -- AND the per-cursor ties (the StmtTies content) for every cursor of b:
    ∧ (the StmtTies bundle for b at every cursor, S1–S5,S7)
  ```
  Consumes: `DriveCorrPlus`, the block run, P3 (`selfPresent_runs`), L1.1/L1.2, the selection
  lemmas (`gasRealises_obs_of_witness`/`sloadRealises_charge_of_witness`), `stash_tail_runs(_covered)`.
  Produces: the `Corr` at the terminator cursor (as today's `sim_stmts_block`) PLUS the threaded
  invariants PLUS the per-cursor statement ties. This is the induction over `b.stmts` (cursor by
  cursor); at each cursor it dispatches on the statement shape:
  - **assign-remat** → S7 (MemRealises transported, `Runs.refl`); alignment unchanged (norecord).
  - **assign .gas** → S3 (`gasRealises_obs_of_witness` with the witness frame = this cursor's
    `gasFrame`) + S4 (descent gas facts); `gasLogAligned_step_gas` advances the gas alignment.
  - **assign .sload k** → S1 (construct via `stash_tail_runs_covered`; the `materialise k` prefix is
    threaded by L1.2 + P3) + S2 (warmth via `sloadRealises_charge_of_witness`);
    `sloadLogAligned_step_sload` advances the sload alignment.
  - **sstore** → S5 (gas via descent; presence via `sstorePresence_of_self` from `SelfPresent`
    threaded through `materialise value; materialise key` by P3/`selfPresent_matRuns`; `vw≠0` is
    the §4-R item).
  - **call** → S6 (CALL trace; the §4-R call black-box item).
  **R: the call channel (S6) and the multi-distinct-read positional selection (S3/S2) — see §4.**

**Then the four terminator wrappers (each builds on L2.0):**

* **L2.1 `driveCorrPlus_step_stop`** — *M* (mirror `drive_step_block_stop`, `:209`). Emits T1 using
  `SelfPresent frT` (`accounts ≠ ∅` from presence). Halt arm — no successor invariant to thread.
* **L2.2 `driveCorrPlus_step_ret`** — *M* (mirror `:235`). Emits T2; value from IR step; gas via
  descent; presence from `SelfPresent frT`.
* **L2.3 `driveCorrPlus_step_jump`** — *N(medium)* (mirror `:281`). Emits T3/D2 (the landing data),
  re-establishes `DriveCorrPlus` at the successor: `Corr` via `corr_at_jumpdest_landing` (as today),
  `SelfPresent (jumpdestFrame fj)` via P3 from `SelfPresent fr` along `Runs fr (jumpdestFrame fj)`,
  alignment carried forward (the terminator's `PUSH4;JUMP;JUMPDEST` contains no GAS/SLOAD ⇒ norecord).
  Plus the strict `totalGas` descent (already `totalGas_succ_lt`, `:179`).
* **L2.4 `driveCorrPlus_step_branch`** — *N(medium)* (mirror `:364`). Emits T4/D3 (cond-materialise
  via `materialise_runs` + `JUMPI` landing); thread `SelfPresent`+alignment across the
  cond-materialise (L1.2/P3) then the `JUMPI`/`JUMPDEST` (norecord); descent as in L2.3.

### Tier 3 — the strengthened drive recursion (mirror F2)

* **L3.1 `DriveStepPlus`** — *N(small)*. The `DriveCorrPlus` analogue of `DriveStep` (`:443`): the
  edge arm carries a strictly-smaller `DriveCorrPlus` successor (not just `DriveCorr`).
* **L3.2 `driveStepPlus_of_block`** — *M* (mirror `driveStep_of_block`, `:477`). Dispatch `b.term`
  into L2.1–L2.4.
* **L3.3 `runFrom_of_driveCorrPlus`** — *M* (mirror `runFrom_of_driveCorr`, `:569`). Strong induction
  on `totalGas`; the strengthened invariant rides along but the measure/recursion is identical.
  **Produces the IR `RunFrom` AND, as a side product, the full `StmtTies`/`TermTies` for every block
  reached** (collected from the L2.* emissions). This is the bridge to P6.

### Tier 4 — collecting the per-block ties into `∀ L b, …`

`sim_cfg` (`LowerConforms.lean:980`) wants `∀ L b, blockAt prog L = some b → SimStmtStep …`
universally, not per-reached-boundary. Two routes:

* **Route 4a (preferred):** prove `simStmtStep_block`/`simTermStep_block` builders' hypotheses
  (`StmtTies`/`TermTies`) hold for EVERY present block by running L2.0 at that block's *reached*
  boundary — but an unreached block has no `Corr` frame, so its ties are **vacuously true** (the
  `StmtTies` conjuncts are all `Corr … → …` implications; with no reachable `Corr` the hypothesis is
  never satisfiable at that block). So: **L4.1 `stmtTies_of_reachable_or_vacuous`** — for a present
  block, either it is reached (ties from L2.0) or every `StmtTies`/`TermTies` antecedent `Corr` is
  unsatisfiable at it (vacuous). *N(medium), R: the vacuity argument needs "Corr at L ⇒ L reachable",
  which is NOT generally true (Corr only pins pc, not reachability — cf. `lower_conforms_cyclic'`'s
  `hpresent`). See §4 fallback.*
* **Route 4b (fallback, simpler):** keep `StmtTies`/`TermTies` as the carried surface but DISCHARGE
  them per-block from the drive emission *at the headline*, where the whole-program walk gives the
  reached set. I.e. P6's headline runs L3.3 once and threads its emitted ties straight into
  `sim_cfg` without the universal — restating `sim_cfg` to consume the drive-emitted ties along the
  reached spine. This avoids the vacuity gap entirely (only reached blocks are tied) at the cost of a
  small `sim_cfg` restatement (`sim_cfg_along_drive`). **Recommended primary route.**

### Tier 5 — P6, the tie-free headlines

* **L5.1 `lower_conforms_cyclic_tiefree`** — restate `lower_conforms_cyclic'` (`:646`) with
  `hjump`/`hbranch`/`hhalt`/the entry `CleanHalts`/`hstmts`/`hterm` all REMOVED, replaced by their
  producers:
  - entry `CleanHalts` ← `cleanHalts_of_runWithLog` (needs P2's `modellableStep_lower`);
  - entry `Corr` ← `entry_corr` (already a builder);
  - entry `SelfPresent` ← `selfPresent_codeFrame` (needs world-wellformedness `accounts.find?
    recipient = some _`);
  - the per-boundary `DriveStepPlus` ← `driveStepPlus_of_block` (L3.2) from `RunDefinable` +
    `WellFormedLowered` + L2.0's emissions;
  - the `sim_cfg` ties ← the drive emission (Route 4b).
* **L5.2 `lower_conforms_acyclic_cfg_tiefree`** — the acyclic specialisation: same, but the
  `totalGas` recursion is replaced by the existing acyclic `irRun_exists` for the IR side, while the
  bytecode-side ties still come from the L2.* walk (the walk is cycle-agnostic; acyclicity only
  simplifies the IR `RunFrom` existence, already handled).

---

## 3. Green-keeping order — checkpoints that each keep `lake build` green + axiom-clean

Each checkpoint is independently committable (always-green, no `sorry`/`axiom`/`native_decide`,
axioms `[propext, Classical.choice, Quot.sound]`). Order chosen so every step builds on closed
proofs.

1. **C1 — Tier 1 new lemmas (L1.1, L1.2).** Pure alignment composites over `MatRuns`. No P2/P3.
   Add to `TieDischarge.lean`. *Green gate: `#print axioms` of both.*
2. **C2 — P3 lands** (`selfPresent_runs`, separate track). Gate: its own axiom check. P5 then
   *consumes* it.
3. **C3 — L2.0 statement-walk core, channels in isolation.** Land the value channels first
   (gas S3/S4, sload S2; assign S7) — these need NO P3 and the selection lemmas already exist.
   Then the structural sload stash S1 (needs P3 for the prefix). Then sstore S5 (needs P3 +
   the `vw≠0` resolution). Then the call S6 (needs P3 + the call black-box, the hardest).
   *Keep each channel a separate `have`-block so partial progress stays green; the theorem
   statement is fixed up front (L2.0's signature), the body grows channel by channel.*
   Gate after each channel: the module still builds (the unfinished channels stay as the
   currently-supplied hypotheses until their `have` lands — i.e. **L2.0 is introduced with its
   not-yet-produced ties still as parameters, then those parameters are deleted one at a time** as
   each channel's `have` is proven; never a `sorry`).
4. **C4 — L2.1/L2.2 (halt wrappers).** Mechanical; emit T1/T2. Gate: axioms.
5. **C5 — L2.3/L2.4 (edge wrappers).** Emit T3/T4/D2/D3, re-establish `DriveCorrPlus` at successor.
   Gate: axioms.
6. **C6 — Tier 3 (L3.1/L3.2/L3.3).** The strengthened recursion. Gate: `runFrom_of_driveCorrPlus`
   axiom-clean; it should reproduce `runFrom_of_driveCorr`'s `RunFrom` plus the tie collection.
7. **C7 — P2 lands** (`modellableStep_lower`, separate track) ⇒ entry `CleanHalts` discharged.
8. **C8 — Route 4b (`sim_cfg_along_drive`).** Thread emitted ties into the world equation.
9. **C9 — P6 (L5.1 then L5.2).** The tie-free headlines.

### The P6 endpoint (stated explicitly)

`lower_conforms_cyclic_tiefree` should END with hypotheses reducing to:

```
theorem lower_conforms_cyclic_tiefree {prog} {p} {log} {w₀} {self} {bentry}
    (hwl     : runWithLog p (seedFuel p.gas) = some log)        -- clean-halt scope boundary
    (hp      : p.codeSource = .Code (lower prog))
    (hmod    : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)                              -- decidable structural
    (hbentry : blockAt prog prog.entry = some bentry)           -- decidable structural
    (hbound  : offsetTable … prog.entry.idx < 2^32)             -- decidable structural
    (hgasj   : Gjumpdest ≤ p.gas.toNat)                         -- decidable structural
    (hwfworld: p.accounts.find? p.recipient = some _)           -- world-wellformedness (self present)
    (hwf     : WellFormedLowered prog)                          -- decidable structural (folded)
    (hdef    : RunDefinable prog)                               -- benign operand-definability
    : O.world = (observe self log.observable).world            -- for the constructed O
```

i.e. **just the clean-halt precondition (`hwl`) + decidable well-formedness
(`WellFormedLowered`/`RunDefinable`/the entry structural facts) + world-wellformedness (self account
present).** No `StmtTies`/`TermTies`, no `hjump`/`hbranch`/`hhalt`, no entry `CleanHalts`/`Corr`,
no `hstmts`/`hterm`. The canonical `w₀ := selfStorage (codeFrame …)` choice
(`entry_storageAgree_codeFrame`, `LowerConforms.lean:1128`) further discharges `hstore`.

---

## 4. Risk flags

* **R1 — the call channel (S6), the black-box for gas/sload reads.** `Runs.call` (`Hoare.lean:114`)
  carries the child as a black-box `CallReturns` node; the recorder's `driveLog` gates on
  `stack.isEmpty` so it records ONLY top-level GAS/SLOAD reads, NOT the child's
  (`RunLog.lean:188`). Good: the alignment witness lists only ever contain top-level frames. But the
  arg-push `Runs fr0 callFr` (S6) crosses materialise sub-runs that may contain spilled-slot MLOADs
  (no GAS/SLOAD, so norecord) — fine. The genuine risk is **P3 across the resume node**: SelfPresent
  must survive `resumeAfterCall result pd`. For a self-call the child commits the self account back;
  for a foreign call the self account is untouched. This is the new fact P3 must carry; if P3's
  call-arm proves too hard, **fallback: keep S6's `CallRealises` supplied** (it is already
  satisfiable) and ship a headline tie-free *except for the call tie*, which is still a real
  improvement (gas/sload/sstore/control-flow all discharged). The prompt's note (gas+ext-call
  oracles ⇒ IR is gas-agnostic AND call-agnostic) means a call-tie residual is the natural seam.

* **R2 — the Prop-vs-Type / single-`obs` vs multi-read boundary at the GAS/SLOAD selection.**
  `gasRealises_obs_of_witness` (`TieDischarge.lean:251`) and `sloadRealises_charge_of_witness`
  (`:373`) are proven ONLY in the single-`obs` `Corr` model (the docstrings at `:226–242` /
  `:364–372` flag the multi-distinct-read converse as the standing obstacle). The `Corr` invariant
  carries one fixed `obs : Word` (`SimStmt.lean:101`), so `evalExpr st obs .gas` reads the SAME word
  for every `Expr.gas`. **A program with two top-level GAS reads of different values cannot satisfy
  the single-`obs` `Corr`.** Since gas/sload are now SPILLED (their values live in memory slots,
  read positionally via `MemRealises`, NOT via the `obs` universal — `Corr` has no gas/sload
  universal, `SimStmt.lean:32`), this is *mostly* moot: the spilled value tie is positional
  (`memAgree`), and the `obs` field is vestigial for gas/sload. **Verify during C3 that the spilled
  path never routes a multi-read through the single-`obs` selection** — if it does, the walk must
  carry the *per-cursor recorded read* directly (the `gasAcc[i]?`/`sloadAcc[i]?` positional entry,
  which `aligned_read_eq_obs`/`alignedSload_read_eq_obs` already give without the single-`obs`
  collapse). **Fallback: drop the `obs`-collapse and thread the positional `gasAcc[i]` value into
  `MemRealises` directly** (the honest per-cursor read), bypassing the single-`obs` model entirely.
  This is likely necessary and should be the DEFAULT: the spilled-value tie is positional, so use
  `aligned_read_eq_obs` (no single-`obs`), not `gasRealises_obs_of_witness`.

* **R3 — `vw ≠ 0` for sstore (S5).** `SstoreRealises` carries `vw ≠ 0` (`SimStmt.lean:368`,
  `simStmtStep_sstore` `:246`). This is NOT a universal EVM fact (SSTORE of 0 is legal). It comes
  from the IR step + the realised run: the lowered `SSTORE` with `vw = 0` still runs, so the tie as
  written (`vw ≠ 0`) is **over-strong**. *Investigate during C3:* either the IR `EvalStmt.sstore`
  step-inversion supplies `vw` and the `sim_sstore` brick genuinely needs `vw ≠ 0` (then the headline
  must carry a "no zero-value sstore" well-formedness, a real residual), OR `sim_sstore` can be
  relaxed to `vw = 0` (the EIP-2200 charge differs but the world-write is still tied). **Fallback:
  carry a decidable `NoZeroSstore prog` in `WellFormedLowered` — honest and structural.**

* **R4 — Tier 4 vacuity gap (Route 4a).** "Corr at L ⇒ L reachable" is false in general (`Corr`
  pins pc but the cyclic headline supplies `hpresent` separately, `DriveSim.lean:655`). **Use Route
  4b** (thread the drive-emitted ties straight into a `sim_cfg_along_drive`), avoiding the universal
  `∀ L b` quantification over unreached blocks. This is the lower-risk path and is the recommended
  default.

* **R5 — cyclic vs acyclic.** The L2.* walk is cycle-agnostic (it threads `DriveCorrPlus` along the
  `totalGas`-descending drive recursion, `runFrom_of_driveCorr` `:569`, which already handles
  cycles). The acyclic headline (L5.2) differs ONLY in the IR `RunFrom` existence (acyclic uses
  `irRun_exists`; cyclic uses `runFrom_of_driveCorrPlus`). The bytecode-side tie production is
  identical. **No extra risk for the acyclic case** — it is strictly easier.

### Honest intermediate headline (if the full walk proves too large)

If the call channel (R1) and/or the full Tier-4 collection prove too large for one sprint, the
honest intermediate is: **a headline tie-free in the gas/sload/sstore/control-flow channels, with
the CALL tie (`CallRealises`) still supplied.** This is a real improvement — every channel the
recorder instruments (GAS/SLOAD) and the world-write channel (SSTORE) is discharged from the real
run; only the external-call black-box trace stays supplied (the natural seam, given the IR is
call-agnostic via the ext-call oracle). Concretely: ship L5.1 with only `hcallties`/`CallRealises`
remaining among the §7 hypotheses.

---

## 5. Parallelizability — independent DAG nodes for concurrent subagents

The following nodes have no inter-dependencies and can be farmed concurrently:

* **Group A (alignment composites, no P2/P3):** L1.1 `gasLogAligned_matRuns` ∥ L1.2
  `sloadLogAligned_matRuns`. Both pure `MatRuns`-over-alignment; verify-no-GAS/SLOAD-in-materialise
  is shared but trivially split.
* **Group B (value channels of L2.0, no P3):** the gas value+envelope channel (S3/S4) ∥ the sload
  value/warmth channel (S2) ∥ the assign-remat channel (S7). Each is a self-contained `have`-block
  inside L2.0's body; they touch disjoint statement shapes. (S1's stash *construction* and the
  sstore S5 and call S6 channels need P3 and should be SERIALIZED after Group B + P3.)
* **Group C (terminator wrappers, after L2.0 signature is fixed):** L2.1 ∥ L2.2 ∥ L2.3 ∥ L2.4. The
  two halt wrappers (L2.1/L2.2) are mechanical and fully independent; the two edge wrappers
  (L2.3/L2.4) share the successor-`DriveCorrPlus` re-establishment pattern but are otherwise
  independent.
* **Group D (leaves, fully independent tracks):** P2 `modellableStep_lower` ∥ P3 `selfPresent_runs`.
  These are the two named external leaves; both can run from the start.

**Serialized spine (cannot parallelize):** L2.0 channels S1/S5/S6 (need P3) → Tier 3 (L3.1→L3.2→
L3.3, each consuming the previous) → Route 4b → P6 (L5.1→L5.2). The Tier-3 recursion and P6 are the
single-threaded assembly tail.

**Suggested fan-out:** kick off Group A + Group D immediately; Group B once L2.0's signature is
committed (C3 start); Group C once L2.0 closes (C4); then the serialized tail.
