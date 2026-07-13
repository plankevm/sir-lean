# exp005 — the INTENDED proof plan / architecture (reference for the restructuring review)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Date: 2026-07-04. Purpose: recover what the exp005 LirLean proof is *trying to be*, so a
restructuring review is grounded in the intended architecture, not just the current file layout.
Read-only synthesis of the planning docs + the actual Lean on the current `main` branch
(the "foundation" lineage). Every claim cites `file:line`.

> **READ THIS FIRST — the tree has moved past most of the prose docs.** `main` is the
> **`foundation`** lineage (git log: `800709f`, `5abdfee` "Merge branch 'foundation'`,
> `1c77c07` call-stream, `1d83587` sstore-zero, `4628201` full-observable). It has evolved
> *past* the `exp005-honesty-cleanup` branch that `docs/target-architecture-2026-07-02.md`,
> `docs/handoff-phase3-2026-07-04.md`, `docs/final-audit-2026-07-03.md`, and
> `docs/achievements-since-main.md` describe. The design *intent* in those docs is intact; the
> *vocabulary* drifted. Section 6 below is the docs→tree rename/change map. When in doubt, the
> Lean on disk wins.

> **P8 status note (2026-07-08).** This architecture note predates the P8 well-formedness
> reshaping. `Acyclic.lean` / `MatFueled` / `AcyclicWellFormed` no longer supply the live
> well-formedness route. The public theorem surface is `IRWellFormed` + `codeFits` +
> `stackFits`, and `wellLowered_of_IRWellFormed` rebuilds the internal `WellLowered` adapter.

---

## 0. What the experiment is (one paragraph)

A Lean 4 formalization of a high-level SSA/CFG IR (`Lir`) lowered to EVM bytecode, proving the
lowering **preserves observable semantics** under a **record-then-replay conformance**
discipline (`docs/achievements-since-main.md:12-27`, `docs/ir-design-v3.md:0`):

1. Run the lowered bytecode once with a **recording interpreter** `runWithLog`/`driveLog`
   (`Spec/Recorder.lean`), producing a `RunLog` (final observable + gas-read stream + sload
   stream + call-record stream).
2. Harvest the run-observed **gas** (`realisedGas log`) and **external-call** results
   (`realisedCall log self`) from that log.
3. Feed those harvested values back as *oracles* into the executable IR semantics and prove the
   IR run exists and its observable matches the bytecode's (`Conforms`).

The governing principle (`docs/ir-design-v3.md:12-31`): **gas and external calls are things the
IR observes but does not model** — each is an opaque value supplied by a trace event, carrying
one minimal law, with a *realisability* side-condition the EVM instance discharges (the CompCert
external-call discipline, applied to gas too). The semantics is **permissive** (non-deterministic
in the trace); the theorem quantifies only over the **realised** trace the bytecode actually
produced — so pathological traces are admitted at the type level and quantified away, never
reasoned about.

---

## 1. The intended layer hierarchy (altitude, bottom = no LirLean deps)

The organizing principle is **altitude, not feature** (`docs/lirlean-dag-2026-07-04.md:23-56`).
Seven layers; each exists because a forward-simulation lowering proof needs a *mid-run band*
that exp003 does not export (single-opcode steps + whole-call `Behaves`, nothing between —
`docs/target-architecture-2026-07-02.md:126-134`). exp005 built that band in-house.

- **L0 — Spec core (reviewer-facing DEFINITIONS).** `Spec/IR` (IR datatypes, root of everything,
  114 LOC), `Spec/Semantics` (IR operational semantics / observables), `Spec/Lowering`
  (the lowering fn `flatBytes`, IR→bytes), `Spec/Recorder` (the recording interpreter model),
  `Spec/Seams` (seam register, forwarders), `Spec/Conformance` (**tombstone stub**, 24 LOC —
  `Spec/Conformance.lean:1-24`). *Why:* the datatypes + semantics + lowering + recorder are the
  trusted surface a reviewer reads before any proof.

- **L1 — `Engine/` (IR-AGNOSTIC frame-level EVM theory).** `AccountMap`, `StepWalk` (1336 LOC,
  the core pc/stack/memory step-walk), `Descent`, `DriveMono`, `MemAlgebra` (996), `CleanHalt`,
  `Charges`, `DriveRuns`. *Why:* pure EVM theory over `Frame`/`Runs`; slated to **graduate to
  exp003** as a reusable library (`docs/lirlean-dag-2026-07-04.md:61-62`,
  `docs/target-architecture-2026-07-02.md:136-152`). It exists in-tree only because exp003's
  surface lacks it.

- **L2 — Decode / pc-offset / control-flow validity (bytes ↔ IR positions).** `LoweringLemmas`,
  `DecodeLower`, `Layout` (byte offsets of segments), `DecodeAnchors` (decode lands at expected
  IR positions — "Layer A" of the grind), `JumpValid`, `NoCreateBytes`, `BoundaryReach`. *Why:*
  a lowering proof must show "these bytes implement this CFG" — pc/jumpdest/landing reasoning
  that no fork eliminates (it is the semantic content; forks evade it) but that can be paid once
  (`docs/target-architecture-2026-07-02.md:153`). NB: JumpValid/NoCreateBytes/BoundaryReach are a
  **triple-duplicated `SegAligned` tower** (~1400 LOC), the biggest genuine dedup target
  (`docs/lirlean-dag-2026-07-04.md:101-103,178`).

- **L3 — Materialise (the spill/recompute VALUE channel) + v1 bricks.** `SmallStep`, `Call`
  (CALL brick, now CallStream-based), `Create` (**dead**, future-CREATE2 scaffold), `StorageErase`
  (zero-write slot-clearing, recent), `DefsSound` ("Layer B3"), `Match` (byte↔opcode hub, 595),
  `MaterialiseGas`, `MaterialiseRuns` (1372, "Layer B1", the materialise `Runs` producer),
  `MatDecLower`, `MaterialiseCleanHalt`, `StashTail`. *Why:* this is the value channel (§5) — how
  each `Expr` becomes bytecode that pushes its value; the linchpin `materialise_runs`.

- **L4 — Per-block gas-aware SIMULATION engine (the `Corr` bricks; the big grind).** `SimStmt`
  (1187; per-statement sim, hosts the 28-hyp `sim_call_stmt` smell), `SimStmts` ("Layer D"),
  `SimTerm` (838; terminator arms, "Layer E"), `CleanHaltExtract` (1118). *Why:* one IR
  statement/terminator ↔ one multi-opcode `Runs` segment, threading the `Corr` boundary invariant.

- **L5 — CFG assembly.** `LowerDecode` (1528; block-walk bricks `sim_stmts_block`/`sim_term_*`,
  load-bearing), `LowerConforms` (1260; hosts `sim_cfg`, `SimTermStep`, `WellFormedLowered` — all
  **live** — plus the **DEAD acyclic capstone** `Lir.lower_conforms`, `LowerConforms.lean:1188`,
  ~73 LOC, zero refs), and residual `Acyclic` rank/fuel support pending P9. *Why:* `sim_cfg`
  inducts on a *given* IR `RunFrom` and is already cycle-agnostic
  (`docs/cyclic-cfg-forward-sim-plan.md:11-14,53`).

- **L6 — V2 gas-free SPINE + cyclic DRIVE.** `Law` (determinism floor), `IRRun`
  (IR-run existence; `CFGAcyclic` self-described "retired"), `Call`/`CallRealises` (the
  CallStream oracle + realisation bridge), `Decode/Modellable`, `DriveSim` (743; **the cyclic
  drive simulation** — hosts `runFrom_of_driveCorr` F2 and `lower_conforms_cyclic'` F3′,
  `DriveSim.lean:588,666`), `Drive/{SelfPresent,CallPreservesSelf,Headline}`. *Why:* the
  gas-free IR semantics spine, plus the drive walk that *simulates* the spine over a real
  bytecode `RunFrom` (the mechanism that retires the CFG-acyclicity restriction).

- **L7 — FLAGSHIP + audit.** `RealisabilitySpec` (3874 LOC, the `WIP` sorry-lib: R0–R12 +
  the flagship + exProg witness — the **only** sorry-carrier), `Audit` (`#guard_msgs`
  axiom/signature guard net, imported last).

**Altitude naming clarification** (`docs/lirlean-dag-2026-07-04.md:58-68`): `Engine/` = IR-agnostic
EVM theory (→ exp003); `` = the exp005 gas-free IR spine; `Drive/` = the cyclic
interpreter-drive walk. (`DriveSim.lean` is a drive-layer file misfiled directly under ``.)

**Honest note on "too many files":** the tree is *large, not bloated* — most of the 44 files are
legitimate stages of a multi-stage lowering proof (`docs/lirlean-dag-2026-07-04.md:189-193`). The
"delete Acyclic+LowerConforms → drop 6k LOC" hope is **not real**: the L4 sim engine is shared by
the cyclic flagship via `sim_cfg`; killing the acyclic path is a ~300-LOC dead-code + relocation
refactor whose payoff is conceptual (one headline, not the appearance of two)
(`docs/lirlean-dag-2026-07-04.md:14-21,154-172`).

---

## 2. The flagship shape + the R0–R12 obligation skeleton

### 2.1 The flagship (the target statement of the whole experiment)

`Lir.lower_conforms` (`RealisabilitySpec.lean:3705-3718`). Current shape:

```lean
theorem lower_conforms {prog params log} {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))          -- definitional pin
    (hmod  : params.canModifyState = true)                    -- definitional pin
    (hself : params.accounts.find? params.recipient = some acc)-- decidable entry fact
    (hgas  : GasConstants.Gjumpdest ≤ params.gas.toNat)        -- decidable entry fact
    (hwl   : WellLowered prog)                                 -- ONE static checkable bundle (R9)
    (hrun  : runWithLog params (seedFuel params.gas) = some log)-- THE runtime premise
    (hclean: log.clean)                                        -- decidable clean-scope
    (hseams: PrecompileAssumptions prog params) :              -- the honest 2-field seam
    ∃ O, RunFrom prog (entryState params) (realisedGas log)
           (realisedCall log params.recipient) prog.entry O
       ∧ Conforms params.recipient log O
```

Key statement decisions (all realized in the tree; design in
`docs/target-architecture-2026-07-02.md:47-79`):
- **Pin the oracles**: `T := realisedGas log`, call oracle `:= realisedCall log recipient`,
  entry `:= entryState params` (`RealisabilitySpec.lean:126-128`, definitional — replaces the
  former supplied entry `StorageAgree`). The old headline's free `{T}` was part of the vacuity;
  it is killed.
- `hwl : WellLowered` folds all static side-conditions into one decidable, checker-dischargeable
  structure (`RealisabilitySpec.lean:477-527`): `wf` (`WellFormedLowered`), `defs`
  (`RunDefinableG`, NOT the unsatisfiable in-tree `RunDefinable`), `defsCons` (`DefsConsistent`),
  `entry0`, `closed` (`ClosedCFG`), `stack` (`StackRoomOK`), `gasBound`, `slotAddr`,
  `retEpilogueBound`, `noSlotSource`.
- `hseams : PrecompileAssumptions` is the **irreducible boundary** (`:550-555`): `noErase`
  (precompile no-erase, the `hprec` seam) + `callsCode` (reachable CALLs target code, not a
  precompile). Neither is dischargeable from the program text.
- `Conforms` (`:155-157`) now compares **both** the world (self-storage lens) **and** the halt
  result (return value / halt kind) — the "full-observable" foundation change; it is no longer
  storage-only.
- Companions: **`lower_conforms_exact`** (`:3752`, R11-all — `RunFromAll`, both leftover streams
  `[]`, closes the drop-the-suffix channel) and **`lower_conforms_gasfree`** (`:3788`, the
  co-flagship under `NoGasReads prog`, meant to be proven FIRST as the de-risking checkpoint).

### 2.2 THE central blocker (load-bearing for any restructuring)

The flagship's proof body (`RealisabilitySpec.lean:3719-3747`) reveals the whole theorem now
reduces to **one packaged `sorry`** (`:3739-3746`): a coupled run-producer the doc names
**`runFrom_of_driveCorrLog`** (`:3724`). Everything *downstream* of that `obtain` is real,
axiom-clean assembly — `conforms_of_worldeq` (`:3661`, **CLOSED**) discharges the `Conforms`
conjunct from the terminal world equation.

Critically, the comment records that this blocker is **NOT citable** from existing leaves
(`:3730-3736`):
- `lower_conforms_cyclic'` (`DriveSim.lean:666`, the only *in-tree* run-producer) needs an
  **unconditional all-frames `SimStmtStep`**, which the reshaped `StmtTies'` cannot supply — its
  arm conclusions hold only under the load-bearing `RecorderCoupled` antecedent, so the
  coupling-free path is exactly the vacuity the reshape exists to kill;
- R6 `runs_atReachableBoundary` cannot produce `hrb` alone (its `(flatBytes prog).length ≤ 2^32`
  side-condition has no producer from `hwl`).

So the true remaining deep node is a NEW coupled driver that walks the `RecorderCoupled`
invariant across the F2 recursion, instantiating the Layer-C sim lemmas only at coupled
walk-frames. `DriveSim.lean`'s `runFrom_of_driveCorr`/`lower_conforms_cyclic'` are the *old*
tie-supplied cyclic path — live code that leads to the vacuous route, retained as salvage.

### 2.3 The R0–R12 skeleton — meaning of each obligation

The R-numbers are the **named gaps** between the green machinery and the flagship
(`RealisabilitySpec.lean:10`). They live as `sorry`-bodied theorems (statements real, proofs
tracked debt) in the `WIP` lib. Landing order is pinned at `RealisabilitySpec.lean:1045-1048`:
`R0 → R9 → R2 → R8 → R5/R4 → R6 → gasfree co-flagship → R7 → R1 → R3 → R10 → R11 → R12`;
substantial proofs are only R0b, R1, R3, R6 — everything else is static folds/assembly.

| R | meaning | tree anchor | status |
|---|---|---|---|
| **R0** | the tie *reshape* itself: `StmtTies'`/`TermTies'` restated with no free value-∀ | `StmtTies'` `:710`, `TermTies'` `:817` (defs, real) | done as statements |
| **R0b** | shadowing-aware sim-machinery reshape criterion (`DefsSoundS`/`invalStep`/`RevalidatesPerBlock`) — the current `Corr.defsSound`-at-every-cursor cannot traverse a loop-exit iteration of a rebinding program | `:1080` (criterion), `defsSoundS_preserved_step` `:1110` | closed (per handoff) |
| **R1** | gas recorder bridge — the un-consumed gas suffix's head = the machine GAS output (the "riskiest") | `:2557` | closed |
| **R2** | clean scope read off the log (replaces the `∀ last halt` universal) | `haltNonException_of_cleanLog` `:1240` | closed |
| **R3** | call realisation from the log (`CallRealisesS` `:406`); needs an arg-push machine-run producer (Piece B) | `callRealises_of_recorded` `:1364` | **open leaf** |
| **R4** | SSTORE realisation, point-wise at the concrete frame (replaces the unsatisfiable `SstoreRealises` ∃) | `sstoreRealises_at_frame` `:1396` | closed |
| **R5** | terminator ties from the walk vocabulary | `termTies'_of_walk` `:1469` | closed |
| **R6** | the boundary walk `hrb` (pc-reachability geometry); statement FIXED with `0 < prog.blocks.size` (was refutable — `not_runs_atReachableBoundary` `:2232`) | `runs_atReachableBoundary` `:2456` | **open leaf** (2 engine edge bricks) |
| **R7a–e** | the recorder-coupling edge lemmas: entry + GAS/SLOAD/other/CALL preservation | `recorderCoupled_entry` `:2474`, `_step_gas` `:2493`, `_sload` `:2615`, `_step_other` `:2651`, `_call` `:2771` | closed (R7e unconditional after recorder gate fix) |
| **R8** | presence threading (named replacement of inside-out `hpresent`) | `present_of_closed` `:2947` | closed |
| **R9** | the static `WellLowered` checker, stated existentially with an anti-vacuity anchor | `wellLowered_check_exists` `:3603` | closed (singleton checker; general `def` is debt) |
| **R10a/b** | build `StmtTies'`/`TermTies'` from the run | `stmtTies'_of_runWithLog` `:3624`, `termTies'_of_runWithLog` `:3638` | R10b closed; R10a open |
| **R11** | THE flagship (+ `_exact`, + gasfree co-flagship) | `:3705`, `:3752`, `:3788` | open (the §2.2 blocker) |
| **R12a/b** | concrete non-vacuity: exProg satisfies + instantiates the flagship | `exProg_satisfies_hypotheses` `:3835`, `exProg_nonvacuity` `:3848` | open (R12b assembles on R11) |

Plus `RunFromLeft` adequacy (`runFrom_of_runFromLeft` `:1017`, `runFromLeft_exists` `:1029`) and
`realisedGas_nil_of_noGasReads` (`:3823`) backing the co-flagship / `_exact`. **Actual open
`sorry` bodies in the file: 11** (verified; the handoff's "13" predates two foundation closures —
`grep -c sorry` returns 26 because it counts docstring mentions of the word).

The **anti-vacuity spine** is machine-checked, not aspirational: `exProg` (`:2975`) exercises
gas-read + spilled-sload + nonzero-sstore + call + a genuine cycle at once; `not_defsSound_stale`
(`:3166`) is a *proved* refutation (the un-scoped `DefsSound` really is false at a loop-exit
mid-block state — the point that motivated R0b); R9's checker must both be sound *and* accept the
witness (`:3603-3605`, the second conjunct is the guard); R12a/b force the flagship's antecedent
true somewhere.

---

## 3. The acyclic-vs-cyclic headline history (what replaced what, and why)

This is the spine of the project's evolution; a reviewer must not read a live-but-superseded
theorem as load-bearing.

1. **v1 / v2 → v3 convergence** (`docs/ir-design-v3.md:5-9`). v1 was the "oracle/cost-accounting"
   line (`ir-design.md`); v2 the "gas-free observable" line (`ir-design-v2.md`). v3 is the
   convergence: keep v2's gas-free observable machine + trace, fold v1's `resumeAfterCall`
   projections in as the call *realisability witness*, unify gas and calls under one principle.

2. **Call-free acyclic base** (`docs/lower-conforms-plan.md`). The first general `lower_conforms`
   was actually **call-free** (a `CallFree` gate) and **acyclic** (needed a static CFG block-rank
   to build the IR run). `sim_cfg` (the structural core) was fully proved; the IR-run *existence*
   was the blocker on loops.

3. **Calls composed in via the memory value channel** (`docs/calls-value-channel-plan.md`).
   `CallFree` was deleted: CALL results spill to EVM memory (Route B) and re-read on use, tied by
   `MemAgree`/`MemRealises` — see §5. This made `lower_conforms` general over `Stmt.call`.

4. **Cyclic via drive-indexed forward simulation** (`docs/cyclic-cfg-forward-sim-plan.md`). The
   key insight: building the IR `RunFrom` by *following the finite, clean-halting bytecode run*
   (measure = `totalGas` descent, not a static CFG rank) removes the acyclicity restriction AND
   discharges the per-cursor ties in one construction (`:1-27`). `sim_cfg` is already
   cycle-agnostic (`:11-14`). Scope: **clean-halt only** — bytecode OOG mid-loop has no gas-free
   IR counterpart, so the theorem is conditioned on `runWithLog` reaching a clean `.halted`
   outcome (`:20-28`). This produced `lower_conforms_cyclic`/`lower_conforms_cyclic'`
   (`DriveSim.lean:620,666`).

5. **The vacuity finding + honesty cleanup** (`docs/target-architecture-2026-07-02.md:16-45`,
   `docs/final-audit-2026-07-03.md`). Adversarial verification showed the assembled cyclic
   headline `lower_conforms_cyclic_assembled` was **VACUOUS, not merely conditional**: its
   supplied `StmtTies`/`TermTies` had the **free-`∀` disease** (a variable ∀-quantified in the
   tie, pinned to a run-specific value in the conclusion, with no antecedent linking it to the
   run) — **unsatisfiable for essentially every nonempty program**. The uniform-spill work had
   *already* killed the vacuous gas/sload *universals* (`docs/uniform-spill-alloc-plan.md:0,13-33`)
   but the tie bundles carried the same disease at the assembly altitude. Response (waves 1–4):
   **delete the entire vacuous surface** (`lower_conforms_cyclic_assembled` + `_tiefree` +
   `lower_conforms_wf` + the `lower_conforms_acyclic*` family + `StmtTies`/`TermTies` + the "Plus"
   assembly + the `Spec` re-export layer) rather than paper over it
   (`docs/final-audit-2026-07-03.md:162-186`; the tombstone is `Spec/Conformance.lean`). Design
   principle vindicated: **a well-placed `sorry` is more honest than a vacuous green theorem**
   (`docs/target-architecture-2026-07-02.md:33-36`).

6. **The reshape → R0–R12 skeleton** (`RealisabilitySpec.lean` header `:15-103`). The obligations
   were reshaped so the ties are **DERIVED from the run** (R10a/b), not supplied; every formerly
   free value variable is antecedent-pinned (through the deterministic `RecorderCoupled.restart`).
   This is the current plan of record.

**Net for a reviewer:** the acyclic path (`Acyclic.lean`, the `Lir.lower_conforms` capstone at
`LowerConforms.lean:1188`) is **dead legacy**; the cyclic tie-supplied path
(`lower_conforms_cyclic'`, `DriveSim.lean:666`) is **live but superseded** (it is the vacuous
route — the honest flagship deliberately does *not* cite it, §2.2). The one true headline in
progress is `Lir.lower_conforms` in `RealisabilitySpec.lean`
(`docs/lirlean-dag-2026-07-04.md:9-12`).

---

## 4. Settled vs in-flux

**SETTLED (do not relitigate):**
- The conformance discipline: record-then-replay, permissive semantics / restrictive theorem
  (`docs/ir-design-v3.md:20-31`); forward simulation, observable-only (`:98-128`).
- **Gas** is a **log-fed exact-equality oracle** (like an external call), value `Word`; the
  gas-*monotonicity* law was proved-but-unused and **deleted** (Mono/Oracle/HonestGasTie apparatus
  gone) — `docs/gas-decision.md`, `docs/ir-design-v3.md:3`,
  `docs/target-architecture-2026-07-02.md:96-100`.
- **Uniform spill/alloc** value channel: gas/call/sload are all `.slot` spills; `Expr.callResult`
  renamed `Expr.slot`; Phases A–C DONE (`docs/uniform-spill-alloc-plan.md:172-321`).
- The **flagship shape**: pinned oracles, one `WellLowered` static bundle, `PrecompileAssumptions`
  as the sole seam (`docs/target-architecture-2026-07-02.md:47-79`).
- The 4 design decisions: HonestGasTie deleted; gasfree co-flagship proven first; tie reshape =
  recorder-suffix coupling (option i); SelfPresent wired not dropped
  (`docs/target-architecture-2026-07-02.md:94-109`).
- **CREATE goes first-class eventually** (CALL/CREATE share one `DescentKind` shape), but the IR
  surface lands post-Phase-3 (`docs/target-architecture-2026-07-02.md:182-194`); `Create.lean` is
  a dead scaffold today.
- Non-determinism / allocator / memory / data-segment directions
  (`docs/target-architecture-2026-07-02.md:154-198`) — settled *directions*, deferred *execution*.

**IN FLUX / OPEN (the restructuring review's live surface):**
- **The coupled run-producer `runFrom_of_driveCorrLog`** — does not exist; the flagship's single
  real blocker (§2.2, `RealisabilitySpec.lean:3723-3746`). Requires walking `RecorderCoupled` /
  `DriveCorrLog` (`:629`) across the F2 recursion. The `DriveCorrPlus` carrier
  (`Drive/Headline.lean:81`) is the *retained salvage*; its entry/recursion were the deleted
  vacuous apparatus (`Drive/Headline.lean:65-80,78-80`).
- **R3** (call realisation, arg-push producer, possible default-target lemma) and **R6** (boundary
  walk, 2 pure-engine geometry edge bricks) — the two hard open leaves
  (`docs/handoff-phase3-2026-07-04.md:34-42`).
- **R10a**, **R11/R11-all/gasfree**, **R12a/b**, RunFromLeft adequacy — assembly/closure that
  goes axiom-clean once the leaves land (`docs/achievements-since-main.md:110-120`).
- **The docs↔tree vocabulary drift** (§6) — a legibility hazard, not a proof gap.
- **Reorg levers** (`docs/lirlean-dag-2026-07-04.md:174-193`): collapse the SegAligned tower ×3
  (~1400→600), split `RealisabilitySpec` (extract exProg §6, ~900 LOC), kill the dead acyclic
  capstone, delete `Create.lean` / `Spec/Conformance` stub / fold `Spec/Seams`→`Audit`, directory
  reorg, trivial merges.

---

## 5. The value / gas / call channel design

The three "observed-not-modelled" values (gas, call results, sload) are **the same operation**:
compute an effectful/dynamic value once, stash it in EVM memory, reuse the stash. Only cheap pure
stable values are rematerialised (`docs/uniform-spill-alloc-plan.md:46-57`).

- **Policy vs mechanism** (`docs/uniform-spill-alloc-plan.md:59-123`): `lower = encode ∘ emit
  (allocate prog) prog`; `allocate : Program → Alloc` is the replaceable policy
  (`Loc := remat Expr | slot Nat`), `emit` the uniform alloc-driven mechanism. Default policy:
  `.slot` for gas/call/sload (correctness floor + gas-optimal), `.remat` for imm/arithmetic.
  Intended headline payoff: `lower_conforms : ∀ a, SoundAlloc prog a → conforms …`
  (`:140-164`) — every future gas-optimizing pass inherits correctness by producing a
  `SoundAlloc`. (Phase D — the `∀ SoundAlloc` quantification — is not yet landed; the tree
  currently proves the one default instance.)

- **The memory channel is bytecode-side only** (`docs/calls-value-channel-plan.md:20-31`): the IR
  (`Lir.IRState`) is NOT extended; memory is unobservable so it never enters the conformance
  statement — exactly as gas/calls are observed-not-modelled. `slotOf t = t.id * 32`
  (`:47-54`). The tie is **`MemRealises`** (a `Corr` clause): for every spilled tmp `t` bound in
  `st.locals`, the frame's memory at `slot` holds that value, with **coverage** (MLOAD grows
  `activeWords`, so bound slots must be provably covered) (`:196-214`). Threaded through
  `materialise_runs` by a `.transport` on `MatRuns.memory` (bytes-unchanged + activeWords-
  nondecreasing — the transportable form, NOT "mload-value preserved" which is false across MLOAD)
  (`:207-214`). Established by the def-site MSTORE, consumed by the use-site MLOAD, preserved by
  assign/sstore and across CALL (zero-size window ⇒ caller memory untouched:
  `resumeAfterCall_mload`, MemAlgebra.lean).

- **Gas channel** (`docs/ir-design-v3.md:32-51`, `docs/uniform-spill-alloc-plan.md:187-238`): value
  `Word` (what `GAS` pushes; realisability is then `rfl`-direct); a **supplied SEQUENCE**, zero
  IR-visible inputs, consumed head-first (`EvalStmt.assignGas` peels `obs :: T`). The honest tie is
  the **positional one-read**: the single `GAS` opcode's output = the consumed suffix head (R1;
  `stash_tail_gas` in StashTail.lean). No `∀`-over-frames, no constancy — this is what replaced
  the vacuous `GasRealises` universal.

- **Call channel** (`docs/ir-design-v3.md:53-66,112-128`, foundation `1c77c07`): now a **consumed
  `CallStream`** (`callStreamOf` maps the WHOLE recorded `CallRecord` list, consumed head-first by
  `Stmt.call`) — the same positional solution as gas. This **deleted** the former function-shaped
  `CallOracle` and the `SingleCall`/`hone` single-call restriction: distinct dynamic calls (incl.
  a per-iteration loop CALL) consume distinct stream heads (`RealisabilitySpec.lean:56-64`,
  header lesson 7). Realisability is `resumeAfterCall`-projection (`evmV2CallOracle`), `rfl`-clean.
  The success flag travels through the memory slot and binds into `locals` at `resultTmp`. The
  recorder's returning-CALL record was course-corrected to be gated on `rest.isEmpty` so it black-
  boxes descended-callee inner calls exactly as `Runs.call` does (`docs/recorder-model-note.md`,
  `docs/final-audit-2026-07-03.md:188-212`).

- **The one realisability contract** (the honest assumption, `docs/ir-design-v3.md:125-128`): the
  lowering preserves the **observable interaction sequence** — order/count of GAS reads, order of
  calls, final storage delta. Storage *writes* may be reordered; only the final delta is observed.
  This is far weaker and more lowering-agnostic than step-matching (correct for an optimizing IR
  with no step-correspondence).

---

## 6. Docs → current-tree (foundation) reconciliation map

The planning docs describe the `exp005-honesty-cleanup` branch; `main` is `foundation`, further
along. Renames/changes an agent will hit:

| docs say | tree (`main`/foundation) has | evidence |
|---|---|---|
| flagship `lowering_conforms` | `lower_conforms` (`Lir`) | commit `7cb54c2`; `RealisabilitySpec.lean:3705` |
| `lowering_conforms_all` | `lower_conforms_exact` | `:3752` |
| `lowering_conforms_gasfree` | `lower_conforms_gasfree` | `:3788` |
| `PrecompileSeams` | `PrecompileAssumptions` | `:550` |
| `r12_hypotheses_inhabited` / `r12_end_to_end` | `exProg_satisfies_hypotheses` / `exProg_nonvacuity` | `:3835,:3848` |
| function `CallOracle` + `SingleCall`/`hone`/`hsingle` | consumed `CallStream`; those premises **deleted** | commit `1c77c07`; `:56-64` |
| `Conforms` = storage only | world **+** result (halt kind / return value) | commit `4628201`; `:155-157` |
| nonzero-SSTORE scope seam / `hnzw` | **gone** (`sim_sstore` covers zero writes via `StorageErase`) | commit `1d83587`; `:96-99` |
| `Nightly` lean_lib | renamed **`WIP`** | commit `800709f`; `lakefile.lean:31-32` |
| "13 sorries remain" | **11** open sorry bodies | verified; `docs/handoff-phase3-2026-07-04.md:3` |
| `LirLean.lean` comment: "RealisabilityObligations bundle (Pattern C)" | **stale** — `Spec/Conformance.lean` is a 24-line stub | `LirLean.lean` tail vs `Spec/Conformance.lean:1-24` |
| lakefile "four headlines" comment | **stale** — two named headlines no longer exist | `docs/lirlean-dag-2026-07-04.md:164-166` |

Also stale docstrings/headers to distrust: `Drive/Headline.lean`'s "headlines deleted" note is
stale (the file is live, load-bearing — `docs/lirlean-dag-2026-07-04.md:146`); `Spec/Semantics`
self-desc "call-free prototype"; `DecodeLower`/`Spec/Lowering` refs to the deleted `Decode.lean`.
