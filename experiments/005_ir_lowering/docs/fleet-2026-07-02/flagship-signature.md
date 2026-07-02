All evidence gathered. Composing the report now.

---

# FLAGSHIP SIGNATURE — Ideal Theorem Surface for exp005

*Design-track report (1 of 5). All paths relative to `/Users/eduardo/workspace/evm-semantics/.worktrees/ir-lowering/experiments/005_ir_lowering/` unless noted. Line numbers verified against branch `exp005-honesty-cleanup` post-Phase-1 (TieDischarge.lean = 4507 lines; headline `lower_conforms_cyclic_assembled` at `LirLean/V2/TieDischarge.lean:4292`, tie-free form at `:4175`).*

## 0. Executive summary and two findings the audit understated

The good news: **all the raw material for the ideal flagship already exists in green form.** `lower_conforms_wf` (`LirLean/LowerConforms.lean:1438`) already takes `runWithLog p (seedFuel p.gas) = some log` and concludes `O.world = (observe self log.observable).world` — but it *supplies* the IR run `hir` and the ties. The cyclic headline (`TieDischarge.lean:4292`) *constructs* the IR run but does not touch `runWithLog`. The ideal flagship is the pushout of these two: entry facts from the recorder (`cleanHalts_of_runWithLog`, `LirLean/V2/DriveSim.lean:141` + `entry_corr`, `LowerConforms.lean:~1101`), run construction from the cyclic driver, ties **built** from the log. No new architecture is required — only the Phase-3 realisability closure, plus one signature-level reshape.

Two findings that sharpen the audit's "conditional headline" verdict:

**(F1) Several supplied tie conjuncts are not merely un-built — they are UNSATISFIABLE for every program the flagship targets.** The defect is a repeated free-`∀` shape: a variable is universally quantified in the tie but pinned to a run-specific value in the conclusion, with no antecedent linking it to the run.

- `StmtTies` gas conjunct (`LowerConforms.lean:1307-1323`): `∀ (ob : Word) …, stmts[pc] = .assign t .gas → Corr st0 fr0 → … ∧ ob = ofUInt64 (fr0.gas − Gbase)`. `ob` is free; if any `(st0, fr0)` inhabits `Corr` at a gas cursor (it does — take empty-locals `st0` and a constructed frame; all `Corr` fields at `SimStmt.lean:103` are satisfiable and none pins `ob`), then `∀ ob, ob = c` is false. So `hstmtties` is **unprovable for any program containing `assign _ .gas`**.
- `StmtTies` sload conjunct (`:1284-1306`): `∀ (w : Word) …, → … ∧ evalExpr st0 0 (.sload k) = some w` — same shape, `w` free.
- `StmtTies` assign conjunct (`:1275-1283`): `st0'` is quantified with **no** `EvalStmt` antecedent, and the conclusion demands `MemRealises prog st0' fr0` — by `MemRealises` (`MaterialiseRuns.lean:601`, `st.locals t = some v → mload slot = v`), choosing `st0'` binding a spilled tmp to two different values forces `mload slot` to equal both. Unsatisfiable for **any program with any spilled tmp** (gas/sload/call results are all spilled by `defsOf`, `Lowering.lean:243`).
- `TermTies` stop/ret conjuncts (`:1347-1352`, `:1353-1377`): demand `self = frT.exec.executionEnv.address ∧ (∃ cp, frT.kind = .call cp) ∧ accounts ≠ ∅` for **every** `Corr`-related `frT` — but `Corr` pins neither address nor kind, so a constructed frame with a different address refutes it.

Consequence: the current headline is not just "conditional on un-built inputs"; for every gas-, sload-, spill- or stop-using program its antecedent is **false**, i.e. the theorem is vacuous on exactly the interesting domain. This is the same disease `HonestGasTie.lean` documents for the retired `Lir.GasRealises` universal ("a single fixed word, universal over frames, unsatisfiable" — `V2/HonestGasTie.lean:20-35`), re-created one level up. It is fixed by the reshape in §3 plus threading the address/kind/presence facts through the walk invariant (§5, decision 4).

**(F2) The headline's IR trace `T` is universally quantified** (`TieDischarge.lean:4294`, `{T : Trace}` implicit, conclusion `RunFrom prog o st₀ T prog.entry O`). A theorem provable "for any gas stream whatsoever" is only possible because the vacuous ties rewrite every consumed read; the honest flagship must pin `T := realisedGas log` and `o := realisedCall log self`. Related: `callOracleOf` (`V2/RunLog.lean:263-266`) reads **only the first** `CallRecord` — the log-fed call oracle is correct only for single-CALL programs (documented, but it caps the flagship's scope and should be surfaced in the statement or generalized; see §2.3).

---

## 1. The ideal flagship statement

### 1.1 Helper definitions (spec-file material, all `Prop`/`def` one-liners)

```lean
namespace Lir.V2

/-- The IR entry state of a top-level call: empty locals, world = the recipient's
storage lens of the pre-call accounts. Replaces the supplied `hstore : StorageAgree …`
(`LowerConforms.lean:1200`) by *definition* — the entry world IS the params' lens. -/
def entryState (params : Evm.CallParams) : IRState :=
  { locals := fun _ => none, world := fun k => storageAt params.accounts params.recipient k }

/-- The recorded run halted cleanly: `.success`/`.revert`, not OOG/exception.
DECIDABLE ON THE LOG — replaces the `∀ last halt, Runs … → HaltNonException halt`
premise of `cleanHalts_of_runWithLog` (`V2/DriveSim.lean:146`). -/
def RunLog.clean (log : RunLog) : Prop := ResultNonException log.observable   -- decidable

/-- Observable agreement, world channel (halt-result channel: documented empty-RETURN
cut, `V2/RunLog.lean:296-299`). -/
def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world

/-- STATIC well-formedness of the lowering — a function of the program text only,
intended to be decidable (`wellLowered_of_check : lowerCheck prog = true → WellLowered prog`). -/
structure WellLowered (prog : Program) : Prop where
  wf      : WellFormedLowered prog          -- LowerConforms.lean:143 (fuel/pc/offset/slot)
  defs    : RunDefinable prog               -- V2/IRRun.lean:257 (operand definability)
  entry0  : prog.entry.idx = 0
  closed  : ClosedCFG prog                  -- entry + every jump/branch target present
                                            -- (folds hpresent/hjumpPresent/hbranchPresent)
  stack   : StackRoomOK prog                -- folds hstkBranch (:4325) + the hstkKey-style
                                            -- per-cursor 1024 bounds (StmtTies :1301, :1332)

/-- The HONEST oracle seams — the precompile boundary, both faces
(headline-transitive-chain.md §3.3/§3.4: "the same boundary from two angles").
Vacuous for call-free programs. -/
structure PrecompileSeams (prog : Program) (params : Evm.CallParams) : Prop where
  noErase   : ∀ cp imm, Evm.beginCall cp = .inr imm →
                ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts   -- hprec, TieDischarge :3478
  callsCode : ∀ fr', ReachableFrom params fr' → CallsCode fr'               -- V2/Modellable.lean:435
```

### 1.2 The flagship

```lean
/-- **FLAGSHIP.** Run the lowered bytecode once with the recording interpreter; feed the
recorded gas reads and call records into the executable IR semantics; the IR run exists,
consumes exactly the recorded streams, and produces the same observable world. -/
theorem lowering_conforms
    {prog : Program} {params : Evm.CallParams} {log : RunLog} {acc : Account}
    -- what we ran (definitional pins, not side conditions):
    (hcode : params.codeSource = .Code (lower prog))
    (hmod  : params.canModifyState = true)
    -- world/gas wellformedness of the entry call (decidable per `params`):
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas  : GasConstants.Gjumpdest ≤ params.gas.toNat)
    -- the static, checkable lowering well-formedness:
    (hwl   : WellLowered prog)
    -- THE RUN (the single runtime premise):
    (hrun  : runWithLog params (seedFuel params.gas) = some log)
    -- honest scope boundary, read off the log:
    (hclean : log.clean)
    -- the two designed oracle seams (precompile boundary; vacuous if call-free):
    (hseams : PrecompileSeams prog params) :
    ∃ O : Observable,
      RunFrom prog (realisedCall log params.recipient)
        (entryState params) (realisedGas log) prog.entry O
      ∧ Conforms params.recipient log O
```

This is Eduardo's target sentence verbatim: *"lowering the program to bytecode and collecting the logs for external calls and gas and then supplying those values through our executable IR semantics yields the same observables."* One runtime premise (`hrun`), one decidable scope premise (`hclean`), one decidable static bundle (`hwl`), two decidable entry facts, one honest seam structure. Everything else from the current signature is either derived or pinned by definition.

Recommended strengthenings (cheap, worth doing):
- **Exact stream consumption**: conclusion variant asserting the IR run consumes the *entire* `realisedGas log` (currently `RunFrom` discards the leftover trace — `V2/Machine.lean:231-242` drop `T'`). Without it, "positional equality" is only over the consumed prefix. A `RunFromAll` wrapper (`RunFrom … ∧ leftover = []`) or an existential leftover pinned to `[]` closes the last vacuity channel.
- **`hrb` residue**: the pc-reachability fact `AtReachableBoundary` (`V2/Modellable.lean:407`) is *deliberately absent* from the signature above because it is dischargeable (obligation R6, §6) — the Track-A boundary walk. Until R6 lands, it appears as a sorry'd lemma, not a flagship hypothesis.

### 1.3 Hypothesis-by-hypothesis comparison with `lower_conforms_cyclic_assembled` (:4292)

| Current hypothesis (TieDischarge.lean) | Fate in ideal flagship |
|---|---|
| `hbase : DriveCorr …` (:4295) | **Derived**: `entry_corr` + `cleanHalts_of_runWithLog` (`DriveSim.lean:141`) from `hrun`+`hclean`+`hseams.callsCode`+R6(`hrb`) |
| `hwf : accounts.find? recipient = some acc` (:4296) | **Kept** as `hself` — honest world wellformedness, decidable per `params` |
| `hdef : RunDefinable` (:4297) | **Folded** into `WellLowered.defs`; static (see caveat, §2 row 3) |
| `hcall : CallPreservesSelf` (:4298) | **Replaced** by `hseams.noErase` (=`hprec`); derived internally via `callPreservesSelf_modGuards` (:3478) — the audit §4#4 wiring fix |
| `hpresent` (∀ DriveCorrPlus → block present) (:4299) | **Eliminated**: restructure — thread presence in the walk invariant, seed from `WellLowered.closed` |
| `hwfl : WellFormedLowered` (:4305) | **Folded** into `WellLowered.wf` |
| `hstmtties` (:4307) / `htermties` (:4309) | **Built** from `hrun` (Phase 3, obligations R1–R5, §6) after the §3 reshape |
| `hjumpPresent`/`hbranchPresent` (:4311/:4316) | **Folded** into `WellLowered.closed` (static CFG closure) |
| `hstkBranch` (:4325) | **Folded** into `WellLowered.stack` (static bound; `chargeOf` length is structural) |
| implicit `{T : Trace}`, `{o : CallOracle}`, `{st₀}`, `{obs}`, `{sloadChg}` (:4292-4294) | **Pinned**: `T := realisedGas log`, `o := realisedCall log self`, `st₀ := entryState params`; `obs` is a **phantom** parameter (no `Corr` field at `SimStmt.lean:103-133` mentions it) — delete; `sloadChg` survives only in `chargeOf` lengths/envelopes — pin to the log-derived resolver or existentially close inside the proof |
| (not present) `runWithLog … = some log` | **The** runtime premise (borrowed from `lower_conforms_wf`, `LowerConforms.lean:1442`) |
| (not present) conclusion pins to `log.observable` | Conclusion is `Conforms` against the log (via `runWithLog_messageCall`, `RunLog.lean:650`), not just "∃ some halt world" |

---

## 2. Hypothesis classification table

Legend: **(a)** dischargeable → tracked sorry-debt; **(b)** honest seam → documented interface; **(c)** should not exist → restructure.

### 2.1 Top-level hypotheses

| Hypothesis | Class | Justification (file:line) |
|---|---|---|
| `hbase.corr` (entry `Corr`) | (a) | `entry_corr` already green (`LowerConforms.lean:~1101`); entry world pinned by `entryState` definition instead of supplied `hstore` (:1200) |
| `hbase.cleanHalts` (`CleanHaltsNonException`) | (a) from log + (b) scope | `cleanHalts_of_runWithLog` green (`DriveSim.lean:141`); its `hne` becomes decidable `log.clean` (R2); its `hcc` stays seam; its `hrb` is debt (R6). The *scope restriction itself* (non-exception runs only) is the honest, settled domain boundary — keep documented |
| `hwf` accounts-find | (b) | World wellformedness: you call code at an existing account; feeds `selfPresent_codeFrame` (`TieDischarge.lean:~3555`); decidable per `params` |
| `hdef : RunDefinable` | (a), with a flag | Static per program (`IRRun.lean:257`). **Flag:** its `∀ st` quantification ("definable from ANY state") is an over-approximation that only holds for programs whose block operands are block-locally defined or spilled; fine for the toy IR, will not survive the real Plank IR — the honest future shape indexes definability by reachable states or has the lowering enforce def-before-use. Track as a known altitude issue, not flagship-blocking |
| `hcall : CallPreservesSelf` | (c) as-supplied → (b) via `hprec` | The 260-line discharge chain exists and is unwired (audit §4#4); take `hprec` (`callPreservesSelf_modGuards`, `TieDischarge.lean:3478`) and derive `hcall` internally. `hprec` itself: **(b)** — a live precompile's `.inr` arm genuinely can erase (docstring :3486-3494) |
| `hpresent` | (c) | Quantifying over the walk invariant (`DriveCorrPlus`) in a *hypothesis* is inside-out; presence of reached labels is an induction consequence of entry-present + `WellLowered.closed` — thread `∃ b, blockAt prog L = some b` in the invariant |
| `hwfl : WellFormedLowered` | (a) | Purely structural (`LowerConforms.lean:143-215`); `MatFueled` fields from def-graph acyclicity (`Acyclic.lean:198`); bounds finite checks. Belongs in `WellLowered` with a checker lemma |
| `hjumpPresent`/`hbranchPresent` | (a) | Static CFG closure, decidable (chain doc §4: "decidable from the CFG text") |
| `hstkBranch` | (a) | `chargeOf` length is a function of program text (`:4325-4327`); decidable fold into `WellLowered.stack` |
| `hstmtties`/`htermties` | mixed | Per-conjunct below |

### 2.2 StmtTies conjuncts (`LowerConforms.lean:1273-1337`)

| Conjunct | Class | Justification |
|---|---|---|
| assign: target-not-spilled, `StepScoped` (:1278-1279) | (a) | Structural scoping facts of `defsOf`/program text |
| assign: post-state locals scoping over free `st0'` (:1280-1282) | (c) | Free-`∀ st0'` — degenerates to a static defs-totality property in disguise; restate statically |
| assign: `MemRealises prog st0' fr0` (:1283) | (c) → (a) | **Unsatisfiable as shaped (F1)**; pin `st0'` to the `EvalStmt` post-state; then it is the invariant `Corr.memAgree` preserved (assign/sstore don't touch memory — the comment at `SimStmt.lean:127-133` already says so) |
| sload: slot registration, `StepScoped`, slot-canonicity (:1287-1289) | (a) | Structural (`defsOf` shape) |
| sload: `evalExpr st0 0 (.sload k) = some w` free `w` (:1290) | (c) → (a) | **Unsatisfiable as shaped (F1)**; after reshape, the value is the storage lens — derived from `Corr.storage` |
| sload: addressability + stack-room + `hawk` activeWords-flatness (:1300-1306) | (a) | Addressability/stack-room static (`Corr.stack_nil` makes the frame term = 0); `hawk` dischargeable from `MemRealises` coverage (an MLOAD of a covered slot does not expand) — modest proof debt |
| gas: slot registration, `StepScoped`, canonicity (:1310-1312) | (a) | Structural |
| gas: `ob = ofUInt64 (fr0.gas − Gbase)` (:1318) | (c) → (a) | **The** reshape target (F1, §3). After reshape: the R1 recorder bridge — recorded head = machine GAS output (`driveLog` records exactly `UInt256.ofUInt64 exec.gasAvailable` at top-level GAS steps, `RunLog.lean:188-190`) |
| sstore: `StepScoped`, stack-room (:1328-1333) | (a) | Structural/static |
| sstore: `∃ acc, SstoreRealises fr0 kw vw acc` (:1334; def `SimStmt.lean:318`) | split (a)/(b) | Gas half (stipend + EIP-2200 charge) **derived** from clean-halt (chain doc §3.1, already done for the materialise envelopes); presence half = `SelfPresent` — **(b)-flavored world invariant**, but *threadable*: seeded by `hself`, preserved by `stepPreservesSelf` (proved, `TieDischarge.lean:~3046`) + `callPreservesSelf_modGuards hprec`. So: derived-through-the-walk given the `hprec` seam → (a) with `hprec` as the only residue |
| call: `CallRealises` (:1335-1337; def :261) | kernel (b), plumbing (a) | Kernel: `CallReturns` + oracle pin `o = evmV2CallOracle result pd self` — grounded by the log (`realisedCall_eq_evmV2`, `RunLog.lean:280`, rfl-clean) + the child-run observation; **(b)**. Plumbing: arg-push `Runs`+pins (from `materialise_runs`), resume pins (rfl on `resumeAfterCall`), Route-B tail (`stash_tail_runs` exists — audit §4#1 says "dischargeable yet supplied"); **(a)**. Post-state scoping conjunct (:290-297): static, (a) |

### 2.3 TermTies conjuncts (`LowerConforms.lean:1342-1423`)

| Conjunct | Class | Justification |
|---|---|---|
| successor presence (:1344-1346) | (a) | Static; `WellLowered.closed` |
| stop: `self = frT.address`, `kind = .call`, `accounts ≠ ∅` (:1347-1352) | (c) → (a) | **Unsatisfiable as shaped (F1)**: `Corr` pins none of these. Restructure: add `addr`/`kind`/`selfPresent` fields to the walk invariant (they are exactly what `DriveCorrPlus.selfPresent` + two new rfl-preserved fields provide); `accounts ≠ ∅` from `accounts_ne_empty_of_selfPresent` — the dead wrappers `driveCorrPlus_step_stop/_ret` were built for precisely this (audit §4#3) |
| ret: same address/kind/nonempty facts + `∃ vw` operand (:1353-1377) | (c) → (a) | Same restructure; `∃ vw` duplicates `RunDefinable.ret_def` (`IRRun.lean:262`) |
| ret: charge gas envelope + 1024 bound (:1358-1360) | (a) | Envelope from clean-halt extractor (pattern of `materialise_runs_of_cleanHalt`); bound static |
| ret: RETURN-epilogue decode facts (:1361-1377) | (a) | Decode facts of `lower prog` at static offsets — `DecodeLower`/`DecodeAnchors` machinery territory |
| jump: 3-step gas guards (:1378-1391) | (a) | Derivable from the threaded `CleanHaltsNonException` — the assembled headline already does this discharge for the *edge bundle* via `jump_landing_of_cleanHalt` (:4345-4371); the same extractor discharges the tie-level guards |
| branch: `MatRuns` existence + 6 gas guards (:1392-1423) | (a) | `materialise_runs_of_cleanHalt` (`MaterialiseCleanHalt.lean:377`) + clean-halt extractor; mirror of `branch_landing_of_cleanHalt` (:4372-4413) |

### 2.4 Residual honest-seam surface (the (b) set — matches chain doc §6 "Net")

1. `hprec` — precompile no-erase (`TieDischarge.lean:3478`).
2. `CallsCode` — reachable CALLs target code accounts (`Modellable.lean:435`).
3. `CallReturns`/`V2.CallOracle` kernel — the child-run observation (`003_bytecode_layer/BytecodeLayer/Hoare.lean:91`, `V2/Machine.lean:96`).
4. `log.clean` — the non-exception scope premise (decidable on the log; the *restriction* is honest, the *hypothesis form* is checkable).
5. `hself` + `hgas` + `hcode` + `hmod` — decidable entry-call wellformedness.

Plus one **flagged gap**: `callOracleOf` single-record limitation (`RunLog.lean:263-266`) — for multi-CALL programs the function-shaped `CallOracle` (`Word → Word → World → World × Word`) cannot distinguish two dynamic calls with identical IR-visible inputs but different EVM outcomes. The gas channel already solved this problem positionally (a consumed stream); the honest completion is to make calls **also a consumed stream** of records (or index the oracle by occurrence). This touches `EvalStmt.call` (`Machine.lean:187-196`) and is the one place the settled "calls are a queried function, not events" doc position (`Machine.lean:82-96`) conflicts with log-fed exactness. Recommend: state the flagship now with a `SingleCall prog ∨` positional generalization decision explicitly recorded; do not silently ship a flagship that is wrong for two-CALL programs.

---

## 3. StmtTies/TermTies reshape (remediation open decision #3)

**Recommendation: option (i), consumed-trace-prefix indexing, implemented as "recorder-restart coupling" carried by the drive invariant.** Repurpose `DriveCorrPlus`'s accumulator slots (`TieDischarge.lean:3589-3601`) — currently four vacuously-empty lists — into **one real coupling field**:

```lean
/-- The remaining recorded streams: restarting the recorder at the current boundary
frame reproduces exactly the un-consumed suffix of the log. -/
aligned : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] []
            = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix)
```

with the tie conjuncts becoming, at a gas cursor: *"the head of `gasSuffix` is `ofUInt64 (fr.gas − Gbase)` and the post-statement invariant holds at `gasSuffix.tail`."*

Why this option:

1. **It matches the IR semantics' consumption shape exactly.** `EvalStmt.assignGas` consumes the stream head (`Machine.lean:175-176`); `RunStmts`/`RunFrom` thread `T` left-to-right; `driveLog` appends per top-level GAS step in program order (`RunLog.lean:188-190`). Head-consumption ↔ append-order aligns under a single left-to-right induction — the same induction `sim_stmts_drop` (`SimStmts.lean:~95`) already performs, so the coupling threads where the proof already walks.
2. **It is cyclic-correct.** A loop revisits the same cursor `(L, pc)` with *different* gas values on each iteration. Any per-cursor scheme is unsound here (see option iii below); suffix-indexing handles multiplicity for free.
3. **It black-boxes child calls correctly.** The recorder gates recording on `stack.isEmpty` (`RunLog.lean:188`), so a descended CALL's internal GAS reads never enter the log; the restart-coupling steps over a `CallReturns` edge by one recorder-composition lemma (descend, run child, resume — `driveLog`'s own recursion), mirroring how `Runs.call` black-boxes the child.
4. **It is the verifereum `Collect`/`Enforce` pattern** the remediation plan names as the one to copy (remediation-plan §"Prior-art lessons"), and it converts the audit's "vacuous alignment channel" (§4#2) into the load-bearing thing it pretended to be — minimal conceptual churn, honest lineage.

Blast radius (moderate, and coincides with already-planned work): `TieDischarge.lean` walk signatures (~15–20 lemmas: replace 4 accumulator params with the suffix params), the two `StmtTies` value conjuncts + `simStmtStep_block`'s gas/sload arms (`LowerConforms.lean:1307-1323`, `:398`), `SimStmts.lean` spine threading, plus ~300–500 new lines of recorder step/restart/determinism lemmas in `RunLog.lean` (R1/R7 in §6). **No change to `Machine.lean`/`IRRun.lean`** (the IR spec surface is untouched — important for reviewability).

Rejected options:

- **(ii) existential supplied-by-recorder** ("∃ ob, consumed = ob ∧ ob = gasReadOf fr"): an existential in a hypothesis cannot pin the `∀`-quantified `EvalStmt` inside `SimStmtStep` (`SimStmts.lean:66-74`) to *the* run's value; to know which value each cursor-visit consumed you need positional coupling anyway. Same eventual cost, weaker statement, messier assembly.
- **(iii) per-cursor value function** (`gasAt : Label → Nat → Word`): **unsound for cyclic CFGs** — the same cursor is visited multiple times with strictly-descending gas, so no function of the cursor exists. Adopting it would silently re-restrict the flagship to acyclic programs, forfeiting the project's genuinely novel result (the `totalGas`-measure cyclic driver, `Measure.lean:59`/`DriveSim.lean:97`). Smallest signature churn, fatal semantics.

---

## 4. Open decisions 1, 2, 4

**Decision 1 — `HonestGasTie.lean`: DELETE (option b), with one condition.** Concur with the previous agent and the remediation plan's own lean. Signature-level reasoning: a regression witness guards a *live* definition against a *live* failure mode; after Phase 2 the guarded universal (`Lir.GasRealises`) and its positive twin (`Oracle.GasRealises`, `V2/Oracle.lean:98`) both leave the tree, so the file guards nothing reachable — and keeping it forces keeping `Oracle.lean` (the entanglement that is blocking Phase 2). The inline-minimal option (a) preserves a guard for a definition that will cease to exist — dead weight by construction; defer (c) leaves misleading gas-law files in-tree during the flagship rebuild, the worst outcome for a reviewer. The condition: the true non-vacuity witness must change owners — the two unsatisfiability *statements* get one paragraph in the Phase-3 spec file's header (docs, not code), and the concrete end-to-end instantiation (R12 below) becomes the machine-checked non-vacuity evidence. Delete the file in the same commit that adds the spec file, so there is never a window with no recorded lesson.

**Decision 2 — gas-introspection-free secondary theorem: co-flagship, and prove it FIRST.** With the §3 reshape, `lowering_conforms_gasfree` is the flagship restricted to `NoGasReads prog` (a static predicate): the gas suffix is `[]`, R1 is vacuous, and the sload channel needs no positional bridge either (post-Phase-C, sload *values* come through the storage lens `Corr.storage`; warmth enters only charge envelopes, which are clean-halt-derived). That makes it precisely the fork-shaped theorem (Verity/vyper-hol scope, gas-decision.md §3) and — decisively — the **de-risking milestone**: it exercises every Phase-3 obligation except the riskiest one (the R1 recorder bridge). Signature-level cost: one theorem statement + one `NoGasReads` predicate; the proof is the flagship spine minus one arm. Document it as co-flagship in PLAN.md (it is the theorem external readers can compare to prior art), with the full flagship as the headline.

**Decision 4 — `SelfPresent`: WIRE IT LOAD-BEARING; do not drop.** The field looks like a passenger only because its consumers were never wired (audit §4#3) — but Phase 3 *needs* it twice: (1) building `StmtTies.sstore`'s `SstoreRealises` presence conjunct (`SimStmt.lean:318`, conjunct 3 — the storage seam's irreducible residue per chain doc §3.1) requires self-presence *at the SSTORE frame*, which is exactly the threaded invariant seeded by `selfPresent_codeFrame` and preserved by `stepPreservesSelf` (proved) + `callPreservesSelf_modGuards hprec`; (2) killing the unsatisfiable `TermTies` stop/ret conjuncts (§2.3) requires the invariant to carry `accounts ≠ ∅` (via `accounts_ne_empty_of_selfPresent`) plus the address/kind pins. Dropping the field in Phase 2 and re-adding it in Phase 3 is churn with an intervening state where the walk invariant is *weaker than what Phase 3 needs* — skip the round-trip. Keep `hwf`/`hself` as the honest entry premise; extend the invariant with the two rfl-preserved companions (`fr.exec.executionEnv.address = self`, `∃ cp, fr.kind = .call cp`) in the same edit.

---

## 5. The honest-sorry skeleton (Phase 3 as a reviewable spec file)

Proposed file: `LirLean/V2/RealisabilitySpec.lean` — statements only, every proof `sorry`, imported by nothing in the main target (nightly-built), with a top docstring declaring "each `sorry` here is tracked debt; the flagship in `Flagship.lean` is conditional on this file becoming sorry-free." Spec/proof separation per Eduardo's standard: this file IS the reviewable spec; proofs land in sibling `Realisability/*.lean` files that restate nothing.

```lean
/- R0 — SHAPE FIX (not a sorry; the §3 reshape prerequisite):
   StmtTies/TermTies value conjuncts re-stated with recorder-suffix coupling;
   the free-∀ (ob / w / st0' / frT-address) shapes eliminated. -/

-- R1 — the gas recorder bridge (the S3 trace↔recorder positional bridge)
theorem gas_suffix_head_realised
    (hcoupling : RecorderCoupled log fr gasSuffix sloadSuffix callSuffix)
    (hcorr : Corr prog sloadChg st fr L pc)
    (hgascur : b.stmts[pc]? = some (.assign t .gas)) :
    gasSuffix.head? = some (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))
    := sorry

-- R2 — clean scope read off the log (replaces the ∀-last-halt `hne`)
theorem haltNonException_of_cleanLog
    (hrun : runWithLog params (seedFuel params.gas) = some log) (hcl : log.clean) :
    ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt → HaltNonException halt := sorry

-- R3 — call realisation from the log (kernel from CallRecord; plumbing from
--      materialise_runs + resumeAfterCall rfl-pins + stash_tail_runs)
theorem callRealises_of_recorded
    (hcoupling : RecorderCoupled log fr …) (hcallcur : b.stmts[pc]? = some (.call cs)) :
    CallRealises prog sloadChg (realisedCall log self) L b pc cs st fr := sorry
-- R3': the multi-call decision — either `SingleCall prog` hypothesis, or calls
--      become a consumed stream (flagged design decision, §2.4)

-- R4 — SSTORE realisation through the threaded invariant (SelfPresent wired)
theorem sstoreRealises_of_walk
    (hsp : SelfPresent fr) (hcs : CleanHaltsNonException fr) … :
    ∃ acc, SstoreRealises fr kw vw acc := sorry

-- R5 — terminator ties from the walk (address/kind/nonempty from the invariant;
--      gas guards from the clean-halt extractor; epilogue decode from DecodeAnchors)
theorem termTies_of_walk … : TermTies' prog … L b := sorry

-- R6 — the boundary walk (Track A; discharges `hrb`)
theorem runs_atReachableBoundary
    (hbegin : beginCall params = .inl fr₀) (hcode : params.codeSource = .Code (lower prog)) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := sorry

-- R7 — recorder-coupling preservation (the new invariant's three edge lemmas)
theorem recorderCoupled_step  … := sorry   -- one .next step (GAS/SLOAD pop the head)
theorem recorderCoupled_call  … := sorry   -- across a CallReturns edge (child black-boxed)
theorem recorderCoupled_entry
    (hrun : runWithLog params (seedFuel params.gas) = some log) :
    RecorderCoupled log fr₀ log.gas log.sloads log.calls := sorry

-- R8 — presence threading (kills hpresent): reached labels are present
theorem present_of_walk (hclosed : ClosedCFG prog) … : ∃ b, blockAt prog L = some b := sorry

-- R9 — the static checker (makes WellLowered supply-free per program)
theorem wellLowered_of_check (h : lowerCheck prog = true) : WellLowered prog := sorry

-- R10 — assembly: ties BUILT
theorem stmtTies_of_runWithLog … : ∀ L b, blockAt prog L = some b → StmtTies' … := sorry
theorem termTies_of_runWithLog … : ∀ L b, blockAt prog L = some b → TermTies' … := sorry

-- R11 — THE FLAGSHIP (assembly of R1–R10; §1.2 statement verbatim)
theorem lowering_conforms … := sorry

-- R12 — the non-vacuity witness: one concrete `lower prog` (gas + sload + call + loop),
--       run end-to-end, `lowering_conforms` instantiated, observables computed
--       (verifereum `deploy_result_correct` template; replaces HonestGasTie's role)
example : … := sorry
```

Suggested landing order (each step keeps the build green with fewer sorries): **R0 → R9 → R2 → R8 → R5/R4 → R6 → co-flagship (gasfree, needs no R1) → R7 → R1 → R3 → R10 → R11 → R12.** The gasfree co-flagship lands mid-sequence as the de-risking checkpoint (decision 2).

---

## 6. One-paragraph verdict

The flagship Eduardo wants is one theorem away from the material in the tree: `lower_conforms_wf` already speaks `runWithLog`, the cyclic driver already constructs the IR run, and the recorder already produces `realisedGas`/`realisedCall` with rfl-clean bridges. What stands between is (1) a shape bug — the free-`∀` tie conjuncts are unsatisfiable for exactly the programs that matter, so the reshape (§3, recorder-suffix coupling) is not polish but a correctness precondition for Phase 3; (2) the wiring debts the audit already named (`hprec` variant, `SelfPresent` consumers); and (3) the R-obligations of §5, of which only R1 (gas bridge), R3 (call plumbing) and R6 (boundary walk) are substantial proofs — everything else is static folds and assembly. The ideal signature (§1.2) has **one runtime premise, five decidable premises, and one two-field seam structure**; every seam in it is one of the four the transitive-chain report already blessed as irreducible.