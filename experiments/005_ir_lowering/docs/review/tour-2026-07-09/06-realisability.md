# 06 — Realisability: the flagship `lower_conforms` and what actually remains

Part of the [exp005 tour](00-overview.md). Upstream: [01-trusted-base](01-trusted-base.md)
(engine + Hoare layer), [02-spec-layer](02-spec-layer.md) (the `Spec/` statement surface),
[03-code-geometry](03-code-geometry.md) (the `Decode/` byte algebra that feeds R6),
[04-value-channel](04-value-channel.md) (Materialise/Frame), [05-simulation](05-simulation.md)
(the coupling-free `Sim/` path this layer deliberately bypasses). Downstream:
[07-assembler](07-assembler.md).

**Scope**: `LirLean/V2/Realisability/` in full, `LirLean/V2/Drive/`, plus the call-channel
companions [`V2/Call.lean`](../../../LirLean/V2/Call.lean),
[`V2/CallRealises.lean`](../../../LirLean/V2/CallRealises.lean),
[`V2/RecorderLemmas.lean`](../../../LirLean/V2/RecorderLemmas.lean).
Source state as read on **2026-07-09**, local `main` at `c760145`.

---

## TL;DR

The experiment's target is one theorem:
[`lower_conforms`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L251) — run the
lowered bytecode once under a recording interpreter, feed the recorded gas/call/create
events back into the executable IR semantics as oracle streams, and the IR run exists and
produces the same observable world and result. The statement (and its exact-consumption and
gas-free siblings) is final and, after two vacuity postmortems, carefully shaped so that
nothing run-dependent is *supplied*: the per-block ties are **derived from the run** through
a recorder-restart coupling
([`RecorderCoupled`](../../../LirLean/V2/Realisability/Surface.lean#L234)). The folder is
majority-proved — R0b/R1/R2/R4/R5/R7(a–e′)/R8/R9/R10b, the entry seeds, three of the five
coupled statement arms, `conforms_of_worldeq`, and the whole witness stack are closed — but
the flagship proof is not: **16 `sorry`s across 15 declarations remain, concentrated in the
coupled run-producer
[`runFrom_of_driveCorrLog`](../../../LirLean/V2/Realisability/Producer.lean#L1442) and the R6
boundary geometry, plus one latent obligation with no placeholder: the CREATE
suffix/coupling channel.** Verification status, once: the default `lake build` cone is
sorry-free (sorries live only in the non-default `WIP` lib, confirmed by grep against
current source); both builds reported green at this census by the
[r11 plan checkpoint](../../planning/r11-plan-2026-07-08.md) (reported, not re-run); the WIP
declarations intentionally carry `sorryAx` and have no axiom guards
([by design](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L424)).

---

## 1. Why it is still open: the history in three beats

**(a) The original headline was vacuous.** The pre-July headline
(`lower_conforms_cyclic_assembled`, since deleted) supplied per-block `StmtTies`/`TermTies`
hypotheses universally quantified over frames. The
[2026-07-02 audit](../../audit-2026-07-02.md) demoted it to a conditional; the skeptic drill
([skeptic-f1-verdict](../../fleet-2026-07-02/skeptic-f1-verdict.md)) then confirmed the
supplied ties are **unsatisfiable for essentially every nonempty program** — a tie variable
(`ob`, `w`, `st0'`, the `TermTies` address/kind/gas demands) was ∀-bound in the hypothesis
but pinned to a run-specific value in the conclusion, with no antecedent linking it to the
run; one adversarial frame refutes it. The apparatus was deleted on 2026-07-03
([final audit](../../final-audit-2026-07-03.md)); the deletion is recorded in the
[`Drive/Headline.lean` header](../../../LirLean/V2/Drive/Headline.lean#L17). The surviving
in-tree driver
[`lower_conforms_cyclic'`](../../../LirLean/V2/Drive/DriveSim.lean#L661) is itself honest
about its own restriction: its `RunDefinable` premise is
[unsatisfiable for any program using `.call`/`.gas`](../../../LirLean/V2/Drive/DriveSim.lean#L666)
— it covers only the pure fragment, and is explicitly **not** the R11 proof route.

**(b) The repair: ties must be derived from the run.** The
[target architecture](../../target-architecture-2026-07-02.md) settled the reshape: the walk
invariant carries one real coupling field — *restarting the recording interpreter
(`driveLog`) at the current boundary frame reproduces the run's final observable and exactly
the un-consumed suffixes of the recorded streams*. Because
[`driveLog`](../../../LirLean/Spec/Recorder.lean#L51) is a deterministic function, the
restart equation pins every formerly-free tie value to the suffix head; the reshaped ties
[`StmtTies'`](../../../LirLean/V2/Realisability/Surface.lean#L351)/
[`TermTies'`](../../../LirLean/V2/Realisability/Surface.lean#L457) are then **built** from
the run (`R10`), never supplied. Eight numbered "vacuity lessons" shaping the statements are
recorded in the
[`RealisabilitySpec` header](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L17)
— including three found *during* the reshape (the unsatisfiable `SstoreRealises`, the
unsatisfiable `RunDefinable`, and the loop-rebinding refutation of `StepScoped` at the
project's own witness program).

**(c) The current state: an R0–R12 skeleton with debt concentrated in the run-producer.**
All `def`s/`structure`s are real; only theorem proofs are `sorry`d, each a named obligation.
The three flagship shells have real proof bodies that `obtain` exactly one blocker — the
coupled producer
[`runFrom_of_driveCorrLog`](../../../LirLean/V2/Realisability/Producer.lean#L1442) — and
close the `Conforms` half via the fully-proved
[`conforms_of_worldeq`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L204).
The authoritative execution plan is
[r11-plan-2026-07-08](../../planning/r11-plan-2026-07-08.md) (chunks 0–8; chunk 0 wiring is
landed, chunk 1 is partially landed — see §5).

---

## 2. The three flagship shells, verbatim

All three live in
[`RealisabilitySpec.lean`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean), the
root of the non-default `WIP` lib
([lakefile](../../../lakefile.lean#L31): `lake build` = sorry-free default cone,
`lake build WIP` = this tracked-debt cone).

### 2.1 [`lower_conforms`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L251) (R11, plain)

```lean
theorem lower_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O
```

Gloss of the hypothesis ledger:

| Hypothesis | Kind | Meaning |
|---|---|---|
| `hcode` | definitional pin | the call's code source is exactly the lowered bytes ([`lower`](../../../LirLean/Spec/Lowering.lean)) of `prog` |
| `hmod` | definitional pin | a state-modifying (non-static) call — SSTORE/CALL are legal |
| `hself` | decidable entry fact | the recipient (self) account exists in the pre-call world; seeds [`SelfPresent`](../../../LirLean/V2/Drive/SelfPresent.lean#L353) |
| `hgas` | decidable entry fact | enough gas to execute the entry `JUMPDEST` (the walk's first step) |
| `hwf` | static, program text | [`IRWellFormed`](../../../LirLean/Spec/WellFormed.lean#L430): define-before-use SSA, `defsOf` consistency, closed CFG, ordered def-env, per-block revalidation, slot addressability |
| `hcodeFits` | static scalar budget | [`codeFits`](../../../LirLean/Spec/WellFormed.lean#L390) `= (flatBytes prog).length < 2^32` — whole code fits a 32-bit pc |
| `hstk` | static scalar budget | [`stackFits`](../../../LirLean/Spec/WellFormed.lean#L413) `= maxChargeDepth prog ≤ 1024` — every materialise fits the EVM stack |
| `hrun` | THE runtime premise | the recording interpreter [`runWithLog`](../../../LirLean/Spec/Recorder.lean#L93), at fuel `seedFuel params.gas`, terminates and returns `log` |
| `hclean` | decidable scope | [`RunLog.clean`](../../../LirLean/Spec/Conformance.lean#L15): recorded outcome is `success ∨ gasRemaining ≠ 0` — non-exception; a genuine zero-gas revert is conservatively out of scope (indistinguishable from OOG on the log) |
| `hseams` | the honest seam bundle | [`PrecompileAssumptions`](../../../LirLean/Spec/Seams.lean#L31), below |

The three genuinely-assumed seams:

```lean
structure PrecompileAssumptions (prog : Program) (params : Evm.CallParams) : Prop where
  noErase : Lir.Spec.PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'
```

— [`Spec/Seams.lean#L31`](../../../LirLean/Spec/Seams.lean#L31). `noErase`: a precompile's
immediate result never erases an account that was present (feeds the `.success` arm of
[`callPreservesSelf_modGuards`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L214)).
`callsCode`/`createResolves`: every reachable child CALL targets code (not a precompile) and
every reachable CREATE resolves — the exp003 engine's modellability side conditions, which
are not structural facts of the machine. This matches the seam census in
[headline-transitive-chain](../../headline-transitive-chain.md). Note `ReachableFrom`
([`Seams.lean#L28`](../../../LirLean/Spec/Seams.lean#L28)) quantifies over the whole
execution — these are trace-quantified hypotheses, but of the benign kind: they constrain
the *environment* (which addresses are precompiles), not the program's behaviour, and are
satisfied by any world whose called addresses hold code.

The conclusion: there is an IR observable `O` such that (i) the executable IR big-step
[`RunFrom`](../../../LirLean/Spec/Semantics.lean#L99) runs `prog` from the pinned
[`entryState params`](../../../LirLean/Spec/Conformance.lean#L11) (empty locals, world = the
recipient's pre-call storage lens), consuming the **realised streams** — the recorded gas
words [`realisedGas`](../../../LirLean/Spec/Recorder.lean#L103), the recorded call effects
[`realisedCall`](../../../LirLean/Spec/Recorder.lean#L110) (each record projected through
`evmV2CallEntry` to a `(post-world, success)` pair), the recorded create effects
[`realisedCreate`](../../../LirLean/Spec/Recorder.lean#L116) — and (ii) `O` agrees with the
bytecode run on both channels:

```lean
def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world
  ∧ O.result = (observe self log.observable).result
```

— [`Spec/Conformance.lean#L20`](../../../LirLean/Spec/Conformance.lean#L20).

### 2.2 [`lower_conforms_exact`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L302) (R11-all)

Identical hypothesis ledger; the conclusion strengthens `RunFrom` to
[`RunFromAll`](../../../LirLean/Spec/Semantics.lean#L188) — the IR run consumes the
**entire** recorded streams, leftovers `[]`:

```lean
    ∃ O : Observable,
      RunFromAll prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O
```

This closes the drop-the-suffix vacuity channel (a plain `RunFrom` could ignore recorded
events past its halt). Its blocker
([sorry at #L333](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L333)) demands an
**exact producer**; the shell comments (and the plan's chunk-7 no-go) forbid deriving
exactness post-hoc from the plain producer.

### 2.3 [`lower_conforms_gasfree`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L341) (co-flagship)

The plain flagship plus one restriction —
`hng :` [`NoGasReads prog`](../../../LirLean/Spec/Conformance.lean#L24) (no `.gas` assign
anywhere) — same conclusion. It avoids R1 (the trace↔recorder gas bridge, historically rated
the riskiest obligation) but **not** the coupled producer: the sload/sstore/call arms still
need the coupling, so its shell calls the same blocker. Its companion
[`realisedGas_nil_of_noGasReads`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L376)
(`sorry`) says a gas-read-free program records an empty gas stream — it needs the R6
boundary walk (no reachable boundary decodes `GAS`). This is the theorem comparable to prior
art (no verified fork models gas introspection at all).

### 2.4 Vacuity discipline: what keeps these non-vacuous

The two failure modes the file is engineered against: **supplied run-dependent ties** (beat
(a)) and **unsatisfiable static bundles** — the header records that the in-tree
`RunDefinable` is unsatisfiable for any gas/call program
([lesson 4](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L34)), `SstoreRealises`
is free-∀ unsatisfiable ([lesson 3](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L28)),
and `StepScoped`'s live-scope clause is refuted by the witness program's own loop
([lesson 8](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L67)). All three were
replaced (`RunDefinableG`, point-wise R4, `StepScopedS`/`invalStep`). The machine-checked
anti-vacuity anchors:

- [`exProg`](../../../LirLean/V2/Realisability/Witness.lean#L38) — the witness program
  (gas read feeding a forwarded-gas CALL, spilled SLOAD, SSTORE, and a genuine gas-derived
  **loop**), with the full static bundle proved concretely:
  [`irWellFormed_exProg`](../../../LirLean/V2/Realisability/Witness.lean#L548),
  [`codeFits_exProg`](../../../LirLean/V2/Realisability/Witness.lean#L560),
  [`stackFits_exProg`](../../../LirLean/V2/Realisability/Witness.lean#L565),
  [`wellLowered_exProg`](../../../LirLean/V2/Realisability/Witness.lean#L590), and the
  R9 checker existential
  [`wellLowered_check_exists`](../../../LirLean/V2/Realisability/Witness.lean#L608)
  (sound checker + accepts the witness). Witness.lean is entirely sorry-free.
- Still debt: the **runtime** half of non-vacuity.
  [`exProg_satisfies_hypotheses`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L388)
  (R12a, `sorry`) must exhibit concrete `params`/`log` making `hrun`+`hclean`+`hseams` true;
  [`exProg_nonvacuity`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L401)
  (R12b) already has a real body consuming R12a + `lower_conforms`. So today the statics
  are machine-checked satisfiable; the full end-to-end witness is pending R12a and R11.

---

## 3. The coupling vocabulary

### 3.1 [`RecorderCoupled`](../../../LirLean/V2/Realisability/Surface.lean#L234) — the load-bearing invariant

```lean
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) : Prop where
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] [] []
      = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix, log.creates)
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  sloadPrefix : ∃ pre, log.sloads = pre ++ sloadSuffix
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix
```

The suffix/prefix cursor idea: at every top-level block-entry boundary the invariant carries
the **un-consumed suffixes** of the recorded streams, plus the `restart` witness — some fuel
replays `fr`'s future to exactly `(log.observable, suffixes…)`. Because `driveLog` is
deterministic, an adversarial `(fr, suffix)` instance must actually reproduce the recorded
future — that is what makes the ties' head equations *derivable* rather than refutable, the
whole point of the reshape. The restart uses pending stack `[]` (coupling holds only at
top-level boundaries, the same `stack.isEmpty` gate `driveLog` records under), so a
descended child call's internal GAS/SLOAD reads are invisible to the restart exactly as to
the original recording. It is indexed by the **frame**, never the cursor, so a loop
revisiting a cursor with different gas is fine. Note the create channel is pinned to the
**whole** `log.creates` — no create suffix exists yet (the latent debt, §5.2).

### 3.2 [`DriveCorrLog`](../../../LirLean/V2/Realisability/Surface.lean#L270) — the coupled walk carrier

```lean
structure DriveCorrLog (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (st : IRState) (fr : Frame) (L : Label)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) :
    Prop where
  corr : Lir.Corr prog sloadChg 0 st fr L 0
  cleanHalts : CleanHaltsNonException fr
  present : ∃ b, blockAt prog L = some b
  selfPresent : SelfPresent fr
  addrPin : fr.exec.executionEnv.address = self
  kindPin : ∃ cp, fr.kind = .call cp
  coupled : RecorderCoupled log fr gasSuffix sloadSuffix callSuffix
```

The boundary invariant the producer threads: the classic `Corr` cursor correspondence
(IR state ↔ frame, from the [04-value-channel](04-value-channel.md) layer) + clean-halt
scope + block presence (R8's channel) + the self/address/kind pins (which turned the old
unsatisfiable `TermTies` demands into supplied antecedents) + the coupling. Established at
entry by [`driveCorrLog_entry`](../../../LirLean/V2/Realisability/Producer.lean#L168)
(closed; note its documented statement correction — the boundary frame is the
post-`JUMPDEST` **landing**, not the beginCall frame), preserved by the R7 edges.

### 3.3 [`StmtTies'`](../../../LirLean/V2/Realisability/Surface.lean#L351) / [`TermTies'`](../../../LirLean/V2/Realisability/Surface.lean#L457) — run-derived per-block ties

Five statement arms (plain assign / spilled sload / spilled gas / sstore / call) and four
terminator arms (stop / ret / jump / branch). Every arm's antecedent block is: cursor
statement + `Corr` + `RecorderCoupled` + `CleanHaltsNonException`; every conclusion is
static, antecedent-carried, or restart-computed (the precision note at
[Surface.lean#L336](../../../LirLean/V2/Realisability/Surface.lean#L336)). The gas arm is
the R1 conjunct, representative of the reshape:

```lean
  ∧ (∀ (pc : Nat) (t : Tmp) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t .gas) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      defsOf prog t = some (.slot (slotOf t))
      ∧ StepScopedS prog (.assign t .gas)
      ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
      ∧ gS.head? = some (UInt256.ofUInt64
          (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))
      ∧ ...
```

The old vacuous form said "for a free `ob`, the recorded word equals `ob`"; the new form
says "the un-consumed gas suffix's **head** equals the machine GAS output at this coupled
frame" — derivable because the restart's first recorded event *is* this read. Both ties are
DERIVED: [`termTies'_of_runWithLog`](../../../LirLean/V2/Realisability/Producer.lean#L2642)
(R10b) is **closed** via
[`termTies'_of_walk`](../../../LirLean/V2/Realisability/Machinery.lean#L503);
[`stmtTies'_of_runWithLog`](../../../LirLean/V2/Realisability/Producer.lean#L2488)
(R10a) is still `sorry` (§5).

### 3.4 [`CallRealisesS`](../../../LirLean/V2/Realisability/Surface.lean#L78) — the shadowing-aware CALL kernel

The call arm's payload: under `Corr`, there exist the recorded `(result, pd)`, the arg-push
run `Runs fr0 callFr` with pc/memory pins, the returning `CallReturns callFr resumeFr` with
`resumeFr = Evm.resumeAfterCall result pd`, the post-state pinned to the record's
`evmV2CallEntry` effect (world = `postStorage`, result tmp = `callSuccessFlag`), and the
Route-B flag-stash tail. It is the in-tree `Lir.CallRealises` with the embedded refutable
`StepScoped` clause replaced by the static `StepScopedS` (lesson 8). The call arm of
`StmtTies'` keys it on the **coupling's `callSuffix` head** `rec :: cS'` — positional,
multi-call, no single-call restriction (the former `SingleCall`/`hone` premises are deleted;
calls are a consumed `CallStream`,
[lesson 7](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L58)).

### 3.5 Producer vocabulary — [`Producer.lean` §0](../../../LirLean/V2/Realisability/Producer.lean#L60) (all real)

```lean
def StreamsAligned (self : AccountAddress) (log : RunLog)
    (gS : List Word) (cS : List CallRecord)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  T = gS ∧ C = callStreamOf cS self ∧ D = createStreamOf log.creates self
```

— [`StreamsAligned`](../../../LirLean/V2/Realisability/Producer.lean#L74): at every coupled
boundary the IR-side streams `(T, C, D)` are the realised image of the recorder suffixes
(note again `D` pinned to the **whole** `log.creates`). The per-boundary output shape
[`RunFromCoupled`](../../../LirLean/V2/Realisability/Producer.lean#L83) packages "some IR
observable whose world/result equal the bytecode terminal's `observe`" + the IR `RunFrom`;
[`DriveLogStep`](../../../LirLean/V2/Realisability/Producer.lean#L97) is the coupled
per-block step (halt, or advance to a strictly-smaller-`totalGas` coupled successor);
[`CoupledAdvance`](../../../LirLean/V2/Realisability/Producer.lean#L114) is one coupled
statement step. The producer itself:

```lean
theorem runFrom_of_driveCorrLog {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account} {fr₀ : Frame}
    (hcode : ...) (hmod : ...) (hself : ...) (hgas : ...) (hwl : WellLowered prog)
    (hrun : ...) (hclean : log.clean) (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∃ O : Observable,
      (∀ fr', Runs fr₀ fr' → CreateResolves fr')
      ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
          ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
          ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
      ∧ RunFrom prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
```

— [`runFrom_of_driveCorrLog`](../../../LirLean/V2/Realisability/Producer.lean#L1442)
(`sorry`; the blocker). Its `hsize` is derived from `hcodeFits` at the flagship call sites
(chunk-0 wiring, landed); `WellLowered` is the
[internal adapter](../../../LirLean/V2/Realisability/Surface.lean#L151) rebuilt from the
public statics by the closed
[`wellLowered_of_IRWellFormed`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L125).
The producer cannot factor through the coupling-free `SimStmtStep`/`DriveStep` path of
[05-simulation](05-simulation.md) — the module header records
[the two documented reasons](../../../LirLean/V2/Realisability/Producer.lean#L15): the
reshaped ties only fire under the coupling antecedent, and R6's walk comes bundled with the
run, not from statics alone.

---

## 4. The exact remaining debt (source census, 2026-07-09)

`rg -n "\bsorry\b" LirLean/V2/Realisability` on current source: **16 proof-position
`sorry`s in 15 declarations** — matching the plan checkpoint's count exactly. Mapped to the
[r11-plan chunks](../../planning/r11-plan-2026-07-08.md):

| # | Declaration | Sorry site(s) | Obligation | Plan chunk |
|---|---|---|---|---|
| 1 | [`atReachableBoundaryVJ_step`](../../../LirLean/V2/Realisability/Machinery.lean#L1372) | [#L1390](../../../LirLean/V2/Realisability/Machinery.lean#L1390), [#L1398](../../../LirLean/V2/Realisability/Machinery.lean#L1398) | R6 bricks **B-pc** (successor pc = sequential or `validJumps` member) and **B-inrange** (sequential successor stays in range) | 1 |
| 2 | [`atReachableBoundaryVJ_call`](../../../LirLean/V2/Realisability/Machinery.lean#L1416) | [#L1431](../../../LirLean/V2/Realisability/Machinery.lean#L1431) | R6 **B-inrange** (CALL instance: `b + 1 < length`) | 1 |
| 3 | [`atReachableBoundaryVJ_create`](../../../LirLean/V2/Realisability/Machinery.lean#L1462) | [#L1464](../../../LirLean/V2/Realisability/Machinery.lean#L1464) | R6 **CREATE resume edge** — no longer vacuous since the lowering emits create bytes; also needs an `hsize` signature fix (plan chunk 1) | 1 (+3) |
| 4 | [`callRealises_of_recorded`](../../../LirLean/V2/Realisability/Machinery.lean#L392) | [#L413](../../../LirLean/V2/Realisability/Machinery.lean#L413) | R3 — Piece A (record extraction from the coupling) is **landed** ([`recorderCoupled_call_extract`](../../../LirLean/V2/Realisability/Machinery.lean#L1929)); the sorry is **Piece B**: no in-tree producer builds the CALL arg-push `Runs fr0 callFr` (~200-line materialise driver) | 2 |
| 5 | [`simStmt_coupled_gas`](../../../LirLean/V2/Realisability/Producer.lean#L453) | [#L467](../../../LirLean/V2/Realisability/Producer.lean#L467) | coupled GAS arm (fires R1 + the gas sim brick + R7b) | 4 |
| 6 | [`simStmt_coupled_sload`](../../../LirLean/V2/Realisability/Producer.lean#L474) | [#L489](../../../LirLean/V2/Realisability/Producer.lean#L489) | coupled SLOAD arm (fires tie arm 2 + R7c) | 4 |
| 7 | [`simStmt_coupled_call`](../../../LirLean/V2/Realisability/Producer.lean#L1279) | [#L1296](../../../LirLean/V2/Realisability/Producer.lean#L1296) | coupled CALL arm — gated on R3 Piece B | 4 (⇐ 2) |
| 8 | [`stmtTies'_of_runWithLog`](../../../LirLean/V2/Realisability/Producer.lean#L2488) | [#L2498](../../../LirLean/V2/Realisability/Producer.lean#L2498) | R10a — build the statement ties from the run | 3→5 seam (order-of-work item 3) |
| 9 | [`simStmts_coupled_block`](../../../LirLean/V2/Realisability/Producer.lean#L1327) | [#L1344](../../../LirLean/V2/Realisability/Producer.lean#L1344) | P3a coupled block walk | 5 |
| 10 | [`driveLogStep_of_block`](../../../LirLean/V2/Realisability/Producer.lean#L1359) | [#L1374](../../../LirLean/V2/Realisability/Producer.lean#L1374) | P3b coupled per-block step | 5 |
| 11 | [`runFrom_of_driveCorrLog_rec`](../../../LirLean/V2/Realisability/Producer.lean#L1385) | [#L1397](../../../LirLean/V2/Realisability/Producer.lean#L1397) | P4 coupled `totalGas` recursion | 5 |
| 12 | [`runFrom_of_driveCorrLog`](../../../LirLean/V2/Realisability/Producer.lean#L1442) | [#L1461](../../../LirLean/V2/Realisability/Producer.lean#L1461) | the packaged producer (top-level assembly) | 6 |
| 13 | [`lower_conforms_exact`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L302) | [#L333](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L333) | the exact producer `obtain` | 7 |
| 14 | [`realisedGas_nil_of_noGasReads`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L376) | [#L381](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L381) | gasfree companion (needs R6 walk) | 8 |
| 15 | [`exProg_satisfies_hypotheses`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L388) | [#L396](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L396) | R12a concrete-params witness grind | order-of-work item 6 |

The plain flagship `lower_conforms` and the gasfree co-flagship have **no sorry of their
own** — their bodies are real assembly over the blocker (#12) plus closed lemmas.

### 4.1 Chunk-1 partial: what the recent commits actually landed

Local commits `e210b3a`…`c760145` (2026-07-09) landed: the P5 helper
[`boundaryWalk_of_wl`](../../../LirLean/V2/Realisability/Producer.lean#L1403) (closed), the
**B-call** brick
[`stepFrame_needsCall_lowering_site_inv`](../../../LirLean/Decode/BoundaryReach.lean#L564)
(+ its CREATE twin
[`stepFrame_needsCreate_lowering_site_inv`](../../../LirLean/Decode/BoundaryReach.lean#L584))
consumed at [Machinery.lean#L1428](../../../LirLean/V2/Realisability/Machinery.lean#L1428),
and ~500 lines of not-yet-consumed boundary support (the new
[`Decode/BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean) cursor-inversion
file — [`flatBytes_cursor_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L99),
[`reachable_lowering_boundary_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L145) —
plus opcode-shape and local-region walkers in
[`BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean#L368)) aimed at B-pc /
B-inrange. **B-pc and both B-inrange sorries remain open in the tree.** Two documentation
rots follow from this landing (see §7): the R6 docstrings at
[#L1408](../../../LirLean/V2/Realisability/Machinery.lean#L1408) and
[#L1506](../../../LirLean/V2/Realisability/Machinery.lean#L1506) still list B-call among the
sorry bricks, and the plan checkpoint cites box-run commits (`ff825e3`, `9d45927`) that do
not exist in local history.

### 4.2 The LATENT obligation: the CREATE coupled channel (no placeholder)

Verified against current source, all three legs of the plan's warning still hold:

- [`RecorderCoupled`](../../../LirLean/V2/Realisability/Surface.lean#L234) has **no create
  suffix** — its `restart` field pins the future's create stream to the whole `log.creates`;
- [`StreamsAligned`](../../../LirLean/V2/Realisability/Producer.lean#L74) pins
  `D = createStreamOf log.creates self` at **every** boundary;
- [`StmtTies'`](../../../LirLean/V2/Realisability/Surface.lean#L351) has five arms and **no
  create arm**; there is no `simStmt_coupled_create` and no recorded-create realisation
  lemma.

Yet `Stmt.create` is public IR syntax and the IR semantics consumes a positional create
head:

```lean
  | create {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream}
      {cs : CreateSpec} {valueW initOffW initSizeW addrW : Word} {world' : World}
      (hvalue : st.locals cs.value = some valueW)
      (hoff   : st.locals cs.initOffset = some initOffW)
      (hsize  : st.locals cs.initSize = some initSizeW) :
      EvalStmt prog st T C ((world', addrW) :: D) (.create cs) ... T C D
```

— [`EvalStmt.create`](../../../LirLean/Spec/Semantics.lean#L71). A walk whose invariant pins
`D` to the whole `log.creates` at every boundary **cannot step through a top-level CREATE**
(the step must consume a head), so a producer closing only the 16 visible sorries would be
unable to cover create-containing programs — and all three flagships range over arbitrary
`IRWellFormed` programs with `realisedCreate` in the conclusion. The plan is explicit:
[chunk 3](../../planning/r11-plan-2026-07-08.md) (create suffix/prefix twin, tie arm,
realisation lemma, `simStmt_coupled_create`) must land **before** R10a and producer
assembly; "closing every currently visible sorry without this latent work is not R11
completion". The bridge-side ingredients already exist:
[`realisedCreate_cons`](../../../LirLean/V2/RecorderLemmas.lean#L164),
[`createRealises_bridge`](../../../LirLean/V2/CallRealises.lean#L118),
[`createPreservesSelf_modGuards`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L300),
and the create arm of
[`defsSoundS_preserved_step`](../../../LirLean/V2/Realisability/Machinery.lean#L209).

**CREATE2-only decision** (plan, resolved 2026-07-09): the IR `create` statement means
**CREATE2 only** — mandatory salt, four operands materialised in CREATE2 stack order,
emit only `Byte.create2`. Note this has **not yet landed in source**: `CreateSpec.salt` is
still [`Option Tmp`](../../../LirLean/Spec/IR.lean#L27) and the lowering still has a
[`Byte.create` branch](../../../LirLean/Spec/Lowering.lean#L141) for the salt-less case (the
correction is owned by the parallel `codex/r11-create2-only` run). Reviewers should treat
the CREATE2-only shape as the spec of record and the current optional-salt lowering as
scheduled for deletion.

---

## 5. What is already CLOSED in this folder

The sorry count should not overshadow this: **the folder is majority-proved.** Everything
below is a real, machine-checked proof in the current tree (one-line method notes only).

**The obligation grid (Machinery/Surface/Spec):**

- **R0** — the reshaped tie *statements* `StmtTies'`/`TermTies'` and the whole §1–§4
  vocabulary of [`Surface.lean`](../../../LirLean/V2/Realisability/Surface.lean) (real defs,
  no sorry).
- **R0b** — [`defsSoundS_preserved_step`](../../../LirLean/V2/Realisability/Machinery.lean#L88):
  the invalidation-set-threaded `DefsSoundS` transfer across one `EvalStmt` step, all five
  statement shapes including create (case analysis on the step; the shadowing repair that
  lets the walk traverse loop-exit iterations).
- **R1** — [`gas_suffix_head_realised`](../../../LirLean/V2/Realisability/Machinery.lean#L1650):
  the historically-riskiest trace↔recorder gas bridge, **closed** (decode from `Corr` +
  clean-halt extraction + R7b head pinning).
- **R2** — [`haltNonException_of_cleanLog`](../../../LirLean/V2/Realisability/Machinery.lean#L268):
  `log.clean` ⇒ every halting terminal is non-exception (drive adequacy + halting-terminal
  uniqueness via [`runs_halt_eq`](../../../LirLean/V2/Realisability/Machinery.lean#L248)).
- **R4** — [`sstoreRealises_at_frame`](../../../LirLean/V2/Realisability/Machinery.lean#L424):
  the point-wise SSTORE realisation replacing the unsatisfiable `SstoreRealises` (stipend and
  EIP-2200 charge bound extracted from clean halt).
- **R5/R10b** — [`termTies'_of_walk`](../../../LirLean/V2/Realisability/Machinery.lean#L503)
  and [`termTies'_of_runWithLog`](../../../LirLean/V2/Realisability/Producer.lean#L2642):
  all four terminator ties derived (the one `maxRecDepth 8192` bump in the folder sits here).
- **R6, partial** — entry seed
  [`atReachableBoundaryVJ_entry`](../../../LirLean/V2/Realisability/Machinery.lean#L1352),
  the strengthened invariant
  [`AtReachableBoundaryVJ`](../../../LirLean/V2/Realisability/Machinery.lean#L1345), the
  `Runs`-induction combinator
  [`atReachableBoundaryVJ_of_runs`](../../../LirLean/V2/Realisability/Machinery.lean#L1472),
  the taken-jump arm, and the B-call brick; the top-level
  [`runs_atReachableBoundary`](../../../LirLean/V2/Realisability/Machinery.lean#L1519) is
  real assembly over the (partially sorry'd) edges. The counterexample
  [`not_runs_atReachableBoundary`](../../../LirLean/V2/Realisability/Machinery.lean#L1279)
  machine-checks that R6's original unconditioned form was false (why `hne`/`hsize` exist).
- **R7a–e′** — the full recorder-coupling edge algebra:
  [`recorderCoupled_entry`](../../../LirLean/V2/Realisability/Machinery.lean#L1537),
  [`recorderCoupled_step_gas`](../../../LirLean/V2/Realisability/Machinery.lean#L1556),
  [`recorderCoupled_sload`](../../../LirLean/V2/Realisability/Machinery.lean#L1681),
  [`recorderCoupled_step_other`](../../../LirLean/V2/Realisability/Machinery.lean#L1719),
  [`recorderCoupled_call`](../../../LirLean/V2/Realisability/Machinery.lean#L1839) (one
  `CallRecord`, no gas/sload, consumed per returning CALL),
  [`recorderCoupled_call_extract`](../../../LirLean/V2/Realisability/Machinery.lean#L1929)
  (R3 Piece A: produces the `CallReturns` witness and the record identity from the coupling)
  and [`recorderCoupled_stepsTo_other`](../../../LirLean/V2/Realisability/Machinery.lean#L2007).
  Method: fuel destruction + the accumulator homomorphism
  [`driveLog_acc_hom`](../../../LirLean/V2/Realisability/Machinery.lean#L1142).
- **R8** — [`present_of_closed`](../../../LirLean/V2/Realisability/Machinery.lean#L2021).
- **R9** — the witness stack and singleton checker (§2.4; Witness.lean sorry-free,
  including the loop-staleness machine-check
  [`not_defsSound_stale`](../../../LirLean/V2/Realisability/Witness.lean#L236) that forced
  R0b).
- **The `Conforms` assembly** —
  [`conforms_of_worldeq`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L204):
  world+result channel closed from the terminal equation via drive adequacy (used verbatim
  by all three flagships), and the static bridge
  [`wellLowered_of_IRWellFormed`](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L125).

**Producer-side (closed pieces of the walk itself):**

- [`streamsAligned_entry`](../../../LirLean/V2/Realisability/Producer.lean#L137) /
  [`driveCorrLog_entry`](../../../LirLean/V2/Realisability/Producer.lean#L168) — the
  induction base, including the entry-storage reconciliation against `codeAccounts`.
- [`simStmt_coupled_assignPure`](../../../LirLean/V2/Realisability/Producer.lean#L398) — the
  plain-assign coupled arm, fully closed (fires tie arm 1; frame unchanged, `Runs.refl`).
- [`recorderCoupled_matRunsC`](../../../LirLean/V2/Realisability/Producer.lean#L510) — the
  coupling fold over a whole `materialise` run (joint recursion mirroring
  `materialise_runsC`; one R7d application per emitted frame).
- [`sim_sstore_stmt'`](../../../LirLean/V2/Realisability/Producer.lean#L1036) and
  [`simStmt_coupled_sstore`](../../../LirLean/V2/Realisability/Producer.lean#L1199) — the
  SSTORE coupled arm, fully closed including zero-writes/slot-clears (the former
  nonzero-write scope seam is gone).
- [`boundaryWalk_of_wl`](../../../LirLean/V2/Realisability/Producer.lean#L1403) (P5) and
  [`createResolves_reachable`](../../../LirLean/V2/Realisability/Producer.lean#L1423) (P6).

So of the producer's P1–P6 plan, P1/P2-assign/P2-sstore/P5/P6 are done; P2-gas/P2-sload/
P2-call, P3a/P3b, P4 and the packaging remain — plus the create channel that has no P-number
yet.

---

## 6. File-by-file account of the rest of the scope

| File | Role | Status |
|---|---|---|
| [`Drive/DriveSim.lean`](../../../LirLean/V2/Drive/DriveSim.lean) | The coupling-free drive layer: [`DriveCorr`](../../../LirLean/V2/Drive/DriveSim.lean#L91), the `totalGas` descent ([`totalGas_succ_lt`](../../../LirLean/V2/Drive/DriveSim.lean#L199)), the four per-block steps, the F2 recursion [`runFrom_of_driveCorr`](../../../LirLean/V2/Drive/DriveSim.lean#L580), and the conditional headlines [`lower_conforms_cyclic`](../../../LirLean/V2/Drive/DriveSim.lean#L618)/[`lower_conforms_cyclic'`](../../../LirLean/V2/Drive/DriveSim.lean#L661). Also [`cleanHalts_of_runWithLog`](../../../LirLean/V2/Drive/DriveSim.lean#L143), consumed by the entry seed. | Sorry-free; default cone. The `cyclic'` pair is the **superseded** route (pure fragment only, ties supplied) — kept as the structural template the producer mirrors, explicitly not the R11 path. Candidate for retirement once R11 closes. |
| [`Drive/Headline.lean`](../../../LirLean/V2/Drive/Headline.lean) | The [`DriveCorrPlus`](../../../LirLean/V2/Drive/Headline.lean#L81) carrier + retained value-channel bricks ([`driveCorrPlus_sload_value_world`](../../../LirLean/V2/Drive/Headline.lean#L194) etc.) and the seedable gas-alignment bricks; header documents the 2026-07-03 vacuous-surface deletion. | Sorry-free. Partially superseded by `DriveCorrLog` (which carries the restart coupling instead of the alignment lists); `DriveCorrPlus` itself is currently unreferenced by the WIP walk — flag for consolidation after R11. |
| [`Drive/SelfPresent.lean`](../../../LirLean/V2/Drive/SelfPresent.lean) | [`SelfPresent`](../../../LirLean/V2/Drive/SelfPresent.lean#L353), [`accounts_ne_empty_of_selfPresent`](../../../LirLean/V2/Drive/SelfPresent.lean#L368), [`selfPresent_codeFrame`](../../../LirLean/V2/Drive/SelfPresent.lean#L398), and the gas/sload log-alignment lemma family. | Sorry-free; the presence chain feeding `DriveCorrLog.selfPresent` and the stop/ret ties. |
| [`Drive/CallPreservesSelf.lean`](../../../LirLean/V2/Drive/CallPreservesSelf.lean) | Engine theory: [`stepPreservesSelf`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L84) (unconditional), [`callPreservesSelf_modGuards`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L214) / [`createPreservesSelf_modGuards`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L300) (from the `noErase` seam), [`selfPresent_runs`](../../../LirLean/V2/Drive/CallPreservesSelf.lean#L321). Covered in depth in [01-trusted-base](01-trusted-base.md). | Sorry-free, axiom-clean per its header. |
| [`V2/RecorderLemmas.lean`](../../../LirLean/V2/RecorderLemmas.lean) | The recorder adequacy layer: [`driveLog_drive`](../../../LirLean/V2/RecorderLemmas.lean#L82) (erasing the log recovers `drive` — induction on fuel, branch-for-branch), [`runWithLog_drive`](../../../LirLean/V2/RecorderLemmas.lean#L138), and the `rfl`-clean head projections [`realisedCall_cons`](../../../LirLean/V2/RecorderLemmas.lean#L64) / [`realisedCreate_cons`](../../../LirLean/V2/RecorderLemmas.lean#L164). | Sorry-free. This is why "the recording interpreter" is not a second trusted semantics: its result projection *is* the verified `drive`. |
| [`V2/CallRealises.lean`](../../../LirLean/V2/CallRealises.lean) | [`callRealises_bridge`](../../../LirLean/V2/CallRealises.lean#L77) / [`createRealises_bridge`](../../../LirLean/V2/CallRealises.lean#L118): a returning CALL/CREATE's realised `evmV2CallEntry`/`evmV2CreateEntry` **is** the lowered opcode's observable effect (`rfl`-clean projections through `resumeAfterCall`). | Sorry-free supporting bricks; the create bridge is a ready ingredient for chunk 3. |
| [`V2/Call.lean`](../../../LirLean/V2/Call.lean) | A worked, frame-free example: [`callIR`](../../../LirLean/V2/Call.lean#L62) (gas read feeding a forwarded-gas call), with [`call_IRRun`](../../../LirLean/V2/Call.lean#L107) and uniqueness [`call_IRRun_unique`](../../../LirLean/V2/Call.lean#L139). | **Example only** — a hand-assembled `EvalStmt` chain demonstrating the two-channel interaction model; nothing in the R11 chain consumes it. |

---

## 7. Smells, discrepancies, and the no-gos that protect honesty

**Source-vs-doc discrepancies found (all doc-side rot, none proof-side):**

1. The [plan checkpoint](../../planning/r11-plan-2026-07-08.md) says a box run "closed B-pc
   and CALL successor in-range through commits `ff825e3` and `9d45927`" — **neither hash
   exists in local history**, and both sorries
   ([B-pc](../../../LirLean/V2/Realisability/Machinery.lean#L1390),
   [CALL in-range](../../../LirLean/V2/Realisability/Machinery.lean#L1431)) are still open
   in the tree. What actually landed locally is B-call + unconsumed support (§4.1). The
   checkpoint's *census* (16/15 + one latent) is nonetheless exact against current source.
2. Stale R6 docstrings: [`atReachableBoundaryVJ_call`](../../../LirLean/V2/Realisability/Machinery.lean#L1408)
   and [`runs_atReachableBoundary`](../../../LirLean/V2/Realisability/Machinery.lean#L1506)
   still list B-call among the sorry'd bricks though it is discharged at
   [#L1428](../../../LirLean/V2/Realisability/Machinery.lean#L1428). The plan's cleanup gate
   ("compress the new per-op support and stale R6 prose") already covers this.
3. Minor line-drift in comments: e.g.
   [Producer.lean#L1276](../../../LirLean/V2/Realisability/Producer.lean#L1276) cites
   `callRealises_of_recorded` at "Machinery.lean:405" (now
   [#L392](../../../LirLean/V2/Realisability/Machinery.lean#L392)).
4. The CREATE2-only spec gate is "resolved" in the plan but not yet landed in source
   (§4.2) — a decision-of-record vs. tree divergence, owned by a parallel run.

**Smells, with the does-a-headline-depend-on-it call:**

- Two `maxRecDepth` bumps: `8192` on
  [`termTies'_of_walk`](../../../LirLean/V2/Realisability/Machinery.lean#L466) (under the
  headline chain — a symptom of the very large `TermTies'` branch-arm term, not of `decide`
  abuse) and `8000` on the concrete
  [`codeFits_exProg`](../../../LirLean/V2/Realisability/Witness.lean#L557)/`stackFits_exProg`
  `decide`s (witness-only, not under the headline until R12 closes). Both acceptable;
  neither hides a reduction on an unbounded term.
- The WIP lib intentionally has **no** `#print axioms` guards
  ([documented](../../../LirLean/V2/Realisability/RealisabilitySpec.lean#L424)); guards
  migrate to the default-cone audit net per closed obligation. Correct policy, but it means
  "closed" claims inside WIP should be re-checked at integration time (this review grepped
  the proof bodies).
- [`Classical.choose` in `driveLogStep_of_block`'s statement](../../../LirLean/V2/Realisability/Producer.lean#L1367)
  (tie hypotheses at the chosen present block) is a mild statement-shape wart; harmless
  because the tie producers are `∀ b`-shaped, but worth simplifying when P3b is proved.

**The per-chunk no-gos** (from the [plan](../../planning/r11-plan-2026-07-08.md); these are
the guardrails that prevent regressing into beat (a)):

- chunk 2: no single-call restriction, no call-count premise, no supplied per-call tie;
- chunk 3: no public no-create restriction on the flagship;
- chunk 5: do not route through `lower_conforms_cyclic'`/`SimStmtStep`/`DriveStep` (the
  coupling-free path);
- chunk 7: no post-hoc exactness from a plain `RunFrom`;
- global gate: no public premise may mention `WellLowered`/`WellFormedLowered`, legacy fuel
  machinery, single-call restrictions, supplied per-block ties, or a new standalone size
  premise — and the `rg sorry` census must shrink monotonically.

---

## 8. Verdict and recommendations

The statement layer is done and, for the first time in this experiment's history, *believed
for the right reasons*: every past vacuity mechanism has a named lesson, a machine-checked
refutation where feasible, and a structural fix in the current shapes. The remaining work is
genuinely proof engineering, not design: (i) three R6 geometry bricks whose support algebra
is already in-tree, (ii) one ~200-line materialise driver (R3 Piece B), (iii) the CREATE
coupled channel — the only remaining *statement* work, and the one item with no `sorry` to
count, and (iv) the block-walk/recursion assembly, which structurally mirrors the
already-proved [`runFrom_of_driveCorr`](../../../LirLean/V2/Drive/DriveSim.lean#L580).

Recommendations:

1. Treat the CREATE coupled channel (chunk 3) as the critical path — it changes
   `RecorderCoupled`/`StreamsAligned`/`StmtTies'` signatures and therefore everything in
   chunks 4–6 that pattern-matches on them; landing it late means reproving arms.
2. Fix the two stale R6 docstrings and the plan-checkpoint commit references at the next
   green checkpoint (cheap, and this layer's docs are its main audit trail).
3. After R11 closes, consolidate: retire `lower_conforms_cyclic`/`cyclic'` and the
   unreferenced `DriveCorrPlus` (both superseded by the coupled path), and land the
   CREATE2-only lowering correction so spec and source agree.
