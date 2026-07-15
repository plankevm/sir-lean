# 00 — Overview: experiment 005, the Plank SIR → EVM-bytecode lowering study

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Review tour of 2026-07-09, synthesis report. Read this first; the eight deep reports are:
[01 trusted base](01-trusted-base.md) · [02 spec layer](02-spec-layer.md) ·
[03 code geometry](03-code-geometry.md) · [04 value channel](04-value-channel.md) ·
[05 simulation](05-simulation.md) · [06 realisability](06-realisability.md) ·
[07 assembler](07-assembler.md) · [08 related work](08-related-work.md).
Source state: local `main` at `c760145`, 2026-07-09.

---

## 1. TL;DR

Exp005 lowers a small SSA-ish IR (temporaries, sload/sstore, gas reads, CALL/CREATE, jumps)
to real EVM bytecode via a total compiler
[`lower`](../../../LirLean/Spec/Lowering.lean#L186), and aims to prove one conformance
flagship: run the lowered bytecode once under a recording interpreter, feed the recorded
gas/call/create events back into the IR semantics as **oracle streams**, and the IR run
exists and matches the machine's observable world and result —
[`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251), quoted in
§3.9 below. **Honest status:** the statement layer is final and, after two vacuity
postmortems, non-vacuous by construction; the three flagship shells live in the non-default
`WIP` lib and delegate to one sorry'd coupled run-producer
([`runFrom_of_driveCorrLog`](../../../LirLean/Realisability/Producer.lean#L1442)); the
default `lake build` cone is sorry-free with build-pinned axiom guards
([`Audit.lean`](../../../LirLean/Audit.lean#L27)); the majority of the R0–R12 obligation
skeleton is already proved (R0b/R1/R2/R4/R5/R7a–e′/R8/R9/R10b, the entry seeds, three of five
coupled arms). What remains is **16 proof-position `sorry`s in 15 declarations**
(re-verified by grep for this synthesis) plus one *latent* obligation with no placeholder —
the CREATE coupling channel — detailed in §5. Verification status, once: zero
`sorry`/`native_decide`/`bv_decide` in the default cone, axioms pinned at
`[propext, Classical.choice, Quot.sound]`; builds and the exp003 conformance suite (22,308
fixtures, 2 expected failures) are **reported, not re-run**.

## 2. Goal & context

The real-world question is whether the project's IR→EVM lowering discipline (recompute-on-use
with uniform spill-to-slot for non-recomputable reads) can carry a machine-checked
conformance theorem against a conformance-tested EVM — including the features every prior
verified-compiler fork excludes: gas introspection, external calls inside loops, CREATE. The
experiment sits on exp003's vendored, empirically-warranted machine
([`EVMLean`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36)) and
has already survived one full teardown: the original headline was found **vacuous**
(supplied per-block ties unsatisfiable; [audit](../../audit-2026-07-02.md),
[target architecture](../../target-architecture-2026-07-02.md)), and the current
R0–R12 rebuild derives every run-dependent fact *from* the run. The execution plan of record
is the [r11 plan](../../planning/r11-plan-2026-07-08.md).

## 3. THE PROOF PATH, bottom to top

```
L8  Flagships: lower_conforms / _exact / _gasfree        RealisabilitySpec.lean   [WIP]  ── 06
L7  Coupled walk: RecorderCoupled, DriveCorrLog,         Realisability/,       [WIP]  ── 06
    StmtTies'/TermTies', producer recursion              Drive/
L6  CFG simulation: sim_cfg + builders                   CfgSim/            [superseded]  ── 05
L5  Per-statement simulation: Corr + arms                Sim/                     [live]  ── 05
L4  Value channel & effect oracles: materialise_runsC,   Materialise/, Frame/     [live]  ── 04
    MemRealises, stash tail, clean-halt envelopes
L3  Code geometry: pcOf anchors, SegAlignedP,            Decode/                  [live]  ── 03
    jump validity, boundary walk
L2  Statement surface: IR, oracle-stream semantics,      Spec/                 [trusted]  ── 02
    lower, recorder, Conforms, seams
L1' In-house engine theory: drive→Runs inversion,        Engine/                  [live]  ── 01
    per-opcode walks, presence/memory algebra
L1  exp003 Hoare surface: Runs, CallReturns,             BytecodeLayer/         [proved]  ── 01
    messageCall_runs, gas monotonicity
L0  exp003 machine: stepFrame/drive/beginCall/Create     EVMLean/            [empirical]  ── 01
```

Dependency shape: L8 consumes L7; L7 consumes L5's `Corr` + L4/L3 bricks + L1' inversions
directly (bypassing L6, whose builder path is superseded — §6a); everything consumes L2's
definitions and L0/L1's machine facts.

### 3.1 L0 — the trusted machine (exp003, empirical warrant)

The base is philogy/leanevm vendored in exp003: one fuel-indexed driver
[`drive`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36) over a
linear frame stack, with [`stepFrame`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Dispatch.lean#L130)
dispatching one opcode and CALL/CREATE handled by suspend-and-resume
([`beginCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L18),
[`resumeAfterCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L122)).
Nothing proves this machine implements the Yellow Paper; its warrant is the conformance
suite (2859/2859 fast, 22,308 − 2 expected full — reported, not re-run), and every exp005
theorem inherits exactly that warrant. Fuel is quarantined in `drive` alone and proved
unobservable ([`messageCall_never_outOfFuel`](../../../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144)).
The linear-frames choice itself is assessed and vindicated in [08](08-related-work.md).
Deep report: [01](01-trusted-base.md).

### 3.2 L1 — exp003's proved Hoare surface

Exp003 contributes the composition relation
[`Runs`](../../../../../EVM/BytecodeLayer/Hoare.lean#L140) (step / black-box
`CallReturns` / `CreateReturns` nodes), the fuel-free boundary bridge
[`messageCall_runs`](../../../../../EVM/BytecodeLayer/Hoare/CallSequence.lean#L195),
per-opcode rules (`runs_push`, `runs_sstore`, the JUMP trio, …), fuel erasure
([`drive_fuel_mono`](../../../../../EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean#L185)),
and gas monotonicity ([`Runs.gasAvailable_le`](../../../../../EVM/BytecodeLayer/Hoare/GasMonotone.lean#L281)).
This was believed to be "everything needed"; report [01](01-trusted-base.md) shows why it
was not: it is a **forward** theory for runs you construct, while the flagship starts from
an actual execution and must reason backward and per-step. Deep report: [01](01-trusted-base.md) §4.

### 3.3 L1′ — exp005's in-house engine theory (`Engine/` + kin)

Five machine-shaped gaps had to be filled in-house (~6.3k lines, ~23% of the package, all
IR-free and staged for relocation to exp003 — decision D10): the **reverse direction**
[`runs_of_drive_ok`](../../../../../EVM/BytecodeLayer/Hoare/DriveRuns.lean#L357) (a completed `drive` run
yields a halting `Runs`, modulo the two honest
[`ModellableStep`](../../../../../EVM/BytecodeLayer/Hoare/DriveRuns.lean#L182) residuals — precompile CALLs
and OOG-faulting CREATE resumes); the ~1,300-line per-opcode account-presence walk
[`stepFrame_next_accMono`](../../../../../EVM/BytecodeLayer/Hoare/StepWalk.lean#L1119) and its whole-run
induction [`drive_accounts_find_mono`](../../../../../EVM/BytecodeLayer/Hoare/DriveMono.lean#L159); the
clean-halt vocabulary [`CleanHaltsNonException`](../../../../../EVM/BytecodeLayer/Hoare/CleanHalt.lean#L62)
that lets gas guards be *extracted* from a run instead of supplied; byte-level memory
algebra for the spill slots ([`MemAlgebra`](../../../../../EVM/BytecodeLayer/Hoare/MemAlgebra.lean#L459));
and RBMap-erase read-back for zero writes
([`StorageErase`](../../../LirLean/Frame/StorageErase.lean#L189)). Without this layer the
flagship's `Conforms` half has no path from the recorded run to a `Runs`, and no storage
arm fires at an arbitrary reachable cursor. Deep report: [01](01-trusted-base.md).

### 3.4 L2 — the Spec/ statement surface

Everything a skeptic must *read and believe*: the IR grammar
([`Spec/IR.lean`](../../../LirLean/Spec/IR.lean#L31)); the oracle-stream big-step semantics
([`EvalStmt`](../../../LirLean/Spec/Semantics.lean#L48), [`RunFrom`](../../../LirLean/Spec/Semantics.lean#L99),
exact-consumption mirror [`RunFromAll`](../../../LirLean/Spec/Semantics.lean#L188)) in which
storage is modelled but gas/call/create results are positional list streams the IR pops but
never computes; the total lowering [`lower`](../../../LirLean/Spec/Lowering.lean#L186)
(recompute-on-use + spill-to-slot via [`Loc`](../../../LirLean/Spec/Lowering.lean#L30));
the recording interpreter [`driveLog`](../../../LirLean/Spec/Recorder.lean#L51) /
[`runWithLog`](../../../LirLean/Spec/Recorder.lean#L93) — a hand-maintained twin of `drive`
whose *result* channel is proved equal to the verified engine
([`runWithLog_drive`](../../../LirLean/RecorderLemmas.lean#L138)) but whose *recorded*
channels are the project's single biggest definitional trust commitment after the machine
itself (§6b); the conclusion vocabulary
([`Conforms`](../../../LirLean/Spec/Conformance.lean#L20),
[`observe`](../../../LirLean/Spec/Recorder.lean#L122)); the static bundle
([`IRWellFormed`](../../../LirLean/Spec/WellFormed.lean#L430) + two scalar budgets); and the
honest seams ([`PrecompileAssumptions`](../../../LirLean/Spec/Seams.lean#L31)). Deep report:
[02](02-spec-layer.md).

### 3.5 L3 — code geometry (`Decode/`)

Before any Hoare rule fires on `lower prog` for an *arbitrary* program, five families of
global byte-list facts are needed: block offsets (prefix sums), decode-at-cursor
([`flatBytes_at_pcOf`](../../../LirLean/Decode/Layout.lean#L248) — the generic "M1" that pins
frame pc to IR cursor), jump-target validity
([`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226)), instruction
alignment — proven **unconditionally** for every program via the elegant
[`SegAlignedP`](../../../LirLean/Decode/SegAligned.lean#L63) calculus
([`segAlignedP_flatBytes`](../../../LirLean/Decode/SegAligned.lean#L443)) — and the
boundary-reachability allow-list
([`decode_reachable_boundary_loweringOp`](../../../LirLean/Decode/BoundaryReach.lean#L529))
feeding the whole-run R6 invariant. This layer is, de facto, the correctness proof of an
assembler fused into the IR — the observation that motivates the planned Asm layer
([07](07-assembler.md)). Deep report: [03](03-code-geometry.md).

### 3.6 L4 — the value channel and effect oracles (`Materialise/` + `Frame/`)

The linchpin theorem: running the emitted bytes for an expression from any well-anchored
frame pushes exactly the IR's value, with all thirteen frame effects pinned —
[`materialise_runsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L812). Its design core
is uniform spill-to-slot: after the free-∀ value ties (`GasRealises`/`SloadRealises`) were
machine-checked unsatisfiable (§6a), every non-recomputable temp is stashed once to memory
slot `t.id * 32` and read back by `PUSH32; MLOAD`, carried by the positional invariant
[`MemRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366) and the proved-once
stash tail [`stash_tail_runs`](../../../LirLean/Materialise/StashTail.lean#L157). Gas
envelopes are **derived, not supplied**: one clean-halt witness at the entry cursor yields
every per-opcode bound
([`materialise_runsC_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372)).
CALL/CREATE effects are pinned *reflexively* to exp003's resume via the oracles
([`call_reflects_oracle`](../../../LirLean/Frame/Match.lean#L473),
[`create_reflects_oracle`](../../../LirLean/Frame/Match.lean#L530)). Deep report:
[04](04-value-channel.md) — which also confirms the v1 frame machine
(`Frame/SmallStep.lean`, `applyCall`/`applyCreate`, the `Match` structure) is dead surface.

### 3.7 L5 — per-statement simulation (`Sim/`)

The between-statements invariant [`Corr`](../../../LirLean/Sim/SimStmt.lean#L102) relates IR
state to EVM frame at every cursor — four geometric fields (pc/code/validJumps/empty stack)
plus five semantic ones (storage lens, recompute soundness, scoping, memory realisation) —
and one proved arm per statement/terminator shape re-establishes it: `sim_assign`,
[`sim_sstore_stmt`](../../../LirLean/Sim/SimStmt.lean#L347), the spill arms, the 25-hypothesis
CALL arm [`sim_call_stmt`](../../../LirLean/Sim/SimStmt.lean#L579), and the terminator
halt/edge arms ([`sim_term_halt_ret`](../../../LirLean/Sim/SimTerm.lean#L312),
[`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503)). The empty-stack-at-
boundaries convention is the design bet that keeps the induction free of stack bookkeeping.
Deep report: [05](05-simulation.md).

### 3.8 L6 — CFG simulation (`CfgSim/`), and the superseded builder path

[`sim_cfg`](../../../LirLean/CfgSim/LowerConforms.lean#L938) is a clean, cycle-agnostic
whole-CFG induction (over the `RunFrom` derivation — no fuel, no acyclicity), fed by
∀-quantified per-block units `SimStmtStep`/`SimTermStep` and builders. It is proved, green —
and **dead as a route to the flagship**: its unit shapes demand the step conclusion for
*every* `Corr`-corresponding pair, including frames the real run never visits, and two of its
supplied seams ([`SstoreRealises`](../../../LirLean/Sim/SimStmt.lean#L317),
[`CallRealises`](../../../LirLean/CfgSim/LowerConforms.lean#L235) with embedded
`StepScoped`) are not producible from a real run. Its endpoint
([`lower_conforms_cyclic'`](../../../LirLean/Drive/DriveSim.lean#L661)) has zero callers.
What *is* live from this folder: [`WellFormedLowered`](../../../LirLean/CfgSim/LowerConforms.lean#L144)
and the low-level decode dischargers
([`decode_gasstash`](../../../LirLean/CfgSim/LowerDecode.lean#L632),
[`term_dest_decode`](../../../LirLean/CfgSim/LowerDecode.lean#L332)). Deep report:
[05](05-simulation.md) §6.

### 3.9 L7+L8 — the coupled walk and the flagship producer (`Drive`, `Realisability`)

The repair for the all-frames disease: the walk invariant
[`DriveCorrLog`](../../../LirLean/Realisability/Surface.lean#L270) carries `Corr` plus one
real coupling field, [`RecorderCoupled`](../../../LirLean/Realisability/Surface.lean#L234)
— *restarting `driveLog` at the current boundary frame reproduces the run's final observable
and exactly the un-consumed stream suffixes*. Because `driveLog` is deterministic, the
restart pins every formerly-free tie value to a suffix head, so the reshaped per-block ties
[`StmtTies'`](../../../LirLean/Realisability/Surface.lean#L351)/
[`TermTies'`](../../../LirLean/Realisability/Surface.lean#L457) are **derived from the
run** (R10b closed via [`termTies'_of_walk`](../../../LirLean/Realisability/Machinery.lean#L503);
R10a open). The recursion template is the already-proved coupling-free
[`runFrom_of_driveCorr`](../../../LirLean/Drive/DriveSim.lean#L580) (gas-measure descent);
its coupled twin [`runFrom_of_driveCorrLog`](../../../LirLean/Realisability/Producer.lean#L1442)
is the single blocker all three flagship shells `obtain`. The `Conforms` half is closed
([`conforms_of_worldeq`](../../../LirLean/Realisability/RealisabilitySpec.lean#L204)).
The plain flagship, verbatim (line verified against current source):

```lean
-- ../../../LirLean/Realisability/RealisabilitySpec.lean#L251  (WIP lib)
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

Plain English: if the machine, entered as a top-level call into an account holding
`lower prog`, runs to a clean (non-exception) halt under the recorder, then the IR — fed the
recorded gas words and call/create effects positionally, from the recipient's actual
pre-storage — has a run whose final storage and result are the machine's. Siblings:
[`lower_conforms_exact`](../../../LirLean/Realisability/RealisabilitySpec.lean#L302)
(concludes `RunFromAll`: the IR explains *every* recorded event, killing the
drop-the-suffix vacuity channel) and
[`lower_conforms_gasfree`](../../../LirLean/Realisability/RealisabilitySpec.lean#L341)
(adds `NoGasReads`; the de-risking co-flagship, first to close). Non-vacuity is anchored by
the loop+gas+call witness [`exProg`](../../../LirLean/Realisability/Witness.lean#L38),
whose full static bundle is machine-checked. Deep report: [06](06-realisability.md).

## 4. Why each file exists

Every `.lean` file in `LirLean/` (60 + root; 26,935 lines). Status legend: **live**
(consumed on the flagship path or trusted spec), **WIP** (carries tracked sorries),
**staged** (proved, awaiting relocation/consumption), **superseded** (proved but bypassed by
the coupled path; retirement candidate post-R11), **dead-candidate** (zero consumers),
**example**.

| File | Ln | Layer / job | Status | Report |
|---|---|---|---|---|
| [`LirLean.lean`](../../../LirLean.lean) | 68 | root import list; audit net last | live | — |
| [`Audit.lean`](../../../LirLean/Audit.lean) | 54 | build-enforced `#print axioms` guards for the closed cone | live | [02](02-spec-layer.md) |
| [`Words.lean`](../../../LirLean/Words.lean) | 16 | BE byte encodings for PUSH immediates (`wordBytesBE`/`offsetBytesBE`) | live | [04](04-value-channel.md) |
| [`Spec/IR.lean`](../../../LirLean/Spec/IR.lean) | 67 | L2: IR grammar | trusted/live | [02](02-spec-layer.md) |
| [`Spec/Semantics.lean`](../../../LirLean/Spec/Semantics.lean) | 219 | L2: oracle-stream big-step, `RunFrom`/`RunFromAll` | trusted/live | [02](02-spec-layer.md) |
| [`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean) | 188 | L2: `Loc`/`Alloc`, emitters, `lower` | trusted/live | [02](02-spec-layer.md) |
| [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean) | 132 | L2: `driveLog`/`runWithLog`, realised streams, `observe` — **the trust fence** | trusted/live | [02](02-spec-layer.md) |
| [`Spec/Conformance.lean`](../../../LirLean/Spec/Conformance.lean) | 28 | L2: `entryState`, `RunLog.clean`, `Conforms`, `NoGasReads` | trusted/live | [02](02-spec-layer.md) |
| [`Spec/WellFormed.lean`](../../../LirLean/Spec/WellFormed.lean) | 443 | L2: `IRWellFormed` + budgets (mixed with `matCache` proofs) | trusted/live | [02](02-spec-layer.md) |
| [`Spec/Seams.lean`](../../../LirLean/Spec/Seams.lean) | 36 | L2: `PrecompileAssumptions`, `ReachableFrom` | trusted/live | [02](02-spec-layer.md) |
| [`Spec/BudgetDerivations.lean`](../../../LirLean/Spec/BudgetDerivations.lean) | 385 | derives per-cursor bounds from the two scalar budgets (proofs; misplaced in `Spec/`) | live | [02](02-spec-layer.md) |
| [`BytecodeLayer/Hoare/AccountMap.lean`](../../../../../EVM/BytecodeLayer/Hoare/AccountMap.lean) | 145 | L1′: `AccPresent` + RBMap presence closers | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/Sequence.lean`](../../../../../EVM/BytecodeLayer/Hoare/Sequence.lean#L61) | integrated | L1′: `subCharges` definition and fold laws | shared exp003 layer | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/CleanHalt.lean`](../../../../../EVM/BytecodeLayer/Hoare/CleanHalt.lean) | 103 | L1′: `CleanHalts(NonException)` + forward closure | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/Descent.lean`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean) | 844 | L1′: CALL/CREATE site inversions, begin/resume framing | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/DriveMono.lean`](../../../../../EVM/BytecodeLayer/Hoare/DriveMono.lean) | 294 | L1′: whole-run account-presence monotonicity | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/DriveRuns.lean`](../../../../../EVM/BytecodeLayer/Hoare/DriveRuns.lean) | 482 | L1′: **the reverse direction** `runs_of_drive_ok` | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/MemAlgebra.lean`](../../../../../EVM/BytecodeLayer/Hoare/MemAlgebra.lean) | 996 | L1′: mstore/mload read-back, slot disjointness (2× `maxHeartbeats 800000`) | staged→exp003 | [01](01-trusted-base.md) |
| [`Decode/Modellable.lean`](../../../LirLean/Decode/Modellable.lean) | 462 | L1′: `ModellableStep` → `CallsCode`/`CreateResolves` residuals | staged→exp003 | [01](01-trusted-base.md) |
| [`BytecodeLayer/Hoare/StepWalk.lean`](../../../../../EVM/BytecodeLayer/Hoare/StepWalk.lean) | 1,336 | L1′: per-opcode env/presence walk over the full dispatch | staged→exp003 | [01](01-trusted-base.md) |
| [`Decode/LoweringLemmas.lean`](../../../LirLean/Decode/LoweringLemmas.lean) | 139 | `defsOf`/`rematOf` routing companions (stowaway; value-channel material) | live, misplaced | [03](03-code-geometry.md) |
| [`Decode/DecodeLower.lean`](../../../LirLean/Decode/DecodeLower.lean) | 157 | L3: `flatBytes`, ByteArray↔list decode bridge | live | [03](03-code-geometry.md) |
| [`Decode/Layout.lean`](../../../LirLean/Decode/Layout.lean) | 257 | L3: prefix-sum layout, `pcOf`, the generic M1 anchor | live | [03](03-code-geometry.md) |
| [`Decode/DecodeAnchors.lean`](../../../LirLean/Decode/DecodeAnchors.lean) | 317 | L3: decode-at-cursor anchors A1–A3, `termOf` | live | [03](03-code-geometry.md) |
| [`Decode/SegAligned.lean`](../../../LirLean/Decode/SegAligned.lean) | 456 | L3: `SegAlignedP` alignment tower, 18-opcode allow-list | live | [03](03-code-geometry.md) |
| [`Decode/JumpValid.lean`](../../../LirLean/Decode/JumpValid.lean) | 271 | L3: every block offset ∈ `validJumpDests` | live | [03](03-code-geometry.md) |
| [`Decode/BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean) | 607 | L3: R6 boundary-walk bricks; B-call closed, chunk-1 support partly unconsumed | live + staged | [03](03-code-geometry.md) |
| [`Decode/BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean) | 151 | L3: byte-offset → source-region inversion (pre-positioned for R6 B-pc/B-inrange) | staged | [03](03-code-geometry.md) |
| [`Materialise/MaterialiseRuns.lean`](../../../LirLean/Materialise/MaterialiseRuns.lean) | 506 | L4: `StashRuns`/`MemRealises`/`StorageAgree` + transports; RETIRED free-∀ universals kept as record | live | [04](04-value-channel.md) |
| [`Materialise/MaterialiseGas.lean`](../../../LirLean/Materialise/MaterialiseGas.lean) | 217 | L4: charge-list folds `chargeExpr`/`chargeCache` | live | [04](04-value-channel.md) |
| [`Materialise/MatFoldChannel.lean`](../../../LirLean/Materialise/MatFoldChannel.lean) | 1,347 | L4: `MatDecC`/`MatRunsC`/`materialise_runsC` — the linchpin | live | [04](04-value-channel.md) |
| [`Materialise/MaterialiseCleanHalt.lean`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean) | 401 | L4: gas envelope derived from one clean-halt witness | live | [04](04-value-channel.md) |
| [`Materialise/MatDecLower.lean`](../../../LirLean/Materialise/MatDecLower.lean) | 147 | L4: PUSH32 immediate round-trip (`uInt256_wordBytesBE`) | live | [04](04-value-channel.md) |
| [`Materialise/DefsSound.lean`](../../../LirLean/Materialise/DefsSound.lean) | 650 | L4: recompute-soundness invariant + per-arm preservation | live | [04](04-value-channel.md) |
| [`Materialise/StashTail.lean`](../../../LirLean/Materialise/StashTail.lean) | 478 | L4: the uniform `PUSH32 slot; MSTORE` stash tail, proved once | live | [04](04-value-channel.md) |
| [`Materialise/CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean) | 1,123 | per-op OOG/inversion/dichotomy bricks (IR-free half is engine theory) + envelope family | live; half staged | [01](01-trusted-base.md)/[04](04-value-channel.md) |
| [`Frame/Call.lean`](../../../LirLean/Frame/Call.lean) | 164 | L4: `CallOracle`/`evmCallOracle` (live); `applyCall` | live / dead-candidate | [04](04-value-channel.md) |
| [`Frame/Create.lean`](../../../LirLean/Frame/Create.lean) | 137 | L4: `CreateOracle`/`evmCreateOracle` (live); `applyCreate` | live / dead-candidate | [04](04-value-channel.md) |
| [`Frame/Match.lean`](../../../LirLean/Frame/Match.lean) | 618 | L4: lenses, `sim_*` opcode bricks, reflexivity headlines (live); v1 `Match` structure | live / dead-candidate | [04](04-value-channel.md) |
| `Frame/SmallStep.lean` (deleted) | 129 | v1 IR machine state — **zero theorem consumers** | removed | [04](04-value-channel.md) |
| [`Frame/StorageErase.lean`](../../../LirLean/Frame/StorageErase.lean) | 217 | RBMap `erase` read-back (zero-write SSTORE) | staged→exp003 | [01](01-trusted-base.md) |
| [`Sim/SimStmt.lean`](../../../LirLean/Sim/SimStmt.lean) | 1,150 | L5: `Corr` + the five statement arms | live | [05](05-simulation.md) |
| [`Sim/SimStmts.lean`](../../../LirLean/Sim/SimStmts.lean) | 164 | L5: `SimStmtStep` + statement-list induction (flagship uses a coupled twin) | live/incremental | [05](05-simulation.md) |
| [`Sim/SimTerm.lean`](../../../LirLean/Sim/SimTerm.lean) | 843 | L5: terminator halt/edge arms; `corr_at_jumpdest_landing` live in flagship | live | [05](05-simulation.md) |
| [`CfgSim/LowerConforms.lean`](../../../LirLean/CfgSim/LowerConforms.lean) | 1,127 | L6: `WellFormedLowered` (live); builders/`sim_cfg`/`entry_corr`/`CallRealises` | live / superseded | [05](05-simulation.md) |
| [`CfgSim/LowerDecode.lean`](../../../LirLean/CfgSim/LowerDecode.lean) | 1,069 | L6 aux: decode dischargers (live) + `_lowered` builder wrappers | live / superseded | [05](05-simulation.md) |
| [`Law.lean`](../../../LirLean/Law.lean) | 178 | IR determinism ladder (`IRRun.det` — the ∃O is unique) | live | [02](02-spec-layer.md) |
| [`IRRun.lean`](../../../LirLean/IRRun.lean) | 173 | pure-fragment existence ladder; `RunDefinable` unsatisfiable for gas/call programs (rename due) | live fragment | [02](02-spec-layer.md) |
| [`RecorderLemmas.lean`](../../../LirLean/RecorderLemmas.lean) | 169 | recorder adequacy (`driveLog_drive`/`runWithLog_drive`) + stream cons projections | live | [02](02-spec-layer.md)/[06](06-realisability.md) |
| [`CallRealises.lean`](../../../LirLean/CallRealises.lean) | 143 | call/create entry bridges (recorded entry = lowered opcode's effect) | live | [02](02-spec-layer.md)/[06](06-realisability.md) |
| [`Call.lean`](../../../LirLean/Call.lean) | 146 | worked two-channel IR example (`callIR`); nothing consumes it | example | [06](06-realisability.md) |
| [`Drive/SelfPresent.lean`](../../../LirLean/Drive/SelfPresent.lean) | 426 | `SelfPresent` + gas/sload log-alignment discharges | live | [06](06-realisability.md) |
| [`Drive/CallPreservesSelf.lean`](../../../LirLean/Drive/CallPreservesSelf.lean) | 350 | self-presence forward-closed along `Runs`, reduced to the precompile seam | live (engine-shaped, staged) | [01](01-trusted-base.md) |
| [`Drive/DriveSim.lean`](../../../LirLean/Drive/DriveSim.lean) | 721 | coupling-free walk template + `lower_conforms_cyclic'` (pure fragment, endpoint uncalled) | superseded (template) | [06](06-realisability.md) |
| [`Drive/Headline.lean`](../../../LirLean/Drive/Headline.lean) | 299 | `DriveCorrPlus` carrier + retained bricks; carrier unreferenced by the WIP walk | partly superseded | [06](06-realisability.md) |
| [`Realisability/Surface.lean`](../../../LirLean/Realisability/Surface.lean) | 588 | L7: `RecorderCoupled`, `DriveCorrLog`, `StmtTies'`/`TermTies'`, `CallRealisesS`, `WellLowered` (defs real, sorry-free) | live (WIP lib) | [06](06-realisability.md) |
| [`Realisability/Machinery.lean`](../../../LirLean/Realisability/Machinery.lean) | 2,034 | L7: R-obligation grid — R0b/R1/R2/R4/R5/R7a–e′/R8 closed; R3 Piece B + 3 R6 bricks open | WIP (5 sorry sites / 4 decls) | [06](06-realisability.md) |
| [`Realisability/Producer.lean`](../../../LirLean/Realisability/Producer.lean) | 1,463 | L7/L8: coupled arms + block walk + recursion + the packaged producer | WIP (7 sorries) | [06](06-realisability.md) |
| [`Realisability/RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean) | 429 | L8: the three flagship shells, `conforms_of_worldeq`, R10/R12 | WIP (4 sorries) | [06](06-realisability.md) |
| [`Realisability/Witness.lean`](../../../LirLean/Realisability/Witness.lean) | 621 | `exProg` non-vacuity witness + static bundle + R9 checker (sorry-free) | example/witness | [06](06-realisability.md) |

## 5. What remains for `lower_conforms`

Condensed from [06](06-realisability.md) §4 (full sorry-by-sorry table there). The census —
re-verified by grep for this synthesis — is **16 proof-position sorries in 15 declarations**,
distributed [`Machinery.lean`](../../../LirLean/Realisability/Machinery.lean) 5 sites /
4 decls, [`Producer.lean`](../../../LirLean/Realisability/Producer.lean) 7,
[`RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean) 4 — all
in the non-default `WIP` lib; the default cone is sorry-free. The dependency-ordered chunks
(per the [r11 plan](../../planning/r11-plan-2026-07-08.md)):

1. **R6 boundary geometry** — three engine-geometry bricks inside the whole-run
   boundary invariant: B-pc and B-inrange in
   [`atReachableBoundaryVJ_step`](../../../LirLean/Realisability/Machinery.lean#L1372),
   the CALL in-range instance
   ([#L1431](../../../LirLean/Realisability/Machinery.lean#L1431)), and the whole CREATE
   resume edge ([#L1464](../../../LirLean/Realisability/Machinery.lean#L1464)). The
   support algebra (cursor inversion, local-region walks, `NoCallCreateOp` tower) is already
   in-tree from R11 chunk 1; B-call is closed.
2. **CALL Piece B** — the one missing machine-run producer: the CALL arg-push driver
   (`Runs fr₀ callFr` over the five zero-pushes + operand materialisation, ~200 lines),
   blocking [`callRealises_of_recorded`](../../../LirLean/Realisability/Machinery.lean#L392)
   and hence the coupled call arm. Piece A (record extraction from the coupling) is landed.
3. **CREATE2-only + the create coupling channel** — the **latent obligation with no
   `sorry` to count**: [`RecorderCoupled`](../../../LirLean/Realisability/Surface.lean#L234)
   has no create suffix, [`StreamsAligned`](../../../LirLean/Realisability/Producer.lean#L74)
   pins `D` to the whole `log.creates`, and `StmtTies'` has no create arm — so a producer
   closing only the visible sorries could not step through a top-level CREATE, while all
   three flagships range over create-containing programs. This changes the coupling
   signatures and must land **before** the arms/walk, or arms get re-proved.
4. **Coupled statement arms** — gas, sload, call
   ([`simStmt_coupled_gas`](../../../LirLean/Realisability/Producer.lean#L453) etc.), plus
   R10a ([`stmtTies'_of_runWithLog`](../../../LirLean/Realisability/Producer.lean#L2488)).
5. **Block walk / recursion / packaging** — P3a/P3b/P4 and the producer itself, structurally
   mirroring the proved coupling-free recursion.
6. **Flagships** — plain (assembly only), exact (needs an exact-consumption producer; post-hoc
   exactness is a plan no-go), gasfree (+ [`realisedGas_nil_of_noGasReads`](../../../LirLean/Realisability/RealisabilitySpec.lean#L376),
   which needs the R6 walk), then the R12a runtime witness.

**Local-tree vs. plan-checkpoint discrepancy** (found independently by [03](03-code-geometry.md)
and [06](06-realisability.md)): the r11 plan checkpoint reports B-pc and the CALL in-range
brick closed in a box run via commits `ff825e3`/`9d45927` — **neither commit exists in the
local tree**, where those sorries are still open; and the CREATE2-only spec decision
(mandatory salt, emit only `Byte.create2`) is resolved in the plan but **not landed in
source** ([`CreateSpec.salt`](../../../LirLean/Spec/IR.lean#L27) is still `Option Tmp`, the
[`Byte.create` branch](../../../LirLean/Spec/Lowering.lean#L141) still emitted). Reconciling
the boxed work is the first practical step.

## 6. Cross-report findings

### (a) One disease, four instances: the free-∀ tie

Every major failure in this experiment's history is the same shape — a run-dependent value
universally quantified in a hypothesis with no antecedent linking it to the run, making the
hypothesis either vacuously strong (unsatisfiable) or the theorem vacuous:

1. **The original headline** (deleted 2026-07-03): supplied `StmtTies`/`TermTies` with
   ∀-bound tie values pinned to run-specific values in conclusions — confirmed unsatisfiable
   for essentially every nonempty program ([06 §1](06-realisability.md)).
2. **The value universals** [`GasRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L318)/
   [`SloadRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L297): one word forced
   to equal the gas reading at *every* same-address frame — machine-checked unsatisfiable
   (gas strictly descends; warmth flips 2100→100). The refutation forced the uniform
   spill-to-slot design ([04 §3](04-value-channel.md)).
3. **The builder path** ([05 §6](05-simulation.md)): `SimStmtStep`'s all-frames ∀,
   [`SstoreRealises`](../../../LirLean/Sim/SimStmt.lean#L317)'s ∀-frames form, and
   `CallRealises`'s embedded live-scope clause are not producible from a real run — which is
   *why* the entire proved `sim_cfg` chain is dead scaffolding and the flagship re-implements
   the walk with coupled, point-wise variants.
4. **[`RunDefinable`](../../../LirLean/IRRun.lean#L155)**: literally `False` on
   `.call`/`.create`, so the surviving pure-fragment driver
   `lower_conforms_cyclic'` covers no target program; narrowed to `RunDefinableG`
   ([02 §9](02-spec-layer.md)).

The cure was applied uniformly and is now structural: make position physical (spill slots +
[`MemRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366)), or derive from the
run (clean-halt envelopes; the deterministic
[`RecorderCoupled`](../../../LirLean/Realisability/Surface.lean#L234) restart). The
retired definitions are deliberately kept as in-source institutional memory, and the plan's
per-chunk no-gos are the vaccination against re-introduction. Any future reviewer should
treat a new ∀-over-frames hypothesis as a presumptive defect.

### (b) The trust story in one place

What a skeptic must *believe* (as opposed to check mechanically) for the flagship to mean
what §3.9 says:

1. **The machine** — exp003's `EVMLean` implements the EVM. Warrant: empirical only
   (conformance fixtures; interpreter-internal plumbing trusted definitionally).
   [01 §2](01-trusted-base.md).
2. **The recorder gates** — [`driveLog`](../../../LirLean/Spec/Recorder.lean#L51) records the
   *right* events: top-level-only (the `stack.isEmpty`/`rest.isEmpty` depth gates),
   post-step gas values, calls at result delivery in return order. Adequacy
   ([`driveLog_drive`](../../../LirLean/RecorderLemmas.lean#L82)) proves only the result
   channel equals `drive`; the recorded channels are ~40 lines of definition read by eye.
   [02 §5](02-spec-layer.md).
3. **The `Spec/` definitions** — the IR semantics' stream-popping discipline, `lower` (total;
   emits garbage on ill-formed input, safety recovered by `IRWellFormed`+budgets in the
   theorem), and [`observe`](../../../LirLean/Spec/Recorder.lean#L122)'s deliberately coarse
   result channel (STOP ≡ empty RETURN; >32-byte outputs truncated — inexpressible by this
   IR, but the definition doesn't know that). [02 §§3–5](02-spec-layer.md).
4. **The seams** — [`PrecompileAssumptions`](../../../LirLean/Spec/Seams.lean#L31)
   (`noErase`, `callsCode`, `createResolves`): trace-quantified but benign — they constrain
   the *environment* (no precompile callees, no 63/64-overflow CREATE), not the program, and
   are vacuous for call/create-free programs. [01 §5](01-trusted-base.md), [02 §6](02-spec-layer.md).
5. **Lean + three standard axioms**, pinned by [`Audit.lean`](../../../LirLean/Audit.lean#L27)
   for the closed cone; the WIP lib intentionally carries no guards until obligations close.

Everything else — Engine, Decode, Materialise, Sim, the coupling — is machine-checked proof
plumbing a reader auditing *meaning* may skip. Notably, `Runs` appearing inside the
statement (via `ReachableFrom`) is checked vocabulary, pinned in both directions by
`messageCall_runs` and `runs_of_drive_ok` ([01 §6](01-trusted-base.md)).

### (c) The relocation / cleanup ledger — a post-R11 queue, not current work

The reports converge on a substantial but non-blocking hygiene backlog. None of it is a
soundness issue; the plan's own quiescence gate ("defer import-moving surgery until the
producer files are quiescent") correctly queues it behind R11:

- **Engine relocation (D10)**: ~6.3k IR-free lines under `EVM/BytecodeLayer/Hoare/` (+ kin) belong in
  exp003 and are still *growing*; the cheap discipline meanwhile is "new engine lemmas land
  exp003-side first" ([01 §8.4](01-trusted-base.md)).
- **Dead v1 surface**: `Frame/SmallStep.lean`, `applyCall`/`applyCreate`, the `Match`
  structure — zero consumers, actively misleading docstrings ([04 §6.2](04-value-channel.md)).
- **Builder-path retirement**: the `SimStmtStep`/builders/`sim_cfg`/`entry_corr`/
  `CallRealises` chain, DriveSim's cyclic endpoints, and the unreferenced `DriveCorrPlus` —
  decide delete-vs-reshape at R11 close-out, with the same discipline as the b144af8 purge
  ([05 §8](05-simulation.md), [06 §8](06-realisability.md)).
- **Structural tidy**: `Spec/` import inversions + `BudgetDerivations` relocation,
  `LoweringLemmas` out of `Decode/`, `Trace`→`GasOracle`, `evalExpr`'s phantom `obs`,
  `RunDefinable` rename. The `Assembly/` → `CfgSim/` role rename is complete.
- **Doc regeneration**: the [codebase map](../../codebase-map-2026-07-06.md) is stale on
  `pcOf`'s location and the whole fuel-era `Materialise` naming; the 2026-07-04 deep-dives
  predate deletions made the same day; exp003's `Hoare.lean` docstring promises an export
  discipline the codebase abandoned and names a nonexistent theorem; assorted in-file line
  references have drifted. Each deep report lists its slice.

### (d) Strategic verdicts

- **Linear frames: keep, vindicated** ([08](08-related-work.md)). Verifereum (HOL4) and KEVM
  independently chose the same explicit-frame-stack shape, and Verifereum re-derives nested
  calls by depth-gating exactly as exp005 does; the in-house bake-off measured the nested
  alternative at 4,746 proof lines vs 764 for the same theorem. The frame-model tax
  (~2 kLOC: `Runs` bundles, `runs_of_drive_ok`, recorder gating) is paid, closed, reusable;
  the *current* grind is lowering-induced and no frame model would remove it.
- **Assembler: pay geometry once, strictly after R11** ([07](07-assembler.md)). The
  fused-assembler diagnosis is real (~3.6k geometry lines stated over `lower prog`);
  the extraction is a re-indexing, not a file move; prototype the `assemble ∘ lowerAsm`
  definitional-equality bridge before committing, and treat the 2026-07-02 signature
  sketches as sketches.
- **Prior-art claim needs correcting** ([08 §4](08-related-work.md)). Our docs' blanket "no
  fork does pc/stack/jumpdest reasoning" is falsified by vyper-hol's `venom/codegen` tree
  (real proved geometry). The defensible — and still strong — form: **no prior project has a
  completed, call-inclusive IR→bytecode simulation** (vyper-hol's top-level simulations are
  `cheat`ed, its Asm model is single-context and call-free, and its own annotation marks the
  claim "FALSE AS STATED" at the call boundary). Gas introspection remains unique to exp005.

### (e) Cross-report errata

[02](02-spec-layer.md)'s TL;DR says "all **6** `sorry`s live in the non-default WIP lib" —
the count is wrong (the location claim is right); the authoritative census is **16 sites /
15 declarations** ([06 §4](06-realisability.md), re-verified by grep for this synthesis).

## 7. Recommendations (prioritized)

1. **Reconcile the boxed R6 work first**: either integrate the plan-cited `ff825e3`/`9d45927`
   closures or re-derive B-pc/B-inrange locally from the already-landed chunk-1 support;
   then apply the plan's consume-or-delete rule to the staged `Decode/` bricks.
2. **Land the CREATE coupling channel (chunk 3) before the coupled arms** — it changes
   `RecorderCoupled`/`StreamsAligned`/`StmtTies'` signatures; sequencing it late means
   re-proving arms. Land the CREATE2-only lowering correction in the same stroke so the
   spec of record and the source agree.
3. **Close R11 in plan order** (Piece B driver → arms → R10a → walk/recursion → producer →
   flagships gasfree-first), keeping the no-gos and the monotone sorry census.
4. **One post-R11 cleanup wave**: builder-path retirement, dead v1 deletion, and stale-doc
   regeneration (§6c) — as a single disciplined sweep, not piecemeal. The `CfgSim/` rename is done.
5. **Adopt the engine-lemmas-land-in-exp003 discipline now** (cheap; stops the D10 debt
   compounding), and fix exp003's two-line `Hoare.lean` docstring rot.
6. **Update the prior-art phrasing** in `remediation-plan`/`bytecode-interface` to the
   defensible "no completed call-inclusive IR→bytecode simulation" form.
7. **Prototype the Asm defeq bridge** before Phase 5 is scheduled, per [07](07-assembler.md)'s
   qualification 3.
