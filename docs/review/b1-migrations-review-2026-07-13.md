# B1 clean-migration review — 2026-07-13

## TL;DR

B1 moved the thirteen planned EVM-generic units from experiment 005 into the
bytecode layer without introducing an IR dependency in any moved declaration or
import. The dependency direction is now one-way: the experiment-005 adapters
import and re-export bytecode-layer declarations, while no bytecode-layer module
imports the IR package. The three flagship statements —
[lower_conforms](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221),
[lower_conforms_exact](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269),
and
[lower_conforms_gasfree](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304)
— are textually unchanged from baseline `e59ae1a6`.

Verdict after the review cleanup: **accept B1.** The moved declarations, imports,
and explanatory comments now stay on the EVM side of the cut; the stale outward
IR/lowering allegations found in the initial pass were removed in a comment-only
follow-up. Static checks found no uses of `sorry`, `admit`, `axiom`,
`native_decide`, or `bv_decide`. Fresh post-cleanup gate, run by the root agent
and reported here without re-running: exp003 `Build completed successfully (1155
jobs).`; exp005 default `Build completed successfully (1180 jobs).`; exp005 WIP
`Build completed successfully (1188 jobs).`; each of the three flagships depends
on exactly `[propext, Classical.choice, Quot.sound]`.

## Goal and cut criterion

The governing [classification](../planning/exp005-ir-vs-generic-classification.md)
calls a declaration generic when its statement is entirely about EVM execution
objects and does not quantify over or inspect IR syntax or lowering. The
[execution runbook](../planning/split-execution-runbook-2026-07-13.md) then asks
B1 to relocate thirteen such units while preserving proof bodies and public
flagship statements. This review checks that cut, not the later assembler work
excluded by the [split-and-assembler plan](../planning/split-and-assembler-plan-2026-07-13.md).

The shared observable vocabulary was already hoisted in B0. Its central shape is
[Observable](../../EVM/BytecodeLayer/Exec/Observable.lean#L32):

```lean
abbrev Word := UInt256

abbrev World := Word → Word

inductive HaltResult where
  | stopped
  | returned (w : Word)
deriving DecidableEq, Repr

abbrev GasOracle := List Word

-- Compatibility alias; declarations generally use `GasOracle`.
abbrev Trace := GasOracle

abbrev CallStream := List (World × Word)

abbrev CreateStream := List (World × Word)

structure Observable where
  world  : World
  result : HaltResult
```

This substrate is structurally generic. Its
[HaltResult](../../EVM/BytecodeLayer/Exec/Observable.lean#L18) name is IR-neutral,
and no B1 declaration mentions the source IR's program, block, statement, term,
expression, temporary, call/create spec, lowering, emission, definition map, or
materialisation cache in its type.

## Migration inventory and import direction

Every planned B1 unit is accounted for below. “Adapter” means the remaining
experiment-005 module imports the generic owner and supplies only re-exports or a
genuinely IR-specific specialization.

| Commit | Planned unit | New generic owner | Experiment-005 side at HEAD | Audit |
|---|---|---|---|---|
| `b3c31593` | Storage erase | [Invariants.lean](../../EVM/BytecodeLayer/Exec/Invariants.lean#L31) | old module deleted | Generic ordered-tree and EVM storage-map facts only. |
| `aedcd7d3` | Word encoders | [Exec.lean](../../EVM/BytecodeLayer/Exec.lean#L12) | old module deleted; lowering imports the owner directly in [Lowering.lean](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L2) | Generic big-endian byte encoders only. |
| `7044a0b6` | CALL effect oracle | [Call.lean](../../EVM/BytecodeLayer/Exec/Call.lean#L33) | old module deleted | Types use only EVM call/result/resume objects and shared observables. |
| `d8af28aa` | CREATE effect oracle | [Create.lean](../../EVM/BytecodeLayer/Exec/Create.lean#L33) | old module deleted | Types use only EVM create/result/resume objects and shared observables. |
| `a41bdd84` | Execution recorder | [Recorder.lean](../../EVM/BytecodeLayer/Exec/Recorder.lean#L26) | [Spec/Recorder.lean](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L1) re-exports the generic surface | Recorder is parameterized by EVM frames, results, pending calls/creates, and streams only. |
| `4c78d6ac` | Recorder lemmas | [RecorderLemmas.lean](../../EVM/BytecodeLayer/Exec/RecorderLemmas.lean#L20) | [RecorderLemmas.lean adapter](../../experiments/005_ir_lowering/LirLean/RecorderLemmas.lean#L1) | Adequacy and stream-cons lemmas are EVM/recorder-only. |
| `1d8fe2fe` | Word decode lemmas | [ByteWindow.lean](../../EVM/BytecodeLayer/Exec/ByteWindow.lean#L23) | [MatDecLower.lean adapter](../../experiments/005_ir_lowering/LirLean/Materialise/MatDecLower.lean#L1) | Arithmetic, byte-window, and decoder facts only. |
| `35ac4da6` | Segmented evaluator | [SegmentedEval.lean](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L24) | [SegmentedEval.lean adapter](../../experiments/005_ir_lowering/LirLean/Realisability/SegmentedEval.lean#L1) | Generic one-step and segmented evaluation of the recorder/checker. |
| `2b43d6f7` | Checked evaluator | [CheckedStep.lean](../../EVM/BytecodeLayer/Exec/CheckedStep.lean#L82) | [CheckedStep.lean adapter](../../experiments/005_ir_lowering/LirLean/Realisability/CheckedStep.lean#L1) | Checked twins and soundness statements use only EVM machine state and recorder configurations. |
| `608caa0c` | Self-presence preservation | [CallPreservesSelf.lean](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L31) | [CallPreservesSelf.lean adapter](../../experiments/005_ir_lowering/LirLean/Drive/CallPreservesSelf.lean#L1) | All predicates quantify over EVM steps, calls, creates, runs, and account presence. |
| `c4714994` | Call/create realization bridges | [CallRealises.lean](../../EVM/BytecodeLayer/Exec/CallRealises.lean#L24) | [CallRealises.lean adapter](../../experiments/005_ir_lowering/LirLean/CallRealises.lean#L1) | The reflection names identify their oracle boundary, and all types are EVM resume/observable equalities. |
| `de400da0` | Clean-halt extraction | [CleanHaltExtract.lean](../../EVM/BytecodeLayer/Exec/CleanHaltExtract.lean#L60) | [CleanHaltExtract.lean adapter](../../experiments/005_ir_lowering/LirLean/Materialise/CleanHaltExtract.lean#L1) retains the IR-specific specialization | Generic opcode envelopes moved; the one theorem that mentions IR syntax and materialisation stayed above the cut. |
| `d3337dd8` | Seam predicates | [Invariants.lean](../../EVM/BytecodeLayer/Exec/Invariants.lean#L268) and [CallPreservesSelf.lean](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L230) | [Spec/Seams.lean](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L1) retains aliases and the phantom program parameter | Generic seam structure no longer depends on the source IR; the adapter preserves the old public shape. |

The bytecode-layer imports at the heads of
[Recorder.lean](../../EVM/BytecodeLayer/Exec/Recorder.lean#L1),
[SegmentedEval.lean](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L1),
[CheckedStep.lean](../../EVM/BytecodeLayer/Exec/CheckedStep.lean#L1),
and
[CallPreservesSelf.lean](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L1)
stay entirely inside EVM/BytecodeLayer dependencies. A repository search found no
bytecode-layer import of `LirLean`; conversely, each adapter in the table imports
its new generic owner. The build therefore enforces the intended one-way package
edge rather than merely hiding an IR reference behind an open namespace.

There is one useful source-versus-plan correction. The classification called the
clean-halt module a whole-file migration, but the live source contains
[sload_envelope_of_cleanHalt](../../experiments/005_ir_lowering/LirLean/Materialise/CleanHaltExtract.lean#L36),
whose type mentions the IR program, temporary, expression, and materialisation-run
relation:

```lean
theorem sload_envelope_of_cleanHalt
    {prog : Program} {sloadChg : Tmp → ℕ} {ekey : Expr} {wkey : Word}
    (fr frk : Frame) (keyVal : UInt256) (slot : Nat)
    (hcs : CleanHaltsNonException fr)
    (hstk0 : fr.exec.stack = [])
    (hmrk : Lir.MatRunsC prog sloadChg ekey wkey fr frk)
```

B1 made the correct cut: this specialization remains in experiment 005 while
the opcode-level extraction theory moved. This is a plan-inventory inaccuracy,
not a code defect.

## Abstraction stack

### 1. Leaf arithmetic, storage, and opcode facts

[findD_erase_self](../../EVM/BytecodeLayer/Exec/Invariants.lean#L192)
and
[findD_erase_of_ne](../../EVM/BytecodeLayer/Exec/Invariants.lean#L202)
give the EVM storage-map readback laws after clearing a slot:

```lean
theorem findD_erase_self (s : Storage) (k : UInt256) :
    (s.erase k).findD k 0 = 0 := by

theorem findD_erase_of_ne (s : Storage) {k' k : UInt256} (h : k' ≠ k) :
    (s.erase k).findD k' 0 = s.findD k' 0 := by
```

[uInt256_wordBytesBE](../../EVM/BytecodeLayer/Exec/ByteWindow.lean#L95)
is the corresponding byte-roundtrip brick:

```lean
theorem uInt256_wordBytesBE (w : Word) :
    uInt256OfByteArray ⟨(BytecodeLayer.Exec.wordBytesBE w).toArray⟩ = w := by
```

The large clean-halt module supplies frame-local decode/gas/memory envelopes. A
representative mainline statement is
[gas_envelope_of_cleanHalt](../../EVM/BytecodeLayer/Exec/CleanHaltExtract.lean#L667):

```lean
theorem gas_envelope_of_cleanHalt (fr : Frame) (slot : Nat)
    (hcs : CleanHaltsNonException fr)
    (hstk0 : fr.exec.stack = [])
    (hdecGAS : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hdecPUSH : decode (gasFrame fr).exec.executionEnv.code (gasFrame fr).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdecMSTORE :
        decode (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.executionEnv.code
          (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.pc
        = some (.Smsf .MSTORE, .none)) :
    Gbase ≤ fr.exec.gasAvailable.toNat
    ∧ 3 ≤ (gasFrame fr).exec.gasAvailable.toNat
    ∧ ∃ words',
        memoryExpansionWords?
          (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.activeWords
          (UInt256.ofNat slot) 32 = some words'
        ∧ memExpansionChargeOf (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words'
            ≤ (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat
        ∧ Gverylow ≤ ((pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable
            - UInt64.ofNat (memExpansionChargeOf
                (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words')).toNat := by
```

These are supporting bricks: the flagship consumes them transitively through the
IR-side simulation, but their statements are independent of that consumer.

### 2. CALL/CREATE effect projection

[CallOracle](../../EVM/BytecodeLayer/Exec/Call.lean#L33)
and
[CreateOracle](../../EVM/BytecodeLayer/Exec/Create.lean#L33)
abstract the state that becomes externally observable after an EVM descent:

```lean
structure CallOracle where
  /-- Post-call storage of `addr` at `key`, through the observable lens. -/
  postStorage : CallResult → PendingCall → AccountAddress → Word → Word
  /-- Gas restored to the caller on resume (`gasAfterReturn`). -/
  restoredGas : CallResult → PendingCall → UInt64
  /-- The 0/1 success word the CALL pushes (`x`). -/
  successWord : CallResult → PendingCall → Word

structure CreateOracle where
  /-- Post-create storage of `addr` at `key`, through the observable lens. -/
  postStorage : CreateResult → PendingCreate → AccountAddress → Word → Word
  /-- The deployed-address-or-`0` word the CREATE pushes. -/
  addressWord : CreateResult → PendingCreate → Word
```

The concrete projections are connected back to returning machine runs by
[callRealises_bridge](../../EVM/BytecodeLayer/Exec/CallRealises.lean#L67)
and
[createRealises_bridge](../../EVM/BytecodeLayer/Exec/CallRealises.lean#L99):

```lean
theorem callRealises_bridge {callFr resumeFr : Frame} (self : AccountAddress)
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (evmCallEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmCallEntry result pd self).2
          = callSuccessFlag result pd := by

theorem createRealises_bridge {createFr resumeFr : Frame} (self : AccountAddress)
    (hc : CreateReturns createFr resumeFr) :
    ∃ result pd, resumeAfterCreate result pd = .ok resumeFr
      ∧ (evmCreateEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmCreateEntry result pd self).2
          = createAddrOrZero result pd := by
```

These bridge the EVM resume semantics to stream entries; they do not mention an
IR call or create instruction.

### 3. Recorder, segmented evaluator, and checked twin

[RunLog](../../EVM/BytecodeLayer/Exec/Recorder.lean#L34)
is the machine-side record consumed by the headline:

```lean
structure RunLog where
  observable : FrameResult
  gas : List Word
  sloads : List Nat
  calls : List CallRecord
  creates : List CreateRecord

def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False
```

[driveLog](../../EVM/BytecodeLayer/Exec/Recorder.lean#L168)
walks the EVM interpreter while collecting top-level gas, storage-load, call, and
create events; [runWithLog](../../EVM/BytecodeLayer/Exec/Recorder.lean#L216)
packages its terminal result. The load-bearing adequacy statement is
[runWithLog_drive](../../EVM/BytecodeLayer/Exec/RecorderLemmas.lean#L105):

```lean
theorem runWithLog_drive {params : CallParams} {fuel : ℕ} {log : RunLog}
    (h : runWithLog params fuel = some log) :
    ∃ frame, beginCall params = .inl frame
      ∧ drive fuel [] (.inl frame) = .ok log.observable := by
```

The segmented layer makes recursion explicit through
[LogConfig](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L24)
and [nextLog](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L45).
Its terminal theorem,
[driveLogC_final](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L171),
says that a finite transition segment fixes the result at every sufficiently
large fuel:

```lean
theorem driveLogC_final {k : ℕ} {c : LogConfig} {res : LogResult}
    (h : stepsLog k c = .inr res) (fuel : ℕ) :
    driveLogC (k + fuel + 1) c = .ok res := by
```

Finally, the checked twins return an option and prove that every produced answer
matches the original segmented evaluator. The two key soundness surfaces are
[stepsLogChk_sound](../../EVM/BytecodeLayer/Exec/CheckedStep.lean#L650)
and
[stepsCCChk_sound](../../EVM/BytecodeLayer/Exec/CheckedStep.lean#L727):

```lean
theorem stepsLogChk_sound {k : ℕ} {c : LogConfig} {x : LogConfig ⊕ LogResult}
    (h : stepsLogChk k c = some x) : stepsLog k c = x := by

theorem stepsCCChk_sound {k : ℕ} {fr : Frame} {x : Frame ⊕ Bool}
    (h : stepsCCChk k fr = some x) : stepsCC k fr = x := by
```

The recorder and its adequacy theorem are mainline dependencies. The segmented
and checked twins primarily support the concrete non-vacuity witness rather than
the three conformance theorems themselves.

### 4. Account-presence and reachable-frame seams

[SelfPresent](../../EVM/BytecodeLayer/Exec/Invariants.lean#L229)
defines the local invariant:

```lean
def SelfPresent (fr : Frame) : Prop :=
  ∃ acc : Account, fr.exec.accounts.find? fr.exec.executionEnv.address = some acc
```

[StepPreservesSelf](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L31),
[CallPreservesSelf](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L45),
and
[CreatePreservesSelf](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L137)
lift it across the three run-edge forms; then
[selfPresent_runs](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L211)
closes over a whole run:

```lean
def StepPreservesSelf : Prop :=
  ∀ ⦃fr fr' : Frame⦄, StepsTo fr fr' → SelfPresent fr → SelfPresent fr'

def CallPreservesSelf : Prop :=
  ∀ ⦃callFr resumeFr : Frame⦄, CallReturns callFr resumeFr → SelfPresent callFr → SelfPresent resumeFr

theorem selfPresent_runs (hstep : StepPreservesSelf) (hcall : CallPreservesSelf)
    (hcreate : CreatePreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' := by
```

The public environmental seam is now the generic
[PrecompileAssumptions](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L248):

```lean
structure PrecompileAssumptions (params : Evm.CallParams) : Prop where
  noErase : PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'
```

The IR adapter preserves the frozen two-argument surface while erasing its unused
program parameter definitionally in
[Lir.PrecompileAssumptions](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L26):

```lean
abbrev PrecompileAssumptions (_prog : Program) (params : Evm.CallParams) : Prop :=
  BytecodeLayer.Exec.Invariants.PrecompileAssumptions params
```

That is not a weakened flagship premise: the old structure's program parameter
was already phantom, and the same three fields remain.

## Frozen headline specifications

The following source statements are identical before and after B1.

[lower_conforms](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221):

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
      ∧ Conforms params.recipient log O := by
```

[lower_conforms_exact](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269):

```lean
theorem lower_conforms_exact {prog : Program} {params : CallParams} {log : RunLog}
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
      RunFromAll prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
```

[lower_conforms_gasfree](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304):

```lean
theorem lower_conforms_gasfree {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hng : NoGasReads prog)
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
      ∧ Conforms params.recipient log O := by
```

The hypotheses remain substantial but honest. They pin the lowered code, mutable
execution, recipient account, minimum entry gas, IR well-formedness, code/stack
budgets, a successful deterministic recording run, a non-exceptional top-level
result, and the three reachable-frame environment seams quoted above. The exact
theorem consumes all recorded streams; the plain theorem permits suffixes. The
gas-free theorem adds only the no-gas-read restriction. No B1 move adds a premise
or hides a conclusion in a new generic assumption.

## Results taxonomy and risks

- **Headline/mainline:** the three frozen conformance theorems above. B1 changes
  only the location and qualification of supporting declarations in their proof
  cone.
- **Mainline supporting bricks:** storage erasure, word decode, opcode clean-halt
  envelopes, CALL/CREATE projections, recorder adequacy, stream realization, and
  self-presence/seam closure. Their statements are now reusable without importing
  the IR package.
- **Witness support:** the segmented evaluator and checked twins are generic, but
  their current consumer is the experiment's concrete kernel-checked witness.
  They are not proof dependencies of the three headline declarations.
- **Inherited reduction smell:**
  [SegmentedEval.lean](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L12)
  sets one million heartbeats globally and repeats a scoped setting at
  [callsCodeOk_succ_eq](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L223).
  This is isolated to witness/checker evaluation, not the flagships.
- **Inherited elaboration smell:**
  [ByteWindow.lean](../../EVM/BytecodeLayer/Exec/ByteWindow.lean#L17)
  raises recursion depth to 8192, and
  [fromBytes_wordBytesBE](../../EVM/BytecodeLayer/Exec/ByteWindow.lean#L52)
  performs a long explicit 32-byte reduction. The roundtrip brick is in the
  mainline lowering/decode cone, so brittleness here can affect headline builds,
  though it introduces no axiom or untrusted evaluator. Both settings predate B1
  and were relocated rather than added.
## Resolved review finding

The initial pass found that migrated declarations were generic but several
comments still alleged relationships to experiment-005 lowering code and
downstream files. The follow-up rewrote the affected module prose in
[Call.lean](../../EVM/BytecodeLayer/Exec/Call.lean#L6),
[Create.lean](../../EVM/BytecodeLayer/Exec/Create.lean#L6),
[CallRealises.lean](../../EVM/BytecodeLayer/Exec/CallRealises.lean#L6),
[CallPreservesSelf.lean](../../EVM/BytecodeLayer/Exec/CallPreservesSelf.lean#L6),
[CheckedStep.lean](../../EVM/BytecodeLayer/Exec/CheckedStep.lean#L4),
[CleanHaltExtract.lean](../../EVM/BytecodeLayer/Exec/CleanHaltExtract.lean#L4),
[ByteWindow.lean](../../EVM/BytecodeLayer/Exec/ByteWindow.lean#L5),
[Recorder.lean](../../EVM/BytecodeLayer/Exec/Recorder.lean#L105),
[RecorderLemmas.lean](../../EVM/BytecodeLayer/Exec/RecorderLemmas.lean#L3),
and
[SegmentedEval.lean](../../EVM/BytecodeLayer/Exec/SegmentedEval.lean#L3)
to describe only local EVM properties, projections, and evaluators. It also
removed false trailing “axiom-cleanliness guard” comments that did not contain
actual guard commands. The cleanup changes comments only, satisfying the
repository's [keep-comments-local rule](../../AGENTS.md#L51) without altering a
definition, theorem statement, proof body, or import.
