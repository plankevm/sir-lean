# Phase B2 mixed-file split review (2026-07-13)

## TL;DR

The eight landed B2 commits put the intended EVM-only declarations under the
[bytecode execution surface](../../experiments/003_bytecode_layer/BytecodeLayer/Exec.lean#L1)
and leave the declarations whose statements mention the IR in exp005. The moved Lean
signatures and bodies are faithful relocations modulo namespace/import/export plumbing; the
three flagship statements are byte-for-byte unchanged across the reviewed range. I found no
semantic defect, new premise, or forbidden proof shortcut in the reviewed declarations.

The Lean split was semantically correct as landed. Review found a source-hygiene defect: several
new generic files still described results in IR terms, and five adapters still claimed to own
declarations that moved. The follow-up cleanup rewrote those comments in bytecode-local terms,
collapsed the adapter headers, and removed redundant imports. The generic theorem
[`lower_modellable`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Modellable.lean#L362)
still has a legacy lowering-flavoured name although its statement is about an arbitrary entry
frame; its docstring is now generic, and the rename is recorded as non-blocking naming debt.
Verdict: **pass after the B2 cleanup; no semantic defect remains.**

Verification status: changed declarations were read against the pre-split versions; the flagship
file has zero diff from the parent of the first reviewed commit through HEAD; an executable-token
scan found no `sorry`, `admit`, `axiom`, `native_decide`, or `bv_decide` in the reviewed code. The
reported full builds and all three reported axiom sets were not re-run here, as required by the
review-agent protocol.

## Goal and cut rule

The governing [runbook](../planning/split-execution-runbook-2026-07-13.md#L80) asks B2 to move
frame/run/recorder facts into the bytecode surface and retain only IR-indexed adapters. The
[classification](../planning/exp005-ir-vs-generic-classification.md#L67) gives the per-module
cut-lines. The [surface design](../planning/split-and-assembler-plan-2026-07-13.md#L43) places
execution bricks in the execution facade, recorder checks under its recorder component, and
presence/modellability facts under invariants; assembler geometry remains a later phase.

The code-level criterion holds: none of the eight new modules imports exp005, and none of their
declaration signatures mentions an IR program, statement, expression, temporary, lowering, or
materialisation function.

## Module map and dependency stack

The abstraction stack is bottom-up: atomic frame and arithmetic facts feed endpoint bundles;
alignment and trace-check soundness feed seam hypotheses; the exp005 adapters re-export those
facts and add only IR-indexed bridges; the unchanged flagships consume the resulting chain.

| reviewed commit | generic destination | retained adapter | assessment |
|---|---|---|---|
| `b49694cb` | [gas arithmetic](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Gas.lean#L1) | [IR charge fold](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseGas.lean#L1) | Correct cut: two frame/list facts moved; the charge-cache tower remains IR-shaped. |
| `1bc50999` | [recorder alignment](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Alignment.lean#L1) | [two value-channel selections](../../experiments/005_ir_lowering/LirLean/Drive/SelfPresent.lean#L58) | Correct cut; the adapter keeps only the IR value-channel selections, alias, and re-exports. |
| `93e731ca` | [atomic frame simulations](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Frame.lean#L1) | [three lowering boundary bridges](../../experiments/005_ir_lowering/LirLean/Frame/Match.lean#L35) | Correct statements and minimal two-import adapter. |
| `00aa813f` | [successful-halt projections](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Results.lean#L1) | [terminator simulation](../../experiments/005_ir_lowering/LirLean/Sim/SimTerm.lean#L1) | Clean cut and focused adapter export. |
| `574c7ed7` | [witness checker soundness](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/WitnessChecks.lean#L1) | [concrete exp005 witness](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessParams.lean#L27) | Correct cut; the adapter now describes only the concrete witness and assembly. |
| `391c1638` | [frame/step modellability](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Modellable.lean#L1) | [lowered-code boundary predicate](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L9) | Correct semantic cut; docstrings are generic/local, with only the legacy theorem name deferred. |
| `2a188960` | [memory/accessor and stash bundle](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Memory.lean#L1) | [IR value-channel relations](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean#L60) | Correct landed subset; explicitly deferred relations remain IR-indexed. |
| `5df82804` | [stash-tail forward runs](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Stash.lean#L1) | [cached-SLOAD composition](../../experiments/005_ir_lowering/LirLean/Materialise/StashTail.lean#L8) | Correct cut; both sides now describe only their local role. |

The root [execution facade imports every landed module](../../experiments/003_bytecode_layer/BytecodeLayer/Exec.lean#L7),
so the new surface is actually exported rather than merely parked in its directory.

## Specs that establish the cut

### Generic arithmetic and alignment

The moved gas facts are independent of the IR. The representative statement is
[`charge_binOpPost_gas`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Gas.lean#L15):

```lean
theorem charge_binOpPost_gas (fr : Frame) (op : UInt256 → UInt256 → UInt256)
    (a b : Word) (rest : Stack Word) :
    (BytecodeLayer.Dispatch.binOpPost fr.exec op a b rest).gasAvailable
      = subCharges fr.exec.gasAvailable [Gverylow] := by
```

The recorder split introduces two generic list/frame relations. Their definitions at
[`GasLogAligned`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Alignment.lean#L34)
and [`SloadLogAligned`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Alignment.lean#L95)
contain only recorded values and reachable EVM frames:

```lean
def GasLogAligned (gasAcc : List Word) (frs : List Frame) : Prop :=
  gasAcc = frs.map gasReadOf ∧ FramesRun frs

def SloadLogAligned (sloadAcc : List Nat) (frs : List Frame) : Prop :=
  sloadAcc = frs.map sloadWarmthOf ∧ FramesRun frs
```

The adapter then adds the genuinely IR-coupled selection. For example,
[`sloadRealises_charge_of_witness`](../../experiments/005_ir_lowering/LirLean/Drive/SelfPresent.lean#L81)
mentions both an IR state and a temporary-indexed resolver, so it is correctly retained:

```lean
theorem sloadRealises_charge_of_witness {sloadChg : Tmp → ℕ} {st : Lir.IRState}
    {sloadAcc : List Nat} {frs : List Frame} {i : Nat} {g fr : Frame} {k : Tmp} {key : Word}
    (halign : SloadLogAligned sloadAcc frs)
    (hwit : frs[i]? = some g)
    (hkey : g.exec.stack.head? = some key)
    (haddr : g.exec.executionEnv.address = fr.exec.executionEnv.address)
    (hlk : st.locals k = some key)
    (htie : SloadRealises sloadChg st fr) :
    sloadAcc[i]? = some (sloadChg k) := by
```

### Frame effects and halt projections

The representative generic opcode theorem
[`sim_sstore`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Frame.lean#L137)
is framed entirely by decode, stack, gas, account, and storage facts:

```lean
theorem sim_sstore (fr : Frame) (key value : Word) (rest : Stack Word) (acc : Account)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: value :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key value ≤ fr.exec.gasAvailable.toNat)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    Runs fr (sstoreFrame fr key value rest)
      ∧ storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address key = value
      ∧ ∀ k', k' ≠ key →
          storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address k'
            = storageAt fr fr.exec.executionEnv.address k' := by
```

By contrast, the retained bridge
[`lower_preserves_discharge`](../../experiments/005_ir_lowering/LirLean/Frame/Match.lean#L41)
is indexed by a program and its lowering, exactly matching the classification cut:

```lean
theorem lower_preserves_discharge (prog : Program) (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (_hcode : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
```

The moved result projection
[`resultStorageAt_endFrame_success`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Results.lean#L10)
is likewise frame-only; the remaining terminator simulation consumes it from the IR side.

### Memory and stash execution

The generic endpoint carrier is
[`StashRuns`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Memory.lean#L176):

```lean
structure StashRuns (fr endFr : Frame) (slot : Nat) (v : Word) (pcΔ : Nat) (rest : Stack Word) :
    Prop where
  runs        : Runs fr endFr
  memory      : endFr.exec.toMachineState.memory
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).memory
  activeWords : endFr.exec.toMachineState.activeWords
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).activeWords
  pc          : endFr.exec.pc = fr.exec.pc + UInt32.ofNat pcΔ
  code        : endFr.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps  : endFr.validJumps = fr.validJumps
  addr        : endFr.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod      : endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts    : endFr.exec.accounts = fr.exec.accounts
  storage     : ∀ k, selfStorage endFr k = selfStorage fr k
  stack       : endFr.exec.stack = rest
```

The forward theorem
[`stash_tail_runs`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Stash.lean#L108)
accepts only local decode, stack, memory-expansion, and gas premises and returns that carrier.
The cached-SLOAD adapter
[`stash_tail_sload`](../../experiments/005_ir_lowering/LirLean/Materialise/StashTail.lean#L56)
correctly remains in exp005 because its statement depends on an IR program, temporary, cached
materialisation run, and materialisation length.

The two deferred relations visibly cross the value channel. The retained
[`StorageAgree`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean#L129)
mentions the IR world, and the retained
[`MemRealises`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean#L169)
mentions the program allocation and IR locals:

```lean
def StorageAgree (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ key, selfStorage fr key = st.world key

def MemRealises (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.slot slot) → st.locals t = some v →
    (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.memory.size
    ∧ (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32
    ∧ slot + 63 < 2 ^ 64
    ∧ (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v
```

That is substantive evidence for the stated deferral: moving either relation without
generalising its value source would not be relocation-only.

### Modellability and executable witness checks

The generic modellability reduction is
[`modellableStep_of`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Modellable.lean#L352):

```lean
theorem modellableStep_of {fr : Frame} (hcr : CreateResolves fr) (hcc : CallsCode fr) :
    ModellableStep fr := by
```

Its run-wide closure is also semantically generic, despite its current name:

```lean
theorem lower_modellable {fr₀ : Frame}
    (hcr : ∀ fr', Runs fr₀ fr' → CreateResolves fr')
    (hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr') :
    ∀ fr', Runs fr₀ fr' → ModellableStep fr' :=
```

The sole declaration left in the adapter is correctly lowering-indexed:
[`AtReachableBoundary`](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L15).

```lean
def AtReachableBoundary (prog : Lir.Program) (fr : Frame) : Prop :=
  ∃ boundary : Nat,
    fr.exec.executionEnv.code = Lir.lower prog
    ∧ fr.exec.pc = UInt32.ofNat boundary
    ∧ Evm.ReachesBoundary (Lir.lower prog) 0 boundary
    ∧ boundary < (Lir.flatBytes prog).length
    ∧ boundary < 2 ^ 32
```

The checker itself was already generic in the recorder layer; the B2 split moved its proof
theory. The entry wrapper
[`entryCallsCodeOk`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/WitnessChecks.lean#L344)
and its two soundness results,
[`callsCode_of_entryCheck`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/WitnessChecks.lean#L350)
and
[`createResolves_of_entryCheck`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/WitnessChecks.lean#L403),
mention only call parameters, reachable frames, and interpreter predicates. The exp005
[`exProg_satisfies_hypotheses_of_checks`](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessParams.lean#L110)
correctly remains as the concrete IR witness that consumes them.

## Frozen headline surface

The statements at
[`lower_conforms`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221),
[`lower_conforms_exact`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269),
and
[`lower_conforms_gasfree`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304)
are unchanged across the reviewed commits. The first remains the representative headline:

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

No reviewed move adds a public premise: consumers see the same hypotheses through re-exports,
while the declarations themselves live under bytecode-owned namespaces.

## Results taxonomy

- **Headline/mainline:** the three unchanged conformance statements linked above.
- **Supporting execution bricks:** the generic gas facts, frame simulations, halt projections,
  memory carrier, and stash forward runs. These are direct dependencies of IR-side simulation.
- **Supporting invariant/recorder bricks:** the two alignment relations, checker soundness, and
  modellability closure. These discharge the runtime seams consumed by the conformance chain.
- **IR adapters:** the remaining charge fold, selection bridges, lowering boundary bridges,
  terminator simulation, concrete witness, reachable-boundary predicate, value-channel relations,
  and cached-SLOAD composition.
- **Examples/demos:** the concrete witness definitions in
  [the witness adapter](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessParams.lean#L27)
  are the only example-shaped material in scope; they are consumed by the witness theorem rather
  than being isolated demos.
- **Proof smells:** only small closed arithmetic `decide` calls occur in the moved code. The
  expensive checker evaluations described by the witness adapter are outside the moved proof
  theory. No new heartbeat crank or native evaluation appears in the reviewed declarations.

## Deferrals

The three recorded deferrals are justified and comply with the runbook's “re-index or defer” rule.

1. The recorder boundary engine is interleaved with IR simulation. Although
   [`RecorderCoupled`](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean#L315)
   is frame/log-generic, the central fold
   [`recorderCoupled_matRunsC`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L2136)
   immediately quantifies over the program, temporary resolver, IR state, expression,
   materialisation decoder, definition soundness, storage agreement, memory realisation, and IR
   evaluation. Extracting the boundary core therefore requires the advertised re-indexing, not a
   body move.
2. The memory/storage remainder is not currently generic: the two quoted relations reach directly
   into the IR world, locals, and allocation policy. Their generic memory lemmas already moved;
   their value-source generalisation is properly deferred.
3. Remaining decode geometry is intentionally held for the assembler phase. The same source file
   contains the generic
   [`SegAlignedP`](../../experiments/005_ir_lowering/LirLean/Decode/SegAligned.lean#L63)
   calculus and IR emission lemmas such as
   [`segAlignedP_emitImm`](../../experiments/005_ir_lowering/LirLean/Decode/SegAligned.lean#L219),
   demonstrating exactly the re-indexing boundary described by the plan.

## Review findings and resolution

### Resolved: generic comments leaked IR vocabulary

The landed generic statements were IR-free, but their comments still classified opcodes as IR
expressions/statements/terminators and named exp005 lowering and coupling consumers. The cleanup
rewrote the relevant sections in bytecode-local terms:

- [atomic opcode simulations](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Frame.lean#L19)
  now discuss only decoded opcodes, frame transitions, and local effects;
- [memory accessors and the stash carrier](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Memory.lean#L14)
  now describe opcode post-frames and the carrier's own fields;
- [stash execution](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Stash.lean#L17)
  now describes MSTORE memory projections and local forward runs; and
- [modellability closure](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Modellable.lean#L335)
  now states only the two per-frame runtime conditions.

A fresh text scan of the eight generic B2 files finds no IR namespace, constructor, lowering,
materialisation, coupling, or IR value-channel reference.

### Resolved: adapter headers and imports exceeded their remaining role

The cleanup collapses each touched adapter to its actual audit surface:

- [the frame adapter](../../experiments/005_ir_lowering/LirLean/Frame/Match.lean#L1) now has two
  imports and describes only the three lowered-program boundary bridges;
- [the materialisation value-channel adapter](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean#L1)
  now has a focused header and retains one compatibility import of the frame adapter in addition
  to the charge fold, definition soundness, and generic memory theory;
- [the charge adapter](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseGas.lean#L1)
  imports the IR lowering definitions directly and no longer carries empty moved sections;
- [the recorded-value adapter](../../experiments/005_ir_lowering/LirLean/Drive/SelfPresent.lean#L1)
  now imports only generic alignment and the IR value-channel relations;
- [the witness adapter](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessParams.lean#L1)
  describes only the concrete witness and assembly theorem;
- [the modellability adapter](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L1)
  is reduced to the generic re-export edge plus the lowered-code boundary tether; and
- [the terminator adapter](../../experiments/005_ir_lowering/LirLean/Sim/SimTerm.lean#L1)
  retains its recorder vocabulary import while taking the moved result projections directly
  from the generic execution surface.

These are import/comment changes only; no declaration statement or proof body changed.

The retained frame-adapter import is deliberate after build evidence: removing it makes downstream
consumers fail because that module is currently the sole declaration site of the frame namespace
they open transitively. Eliminating this import therefore requires an import-graph/namespace
re-indexing change rather than a relocation-only cleanup; defer it with the other re-indexing work.

### Deferred: legacy generic theorem name

The statement at
[`lower_modellable`](../../experiments/003_bytecode_layer/BytecodeLayer/Exec/Modellable.lean#L362)
does not mention lowering or code. Its docstring is now generic, so the legacy name is not a
correctness or dependency defect. Renaming would require a broad Lean-and-documentation reference
sweep; record it as naming debt for a dedicated surface naming pass. If renamed later, update all
callers and prose references in the same change.

## Recommendation

Accept all eight B2 splits after the cleanup gate. Carry the three documented re-indexing
deferrals and the materialisation adapter's namespace/import debt into the assembler phase, and
keep the modellability theorem rename as non-blocking naming debt. No proof redesign, premise
change, or further B2 extraction is warranted.
