# Phase C2 cyclic-simulation extraction review — 2026-07-14

## TL;DR

Phase C2 successfully moves the recorder-restart carrier and its EVM transition theory out of
experiment 005: the new [recorder carrier](../../EVM/BytecodeLayer/Exec/Recorder.lean#L230) and
[cyclic-simulation module](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L1) contain no `Lir`,
program, label, block, temporary, lowering, or IR-state dependency. The key reusable split is
between a generic fold over EVM run edges and the retained Lir boundary predicate; that is a sound
cut, not a disguised IR interface. I found no semantic correctness defect in the moved statements
or their use by the three unchanged flagships. The review cleanup moved the carrier explanation and
seven residual EVM-only bricks to BytecodeLayer, leaving the retained file as the Lir composition
layer; the consumer-shaped CALL/CREATE dispatch theorems intentionally remain there.

Verification status, stated once: all six changed Lean files and the C2 diff were inspected; there
are no uses of `sorry`, `admit`, `axiom`, `native_decide`, or `bv_decide` in the C2 additions, and
the flagship source file is untouched by the range. After the review cleanup, all five builds were
re-run successfully (1101, 1106, 1164, 1189, and 1197 jobs), and all three flagships reported
exactly `[propext, Classical.choice, Quot.sound]`.

## Findings, ranked

### Resolved P2 — The carrier's design documentation stayed in the Lir adapter

The original C2 commits left the field-by-field generic explanation in the Lir surface and two
process-history comments in the generic proof. The cleanup moved the durable rationale to
[the carrier declaration](../../EVM/BytecodeLayer/Exec/Recorder.lean#L230), reduced
[the Lir section](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean#L282) to its
local walk-invariant role, and made the accumulator comments describe only their local cases.
This resolves the repository's local-comment requirement without changing a declaration type or
proof argument.

### Resolved P2 — Seven public EVM-only bricks remained in the Lir adapter

The moved coupling core is genuinely IR-free, and the declarations that directly compose it with
materialisation, ties, and realisation are appropriately retained. In particular,
[the materialisation fold](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L905),
[the term-tie theorem](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L1480),
[the call-site suffix adapter](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L3123),
and [the create-site suffix adapter](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L3882)
all quantify over Lir programs, expressions, cursors, materialisation, or IR correspondence.

The original C2 cut still publicly declared seven purely EVM bricks in the retained file. The
cleanup moved [halting-run inversion](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L30) and
[frame-kind preservation](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L43) to the generic run
module, and moved the five [CALL-resume projections](../../EVM/BytecodeLayer/Exec/Call.lean#L73)
next to the concrete CALL effect they project. Compatibility exports preserve existing Lir users.
The [CREATE dispatch split](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L3732)
is also EVM-only in its type and carries two deliberately unused hypotheses. It is shaped for the
Lir consumer, so leaving that composition theorem in the adapter is defensible.
The [CALL dispatch split](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L2516)
has an EVM-only type too, but its seven-word stack with five literal zero operands encodes the
current Lir CALL materialisation policy, so it is correctly treated as an adapter despite the lack
of a source-language parameter.

These dispatch results remain consumer-shaped Lir lowering adapters. The CREATE theorem's type is
EVM-only, but its exact four-word stack and two parity hypotheses are the interface its Lir
consumer needs; moving it would not remove a source-policy assumption from the retained proof.

### P3 — “Boundary engine” means a generic fold, not generic boundary geometry

The new [run-invariant driver](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L17) is fully generic,
but the boundary predicate and its ordinary/CALL/CREATE preservation obligations remain
[Lir-indexed](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L547).
That is the correct staging for C2: the driver owns the recursion over EVM edges, while the
assembler work must later replace the predicate's dependence on lowered bytes and Lir cursor
geometry. Reports should say “generic boundary-walk driver” rather than imply that the boundary
geometry itself has already been re-indexed.

## Goal and module accounting

The deferred B2 item was to separate the generic recorder/boundary machinery described in the
[split outcome](./split-outcome-2026-07-13.md#b2-deferrals-to-phase-c), while preserving the
[five-file target architecture](../planning/split-and-assembler-plan-2026-07-13.md#target-architecture-five-files--one-ir-adapter).
C2 covers commits 55ec4025 through 741d4894.

| Changed file | Role in C2 |
|---|---|
| [execution aggregate](../../EVM/BytecodeLayer/Exec.lean#L1) | Re-exports the new cyclic-simulation module. |
| [recorder](../../EVM/BytecodeLayer/Exec/Recorder.lean#L230) | Owns the generic coupling carrier next to the recorder it specifies. |
| [cyclic simulation](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L1) | Owns the IR-free run fold, accumulator transport, event consumption, descent/soft-failure transitions, extraction, and halt projections. |
| [Lir machinery](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L1) | Re-exports the generic API for existing consumers, instantiates the run fold with Lir boundary geometry, and retains Lir materialisation/tie/realisation composition. |
| [Lir surface](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean#L282) | Retains the local IR walk invariant that embeds the generic carrier. |
| [Lir recorder facade](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L1) | Re-exports the moved carrier along with the existing generic recorder vocabulary. |

## The abstraction stack

### 1. Recorder and coupling carrier

The recorder accumulates a final EVM result plus three positional streams. The C2 carrier says that
restarting the same deterministic recorder from a current top-level frame produces the final result
and the remaining suffixes, and that each remaining stream really is a suffix of the original log.
This is the complete [carrier specification](../../EVM/BytecodeLayer/Exec/Recorder.lean#L214):

```lean
/-- Restarting the recorder at a top-level boundary frame reproduces the final observable
and the unconsumed event suffixes. The empty pending stack makes the boundary top-level;
nested CALL/CREATE execution remains hidden by the recorder's stack gate. The prefix
witnesses ensure that every replayed suffix belongs to the original log. -/
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (callSuffix : List CallRecord) (createSuffix : List CreateRecord) : Prop where
  /-- A deterministic replay from the boundary produces exactly the remaining streams. -/
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] []
      = .ok (log.observable, gasSuffix, callSuffix, createSuffix)
  /-- The remaining gas events form a suffix of the recorded gas stream. -/
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  /-- The remaining CALL events form a suffix of the recorded CALL stream. -/
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix
  /-- The remaining CREATE events form a suffix of the recorded CREATE stream. -/
  createPrefix : ∃ pre, log.creates = pre ++ createSuffix
```

The existential replay fuel is not an unproven semantic assumption: it is evidence carried by the
invariant, established from a successful recorder run and decreased/reconciled by the transition
lemmas. The three prefix witnesses prevent an arbitrary replay suffix from masquerading as part of
an unrelated log.

### 2. Generic run recursion

The engine's control relation is the EVM
[run closure](../../EVM/BytecodeLayer/Hoare.lean#L140), whose edges are ordinary steps,
completed calls, and successfully resumed creates:

```lean
inductive Runs : Frame → Frame → Prop where
  /-- Zero steps: a frame reaches itself. -/
  | refl (fr : Frame) : Runs fr fr
  /-- One opcode step `fr → mid`, then the rest of the block `mid → fr'`. -/
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') :
      Runs fr fr'
  /-- An external CALL at `callFr` that returns, resuming at `resumeFr`
  (`CallReturns callFr resumeFr`), then the rest of the block `resumeFr → fr'`. -/
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
  /-- A CREATE at `createFr` that returns and successfully resumes at `resumeFr`
  (`CreateReturns createFr resumeFr`), then the rest of the block `resumeFr → fr'`
  (SPIKE: the CREATE twin of the `call` node). -/
  | create {createFr resumeFr fr' : Frame} (hc : CreateReturns createFr resumeFr)
      (rest : Runs resumeFr fr') : Runs createFr fr'
```

C2 abstracts the induction pattern as
[a predicate-parametric driver](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L17):

```lean
/-- An invariant preserved by ordinary steps and completed CALL/CREATE descents
is preserved by a whole cyclic execution path. -/
theorem invariant_of_runs {Inv : Frame → Prop}
    (step : ∀ {fr fr'}, StepsTo fr fr' → Inv fr → Inv fr')
    (call : ∀ {fr fr'}, CallReturns fr fr' → Inv fr → Inv fr')
    (create : ∀ {fr fr'}, CreateReturns fr fr' → Inv fr → Inv fr')
    {fr fr' : Frame} (run : Runs fr fr') :
    Inv fr → Inv fr' := by
```

This statement is genuinely IR-agnostic: the invariant is an arbitrary predicate on EVM frames,
and every edge type is owned by BytecodeLayer.

### 3. Recorder transitions

The coupling is seeded from a successful top-level recording by
[the entry theorem](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L178):

```lean
theorem recorderCoupled_entry {params : CallParams} {log : RunLog} {fr₀ : Frame}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀) :
    RecorderCoupled log fr₀ log.gas log.calls log.creates := by
```

The ordinary-step API distinguishes recorded GAS from all other ordinary steps. The GAS face is
[stated here](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L194):

```lean
theorem recorderCoupled_step_gas {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {g : Word} {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr (g :: gS) cS dS)
    (hgas : isGasOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS cS dS
    ∧ g = UInt256.ofUInt64 exec.gasAvailable := by
```

CALL and CREATE descents consume exactly one event while leaving the gas suffix unchanged.
The stronger [CREATE extraction theorem](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L642) shows
the modeling seam explicitly:

```lean
theorem recorderCoupled_create_extract {log : RunLog} {createFr : Frame}
    {cp : CreateParams} {pending : PendingCreate}
    {gS : List Word} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log createFr gS cS (rec :: dS))
    (hstep : stepFrame createFr = .needsCreate cp pending)
    (hresolve : CreateResolves createFr) :
    ∃ (childRes : FrameResult) (resumeFr : Frame),
        CreateReturns createFr resumeFr
      ∧ rec = { result := childRes.toCreateResult, pending := pending }
      ∧ resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr
      ∧ RecorderCoupled log resumeFr gS cS dS := by
```

The [CREATE-resolution predicate](../../EVM/BytecodeLayer/Exec/Invariants.lean#L272) assumes only
that any child result actually produced by the EVM drive can be delivered successfully to some
resumed parent. This is a real EVM seam: create resumption is exception-valued, unlike CALL
resumption. It does not mention or quantify over an IR execution.

At a halt, the generic theory closes the replay and all streams. The two projections needed by the
adapter are [the suffix theorem](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L992) and
[the observable theorem](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L1000):

```lean
theorem recorderCoupled_halted_suffixes_nil {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h) :
    gS = [] ∧ cS = [] ∧ dS = [] := by

theorem recorderCoupled_halted_observable {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h) :
    log.observable = endFrame fr h :=
```

### 4. Lir instantiation

The retained boundary predicate is deliberately still indexed by a Lir program and its lowered
bytecode. Its complete [definition](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L547)
is:

```lean
def AtReachableBoundaryVJ (prog : Lir.Program) (fr : Frame) : Prop :=
  AtReachableBoundary prog fr ∧ fr.validJumps = validJumpDests (Lir.lower prog) 0
```

The C2 change replaces a duplicated induction with the generic driver after supplying the three
Lir-specific edge proofs. The resulting
[adapter theorem](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L689) is:

```lean
theorem atReachableBoundaryVJ_of_runs {prog : Lir.Program}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    {fr fr' : Frame} (hr : Runs fr fr') :
    AtReachableBoundaryVJ prog fr → AtReachableBoundaryVJ prog fr' := by
```

That adapter is minimal in the important sense: all source-language content is confined to the
predicate and its three edge-preservation obligations; the recursion over arbitrary cyclic run
paths is reusable.

The semantic walk combines this generic coupling with Lir correspondence in
[the local invariant](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean#L302):

```lean
structure DriveCorrLog (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (st : IRState) (fr : Frame) (L : Label)
    (gasSuffix : List Word) (callSuffix : List CallRecord) (createSuffix : List CreateRecord) :
    Prop where
  /-- The `Corr` boundary at the block-entry cursor `(L, 0)` (phantom `obs` pinned to 0). -/
  corr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L 0
  /-- The non-exception clean-halt scope from this boundary on. -/
  cleanHalts : CleanHaltsNonException fr
  /-- The reached label is present (R8 threads it; seeded from `ClosedCFG.entry_present`). -/
  present : ∃ b, blockAt prog L = some b
  /-- The self account is present (seeded by the flagship's `hself`; preserved by
  `stepPreservesSelf` / `callPreservesSelf_modGuards`). -/
  selfPresent : SelfPresent fr
  /-- The frame executes at the self address (rfl-preserved along the walk). -/
  addrPin : fr.exec.executionEnv.address = self
  /-- The frame is a call frame (rfl-preserved along the walk). -/
  kindPin : ∃ cp, fr.kind = .call cp
  /-- The §2 recorder-restart coupling at the un-consumed suffixes. -/
  coupled : RecorderCoupled log fr gasSuffix callSuffix createSuffix
```

## Flagship surface

The entire flagship file is unchanged in the C2 commit range. The three frozen statements remain
[plain conformance](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221),
[exact stream consumption](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269),
and [gas-free conformance](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304):

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

C2 introduces no new flagship hypothesis and no new premise from which a conclusion could be
smuggled. The generic replay-fuel existential remains internal to the derived coupling carrier.
The only notable generic seam in the extracted API is successful CREATE resumption, already part
of the established EVM modellability assumptions.

## Results taxonomy and dependency path

- **Headlines:** the three unchanged flagship statements above. C2 changes their dependency
  location, not their specification.

- **Reusable mainline:** the generic run-invariant fold, recorder entry, GAS/SLOAD/ordinary-step
  preservation, CALL/CREATE descent, soft-failure consumption, event extraction, and halt
  projections in [the new engine](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L17).

- **Private bricks:** accumulator append transport, recorder framing over a nonempty pending stack,
  opcode-gate disjointness, and the combined halted invariant. These support the public API and are
  not alternate specifications.

- **IR adapters:** the strengthened boundary predicate and its edge proofs, the materialisation
  fold, term ties, call/create dispatch and realisation, and the coupled producer retained in
  [Lir machinery](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L547).

- **Examples/demos:** none were added or moved by C2.

- **Proof smells:** six plain `decide` calls in
  [opcode-gate disjointness](../../EVM/BytecodeLayer/Exec/CyclicSim.lean#L163) decide equality of
  concrete opcode constructors; they are small and feed the mainline, but are not large-term
  computation. There is no heartbeat increase, native evaluation, bit-vector decision procedure,
  hardcoded execution witness, or new axiom in the extracted module.

The dependency path is: successful recorder run → generic coupling at entry → event-specific
coupling transitions → Lir materialisation/statement/terminator adapters → coupled Lir producer →
the three flagships. Independently, the Lir boundary edge facts instantiate the generic run fold;
their resulting boundary witness travels with the same producer. Halt projections close both the
observable equality and exact leftover-stream result.

## Recommendations

1. Keep the current generic run-fold/Lir-predicate split. Re-index the predicate itself only with
   the assembler geometry, where lowered-bytecode and valid-jump ownership can actually move.
2. When the CALL/CREATE consumer interface changes, reconsider whether the dispatch splits still
   belong in the Lir adapter; their present exact-stack shapes encode current lowering policy.
