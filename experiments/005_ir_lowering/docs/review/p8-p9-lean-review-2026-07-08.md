# Experiment 005 P8/P9 Lean Review

## TL;DR

The P8/P9 cleanup leaves a much cleaner public statement surface: source programs are checked by [`IRWellFormed`](../../LirLean/Spec/WellFormed.lean#L731), [`codeFits`](../../LirLean/Spec/WellFormed.lean#L650), and [`stackFits`](../../LirLean/Spec/WellFormed.lean#L698), then the old internal [`WellLowered`](../../LirLean/Realisability/Surface.lean#L151) adapter is rebuilt by [`wellLowered_of_IRWellFormed`](../../LirLean/Realisability/RealisabilitySpec.lean#L124). The intended headline is still [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L250). After R11 Chunk 0, the plain and gasfree shells call the coupled producer directly; the producer itself remains WIP, and [`lower_conforms_exact`](../../LirLean/Realisability/RealisabilitySpec.lean#L304) still waits for the exact `RunFromAll` producer sibling.

The proven default-cone infrastructure is substantial: fold-based lowering through [`matCache`](../../LirLean/Spec/Lowering.lean#L213), decode/layout anchors through [`flatBytes`](../../LirLean/Decode/DecodeLower.lean#L45), [`pcOf`](../../LirLean/Decode/Layout.lean#L227), and [`termOf`](../../LirLean/Decode/DecodeAnchors.lean#L156), jump-validity and reachable-boundary facts through [`block_offset_validJump`](../../LirLean/Decode/JumpValid.lean#L226) and [`decode_reachable_boundary_loweringOp`](../../LirLean/Decode/BoundaryReach.lean#L163), plus the fold value channel [`MatRunsC`](../../LirLean/Materialise/MatFoldChannel.lean#L782). [`sim_cfg`](../../LirLean/Assembly/LowerConforms.lean#L938) is proven whole-CFG simulation over supplied per-block ties, but [`LowerConforms.lean`](../../LirLean/Assembly/LowerConforms.lean#L1103) explicitly says it no longer contains a discharged conformance headline.

Verification status: I did not run `lake build`; targeted grep found no live `sorry`/`admit`/`native_decide`/`bv_decide`/`axiom` in the reviewed default-cone Spec/Decode/Materialise/Assembly/Sim files beyond prose comments and `set_option maxRecDepth`, while the non-default [`WIP`](../../lakefile.lean#L31) realisability library intentionally contains 20 `sorry` bodies across [`RealisabilitySpec.lean`](../../LirLean/Realisability/RealisabilitySpec.lean#L176), [`Machinery.lean`](../../LirLean/Realisability/Machinery.lean#L413), and [`Producer.lean`](../../LirLean/Realisability/Producer.lean#L467).

## Goal And Context

Experiment 005 is trying to state and eventually prove that running lowered EVM bytecode from a recorded top-level call induces a source-level IR run with the same observable result and self-storage world. After P8/P9, the reviewer-facing promise is not "here is a closed conformance theorem"; it is "the source specification surface is high-level, the lowering/materialisation/decode infrastructure is in place, and the remaining conformance gap is isolated in the WIP coupled producer."

The live target shape is documented in the current [`r11-plan-2026-07-08.md`](../planning/r11-plan-2026-07-08.md#L10), and the source matches its main warning: CREATE is already in the public statement shape, but the producer still does not fully thread a create suffix or statement tie ([plan warning](../planning/r11-plan-2026-07-08.md#L114)).

## Abstraction Stack

| Layer | Files | Role | Classification |
| --- | --- | --- | --- |
| Source IR and public checks | [`IR.lean`](../../LirLean/Spec/IR.lean#L75), [`Lowering.lean`](../../LirLean/Spec/Lowering.lean#L92), [`WellFormed.lean`](../../LirLean/Spec/WellFormed.lean#L731), [`Conformance.lean`](../../LirLean/Spec/Conformance.lean#L41), [`Seams.lean`](../../LirLean/Spec/Seams.lean#L119), [`Semantics.lean`](../../LirLean/Spec/Semantics.lean#L1), [`Recorder.lean`](../../LirLean/Spec/Recorder.lean#L1), [`CallEntry.lean`](../../LirLean/Spec/CallEntry.lean#L1) | Defines the source grammar, byte emission policy, public well-formedness/budgets, observable vocabulary, runtime seams, and stream/recorder vocabulary. | Headline surface and support |
| Budget derivation | [`BudgetDerivations.lean`](../../LirLean/Spec/BudgetDerivations.lean#L17) | Rebuilds per-cursor pc and stack obligations from the two scalar budgets. | Supporting brick |
| Decode/layout | [`LoweringLemmas.lean`](../../LirLean/Decode/LoweringLemmas.lean#L1), [`DecodeLower.lean`](../../LirLean/Decode/DecodeLower.lean#L45), [`Layout.lean`](../../LirLean/Decode/Layout.lean#L117), [`DecodeAnchors.lean`](../../LirLean/Decode/DecodeAnchors.lean#L156), [`SegAligned.lean`](../../LirLean/Decode/SegAligned.lean#L63), [`JumpValid.lean`](../../LirLean/Decode/JumpValid.lean#L226), [`BoundaryReach.lean`](../../LirLean/Decode/BoundaryReach.lean#L150) | Turns `lower prog` into indexable bytes, proves cursor anchors, instruction alignment, jump-destination validity, and reachable-boundary opcode allow-listing. | Supporting bricks |
| Value channel | [`MaterialiseGas.lean`](../../LirLean/Materialise/MaterialiseGas.lean#L92), [`MatFoldChannel.lean`](../../LirLean/Materialise/MatFoldChannel.lean#L373), [`MaterialiseCleanHalt.lean`](../../LirLean/Materialise/MaterialiseCleanHalt.lean#L71), [`MaterialiseRuns.lean`](../../LirLean/Materialise/MaterialiseRuns.lean#L217), [`StashTail.lean`](../../LirLean/Materialise/StashTail.lean#L157), [`DefsSound.lean`](../../LirLean/Materialise/DefsSound.lean#L127), [`MatDecLower.lean`](../../LirLean/Materialise/MatDecLower.lean#L110), [`CleanHaltExtract.lean`](../../LirLean/Materialise/CleanHaltExtract.lean#L1) | Replaces old fuel/materialise APIs with fold byte/charge caches, cache-keyed decode, endpoint run bundles, clean-halt gas derivation, memory spill readback, and stash-tail runs. | Supporting bricks; some retained legacy smells |
| Statement/terminator simulation | [`SimStmt.lean`](../../LirLean/Sim/SimStmt.lean#L102), [`SimStmts.lean`](../../LirLean/Sim/SimStmts.lean#L1), [`SimTerm.lean`](../../LirLean/Sim/SimTerm.lean#L1), [`LowerDecode.lean`](../../LirLean/Assembly/LowerDecode.lean#L112), [`LowerConforms.lean`](../../LirLean/Assembly/LowerConforms.lean#L938) | Consumes decode/value-channel facts to simulate statement lists, terminators, and whole CFGs under supplied ties. | Supporting infrastructure |
| Engine support | [`CleanHalt.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L62), plus reachable-frame machinery in [`Modellable.lean`](../../LirLean/Decode/Modellable.lean#L413), [`DriveRuns.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L1), [`DriveMono.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L1), [`Descent.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L1), [`StepWalk.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1), [`Charges.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L1), [`MemAlgebra.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L1), [`AccountMap.lean`](../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L1) | Supplies clean-halt propagation, modellability, frame-walk, gas, memory, and account-map support consumed by the WIP producer and default simulation bricks. | Supporting bricks |
| V2 realisability | [`Surface.lean`](../../LirLean/Realisability/Surface.lean#L151), [`Machinery.lean`](../../LirLean/Realisability/Machinery.lean#L392), [`Producer.lean`](../../LirLean/Realisability/Producer.lean#L74), [`RealisabilitySpec.lean`](../../LirLean/Realisability/RealisabilitySpec.lean#L250), [`Witness.lean`](../../LirLean/Realisability/Witness.lean#L38) | States the public WIP headline, the internal coupled invariant, open producer obligations, and concrete non-vacuity witness. | WIP headline, support, example |

Dependency shape: [`IRWellFormed`](../../LirLean/Spec/WellFormed.lean#L731) plus [`codeFits`](../../LirLean/Spec/WellFormed.lean#L650) and [`stackFits`](../../LirLean/Spec/WellFormed.lean#L698) feed [`wellLowered_of_IRWellFormed`](../../LirLean/Realisability/RealisabilitySpec.lean#L124); that internal adapter feeds reshaped ties in [`StmtTies'`](../../LirLean/Realisability/Surface.lean#L351) and [`TermTies'`](../../LirLean/Realisability/Surface.lean#L457); the intended producer [`runFrom_of_driveCorrLog`](../../LirLean/Realisability/Producer.lean#L1440) should package an IR [`RunFrom`](../../LirLean/Spec/Semantics.lean#L1) plus terminal observable equation; [`conforms_of_worldeq`](../../LirLean/Realisability/RealisabilitySpec.lean#L203) then turns that into [`Conforms`](../../LirLean/Spec/Conformance.lean#L70).

## Specs That Matter

The public source grammar is a CFG/register IR over EVM words. [`Expr`](../../LirLean/Spec/IR.lean#L75), [`Stmt`](../../LirLean/Spec/IR.lean#L91), [`Term`](../../LirLean/Spec/IR.lean#L107), and [`Program`](../../LirLean/Spec/IR.lean#L127) are the surface a reviewer should read before any bytecode theorem:

```lean
inductive Expr where
  | imm   (w : Word)
  | tmp   (t : Tmp)
  | add   (a b : Tmp)
  | lt    (a b : Tmp)
  | sload (key : Tmp)
  | gas
deriving DecidableEq, Repr

inductive Stmt where
  | assign (t : Tmp) (e : Expr)
  | sstore (key value : Tmp)
  | call   (cs : CallSpec)
  | create (cs : CreateSpec)
deriving DecidableEq, Repr

inductive Term where
  | ret    (t : Tmp)
  | stop
  | jump   (dst : Label)
  | branch (cond : Tmp) (thenL elseL : Label)
deriving DecidableEq, Repr

structure Program where
  blocks : Array Block
  entry  : Label
deriving Repr
```

The lowering policy is now fold-based and total. [`defEnv`](../../LirLean/Spec/Lowering.lean#L137) records program-order definitions, [`defsOf`](../../LirLean/Spec/Lowering.lean#L152) is the first-find allocation view, and [`matCache`](../../LirLean/Spec/Lowering.lean#L213) is the byte cache used by [`emitStmt`](../../LirLean/Spec/Lowering.lean#L266), [`emitTerm`](../../LirLean/Spec/Lowering.lean#L303), and [`lower`](../../LirLean/Spec/Lowering.lean#L358):

```lean
inductive Loc where
  | remat (e : Expr)
  | slot  (n : Nat)
deriving DecidableEq, Repr

def defEnv (prog : Program) : List (Tmp × Loc) :=
  prog.blocks.toList.flatMap (fun b =>
    b.stmts.filterMap (fun
      | .assign t .gas       => some (t, Loc.slot (slotOf t))
      | .assign t (.sload _) => some (t, Loc.slot (slotOf t))
      | .assign t e          => some (t, locOfExpr e)
      | .call ⟨_, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | .create ⟨_, _, _, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | _                    => none))

def defsOf (prog : Program) : Alloc :=
  fun t => ((defEnv prog).find? (fun p => p.1 == t)).map (·.2)

def matCache (prog : Program) : Tmp → List UInt8 :=
  matFold (fun _ => emitImm 0) (defEnv prog)

def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)
```

The public well-formedness is not bytecode-shaped. [`RunDefinableG`](../../LirLean/Spec/WellFormed.lean#L68) supplies gas/call-aware definability, [`DefsConsistent`](../../LirLean/Spec/WellFormed.lean#L107) prevents shadowing mismatches between first-find allocation and emitted def-sites, [`DefEnvOrdered`](../../LirLean/Spec/WellFormed.lean#L265) replaces the deleted fuel/rank route, and [`IRWellFormed`](../../LirLean/Spec/WellFormed.lean#L731) bundles the source-side conditions:

```lean
def DefsConsistent (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat), blockAt prog L = some b →
    (∀ (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) →
      defsOf prog t = some (match e with
        | .gas => .slot (slotOf t)
        | .sload _ => .slot (slotOf t)
        | e' => locOfExpr e'))
    ∧ (∀ (cs : CallSpec) (t : Tmp), b.stmts[pc]? = some (.call cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))
    ∧ (∀ (cs : CreateSpec) (t : Tmp), b.stmts[pc]? = some (.create cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))

def DefEnvOrdered (prog : Program) : Prop :=
  ∀ (i : Nat) (t : Tmp) (e : Expr),
    (defEnv prog)[i]? = some (t, Loc.remat e) →
    ∀ t' : Tmp, usesInExpr t' e ≠ 0 →
      ∃ j, j < i ∧ ∃ loc : Loc, (defEnv prog)[j]? = some (t', loc)

def codeFits (prog : Program) : Prop := (flatBytes prog).length < 2 ^ 32

def stackFits (prog : Program) : Prop := maxChargeDepth prog ≤ 1024

structure IRWellFormed (prog : Program) : Prop where
  defineBeforeUse : RunDefinableG prog
  defsConsistent  : DefsConsistent prog
  entry0          : prog.entry.idx = 0
  cfgClosed       : CFGClosed prog
  defEnvOrdered   : DefEnvOrdered prog
  revalidates     : RevalidatesPerBlock prog
  slotAddr        : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b →
    (b.stmts[pc]? = some (.assign t .gas)
      ∨ ∃ k, b.stmts[pc]? = some (.assign t (.sload k))) →
    slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
```

The budget bridge is the P8/P9 public-to-internal adapter. [`pcBounds_of_codeFits`](../../LirLean/Spec/BudgetDerivations.lean#L285) derives the pc/offset obligations, [`stackBounds_of_stackFits`](../../LirLean/Spec/BudgetDerivations.lean#L377) derives [`StackRoomOK`](../../LirLean/Spec/WellFormed.lean#L704), and [`wellLowered_of_IRWellFormed`](../../LirLean/Realisability/RealisabilitySpec.lean#L124) packages them:

```lean
theorem wellLowered_of_IRWellFormed {prog : Program}
    (hwf : IRWellFormed prog) (hcode : codeFits prog) (hstk : stackFits prog) :
    WellLowered prog := by
```

The observable vocabulary is small and source-facing. [`entryState`](../../LirLean/Spec/Conformance.lean#L41) pins the IR entry world to the recipient account's storage lens, [`RunLog.clean`](../../LirLean/Spec/Conformance.lean#L58) excludes top-level creates and zero-gas reverts, [`Conforms`](../../LirLean/Spec/Conformance.lean#L70) compares both world and result, and [`NoGasReads`](../../LirLean/Spec/Conformance.lean#L78) is the gas-free static predicate:

```lean
def entryState (params : CallParams) : IRState :=
  { locals := fun _ => none
    world  := fun k => (params.accounts.find? params.recipient).option 0 (·.lookupStorage k) }

def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world
  ∧ O.result = (observe self log.observable).result

def NoGasReads (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ (pc : Nat) (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) → e ≠ .gas
```

The decode stack is reusable and generic over arbitrary lowered programs. [`flatBytes`](../../LirLean/Decode/DecodeLower.lean#L45) is the list model of the bytes, [`lower_eq_flatBytes`](../../LirLean/Decode/DecodeLower.lean#L59) connects it to the `ByteArray`, [`pcOf`](../../LirLean/Decode/Layout.lean#L227) and [`termOf`](../../LirLean/Decode/DecodeAnchors.lean#L156) are cursor offsets, and [`SegAlignedP`](../../LirLean/Decode/SegAligned.lean#L63) is the consolidated alignment tower:

```lean
def flatBytes (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let alloc := defsOf prog
  let labelOff := offsetTable cache alloc prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache alloc labelOff b)

theorem lower_eq_flatBytes (prog : Program) : lower prog = ⟨(flatBytes prog).toArray⟩ := by

def pcOf (prog : Program) (L : Label) (pc : Nat) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b =>
          ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length)).getD 0)

def termOf (prog : Program) (L : Label) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b => (b.stmts.flatMap (emitStmt cache alloc)).length)).getD 0)

inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hP : P (Evm.parseInstr byte))
      (hrest : SegAlignedP P rest) :
      SegAlignedP P (byte :: (imm ++ rest))
```

The CREATE-related decode cleanup is real in source: [`IsLoweringOp`](../../LirLean/Decode/SegAligned.lean#L205) includes CREATE and CREATE2, and [`segAlignedP_flatBytes`](../../LirLean/Decode/SegAligned.lean#L443) is unconditional:

```lean
def IsLoweringOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD
    ∨ op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP
    ∨ op = .JUMPI ∨ op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4
    ∨ op = .PUSH32 ∨ op = .CALL ∨ op = .RETURN
    ∨ op = .System .CREATE ∨ op = .System .CREATE2

theorem segAlignedP_flatBytes (prog : Program) :
    SegAlignedP IsLoweringOp (flatBytes prog) := by
```

The value channel's endpoint is [`MatRunsC`](../../LirLean/Materialise/MatFoldChannel.lean#L782), backed by [`chargeExpr`](../../LirLean/Materialise/MaterialiseGas.lean#L92), [`chargeCache`](../../LirLean/Materialise/MaterialiseGas.lean#L121), [`MatDecC`](../../LirLean/Materialise/MatFoldChannel.lean#L373), and [`materialise_runsC`](../../LirLean/Materialise/MatFoldChannel.lean#L812):

```lean
structure MatRunsC (prog : Program) (sloadChg : Tmp → ℕ) (e : Expr) (w : Word) (fr fr' : Frame) :
    Prop where
  runs       : Runs fr fr'
  stack      : fr'.exec.stack = fr.exec.stack.push w
  code       : fr'.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps : fr'.validJumps = fr.validJumps
  addr       : fr'.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod     : fr'.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts   : fr'.exec.accounts = fr.exec.accounts
  storage    : ∀ k, selfStorage fr' k = selfStorage fr k
  pc         : fr'.exec.pc = fr.exec.pc + UInt32.ofNat (matExpr (matCache prog) e).length
  gasCharge  : fr'.exec.gasAvailable
                 = subCharges fr.exec.gasAvailable (chargeExpr sloadChg (chargeCache prog sloadChg) e)
  gasToNat   : fr'.exec.gasAvailable.toNat
                 = fr.exec.gasAvailable.toNat
                     - (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum
  memBytes   : fr'.exec.toMachineState.memory = fr.exec.toMachineState.memory
  memActive  : fr.exec.toMachineState.activeWords.toNat
                 ≤ fr'.exec.toMachineState.activeWords.toNat
```

The consumer-facing gas wrapper is [`materialise_runsC_of_cleanHalt`](../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372), deriving the aggregate charge bound from [`CleanHaltsNonException`](../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L62):

```lean
def CleanHaltsNonException (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt ∧ HaltNonException halt

theorem materialise_runsC_of_cleanHalt {prog : Program} (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSound prog st)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hcs : CleanHaltsNonException fr)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024) :
    ∃ fr', MatRunsC prog sloadChg e w fr fr'
      ∧ (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat := by
```

The memory spill channel is the live replacement for the old gas/sload universals. [`SloadRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L297) and [`GasRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L318) remain exported but are explicitly retired; [`MemRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L366) is what [`Corr`](../../LirLean/Sim/SimStmt.lean#L102) carries:

```lean
def MemRealises (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.slot slot) → st.locals t = some v →
    (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.memory.size
    ∧ (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32
    ∧ slot + 63 < 2 ^ 64
    ∧ (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v
```

The assembly layer has a proven but deliberately abstract whole-CFG simulation. [`SimTermStep`](../../LirLean/Assembly/LowerConforms.lean#L101) and [`CallRealises`](../../LirLean/Assembly/LowerConforms.lean#L235) define the per-block tie interfaces; [`simStmtStep_block`](../../LirLean/Assembly/LowerConforms.lean#L337) builds statement simulation for non-create blocks; [`simTermStep_block`](../../LirLean/Assembly/LowerConforms.lean#L799) builds terminator simulation; [`sim_cfg`](../../LirLean/Assembly/LowerConforms.lean#L938) composes them:

```lean
theorem sim_cfg {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress}
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs self L b)
    {st : Lir.IRState} {T : Trace} {C : CallStream} {D : CreateStream}
    {L : Label} {O : Lir.Observable} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hcs : CleanHaltsNonException fr)
    (hrun : Lir.RunFrom prog st T C D L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world := by
```

The live WIP headline is exactly this statement shape:

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

This is a good theorem surface: it is observable, not opcode-mirroring. Its proof status is the issue, not its statement.

## Hypotheses And Modeling

[`IRWellFormed`](../../LirLean/Spec/WellFormed.lean#L731) is static/program-text oriented, but it contains semantically quantified [`RunDefinableG`](../../LirLean/Spec/WellFormed.lean#L68). This is intentional: gas and calls are supplied by streams/oracles, so definability is stated along [`RunStmts`](../../LirLean/Spec/Semantics.lean#L1) prefixes rather than as a false call-free predicate.

[`codeFits`](../../LirLean/Spec/WellFormed.lean#L650) is exactly `(flatBytes prog).length < 2^32`; [`stackFits`](../../LirLean/Spec/WellFormed.lean#L698) is a stack-depth budget over charge-list lengths, not a gas-sufficiency theorem. [`chargeCache_length_sloadChg_eq`](../../LirLean/Materialise/MaterialiseGas.lean#L209) is what lets [`stackBounds_of_stackFits`](../../LirLean/Spec/BudgetDerivations.lean#L377) use `sloadChg := fun _ => 0`.

[`RunLog.clean`](../../LirLean/Spec/Conformance.lean#L58) is a real scope cut. It accepts successful top-level calls and nonzero-gas reverts, but excludes `.create` observables and zero-gas reverts. [`PrecompileAssumptions`](../../LirLean/Spec/Seams.lean#L119) is the honest seam bundle for precompile presence, reachable [`CallsCode`](../../LirLean/Spec/Seams.lean#L124), and reachable [`CreateResolves`](../../LirLean/Decode/Modellable.lean#L413).

[`RecorderCoupled`](../../LirLean/Realisability/Surface.lean#L234) is the critical WIP invariant: it pins a boundary frame's restarted recorder future to the unconsumed gas/sload/call suffixes. It still pins the create channel to the full [`log.creates`](../../LirLean/Realisability/Surface.lean#L244), and [`StreamsAligned`](../../LirLean/Realisability/Producer.lean#L74) maps `D` to `createStreamOf log.creates self` at every boundary. That is enough for the current CALL-first skeleton, but not for arbitrary programs with create statements.

```lean
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) : Prop where
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] [] []
      = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix, log.creates)
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  sloadPrefix : ∃ pre, log.sloads = pre ++ sloadSuffix
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix

def StreamsAligned (self : AccountAddress) (log : RunLog)
    (gS : List Word) (cS : List CallRecord)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  T = gS ∧ C = callStreamOf cS self ∧ D = createStreamOf log.creates self
```

The intended producer is still open:

```lean
theorem runFrom_of_driveCorrLog {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account} {fr₀ : Frame}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∃ O : Observable,
      (∀ fr', Runs fr₀ fr' → CreateResolves fr')
      ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
          ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
          ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
      ∧ RunFrom prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O := by
```

## Results Taxonomy

**Headline / mainline.** [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L250), [`lower_conforms_exact`](../../LirLean/Realisability/RealisabilitySpec.lean#L304), and [`lower_conforms_gasfree`](../../LirLean/Realisability/RealisabilitySpec.lean#L343) are the real public targets. The plain and gasfree shells are now wired to [`runFrom_of_driveCorrLog`](../../LirLean/Realisability/Producer.lean#L1438); the producer body remains WIP, and the exact shell remains aligned to a future producer that returns `RunFromAll` directly.

**Supporting bricks.** The strong supporting results are [`wellLowered_of_IRWellFormed`](../../LirLean/Realisability/RealisabilitySpec.lean#L124), [`pcBounds_of_codeFits`](../../LirLean/Spec/BudgetDerivations.lean#L285), [`stackBounds_of_stackFits`](../../LirLean/Spec/BudgetDerivations.lean#L377), [`matCache_unfold`](../../LirLean/Spec/WellFormed.lean#L596), [`matCache_chargeCache_unfold`](../../LirLean/Materialise/MatFoldChannel.lean#L244), [`matDecC_of_lower`](../../LirLean/Materialise/MatFoldChannel.lean#L1306), [`matDecC_of_term`](../../LirLean/Materialise/MatFoldChannel.lean#L1328), [`block_offset_validJump`](../../LirLean/Decode/JumpValid.lean#L226), [`decode_reachable_boundary_loweringOp`](../../LirLean/Decode/BoundaryReach.lean#L163), [`sim_sstore_stmt_lowered`](../../LirLean/Assembly/LowerDecode.lean#L112), [`sim_assign_gas_lowered`](../../LirLean/Assembly/LowerDecode.lean#L705), [`sim_assign_sload_lowered`](../../LirLean/Assembly/LowerDecode.lean#L915), and [`sim_cfg`](../../LirLean/Assembly/LowerConforms.lean#L938).

**Examples / demos.** [`exProg`](../../LirLean/Realisability/Witness.lean#L38) exercises gas, sload, sstore, call, and a loop, but not create. Its static facts [`irWellFormed_exProg`](../../LirLean/Realisability/Witness.lean#L548), [`codeFits_exProg`](../../LirLean/Realisability/Witness.lean#L560), [`stackFits_exProg`](../../LirLean/Realisability/Witness.lean#L565), and [`wellLowered_exProg`](../../LirLean/Realisability/Witness.lean#L590) are useful non-vacuity anchors. [`exProg_nonvacuity`](../../LirLean/Realisability/RealisabilitySpec.lean#L406) is not closed independently; it depends on the WIP [`exProg_satisfies_hypotheses`](../../LirLean/Realisability/RealisabilitySpec.lean#L393) and [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L250).

```lean
def exProg : Program :=
  { blocks := #[
      { stmts := [
          .assign ⟨0⟩ (.imm 5),
          .assign ⟨1⟩ .gas,
          .assign ⟨2⟩ (.sload ⟨0⟩),
          .assign ⟨3⟩ (.imm 1),
          .sstore ⟨0⟩ ⟨3⟩,
          .assign ⟨4⟩ (.imm 0x100),
          .call { callee := ⟨4⟩, gasFwd := ⟨1⟩, resultTmp := some ⟨5⟩ } ],
        term := .jump ⟨1⟩ },
      { stmts := [
          .assign ⟨6⟩ .gas,
          .assign ⟨7⟩ (.imm 1000),
          .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ],
        term := .branch ⟨8⟩ ⟨2⟩ ⟨1⟩ },
      { stmts := [], term := .stop } ],
    entry := ⟨0⟩ }
```

**Smells / weak spots.** The repeated [`set_option maxRecDepth 8192`](../../LirLean/Assembly/LowerDecode.lean#L29) settings in [`LowerDecode.lean`](../../LirLean/Assembly/LowerDecode.lean#L67) and [`MatDecLower.lean`](../../LirLean/Materialise/MatDecLower.lean#L32), plus [`set_option maxRecDepth 8000`](../../LirLean/Realisability/Witness.lean#L557) in the witness, are proof-engineering smells. They do not change the spec surface, but they sit under load-bearing decode/witness proofs and suggest brittle arithmetic reductions.

The retained [`SloadRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L297) and [`GasRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L318) definitions are explicitly off-cone regression subjects. They should not be described as live assumptions of [`Corr`](../../LirLean/Sim/SimStmt.lean#L102), [`materialise_runsC`](../../LirLean/Materialise/MatFoldChannel.lean#L812), or any headline.

The current assembly builder is still create-free. [`Stmt.create`](../../LirLean/Spec/IR.lean#L100), [`emitStmt`](../../LirLean/Spec/Lowering.lean#L281), and [`IsLoweringOp`](../../LirLean/Decode/SegAligned.lean#L205) include CREATE/CREATE2, but [`StmtDefinableG`](../../LirLean/Spec/WellFormed.lean#L54) and [`StepScopedS`](../../LirLean/Spec/WellFormed.lean#L218) have create placeholders, and [`simStmtStep_block`](../../LirLean/Assembly/LowerConforms.lean#L425) excludes `.create` with [`hnocreate`](../../LirLean/Assembly/LowerConforms.lean#L429). A headline claiming arbitrary CREATE conformance would overstate the current proof.

[`SstoreRealises`](../../LirLean/Sim/SimStmt.lean#L317) remains a risk. The WIP header says its former free-forall shape is unsatisfiable ([`RealisabilitySpec.lean`](../../LirLean/Realisability/RealisabilitySpec.lean#L27)), but the current default statement simulation still exposes it through [`sim_sstore_stmt`](../../LirLean/Sim/SimStmt.lean#L347) and [`simStmtStep_block`](../../LirLean/Assembly/LowerConforms.lean#L410). The R11 producer must replace it pointwise at the concrete frame, not smuggle it back as a broad supplied tie.

## Discrepancies And Drift

1. Current source deleted the old no-CREATE-byte claim: [`SegAligned.lean`](../../LirLean/Decode/SegAligned.lean#L15) says the [`SegAlignedSafe`](../../LirLean/Decode/SegAligned.lean#L15) / [`NoCreateBytes`](../../LirLean/Decode/SegAligned.lean#L15) tower was deleted, and [`IsLoweringOp`](../../LirLean/Decode/SegAligned.lean#L205) includes CREATE/CREATE2. Live docs still mention the old tower, including [`docs/lirlean-dag-2026-07-04.md`](../lirlean-dag-2026-07-04.md#L150) and [`docs/fleet-2026-07-04/cluster-spec-decode.md`](../fleet-2026-07-04/cluster-spec-decode.md#L31).

2. Current signatures are multi-call/positional: [`Spec/Conformance.lean`](../../LirLean/Spec/Conformance.lean#L18), [`CallRealises`](../../LirLean/Assembly/LowerConforms.lean#L220), and the [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L244) docstring all say the single-call premise is gone. Stale source prose remains in [`Spec/Lowering.lean`](../../LirLean/Spec/Lowering.lean#L27) and [`Spec/IR.lean`](../../LirLean/Spec/IR.lean#L96).

3. [`Assembly/LowerConforms.lean`](../../LirLean/Assembly/LowerConforms.lean#L1111) correctly says this file no longer contains a discharged headline, but its stale line pointer names [`RealisabilitySpec.lean:206`](../../LirLean/Assembly/LowerConforms.lean#L1115); the current [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L250) starts at line 250.

4. [`DefsSound.lean`](../../LirLean/Materialise/DefsSound.lean#L31) still has header prose saying non-recomputable tmps are used at most once, while the actual [`WellFormed`](../../LirLean/Materialise/DefsSound.lean#L144) only restricts call-result tmps and later prose correctly says gas/sload are spilled and unrestricted ([`DefsSound.lean`](../../LirLean/Materialise/DefsSound.lean#L122)).

5. [`SimStmt.lean`](../../LirLean/Sim/SimStmt.lean#L42) still says "The three arms", but the file now has explicit spilled gas and spilled sload arms at [`sim_assign_gas`](../../LirLean/Sim/SimStmt.lean#L880) and [`sim_assign_sload`](../../LirLean/Sim/SimStmt.lean#L1030).

6. [`docs/exec/realisability-spec.md`](../exec/realisability-spec.md#L4) still names non-default `Nightly`, while the current WIP library is [`WIP`](../../lakefile.lean#L31); the same doc still discusses [`SingleCall`](../exec/realisability-spec.md#L99), which current source says was deleted in [`RealisabilitySpec.lean`](../../LirLean/Realisability/RealisabilitySpec.lean#L57).

## Open Questions

1. Is the reachable-frame [`CreateResolves`](../../LirLean/Decode/Modellable.lean#L413) field on [`PrecompileAssumptions`](../../LirLean/Spec/Seams.lean#L119) the final public seam shape, or should it move to a narrower companion bundle before R11 is closed?

2. Will the R11 producer land CREATE suffix/prefix threading before claiming plain [`lower_conforms`](../../LirLean/Realisability/RealisabilitySpec.lean#L250), or will the first closed theorem explicitly restrict to create-free programs? The source currently has CREATE in the grammar and headline streams, but the producer and assembly builder are not create-complete.

3. Should the retained retired definitions [`SloadRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L297) and [`GasRealises`](../../LirLean/Materialise/MaterialiseRuns.lean#L318) remain exported, or move to a clearly marked regression/witness module so future readers do not mistake them for live assumptions?

4. Once R11 is closed, should [`Assembly/LowerConforms.lean`](../../LirLean/Assembly/LowerConforms.lean#L1103) be further narrowed to simulation infrastructure only, with stale "call-free" headings and old line pointers removed in the same sweep?
