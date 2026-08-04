import Sir.Spec.Observation
import Sir.Theorems
import Sir.Proofs.Memory
import Sir.Proofs.Progress
import Sir.Proofs.Steps
import BytecodeLayer.Hoare.MemAlgebra
import BytecodeLayer.Semantics.Maps

open BytecodeLayer.Hoare.MemAlgebra
  (fromByteArray_toByteArray ofNat_toNat toByteArray_size toList_eq_data_toList)
namespace Sir.Examples

private abbrev sizeVar : VarId := ⟨0⟩
private abbrev xVar : VarId := ⟨1⟩
private abbrev valueVar : VarId := ⟨2⟩
private abbrev zVar : VarId := ⟨3⟩

private abbrev entryBlock : BlockId := ⟨0⟩
private abbrev entryFunction : FunctionId := ⟨0⟩

def initializedLoad : Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[]
        statements := #[
          .assign sizeVar (.constant 32),
          .mallocUninit xVar sizeVar,
          .assign valueVar (.constant 42),
          .mstore32 xVar valueVar,
          .mload32 zVar xVar,
          .sstore zVar zVar]
        terminator := .halt
        outputs := #[]}]
      entry := entryBlock }]
    initEntry := entryFunction
    mainEntry := none }

def zeroSizeStore : Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[]
        statements := #[
          .assign sizeVar (.constant 0),
          .mallocUninit xVar sizeVar,
          .sstore xVar xVar]
        terminator := .halt
        outputs := #[]}]
      entry := entryBlock }]
    initEntry := entryFunction
    mainEntry := none }

def bareLoad : Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[]
        statements := #[
          .assign xVar (.constant 0),
          .mload32 zVar xVar,
          .sstore zVar zVar]
        terminator := .halt
        outputs := #[]}]
      entry := entryBlock }]
    initEntry := entryFunction
    mainEntry := none }

private theorem read_written_word (m : MemoryState) (offset : Word) (w : Word) :
    ((m.writeBytes offset w.toByteArray).readBytes offset 32) = w.toByteArray := by
  have h := m.readBytes_writeBytes offset w.toByteArray
  rwa [toByteArray_size] at h

private def stmtControl (index : Nat) : MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .statement index }

private def termControl : MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .terminator }

private def initializedAlloc : Allocation :=
  { offset := 0, size := 32 }

private theorem initialized_inBounds (alloc : Allocation) (hsize : alloc.size = 32) :
    (MemoryState.empty.push alloc).InBounds alloc.offset.toNat 32 := by
  refine ⟨alloc, by simp [MemoryState.empty, MemoryState.push], ?_⟩
  exact ⟨Nat.le_refl _, by simp [Allocation.endExclusive, Allocation.start, hsize]⟩

private def locals1 : Locals := Locals.empty.assign sizeVar 32
private def locals2 (alloc : Allocation) : Locals := locals1.assign xVar alloc.offset
private def locals3 (alloc : Allocation) : Locals := (locals2 alloc).assign valueVar 42
private def locals5 (alloc : Allocation) : Locals := (locals3 alloc).assign zVar 42

private def initializedState0 (world : World) : MachineState :=
  { globals := { world }, control := stmtControl 0 }

private def initializedState1 (world : World) : MachineState :=
  { globals := { world }, locals := locals1, control := stmtControl 1 }

private def initializedState2 (world : World) (alloc : Allocation) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push alloc }
    locals := locals2 alloc
    control := stmtControl 2 }

private def initializedState3 (world : World) (alloc : Allocation) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push alloc }
    locals := locals3 alloc
    control := stmtControl 3 }

private def initializedState4 (world : World) (alloc : Allocation) : MachineState :=
  { globals :=
      { world
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    locals := locals3 alloc
    control := stmtControl 4 }

private def initializedState5 (world : World) (alloc : Allocation) : MachineState :=
  { globals :=
      { world
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    locals := locals5 alloc
    control := stmtControl 5 }

private def initializedState6 (ctx : CallContext) (world : World) (alloc : Allocation) : MachineState :=
  { globals :=
      { world := world.storeStorage ctx.self 42 42
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    locals := locals5 alloc
    control := termControl }

private def initializedState7 (ctx : CallContext) (world : World) (alloc : Allocation) : MachineState :=
  { initializedState6 ctx world alloc with control := .halted }

private inductive InitializedReachable (ctx : CallContext) (world : World) : MachineState → Prop where
  | state0 : InitializedReachable ctx world (initializedState0 world)
  | state1 : InitializedReachable ctx world (initializedState1 world)
  | state2 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState2 world alloc)
  | state3 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState3 world alloc)
  | state4 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState4 world alloc)
  | state5 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState5 world alloc)
  | state6 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState6 ctx world alloc)
  | state7 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState7 ctx world alloc)

@[simp]
private theorem bindValues_empty (locals : Locals) :
    Locals.bindValues locals #[] #[] = .ok locals := by
  simp [Locals.bindValues, bind, Except.bind, pure, Except.pure]

private theorem bindValues_singleton (locals : Locals) (var : VarId) (value : Word) :
    Locals.bindValues locals #[var] #[value] = .ok (locals.assign var value) := by
  simp [Locals.bindValues, bind, Except.bind, pure, Except.pure]

set_option linter.unusedSimpArgs false in
private theorem initialized_step_closed {ctx : CallContext} {world : World}
    {state : MachineState} {final : Generic.GenericState localOperandFrame} {trace : Trace}
    (hstate : InitializedReachable ctx world state)
    (hstep : Generic.GenericStep localOperandFrame (sirDecoder initializedLoad) Generic.MemoryPolicy.permissive ctx
      state.toGenericState trace final) :
    trace = [] ∧ InitializedReachable ctx world
      { globals := final.globals, locals := final.environment, control := final.control } := by
  cases hstate <;> cases hstep
  all_goals try { exact (firesHalt_false (ctx := ctx) (by assumption)).elim }
  all_goals simp_all [sirDecoder, sirDecode, sirControl, initializedLoad,
    Program.decodeStmt, Program.terminatorAt, Program.block?, Program.function?,
    Function.block?, BasicBlock.absoluteToPosition, decodeSirStatement, decodeExpression,
    initializedState0, initializedState1, initializedState2, initializedState3,
    initializedState4, initializedState5, initializedState6, initializedState7,
    stmtControl, termControl, MachineState.toGenericState,
    eval_terminator, pure, Except.pure]
  all_goals first
    | obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := ‹(_ ∧ _ ∧ _) ∧ _›
    | skip
  all_goals first
    | cases ‹Generic.OperandFrame.Fires _ _ _ _ _ _ _ _ _ _ _›
    | skip
  all_goals simp_all [initializedState0, initializedState1, initializedState2,
    initializedState3, initializedState4, initializedState5, initializedState6,
    initializedState7, stmtControl, termControl, localOperandFrame, Generic.Operation.execute,
    Generic.Operation.Admissible, Generic.MemoryPolicy.permissive, Locals.empty,
    locals1, locals2, locals3, locals5, Locals.lookup, Locals.lookup?, Locals.assign,
    StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
    bindValues_empty, bindValues_singleton, read_written_word,
    fromByteArray_toByteArray, ofNat_toNat]
  case state3.operation.next =>
    rename_i alloc hsize env' globals' operands results oracle hfetch hstore hexecute
    subst operands
    simp [initialized_inBounds alloc hsize] at hexecute
    obtain ⟨rfl, rfl, rfl⟩ := hexecute
    simp [bindValues_empty] at hstore
    subst env'
    exact ⟨rfl, InitializedReachable.state4 alloc hsize⟩
  all_goals first
    | obtain ⟨size, hoperand, hvalid, hsize⟩ := ‹∃ _, _›
    | skip
  all_goals try simp_all [Generic.Operation.execute, read_written_word,
    fromByteArray_toByteArray, ofNat_toNat]
  all_goals first
    | obtain ⟨rfl, rfl, rfl, rfl⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _ ∧ _ = _›
    | obtain ⟨rfl, rfl, rfl⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _›
    | skip
  all_goals try simp_all [Generic.Operation.execute, localOperandFrame,
    Locals.empty, locals1, locals2, locals3, locals5, Locals.lookup,
    Locals.lookup?, Locals.assign, bindValues_empty, bindValues_singleton,
    read_written_word, fromByteArray_toByteArray, ofNat_toNat]
  all_goals subst_vars
  all_goals try simp_all [Generic.Operation.execute, read_written_word,
    fromByteArray_toByteArray, ofNat_toNat]
  all_goals first
    | obtain ⟨rfl, rfl, rfl⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _›
    | skip
  all_goals subst_vars
  all_goals try simp_all [bindValues_empty, bindValues_singleton, locals1, locals2,
    locals3, locals5, Locals.assign]
  all_goals subst_vars
  all_goals first
    | exact InitializedReachable.state1
    | exact InitializedReachable.state2 _ (by assumption)
    | exact InitializedReachable.state3 _ (by assumption)
    | exact InitializedReachable.state4 _ (by assumption)
    | exact InitializedReachable.state5 _ (by assumption)
    | exact InitializedReachable.state6 _ (by assumption)
    | exact InitializedReachable.state7 _ (by assumption)

private theorem initialized_steps_from {ctx : CallContext} {world : World}
    {start final : MachineState} {trace : Trace}
    (hstart : InitializedReachable ctx world start)
    (hsteps : Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) Generic.MemoryPolicy.permissive ctx
      start.toGenericState trace final.toGenericState) :
    trace = [] ∧ InitializedReachable ctx world final := by
  apply Steps.inductionOn
    (motive := fun state trace final _ =>
      InitializedReachable ctx world state →
        trace = [] ∧ InitializedReachable ctx world final)
    (fun _ hstate => ⟨rfl, hstate⟩)
    (fun steps next ih hstate => by
      rcases ih hstate with ⟨rfl, hmiddle⟩
      rcases initialized_step_closed hmiddle next with ⟨rfl, hfinal⟩
      exact ⟨rfl, hfinal⟩)
    hsteps hstart

private theorem initialized_steps {ctx : CallContext} {world : World}
    {trace : Trace} {state : MachineState}
    (hsteps : Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) Generic.MemoryPolicy.permissive ctx
      (initializedState0 world).toGenericState trace state.toGenericState) :
    trace = [] ∧ InitializedReachable ctx world state :=
  initialized_steps_from .state0 hsteps

private theorem initialized_entry (world : World) :
    initializedLoad.callState? entryFunction { world := world } #[] =
      some (initializedState0 world) := by
  apply Program.callState?_eq_some_iff.mpr
  refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
  simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
    Array.toList_zip]
  rfl

private theorem initialized_no_next_event {ctx : CallContext} {world : World}
    {trace history rest : Trace} {event : Event} {state : MachineState}
    (hrun : initializedLoad.RunsFunction Generic.MemoryPolicy.permissive ctx entryFunction { world := world } #[] trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  have : initial = initializedState0 world := Option.some.inj
    (hentry.symm.trans (initialized_entry world))
  subst initial
  have hnil := (initialized_steps hsteps).1
  rw [htrace] at hnil
  have := congrArg List.length hnil
  simp at this

private theorem initialized_halted_world {ctx : CallContext} {world : World}
    {trace : Trace} {globals : Globals}
    (hrun : Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder initializedLoad) Generic.MemoryPolicy.permissive ctx
      entryFunction { world := world } #[] trace globals .halted) :
    trace = [] ∧ globals.world = world.storeStorage ctx.self 42 42 := by
  cases hrun with
  | halted hentry hsteps hhalt =>
      rename_i initial exit
      have hinitial : initial = (initializedState0 world).toGenericState := Option.some.inj
        (hentry.symm.trans (by simp [sirEntry_eq, initialized_entry]))
      subst initial
      obtain ⟨exitGlobals, exitLocals, exitControl⟩ := exit
      change Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) Generic.MemoryPolicy.permissive ctx
        (initializedState0 world).toGenericState trace
        ({ globals := exitGlobals, locals := exitLocals, control := exitControl } : MachineState).toGenericState
        at hsteps
      rcases initialized_steps hsteps with ⟨htrace, hstate⟩
      refine ⟨htrace, ?_⟩
      change exitControl = .halted at hhalt
      cases hstate <;> simp [initializedState6, stmtControl, termControl] at hhalt ⊢


private def zeroAlloc (offset : Word) : Allocation :=
  { offset, size := 0 }

private theorem zeroAlloc_valid (offset : Word) :
    MemoryState.empty.IsValidNewAlloc (zeroAlloc offset) := by
  constructor
  · change offset.toBitVec.toNat ≤ 2 ^ 256
    exact offset.toBitVec.isLt.le
  · simp [MemoryState.empty]

private def zeroState0 (world : World) : MachineState :=
  { globals := { world }, control := stmtControl 0 }

private def zeroState1 (world : World) : MachineState :=
  { globals := { world }, locals := Locals.empty.assign sizeVar 0, control := stmtControl 1 }

private def zeroState2 (world : World) (offset : Word) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push (zeroAlloc offset) }
    locals := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 2 }

private def zeroState2Eval (world : World) (offset : Word) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push (zeroAlloc offset) }
    locals := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 1 }

private def zeroState3 (ctx : CallContext) (world : World) (offset : Word) : MachineState :=
  { zeroState2 world offset with
    globals := { (zeroState2 world offset).globals with
      world := world.storeStorage ctx.self offset offset }
    control := termControl }

private def zeroState4 (ctx : CallContext) (world : World) (offset : Word) : MachineState :=
  { zeroState3 ctx world offset with control := .halted }

private theorem zero_entry (world : World) :
    zeroSizeStore.callState? entryFunction { world := world } #[] = some (zeroState0 world) := by
  apply Program.callState?_eq_some_iff.mpr
  refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
  simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
    Array.toList_zip]
  rfl

private theorem zero_steps (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World) (offset : Word)
    (hallows : policy.Allows MemoryState.empty 0 (zeroAlloc offset)) :
    Generic.GenericSteps localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      (zeroState0 world).toGenericState [] (zeroState4 ctx world offset).toGenericState := by
  have hfetchEmpty : (#[] : Array VarId).mapM ((zeroState0 world).locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreSize : Locals.bindValues (zeroState0 world).locals #[sizeVar] #[0] =
      .ok (zeroState1 world).locals := by
    simp only [zeroState0, zeroState1, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have step01 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      (zeroState0 world).toGenericState [] (zeroState1 world).toGenericState := by
    apply step_assign (program := zeroSizeStore) (ctx := ctx)
      (result := sizeVar) (expr := .constant 0)
      (by simp [zeroSizeStore, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, zeroState0, stmtControl])
    simp only [decodeExpression, Generic.Instruction.Fires]
    exact fires_of hfetchEmpty (by trivial)
      (Generic.Operation.execute_constant_ok ctx 0 (zeroState0 world).globals #[]) hstoreSize
  have hfetchSize : #[sizeVar].mapM ((zeroState1 world).locals.lookup ·) = .ok #[0] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreOffset : Locals.bindValues (zeroState1 world).locals #[xVar] #[offset] =
      .ok (zeroState2 world offset).locals := by
    simp only [zeroState1, zeroState2, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hvalid : (zeroState1 world).globals.memory.IsValidNewAlloc (zeroAlloc offset) :=
    zeroAlloc_valid offset
  have hsize : (zeroAlloc offset).size = (0 : Word).toNat := by
    change 0 = (0 : Word).toNat
    decide
  have step12 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      (zeroState1 world).toGenericState [] (zeroState2 world offset).toGenericState := by
    apply step_mallocUninit (program := zeroSizeStore) (ctx := ctx)
      (result := xVar) (size := sizeVar)
      (by simp [zeroSizeStore, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, zeroState1, stmtControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchSize ⟨0, rfl, hallows, hvalid, hsize⟩
      (Generic.Operation.execute_malloc_ok ctx (zeroAlloc offset)
        (zeroState1 world).globals 0 hsize) hstoreOffset
  have hfetchOffset : #[xVar, xVar].mapM ((zeroState2 world offset).locals.lookup ·) =
      .ok #[offset, offset] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreEmpty : Locals.bindValues (zeroState2 world offset).locals #[] #[] =
      .ok (zeroState2 world offset).locals := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have step23 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      (zeroState2 world offset).toGenericState [] (zeroState3 ctx world offset).toGenericState := by
    apply step_sstore (program := zeroSizeStore) (ctx := ctx)
      (key := xVar) (value := xVar)
      (by simp [zeroSizeStore, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, zeroState2, stmtControl, termControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchOffset (by trivial)
      (Generic.Operation.execute_sstore_ok ctx offset offset (zeroState2 world offset).globals)
      hstoreEmpty
  have step34 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      (zeroState3 ctx world offset).toGenericState [] (zeroState4 ctx world offset).toGenericState :=
    step_terminator (terminator := .halt)
      (by simp [zeroSizeStore, Program.terminatorAt, Program.block?, Program.function?,
        Function.block?, zeroState3, termControl])
      (by simp [eval_terminator, zeroState3, zeroState4, pure, Except.pure])
  exact .tail (.tail (.tail (.tail .refl step01) step12) step23) step34

private theorem zero_eval (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World) (offset : Word)
    (hallows : policy.Allows MemoryState.empty 0 (zeroAlloc offset)) :
    Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder zeroSizeStore) policy ctx
      entryFunction { world := world } #[] [] (zeroState4 ctx world offset).globals .halted :=
  EvalFn.halted (zero_entry world) (zero_steps policy ctx world offset hallows) rfl

def zeroContext : CallContext :=
  { self := 0, caller := 0, value := 0, calldata := ByteArray.empty, isStatic := false }

private theorem permissive_allows_zero (offset : Word) :
    Generic.MemoryPolicy.permissive.Allows MemoryState.empty 0 (zeroAlloc offset) :=
  ⟨zeroAlloc_valid offset, rfl⟩

private theorem bump_allows_zero :
    Generic.MemoryPolicy.bump.Allows MemoryState.empty 0 (zeroAlloc 0) := by
  constructor
  · decide
  · rfl

private theorem zero_worlds_differ :
    (default : World).storeStorage zeroContext.self 1 1 ≠
      (default : World).storeStorage zeroContext.self 2 2 := by
  intro heq
  have hread := congrArg (fun world => world.loadStorage zeroContext.self 1) heq
  dsimp only at hread
  have hleft :
      ((default : World).storeStorage zeroContext.self 1 1).loadStorage
        zeroContext.self 1 = 1 := by decide
  have hright :
      ((default : World).storeStorage zeroContext.self 2 2).loadStorage
        zeroContext.self 1 = 0 := by decide
  rw [hleft, hright] at hread
  exact (by decide : (1 : Word) ≠ 0) hread

private theorem initialized_valid_alloc :
    MemoryState.empty.IsValidNewAlloc initializedAlloc := by decide

private theorem permissive_allows_initialized :
    Generic.MemoryPolicy.permissive.Allows MemoryState.empty (32 : Word).toNat
      initializedAlloc :=
  ⟨by decide, by decide⟩

private theorem bump_allows_initialized :
    Generic.MemoryPolicy.bump.Allows MemoryState.empty (32 : Word).toNat initializedAlloc :=
  ⟨by decide, rfl⟩

private theorem initialized_step01 (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World) :
    SmallStep initializedLoad policy ctx (initializedState0 world) []
      (initializedState1 world) := by
  have hfetch : (#[] : Array VarId).mapM ((initializedState0 world).locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstore : Locals.bindValues (initializedState0 world).locals #[sizeVar] #[32] =
      .ok (initializedState1 world).locals := by
    simpa [initializedState0, initializedState1, locals1] using
      bindValues_singleton Locals.empty sizeVar 32
  apply step_assign (program := initializedLoad) (ctx := ctx)
    (result := sizeVar) (expr := .constant 32)
    (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
      Function.block?, BasicBlock.absoluteToPosition, initializedState0, stmtControl])
  simp only [decodeExpression, Generic.Instruction.Fires]
  exact fires_of hfetch (by trivial)
    (Generic.Operation.execute_constant_ok ctx 32 (initializedState0 world).globals #[]) hstore

private theorem initialized_step12 (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World)
    (hallows : policy.Allows MemoryState.empty (32 : Word).toNat initializedAlloc) :
    SmallStep initializedLoad policy ctx (initializedState1 world) []
      (initializedState2 world initializedAlloc) := by
  have hfetch : #[sizeVar].mapM ((initializedState1 world).locals.lookup ·) = .ok #[32] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hvalid : (initializedState1 world).globals.memory.IsValidNewAlloc initializedAlloc :=
    initialized_valid_alloc
  have hsize : initializedAlloc.size = (32 : Word).toNat := by decide
  have hstore :
      Locals.bindValues (initializedState1 world).locals #[xVar] #[initializedAlloc.offset] =
        .ok (initializedState2 world initializedAlloc).locals := by
    simpa [initializedState1, initializedState2, locals1, locals2] using
      bindValues_singleton locals1 xVar initializedAlloc.offset
  apply step_mallocUninit (program := initializedLoad) (ctx := ctx)
    (result := xVar) (size := sizeVar)
    (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
      Function.block?, BasicBlock.absoluteToPosition, initializedState1, stmtControl])
  simp only [decodeSirStatement, Generic.Instruction.Fires]
  exact fires_of hfetch ⟨32, rfl, hallows, hvalid, hsize⟩
    (Generic.Operation.execute_malloc_ok ctx initializedAlloc
      (initializedState1 world).globals 32 hsize) hstore

private theorem initialized_step23 (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World) (alloc : Allocation) :
    SmallStep initializedLoad policy ctx (initializedState2 world alloc) []
      (initializedState3 world alloc) := by
  have hfetch : (#[] : Array VarId).mapM ((initializedState2 world alloc).locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstore : Locals.bindValues (initializedState2 world alloc).locals #[valueVar] #[42] =
      .ok (initializedState3 world alloc).locals := by
    simpa [initializedState2, initializedState3, locals2, locals3] using
      bindValues_singleton (locals2 alloc) valueVar 42
  apply step_assign (program := initializedLoad) (ctx := ctx)
    (result := valueVar) (expr := .constant 42)
    (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
      Function.block?, BasicBlock.absoluteToPosition, initializedState2, stmtControl])
  simp only [decodeExpression, Generic.Instruction.Fires]
  exact fires_of hfetch (by trivial)
    (Generic.Operation.execute_constant_ok ctx 42
      (initializedState2 world alloc).globals #[]) hstore

private theorem initialized_step34 (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World) (alloc : Allocation) (hsize : alloc.size = 32) :
    SmallStep initializedLoad policy ctx (initializedState3 world alloc) []
      (initializedState4 world alloc) := by
  have hfetch : #[xVar, valueVar].mapM ((initializedState3 world alloc).locals.lookup ·) =
      .ok #[alloc.offset, 42] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstore : Locals.bindValues (initializedState3 world alloc).locals #[] #[] =
      .ok (initializedState3 world alloc).locals := bindValues_empty _
  have hin : (initializedState3 world alloc).globals.memory.InBounds alloc.offset.toNat 32 :=
    initialized_inBounds alloc hsize
  apply step_mstore32 (program := initializedLoad) (ctx := ctx)
    (offset := xVar) (value := valueVar)
    (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
      Function.block?, BasicBlock.absoluteToPosition, initializedState3, stmtControl])
  simp only [decodeSirStatement, Generic.Instruction.Fires]
  exact fires_of hfetch (by trivial)
    (Generic.Operation.execute_mstore32_ok ctx (initializedState3 world alloc).globals
      alloc.offset 42 hin) hstore

private theorem initialized_runs_to_allocation (policy : Generic.MemoryPolicy)
    (ctx : CallContext) (world : World) :
    initializedLoad.RunsFunction policy ctx initializedLoad.initEntry { world } #[] []
      (initializedState1 world) :=
  ⟨initializedState0 world, initialized_entry world, .tail .refl
    (initialized_step01 policy ctx world)⟩

private theorem initialized_runs_to_store (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (world : World)
    (hallows : policy.Allows MemoryState.empty (32 : Word).toNat initializedAlloc) :
    initializedLoad.RunsFunction policy ctx initializedLoad.initEntry { world } #[] []
      (initializedState3 world initializedAlloc) :=
  ⟨initializedState0 world, initialized_entry world,
    .tail (.tail (.tail .refl (initialized_step01 policy ctx world))
      (initialized_step12 policy ctx world hallows))
      (initialized_step23 policy ctx world initializedAlloc)⟩

private theorem initialized_decode_allocation (world : World) :
    initializedLoad.decodeStmt (initializedState1 world).control =
      some (stmtControl 2, .mallocUninit xVar sizeVar) := rfl

private theorem initialized_decode_store (world : World) (alloc : Allocation) :
    initializedLoad.decodeStmt (initializedState3 world alloc).control =
      some (stmtControl 4, .mstore32 xVar valueVar) := rfl

private theorem initialized_size_lookup (world : World) {size : VarId} {word : Word}
    (hsize : sizeVar = size) (hword : (initializedState1 world).locals.lookup size = .ok word) :
    word = 32 := by
  subst hsize
  rw [show (initializedState1 world).locals.lookup sizeVar = .ok (32 : Word) from rfl] at hword
  injection hword with hword
  exact hword.symm

private theorem initialized_offset_lookup (world : World) (alloc : Allocation)
    {offset : VarId} {word : Word} (hoffset : xVar = offset)
    (hword : (initializedState3 world alloc).locals.lookup offset = .ok word) :
    word = alloc.offset := by
  subst hoffset
  rw [show (initializedState3 world alloc).locals.lookup xVar = .ok alloc.offset from rfl]
    at hword
  injection hword with hword
  exact hword.symm

private theorem initialized_allocation_space (world : World) :
    ∀ nextControl result size word,
      initializedLoad.decodeStmt (initializedState1 world).control =
          some (nextControl, .mallocUninit result size) →
      (initializedState1 world).locals.lookup size = .ok word →
      (initializedState1 world).globals.memory.watermark + word.toNat ≤ Evm.UInt256.size := by
  intro nextControl result size word hdecode hword
  rw [initialized_decode_allocation] at hdecode
  simp only [Option.some.injEq, Prod.mk.injEq, Stmt.mallocUninit.injEq] at hdecode
  rw [initialized_size_lookup world hdecode.2.2 hword]
  exact bump_allows_initialized.1

private theorem initialized_allocation_fresh (world : World) :
    ∀ nextControl result size word,
      initializedLoad.decodeStmt (initializedState1 world).control =
          some (nextControl, .mallocUninit result size) →
      (initializedState1 world).locals.lookup size = .ok word →
      ∃ allocation,
        Generic.MemoryPolicy.permissive.Allows (initializedState1 world).globals.memory
          word.toNat allocation ∧
        (initializedState1 world).globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = word.toNat := by
  intro nextControl result size word hdecode hword
  rw [initialized_decode_allocation] at hdecode
  simp only [Option.some.injEq, Prod.mk.injEq, Stmt.mallocUninit.injEq] at hdecode
  rw [initialized_size_lookup world hdecode.2.2 hword]
  exact ⟨initializedAlloc, permissive_allows_initialized, initialized_valid_alloc, by decide⟩

private theorem initialized_allocation_no_store (world : World) :
    ∀ nextControl offset value word,
      initializedLoad.decodeStmt (initializedState1 world).control =
          some (nextControl, .mstore32 offset value) →
      (initializedState1 world).locals.lookup offset = .ok word →
      (initializedState1 world).globals.memory.InBounds word.toNat 32 := by
  intro nextControl offset value word hdecode _
  rw [initialized_decode_allocation] at hdecode
  simp at hdecode

private theorem initialized_store_no_allocation (world : World) (alloc : Allocation) :
    ∀ nextControl result size word,
      initializedLoad.decodeStmt (initializedState3 world alloc).control =
          some (nextControl, .mallocUninit result size) →
      (initializedState3 world alloc).locals.lookup size = .ok word →
      (initializedState3 world alloc).globals.memory.watermark + word.toNat ≤
        Evm.UInt256.size := by
  intro nextControl result size word hdecode _
  rw [initialized_decode_store] at hdecode
  simp at hdecode

private theorem initialized_store_inBounds (world : World) (alloc : Allocation)
    (hsize : alloc.size = 32) :
    ∀ nextControl offset value word,
      initializedLoad.decodeStmt (initializedState3 world alloc).control =
          some (nextControl, .mstore32 offset value) →
      (initializedState3 world alloc).locals.lookup offset = .ok word →
      (initializedState3 world alloc).globals.memory.InBounds word.toNat 32 := by
  intro nextControl offset value word hdecode hword
  rw [initialized_decode_store] at hdecode
  simp only [Option.some.injEq, Prod.mk.injEq, Stmt.mstore32.injEq] at hdecode
  rw [initialized_offset_lookup world alloc hdecode.2.1 hword]
  exact initialized_inBounds alloc hsize

private theorem initialized_nonIcall {control : MachineControl}
    {next : MachineControl} {statement : Stmt}
    (hdecode : initializedLoad.decodeStmt control = some (next, statement))
    (hstatement : ∀ callee callArgs destinations,
      statement ≠ .icall callee callArgs destinations) :
    (∃ nextControl statement,
      initializedLoad.decodeStmt control = some (nextControl, statement) ∧
      ∀ callee callArgs destinations, statement ≠ .icall callee callArgs destinations) ∨
    ∃ terminator, initializedLoad.terminatorAt control = some terminator :=
  Or.inl ⟨next, statement, hdecode, hstatement⟩

theorem initializedLoad_wellFormed : initializedLoad.WellFormed := by
  constructor
  · rintro callee args dests hstatement
    simp [Program.HasStmt, Function.HasStmt, initializedLoad] at hstatement
  · intro fn hfn block hblock hterm
    simp [initializedLoad] at hfn
    subst hfn
    simp at hblock
    subst hblock
    simp at hterm
  · intro function hcycle
    have absurd {caller callee : FunctionId}
        (h : Relation.TransGen initializedLoad.callEdge caller callee) : False := by
      have noEdge (caller callee : FunctionId) : ¬ initializedLoad.callEdge caller callee := by
        rcases caller with ⟨_ | caller⟩ <;>
          simp [Program.callEdge, Program.function?, Function.HasStmt, initializedLoad]
      induction h with
      | single edge => exact noEdge _ _ edge
      | tail _ edge _ => exact noEdge _ _ edge
    exact absurd hcycle
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro entry hentry
      simp [initializedLoad] at hentry
  · intro fn hfn block hblock target htarget
    simp [initializedLoad] at hfn
    subst hfn
    simp at hblock
    subst hblock
    simp [Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [initializedLoad] at hfn
    subst hfn
    simp at hblock
    subst hblock
    constructor
    · intro index statement hstatement
      rcases index with (_ | _ | _ | _ | _ | _ | index) <;> simp at hstatement
      all_goals subst statement
      all_goals simp [BasicBlock.variablesDefinedBefore, Expr.variablesRead,
        Stmt.variablesRead, Stmt.variablesDefined, sizeVar, xVar, valueVar, zVar]
    · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead]

theorem initializedLoad_store_inBounds :
    (MemoryState.empty.push { offset := 0, size := 32 }).InBounds 0 32 := by
  decide

theorem initializedLoad_progress_at_allocation_bump (ctx : CallContext) (world : World) :
    ∃ state next result size,
      initializedLoad.RunsFunction Generic.MemoryPolicy.bump ctx initializedLoad.initEntry
        { world } #[] [] state ∧
      initializedLoad.decodeStmt state.control = some (next, .mallocUninit result size) ∧
      ∃ trace state',
        SmallStep initializedLoad Generic.MemoryPolicy.bump ctx state trace state' :=
  ⟨initializedState1 world, stmtControl 2, xVar, sizeVar,
    initialized_runs_to_allocation Generic.MemoryPolicy.bump ctx world,
    initialized_decode_allocation world,
    initializedLoad_wellFormed.progress_reachable_nonIcall_bump
      (initialized_runs_to_allocation Generic.MemoryPolicy.bump ctx world)
      (initialized_nonIcall (initialized_decode_allocation world) (by simp))
      (initialized_allocation_space world)
      (initialized_allocation_no_store world)⟩

theorem initializedLoad_progress_at_store_bump (ctx : CallContext) (world : World) :
    ∃ state next offset value,
      initializedLoad.RunsFunction Generic.MemoryPolicy.bump ctx initializedLoad.initEntry
        { world } #[] [] state ∧
      initializedLoad.decodeStmt state.control = some (next, .mstore32 offset value) ∧
      ∃ trace state',
        SmallStep initializedLoad Generic.MemoryPolicy.bump ctx state trace state' :=
  ⟨initializedState3 world initializedAlloc, stmtControl 4, xVar, valueVar,
    initialized_runs_to_store Generic.MemoryPolicy.bump ctx world bump_allows_initialized,
    initialized_decode_store world initializedAlloc,
    initializedLoad_wellFormed.progress_reachable_nonIcall_bump
      (initialized_runs_to_store Generic.MemoryPolicy.bump ctx world bump_allows_initialized)
      (initialized_nonIcall (initialized_decode_store world initializedAlloc) (by simp))
      (initialized_store_no_allocation world initializedAlloc)
      (initialized_store_inBounds world initializedAlloc rfl)⟩

theorem initializedLoad_progress_at_allocation_permissive (ctx : CallContext) (world : World) :
    ∃ state next result size,
      initializedLoad.RunsFunction Generic.MemoryPolicy.permissive ctx
        initializedLoad.initEntry { world } #[] [] state ∧
      initializedLoad.decodeStmt state.control = some (next, .mallocUninit result size) ∧
      ∃ trace state',
        SmallStep initializedLoad Generic.MemoryPolicy.permissive ctx state trace state' :=
  ⟨initializedState1 world, stmtControl 2, xVar, sizeVar,
    initialized_runs_to_allocation Generic.MemoryPolicy.permissive ctx world,
    initialized_decode_allocation world,
    initializedLoad_wellFormed.progress_reachable_nonIcall
      (initialized_runs_to_allocation Generic.MemoryPolicy.permissive ctx world)
      (initialized_nonIcall (initialized_decode_allocation world) (by simp))
      (initialized_allocation_fresh world)
      (initialized_allocation_no_store world)⟩

theorem initializedLoad_reaches_successful_store :
    ∃ ctx function world initial before after,
      initializedLoad.callState? function { world } #[] = some initial ∧
      Steps initializedLoad Generic.MemoryPolicy.permissive ctx initial [] before ∧
      before.globals.memory = MemoryState.empty.push { offset := 0, size := 32 } ∧
      before.globals.memory.InBounds 0 32 ∧
      SmallStep initializedLoad Generic.MemoryPolicy.permissive ctx before [] after ∧
      after.globals.memory =
        (MemoryState.empty.push { offset := 0, size := 32 }).writeBytes 0
          (42 : Word).toByteArray := by
  refine ⟨zeroContext, entryFunction, default, initializedState0 default,
    initializedState3 default initializedAlloc, initializedState4 default initializedAlloc,
    initialized_entry default, ?_, rfl, ?_,
    initialized_step34 Generic.MemoryPolicy.permissive zeroContext default initializedAlloc rfl,
    rfl⟩
  · exact .tail (.tail (.tail .refl
      (initialized_step01 Generic.MemoryPolicy.permissive zeroContext default))
      (initialized_step12 Generic.MemoryPolicy.permissive zeroContext default
        permissive_allows_initialized))
      (initialized_step23 Generic.MemoryPolicy.permissive zeroContext default initializedAlloc)
  · simpa [initializedState3, initializedAlloc] using initializedLoad_store_inBounds

theorem initializedLoad_deterministic : initializedLoad.Deterministic Generic.MemoryPolicy.permissive := by
  intro ctx world
  constructor
  · intro history outcome₁ outcome₂ h₁ h₂
    cases outcome₁ <;> cases outcome₂
    · rfl
    · rcases h₁ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₂ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₂ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rename_i world₁ world₂
      rcases h₁ with ⟨state₁, hrun₁, hworld₁⟩
      rcases h₂ with ⟨state₂, hrun₂, hworld₂⟩
      have fixed₁ := (initialized_halted_world hrun₁).2
      have fixed₂ := (initialized_halted_world hrun₂).2
      have : world₁ = world₂ :=
        hworld₁.symm.trans (fixed₁.trans (fixed₂.symm.trans hworld₂))
      exact congrArg ObservableOutcome.halt this
  · intro entry hentry
    simp [initializedLoad] at hentry

theorem bareLoad_allocationFree : bareLoad.AllocationFree := by
  rintro statement hstatement
  simp [Program.HasStmt, Function.HasStmt, bareLoad] at hstatement
  rcases hstatement with rfl | rfl | rfl <;> simp [Stmt.isAllocation]

theorem bareLoad_deterministic (policy : Generic.MemoryPolicy) :
    bareLoad.Deterministic policy :=
  Program.deterministic_of_allocationDeterministic (.inr bareLoad_allocationFree)

theorem zeroSizeStore_deterministic_bump :
    zeroSizeStore.Deterministic Generic.MemoryPolicy.bump :=
  Program.deterministic_of_allocationDeterministic
    (.inl Generic.MemoryPolicy.bump_deterministic)

theorem zeroSizeStore_runs_bump (world : World) :
    EvalFn zeroSizeStore Generic.MemoryPolicy.bump zeroContext entryFunction
      { world } #[] []
      { world := world.storeStorage zeroContext.self 0 0,
        memory := MemoryState.empty.push { offset := 0, size := 0 } }
      .halted := by
  simpa [zeroState4, zeroState3, zeroState2, zeroAlloc] using
    zero_eval Generic.MemoryPolicy.bump zeroContext world 0 bump_allows_zero

theorem zeroSizeStore_not_deterministic : ¬ zeroSizeStore.Deterministic Generic.MemoryPolicy.permissive := by
  intro hdet
  have eval₁ : EvalFn zeroSizeStore Generic.MemoryPolicy.permissive zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 1).globals .halted :=
    zero_eval Generic.MemoryPolicy.permissive zeroContext default 1
      (permissive_allows_zero 1)
  have eval₂ : EvalFn zeroSizeStore Generic.MemoryPolicy.permissive zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 2).globals .halted :=
    zero_eval Generic.MemoryPolicy.permissive zeroContext default 2
      (permissive_allows_zero 2)
  have heq := (hdet zeroContext (default : World)).1 []
    (.halt ((default : World).storeStorage zeroContext.self 1 1))
    (.halt ((default : World).storeStorage zeroContext.self 2 2))
    ⟨(zeroState4 zeroContext default 1).globals, eval₁, rfl⟩
    ⟨(zeroState4 zeroContext default 2).globals, eval₂, rfl⟩
  exact zero_worlds_differ (ObservableOutcome.halt.inj heq)

end Sir.Examples
