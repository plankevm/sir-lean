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

theorem initializedLoad_store_inBounds :
    (MemoryState.empty.push { offset := 0, size := 32 }).InBounds 0 32 := by
  decide

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
  have hfetchEmpty : (#[] : Array VarId).mapM ((initializedState0 default).locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreSize :
      Locals.bindValues (initializedState0 default).locals #[sizeVar] #[32] =
        .ok (initializedState1 default).locals := by
    simpa [initializedState0, initializedState1, locals1] using
      bindValues_singleton Locals.empty sizeVar 32
  have step01 :
      SmallStep initializedLoad Generic.MemoryPolicy.permissive zeroContext (initializedState0 default) []
        (initializedState1 default) := by
    apply step_assign (program := initializedLoad) (ctx := zeroContext)
      (result := sizeVar) (expr := .constant 32)
      (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, initializedState0, stmtControl])
    simp only [decodeExpression, Generic.Instruction.Fires]
    exact fires_of hfetchEmpty (by trivial)
      (Generic.Operation.execute_constant_ok zeroContext 32
        (initializedState0 default).globals #[]) hstoreSize
  have hfetchSize :
      #[sizeVar].mapM ((initializedState1 default).locals.lookup ·) = .ok #[32] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hvalid :
      (initializedState1 default).globals.memory.IsValidNewAlloc initializedAlloc := by
    decide
  have hsize : initializedAlloc.size = (32 : Word).toNat := by
    decide
  have hstoreOffset :
      Locals.bindValues (initializedState1 default).locals #[xVar] #[initializedAlloc.offset] =
        .ok (initializedState2 default initializedAlloc).locals := by
    simpa [initializedState1, initializedState2, locals1, locals2] using
      bindValues_singleton locals1 xVar initializedAlloc.offset
  have step12 :
      SmallStep initializedLoad Generic.MemoryPolicy.permissive zeroContext (initializedState1 default) []
        (initializedState2 default initializedAlloc) := by
    apply step_mallocUninit (program := initializedLoad) (ctx := zeroContext)
      (result := xVar) (size := sizeVar)
      (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, initializedState1, stmtControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchSize ⟨32, rfl, ⟨hvalid, hsize⟩, hvalid, hsize⟩
      (Generic.Operation.execute_malloc_ok zeroContext initializedAlloc
        (initializedState1 default).globals 32 hsize) hstoreOffset
  have hfetchEmpty₂ :
      (#[] : Array VarId).mapM ((initializedState2 default initializedAlloc).locals.lookup ·) =
        .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreValue :
      Locals.bindValues (initializedState2 default initializedAlloc).locals #[valueVar] #[42] =
        .ok (initializedState3 default initializedAlloc).locals := by
    simpa [initializedState2, initializedState3, locals2, locals3] using
      bindValues_singleton (locals2 initializedAlloc) valueVar 42
  have step23 :
      SmallStep initializedLoad Generic.MemoryPolicy.permissive zeroContext (initializedState2 default initializedAlloc) []
        (initializedState3 default initializedAlloc) := by
    apply step_assign (program := initializedLoad) (ctx := zeroContext)
      (result := valueVar) (expr := .constant 42)
      (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, initializedState2, stmtControl])
    simp only [decodeExpression, Generic.Instruction.Fires]
    exact fires_of hfetchEmpty₂ (by trivial)
      (Generic.Operation.execute_constant_ok zeroContext 42
        (initializedState2 default initializedAlloc).globals #[]) hstoreValue
  have hfetchStore :
      #[xVar, valueVar].mapM
        ((initializedState3 default initializedAlloc).locals.lookup ·) =
          .ok #[initializedAlloc.offset, 42] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreEmpty :
      Locals.bindValues (initializedState3 default initializedAlloc).locals #[] #[] =
        .ok (initializedState3 default initializedAlloc).locals :=
    bindValues_empty _
  have hin :
      (initializedState3 default initializedAlloc).globals.memory.InBounds
        initializedAlloc.offset.toNat 32 := by
    exact initialized_inBounds initializedAlloc rfl
  have step34 :
      SmallStep initializedLoad Generic.MemoryPolicy.permissive zeroContext (initializedState3 default initializedAlloc) []
        (initializedState4 default initializedAlloc) := by
    apply step_mstore32 (program := initializedLoad) (ctx := zeroContext)
      (offset := xVar) (value := valueVar)
      (by simp [initializedLoad, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, initializedState3, stmtControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchStore (by trivial)
      (Generic.Operation.execute_mstore32_ok zeroContext
        (initializedState3 default initializedAlloc).globals initializedAlloc.offset 42 hin)
      hstoreEmpty
  refine ⟨zeroContext, entryFunction, default, initializedState0 default,
    initializedState3 default initializedAlloc, initializedState4 default initializedAlloc,
    initialized_entry default, ?_, ?_, ?_, step34, ?_⟩
  · exact .tail (.tail (.tail .refl step01) step12) step23
  · rfl
  · simpa [initializedState3, initializedAlloc] using initializedLoad_store_inBounds
  · rfl

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
