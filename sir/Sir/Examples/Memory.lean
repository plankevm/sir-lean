import Sir.Spec.Observation
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

private theorem fold_set_get? {α : Type} (xs : List α) (start j : Nat) (dest : Array α)
    (hbound : start + xs.length ≤ dest.size) :
    ((xs.zipIdx start).foldl (fun a x => a.setIfInBounds x.2 x.1) dest)[j]? =
      if start ≤ j ∧ j < start + xs.length then xs[j - start]? else dest[j]? := by
  induction xs generalizing start dest with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons] at hbound
      rw [List.zipIdx_cons, List.foldl_cons,
        ih (start + 1) (dest.setIfInBounds start x) (by simp only [Array.size_setIfInBounds]; omega)]
      by_cases heq : start = j
      · subst j
        simp [show start < dest.size by omega]
      · by_cases hle : start ≤ j
        · have hnext : start + 1 ≤ j := by omega
          simp only [List.length_cons]
          by_cases hrange : j < start + 1 + xs.length
          · rw [if_pos ⟨hnext, hrange⟩, if_pos ⟨hle, by omega⟩]
            rw [show j - start = (j - (start + 1)) + 1 by omega]
            rfl
          · rw [if_neg (by simp [hrange]), if_neg (by intro h; apply hrange; omega)]
            simp [heq]
        · have hnext : ¬start + 1 ≤ j := by omega
          simp [heq, hle, hnext]

private theorem fold_set_size {α : Type} (xs : List (α × Nat)) (dest : Array α) :
    (xs.foldl (fun a x => a.setIfInBounds x.2 x.1) dest).size = dest.size := by
  induction xs generalizing dest with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem fold_set_zipIdx_eq {α : Type} (source dest : Array α)
    (hsize : dest.size = source.size) :
    source.toList.zipIdx.foldl (fun a x => a.setIfInBounds x.2 x.1) dest = source := by
  apply Array.ext
  · rw [fold_set_size, hsize]
  · intro i hi₁ hi₂
    have hget := fold_set_get? source.toList 0 i dest (by simp [hsize])
    simp [hi₂] at hget
    simpa only [Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂,
      Option.some.injEq] using hget


private def singletonMemory (alloc : Allocation) (data : Array UInt8) : MemoryState :=
  { provisioned := #[{ alloc with bytes := ⟨data⟩ }] }

private theorem writeByte_singleton (alloc : Allocation) (data : Array UInt8)
    (index : Nat) (byte : UInt8) :
    (singletonMemory alloc data).writeByte (alloc.start + index) byte =
      singletonMemory alloc (data.setIfInBounds index byte) := by
  have hc :
      alloc.start ≤ alloc.start + index ∧ alloc.start + index < alloc.start + data.size ↔
        index < data.size := by omega
  simp [singletonMemory, MemoryState.writeByte, Allocation.writeByte,
    Allocation.start, Allocation.endExclusive, Allocation.size]
  intro hle
  rw [Array.setIfInBounds_eq_of_size_le hle]

private theorem writeBytes_singleton (alloc : Allocation) (bytes : ByteArray)
    (hsize : alloc.bytes.size = bytes.size) :
    (MemoryState.empty.push alloc).writeBytes alloc.offset bytes =
      singletonMemory alloc bytes.data := by
  unfold MemoryState.writeBytes MemoryState.empty MemoryState.push
  change bytes.toList.zipIdx.foldl _ (singletonMemory alloc alloc.bytes.data) = _
  rw [List.foldl_hom (singletonMemory alloc)
    (g₁ := fun data x => data.setIfInBounds x.2 x.1)]
  · rw [toList_eq_data_toList]
    rw [fold_set_zipIdx_eq bytes.data alloc.bytes.data (by simpa using hsize)]
  · intro data x
    exact writeByte_singleton alloc data x.2 x.1

private theorem readBytes_singleton (alloc : Allocation) (bytes assumed : ByteArray)
    (hsize : assumed.size = bytes.size) :
    (singletonMemory alloc bytes.data).readBytes alloc.offset assumed = bytes := by
  unfold MemoryState.readBytes
  have hround : bytes.toList.toByteArray = bytes := by
    apply ByteArray.ext
    rw [List.data_toByteArray, BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList]
  conv_rhs => rw [← hround]
  apply congrArg List.toByteArray
  apply List.ext_getElem
  · simpa [BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList] using hsize
  · intro i hout hbytes
    have hi : i < bytes.size := by
      simpa [BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList] using hbytes
    simp [MemoryState.readByte?, singletonMemory, Allocation.readByte?, Allocation.start,
      Allocation.endExclusive, Allocation.size,
      BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList, ByteArray.get?, hi]
    rfl

private theorem read_written_word (alloc : Allocation)
    (hsize : alloc.size = 32) (assumed : Vector UInt8 32) :
    ((MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray).readBytes
      alloc.offset ⟨assumed.toArray⟩ = (42 : Word).toByteArray := by
  rw [writeBytes_singleton]
  · apply readBytes_singleton
    change assumed.toArray.size = (42 : Word).toByteArray.size
    rw [assumed.size_toArray, toByteArray_size]
  · simpa [BytecodeLayer.Hoare.MemAlgebra.toByteArray_size] using hsize

private def stmtControl (index : Nat) : MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .statement index }

private def termControl : MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .terminator }

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
    (hstep : Generic.GenericStep localOperandFrame (sirDecoder initializedLoad) sirMemoryPolicy ctx
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
    Generic.Operation.Admissible, sirMemoryPolicy, Locals.empty,
    locals1, locals2, locals3, locals5, Locals.lookup, Locals.lookup?, Locals.assign,
    StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
    bindValues_empty, bindValues_singleton, read_written_word,
    fromByteArray_toByteArray, ofNat_toNat]
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
    (hsteps : Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) sirMemoryPolicy ctx
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
    (hsteps : Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) sirMemoryPolicy ctx
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
    (hrun : initializedLoad.RunsFunction ctx entryFunction { world := world } #[] trace state)
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
    (hrun : Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder initializedLoad) sirMemoryPolicy ctx
      entryFunction { world := world } #[] trace globals .halted) :
    trace = [] ∧ globals.world = world.storeStorage ctx.self 42 42 := by
  cases hrun with
  | halted hentry hsteps hhalt =>
      rename_i initial exit
      have hinitial : initial = (initializedState0 world).toGenericState := Option.some.inj
        (hentry.symm.trans (by simp [sirEntry_eq, initialized_entry]))
      subst initial
      obtain ⟨exitGlobals, exitLocals, exitControl⟩ := exit
      change Generic.GenericSteps localOperandFrame (sirDecoder initializedLoad) sirMemoryPolicy ctx
        (initializedState0 world).toGenericState trace
        ({ globals := exitGlobals, locals := exitLocals, control := exitControl } : MachineState).toGenericState
        at hsteps
      rcases initialized_steps hsteps with ⟨htrace, hstate⟩
      refine ⟨htrace, ?_⟩
      change exitControl = .halted at hhalt
      cases hstate <;> simp [initializedState6, stmtControl, termControl] at hhalt ⊢


private def zeroAlloc (offset : Word) : Allocation :=
  { offset, bytes := ByteArray.empty }

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

private theorem zero_steps (ctx : CallContext) (world : World) (offset : Word) :
    Generic.GenericSteps localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
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
  have step01 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
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
  have hvalid : (zeroState1 world).globals.memory.IsValidNewAlloc (zeroAlloc offset) := by
    constructor
    · change offset.toBitVec.toNat ≤ 2 ^ 256
      exact offset.toBitVec.isLt.le
    · simp [zeroState1, MemoryState.empty]
  have hsize : (zeroAlloc offset).size = (0 : Word).toNat := by
    change 0 = (0 : Word).toNat
    decide
  have step12 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
      (zeroState1 world).toGenericState [] (zeroState2 world offset).toGenericState := by
    apply step_mallocUninit (program := zeroSizeStore) (ctx := ctx)
      (result := xVar) (size := sizeVar)
      (by simp [zeroSizeStore, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, zeroState1, stmtControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchSize ⟨0, rfl, ⟨hvalid, hsize⟩, hvalid, hsize⟩
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
  have step23 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
      (zeroState2 world offset).toGenericState [] (zeroState3 ctx world offset).toGenericState := by
    apply step_sstore (program := zeroSizeStore) (ctx := ctx)
      (key := xVar) (value := xVar)
      (by simp [zeroSizeStore, Program.decodeStmt, Program.block?, Program.function?,
        Function.block?, BasicBlock.absoluteToPosition, zeroState2, stmtControl, termControl])
    simp only [decodeSirStatement, Generic.Instruction.Fires]
    exact fires_of hfetchOffset (by trivial)
      (Generic.Operation.execute_sstore_ok ctx offset offset (zeroState2 world offset).globals)
      hstoreEmpty
  have step34 : Generic.GenericStep localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
      (zeroState3 ctx world offset).toGenericState [] (zeroState4 ctx world offset).toGenericState :=
    step_terminator (terminator := .halt)
      (by simp [zeroSizeStore, Program.terminatorAt, Program.block?, Program.function?,
        Function.block?, zeroState3, termControl])
      (by simp [eval_terminator, zeroState3, zeroState4, pure, Except.pure])
  exact .tail (.tail (.tail (.tail .refl step01) step12) step23) step34

private theorem zero_eval (ctx : CallContext) (world : World) (offset : Word) :
    Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder zeroSizeStore) sirMemoryPolicy ctx
      entryFunction { world := world } #[] [] (zeroState4 ctx world offset).globals .halted :=
  EvalFn.halted (zero_entry world) (zero_steps ctx world offset) rfl

private def zeroContext : CallContext :=
  { self := 0, caller := 0, value := 0, calldata := ByteArray.empty, isStatic := false }

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

theorem initializedLoad_deterministic : initializedLoad.Deterministic := by
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

theorem zeroSizeStore_not_deterministic : ¬ zeroSizeStore.Deterministic := by
  intro hdet
  have eval₁ : EvalFn zeroSizeStore zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 1).globals .halted :=
    zero_eval zeroContext default 1
  have eval₂ : EvalFn zeroSizeStore zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 2).globals .halted :=
    zero_eval zeroContext default 2
  have heq := (hdet zeroContext (default : World)).1 []
    (.halt ((default : World).storeStorage zeroContext.self 1 1))
    (.halt ((default : World).storeStorage zeroContext.self 2 2))
    ⟨(zeroState4 zeroContext default 1).globals, eval₁, rfl⟩
    ⟨(zeroState4 zeroContext default 2).globals, eval₂, rfl⟩
  exact zero_worlds_differ (ObservableOutcome.halt.inj heq)

end Sir.Examples
