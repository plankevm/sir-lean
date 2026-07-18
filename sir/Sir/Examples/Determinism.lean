import Sir.Semantics.SmallStep
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

/-- Allocates a word, writes and reads `42`, then stores the result at its own key. -/
def initializedLoad : Program :=
  { blocks := #[{
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
    entry := entryBlock }

/-- A zero-size allocation can return any pointer, which is used as a storage key and value. -/
def zeroSizeStore : Program :=
  { blocks := #[{
      inputs := #[]
      statements := #[
        .assign sizeVar (.constant 0),
        .mallocUninit xVar sizeVar,
        .sstore xVar xVar]
      terminator := .halt
      outputs := #[]}]
    entry := entryBlock }

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
  .running { block := entryBlock, position := .statement index }

private def termControl : MachineControl :=
  .running { block := entryBlock, position := .terminator }

private def locals1 : Locals := Locals.empty.assign sizeVar 32
private def locals2 (alloc : Allocation) : Locals := locals1.assign xVar alloc.offset
private def locals3 (alloc : Allocation) : Locals := (locals2 alloc).assign valueVar 42
private def locals5 (alloc : Allocation) : Locals := (locals3 alloc).assign zVar 42

private def initializedState0 (world : World) : MachineState :=
  { world, control := stmtControl 0 }

private def initializedState1 (world : World) : MachineState :=
  { world, locals := locals1, control := stmtControl 1 }

private def initializedState2 (world : World) (alloc : Allocation) : MachineState :=
  { world, memory := MemoryState.empty.push alloc, locals := locals2 alloc, control := stmtControl 2 }

private def initializedState3 (world : World) (alloc : Allocation) : MachineState :=
  { world, memory := MemoryState.empty.push alloc, locals := locals3 alloc, control := stmtControl 3 }

private def initializedState4 (world : World) (alloc : Allocation) : MachineState :=
  { world
    memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray
    locals := locals3 alloc
    control := stmtControl 4 }

private def initializedState5 (world : World) (alloc : Allocation) : MachineState :=
  { world
    memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray
    locals := locals5 alloc
    control := stmtControl 5 }

private def initializedState6 (ctx : CallContext) (world : World) (alloc : Allocation) : MachineState :=
  { world := world.storeStorage ctx.self 42 42
    memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray
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
private theorem run_liftM_locals {m : Type → Type} [Monad m] {α : Type}
    (action : StateT Locals m α) (state : MachineState) :
    (liftM action : StateT MachineState m α).run state =
      action.run state.locals >>= fun pair =>
        pure (pair.1, { state with locals := pair.2 }) := rfl

@[simp]
private theorem run_lookupM_locals (locals : Locals) (var : VarId) :
    (Locals.lookupM var).run locals =
      match locals.lookup var with
      | .error error => .error error
      | .ok value => .ok (value, locals) := by
  simp only [Locals.lookupM, StateT.run_bind]
  have hget : (StateT.get : StateT Locals (Except IRError) Locals).run locals =
      .ok (locals, locals) := rfl
  rw [hget]
  cases hlookup : locals.lookup? var <;>
    simp [hlookup, Locals.lookup, bind, Except.bind, pure, Except.pure]

@[simp]
private theorem run_lookupM_machine (state : MachineState) (var : VarId) :
    (Locals.lookupM var : MachineStateM Word).run state =
      match state.locals.lookup var with
      | .error error => .error error
      | .ok value => .ok (value, state) := by
  rw [run_liftM_locals]
  simp only [Locals.lookupM, StateT.run_bind]
  have hget : (StateT.get : StateT Locals (Except IRError) Locals).run state.locals =
      .ok (state.locals, state.locals) := rfl
  rw [hget]
  cases hlookup : state.locals.lookup? var <;>
    simp [hlookup, Locals.lookup, bind, Except.bind, pure, Except.pure]

@[simp]
private theorem run_assignM_machine (state : MachineState) (var : VarId) (value : Word) :
    (liftM (Locals.assignM var value) : MachineStateM Unit).run state =
      .ok ((), { state with locals := state.locals.assign var value }) := rfl

private theorem eval_initialized_malloc {world : World} {alloc : Allocation}
    {state : MachineState}
    (heval : (eval_malloc_uninit alloc xVar sizeVar).run (initializedState1 world) =
      .ok ((), state)) :
    alloc.size = 32 ∧ state = { initializedState1 world with
      memory := MemoryState.empty.push alloc, locals := locals2 alloc } := by
  simp only [eval_malloc_uninit, StateT.run_bind] at heval
  rw [run_lookupM_machine] at heval
  simp [initializedState1, locals1, Locals.lookup, Locals.lookup?, Locals.assign,
    Locals.empty, bind, Except.bind] at heval
  have h32 : (32 : Word).toNat = 32 := by decide
  rw [h32] at heval
  by_cases hsize : alloc.size = 32
  · rw [if_pos hsize] at heval
    change Except.ok ((), { initializedState1 world with
      memory := MemoryState.empty.push alloc, locals := locals2 alloc }) =
        Except.ok ((), state) at heval
    exact ⟨hsize, (congrArg Prod.snd (Except.ok.inj heval)).symm⟩
  · rw [if_neg hsize] at heval
    change Except.error IRError.invalidAlloc = Except.ok ((), state) at heval
    contradiction

private theorem eval_initialized_mstore {world : World} {alloc : Allocation}
    {state : MachineState}
    (heval : (eval_mstore32 xVar valueVar).run (initializedState3 world alloc) =
      .ok ((), state)) :
    state = { initializedState3 world alloc with
      memory := (MemoryState.empty.push alloc).writeBytes alloc.offset
        (42 : Word).toByteArray } := by
  simp only [eval_mstore32, StateT.run_bind] at heval
  rw [run_lookupM_machine] at heval
  simp [initializedState3, locals1, locals2, locals3, run_lookupM_locals, Locals.lookup,
    Locals.lookup?, Locals.assign, Locals.empty, StateT.run_modify,
    bind, Except.bind, pure, Except.pure] at heval
  simpa [initializedState3, locals3] using heval.symm

private theorem eval_initialized_mload {world : World} {alloc : Allocation}
    {state : MachineState} (hsize : alloc.size = 32) (assumed : Vector UInt8 32)
    (heval : (eval_mload32 ⟨assumed.toArray⟩ zVar xVar).run
      (initializedState4 world alloc) = .ok ((), state)) :
    state = { initializedState4 world alloc with locals := locals5 alloc } := by
  simp only [eval_mload32, StateT.run_bind] at heval
  rw [run_lookupM_machine] at heval
  simp [initializedState4, locals1, locals2, locals3, Locals.lookup,
    Locals.lookup?, Locals.assign, Locals.empty, bind, Except.bind, pure, Except.pure,
    read_written_word alloc hsize assumed, fromByteArray_toByteArray, ofNat_toNat] at heval
  simpa [initializedState4, locals5] using heval.symm

private theorem initialized_step_closed {ctx : CallContext} {world : World}
    {state state' : MachineState} {trace : Trace}
    (hstate : InitializedReachable ctx world state)
    (hstep : SmallStep initializedLoad ctx state trace state') :
    trace = [] ∧ InitializedReachable ctx world state' := by
  cases hstate <;> cases hstep <;>
    simp_all [initializedLoad, Program.decodeStmt, Program.terminatorAt, Program.block?,
      BasicBlock.absoluteToPosition, initializedState0, initializedState1, initializedState2,
      initializedState3, initializedState4, initializedState5, initializedState6,
      initializedState7, stmtControl, termControl]
  case state0.assign state' nextControl result expr hstmt heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    simp [eval_assign, Expr.eval, Locals.assign, bind, Except.bind] at heval
    subst state'
    exact .state1
  case state1.mallocUninit state' nextControl alloc result size hstmt _ heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    rcases eval_initialized_malloc heval with ⟨hsize, rfl⟩
    exact .state2 alloc hsize
  case state2.assign alloc hsize state' nextControl result expr hstmt heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    simp [eval_assign, Expr.eval, Locals.assign, bind, Except.bind] at heval
    subst state'
    exact .state3 alloc hsize
  case state3.mstore32 alloc hsize state' nextControl offset value hstmt heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    have := eval_initialized_mstore heval
    subst state'
    exact .state4 alloc hsize
  case state4.mload32 alloc hsize state' nextControl assumed result offset hstmt heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    have := eval_initialized_mload hsize assumed heval
    subst state'
    exact .state5 alloc hsize
  case state5.sstore alloc hsize state' nextControl key value hstmt heval =>
    obtain ⟨rfl, rfl, rfl⟩ := hstmt
    simp [eval_sstore, locals1, locals2, locals3, locals5,
      Locals.lookup, Locals.lookup?, Locals.empty, Locals.assign, bind, Except.bind,
      pure, Except.pure] at heval
    subst state'
    exact .state6 alloc hsize
  case state6.terminator alloc hsize terminator hterm heval =>
    subst terminator
    simp [eval_terminator, pure, Except.pure] at heval
    subst state'
    exact .state7 alloc hsize

private theorem initialized_steps {ctx : CallContext} {world : World}
    {trace : Trace} {state : MachineState}
    (hsteps : Steps initializedLoad ctx (initializedState0 world) trace state) :
    trace = [] ∧ InitializedReachable ctx world state := by
  induction hsteps with
  | refl => exact ⟨rfl, .state0⟩
  | tail start next ih =>
      rcases ih with ⟨rfl, hmid⟩
      rcases initialized_step_closed hmid next with ⟨rfl, hstate⟩
      exact ⟨rfl, hstate⟩

private theorem initialized_no_next_event {ctx : CallContext} {world : World}
    {trace : Trace} {event : Event} {state : MachineState}
    (hrun : Runs initializedLoad ctx world (trace ++ [event]) state) : False := by
  rcases hrun with ⟨cursor, hcursor, hsteps⟩
  have hcursor' : cursor = { block := entryBlock, position := .statement 0 } := by
    symm
    simpa [initializedLoad, Program.startCursor?, Program.block?, BasicBlock.startPosition,
      BasicBlock.absoluteToPosition] using hcursor
  subst cursor
  have htrace := (initialized_steps hsteps).1
  have := congrArg List.length htrace
  simp at this

private theorem initialized_halted_world {ctx : CallContext} {world : World}
    {trace : Trace} {state : MachineState}
    (hrun : Runs initializedLoad ctx world trace state) (hhalt : state.control = .halted) :
    trace = [] ∧ state.world = world.storeStorage ctx.self 42 42 := by
  rcases hrun with ⟨cursor, hcursor, hsteps⟩
  have hcursor' : cursor = { block := entryBlock, position := .statement 0 } := by
    symm
    simpa [initializedLoad, Program.startCursor?, Program.block?, BasicBlock.startPosition,
      BasicBlock.absoluteToPosition] using hcursor
  subst cursor
  rcases initialized_steps hsteps with ⟨htrace, hstate⟩
  refine ⟨htrace, ?_⟩
  cases hstate <;> simp [initializedState0, initializedState1, initializedState2,
    initializedState3, initializedState4, initializedState5, initializedState6,
    initializedState7, stmtControl, termControl] at hhalt ⊢


private def zeroAlloc (offset : Word) : Allocation :=
  { offset, bytes := ByteArray.empty }

private def zeroState0 (world : World) : MachineState :=
  { world, control := stmtControl 0 }

private def zeroState1 (world : World) : MachineState :=
  { world, locals := Locals.empty.assign sizeVar 0, control := stmtControl 1 }

private def zeroState2 (world : World) (offset : Word) : MachineState :=
  { world
    memory := MemoryState.empty.push (zeroAlloc offset)
    locals := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 2 }

private def zeroState2Eval (world : World) (offset : Word) : MachineState :=
  { world
    memory := MemoryState.empty.push (zeroAlloc offset)
    locals := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 1 }

private def zeroState3 (ctx : CallContext) (world : World) (offset : Word) : MachineState :=
  { zeroState2 world offset with
    world := world.storeStorage ctx.self offset offset
    control := termControl }

private def zeroState4 (ctx : CallContext) (world : World) (offset : Word) : MachineState :=
  { zeroState3 ctx world offset with control := .halted }

private theorem zero_run (ctx : CallContext) (world : World) (offset : Word) :
    Runs zeroSizeStore ctx world [] (zeroState4 ctx world offset) := by
  refine ⟨{ block := entryBlock, position := .statement 0 }, ?_, ?_⟩
  · simp [zeroSizeStore, Program.startCursor?, Program.block?, BasicBlock.startPosition,
      BasicBlock.absoluteToPosition]
  · change Steps zeroSizeStore ctx (zeroState0 world) [] (zeroState4 ctx world offset)
    have step01 : SmallStep zeroSizeStore ctx (zeroState0 world) [] (zeroState1 world) := by
      refine .assign
        (state' := { zeroState1 world with control := stmtControl 0 })
        (nextControl := stmtControl 1) (result := sizeVar) (expr := .constant 0) ?_ ?_
      · simp [zeroSizeStore, Program.decodeStmt, Program.block?, BasicBlock.absoluteToPosition,
          zeroState0, stmtControl]
      · simp [eval_assign, Expr.eval, zeroState0, zeroState1, stmtControl,
          Locals.empty, Locals.assign, bind, Except.bind]
    have step12 :
        SmallStep zeroSizeStore ctx (zeroState1 world) [] (zeroState2 world offset) := by
      unfold zeroState2
      refine SmallStep.mallocUninit
        (state' := zeroState2Eval world offset)
        (nextControl := stmtControl 2) (alloc := zeroAlloc offset)
        (result := xVar) (size := sizeVar) ?_ ?_ ?_
      · simp [zeroSizeStore, Program.decodeStmt, Program.block?, BasicBlock.absoluteToPosition,
          zeroState1, stmtControl]
      · constructor
        · change offset.toBitVec.toNat ≤ 2 ^ 256
          exact offset.toBitVec.isLt.le
        · simp [zeroState1, MemoryState.empty]
      · simp only [eval_malloc_uninit, StateT.run_bind]
        rw [run_lookupM_machine]
        have hzero : (0 : Word).toNat = 0 := by decide
        simp [zeroState1, zeroAlloc, Allocation.size, Locals.lookup, Locals.lookup?,
          Locals.assign, Locals.empty, bind, Except.bind, pure, hzero]
        rfl
    have step23 :
        SmallStep zeroSizeStore ctx (zeroState2 world offset) [] (zeroState3 ctx world offset) := by
      unfold zeroState3
      refine SmallStep.sstore
        (state' := { zeroState2 world offset with
          world := world.storeStorage ctx.self offset offset })
        (nextControl := termControl) (key := xVar) (value := xVar) ?_ ?_
      · simp [zeroSizeStore, Program.decodeStmt, Program.block?, BasicBlock.absoluteToPosition,
          zeroState2, stmtControl, termControl]
      · simp [eval_sstore, zeroState2, stmtControl,
          Locals.lookup, Locals.lookup?, Locals.empty, Locals.assign, bind, Except.bind,
          pure, Except.pure]
    have step34 :
        SmallStep zeroSizeStore ctx (zeroState3 ctx world offset) []
          (zeroState4 ctx world offset) := by
      apply SmallStep.terminator (terminator := .halt)
      · simp [zeroSizeStore, Program.terminatorAt, Program.block?, zeroState3, termControl]
      · simp [eval_terminator, zeroState3, zeroState4, pure, Except.pure]
    exact .tail (.tail (.tail (.tail .refl step01) step12) step23) step34

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

theorem initializedLoad_deterministic : Deterministic initializedLoad := by
  intro ctx world trace outcome₁ outcome₂ h₁ h₂
  cases outcome₁ <;> cases outcome₂
  · rfl
  · rcases h₁ with ⟨_, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₁ with ⟨_, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₁ with ⟨_, _, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₁ with ⟨_, _, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₁ with ⟨_, _, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₂ with ⟨_, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₂ with ⟨_, _, _, hrun⟩
    exact (initialized_no_next_event hrun).elim
  · rcases h₁ with ⟨state₁, hrun₁, hhalt₁, hworld₁⟩
    rcases h₂ with ⟨state₂, hrun₂, hhalt₂, hworld₂⟩
    have hworld : state₁.world = state₂.world :=
      (initialized_halted_world hrun₁ hhalt₁).2.trans
        (initialized_halted_world hrun₂ hhalt₂).2.symm
    subst hworld₂
    exact congrArg ObservableOutcome.halt (hworld₁.symm.trans hworld)

theorem zeroSizeStore_not_deterministic : ¬ Deterministic zeroSizeStore := by
  intro hdet
  have heq := hdet zeroContext (default : World) []
    (.halt ((default : World).storeStorage zeroContext.self 1 1))
    (.halt ((default : World).storeStorage zeroContext.self 2 2))
    ⟨zeroState4 zeroContext default 1, zero_run zeroContext default 1, rfl, rfl⟩
    ⟨zeroState4 zeroContext default 2, zero_run zeroContext default 2, rfl, rfl⟩
  exact zero_worlds_differ (ObservableOutcome.halt.inj heq)

end Sir.Examples
