import Sir.Vars.Theorems

namespace Sir.Vars

def memorySize : VarId := ⟨0⟩
def memoryPointer : VarId := ⟨1⟩
def memoryValue : VarId := ⟨2⟩
def memoryLoaded : VarId := ⟨3⟩
def memoryEntry : FunctionId := ⟨0⟩
def memoryBlockId : BlockId := ⟨0⟩

def memoryBlock : Block :=
  { inputs := #[]
    statements := #[
      .assign memorySize (.constant 32),
      .malloc memoryPointer memorySize,
      .assign memoryValue (.constant 42),
      .mstore32 memoryPointer memoryValue,
      .mload32 memoryLoaded memoryPointer]
    terminator := .halt
    outputs := #[] }

def memoryFunction : Function := { entry := memoryBlock, rest := #[] }

def memoryProgram : Program := { init := memoryFunction, main := none, rest := #[] }

def memoryGlobals (world : World) : Globals := { world }

def memoryAllocation : Allocation :=
  { offset := 0, bytes := ByteArray.mk (Array.replicate 32 0) }

def memoryCursor (index : Nat) : Control :=
  .running { fn := memoryEntry, block := memoryBlockId, position := .statement index }

def memoryInitial (world : World) : State :=
  { globals := memoryGlobals world, environment := .empty, control := memoryCursor 0 }

def memoryAtMalloc (world : World) : State :=
  { globals := memoryGlobals world
    environment := Locals.empty.assign memorySize 32
    control := memoryCursor 1 }

def memoryAtValue (world : World) : State :=
  { globals := (memoryGlobals world).pushAlloc memoryAllocation
    environment := (Locals.empty.assign memorySize 32).assign memoryPointer 0
    control := memoryCursor 2 }

def memoryAtStore (world : World) : State :=
  { globals := (memoryGlobals world).pushAlloc memoryAllocation
    environment :=
      ((Locals.empty.assign memorySize 32).assign memoryPointer 0).assign memoryValue 42
    control := memoryCursor 3 }

def memoryAtLoad (world : World) : State :=
  { globals := ((memoryGlobals world).pushAlloc memoryAllocation).writeWord32 0 42
    environment :=
      ((Locals.empty.assign memorySize 32).assign memoryPointer 0).assign memoryValue 42
    control := memoryCursor 4 }

def memoryFinal (world : World) (assumed : Vector UInt8 32) : State :=
  { globals := ((memoryGlobals world).pushAlloc memoryAllocation).writeWord32 0 42
    environment :=
      (((Locals.empty.assign memorySize 32).assign memoryPointer 0).assign memoryValue 42).assign
        memoryLoaded ((memoryAtLoad world).globals.readWord32 0 assumed)
    control := .running { fn := memoryEntry, block := memoryBlockId, position := .terminator } }

theorem memory_word_toNat : (32 : Word).toNat = 32 := by decide

theorem memory_functions {fn : Function} (hfn : fn ∈ memoryProgram.functions) :
    fn = memoryFunction := by
  simpa [memoryProgram] using hfn

theorem memory_blocks {fn : Function} (hfn : fn ∈ memoryProgram.functions)
    {block : Block} (hblock : block ∈ fn.blocks) : block = memoryBlock := by
  obtain rfl := memory_functions hfn
  simpa [memoryFunction] using hblock

theorem memory_hasStmt {statement : Stmt} (hstatement : memoryProgram.HasStmt statement) :
    statement = .assign memorySize (.constant 32) ∨
      statement = .malloc memoryPointer memorySize ∨
      statement = .assign memoryValue (.constant 42) ∨
      statement = .mstore32 memoryPointer memoryValue ∨
      statement = .mload32 memoryLoaded memoryPointer := by
  simpa [Program.HasStmt, Function.HasStmt, memoryProgram, memoryFunction, memoryBlock]
    using hstatement

theorem memory_no_callEdge (caller callee : FunctionId) :
    ¬ memoryProgram.callEdge caller callee := by
  rintro ⟨_, _, fn, hfn, hstatement⟩
  rcases memory_hasStmt ⟨fn, Array.mem_of_getElem? hfn, hstatement⟩ with
    hcase | hcase | hcase | hcase | hcase <;> exact Stmt.noConfusion hcase

theorem memory_no_callCycle (f : FunctionId) :
    ¬ Relation.TransGen memoryProgram.callEdge f f := by
  intro hcycle
  cases hcycle with
  | single hedge => exact memory_no_callEdge _ _ hedge
  | tail _ hedge => exact memory_no_callEdge _ _ hedge

theorem memory_wellFormed : memoryProgram.WellFormed where
  icallArity _ _ _ hstatement := by
    rcases memory_hasStmt hstatement with hcase | hcase | hcase | hcase | hcase <;>
      exact Stmt.noConfusion hcase
  iretArity := by
    intro fn hfn block hblock hterminator
    obtain rfl := memory_blocks hfn hblock
    simp [memoryBlock] at hterminator
  acyclicCalls := memory_no_callCycle
  entryArity := by
    simp [memoryProgram, memoryFunction, memoryBlock, Function.paramsOf, Function.outputs?,
      Function.blocks]
  validJumpTargets := by
    intro fn hfn block hblock target htarget
    obtain rfl := memory_blocks hfn hblock
    simp [memoryBlock, Terminator.jumpTargets] at htarget
  variablesDefinedBeforeUse := by
    intro fn hfn block hblock
    obtain rfl := memory_blocks hfn hblock
    refine ⟨?_, ?_⟩
    · intro index statement hstatement identifier hread
      rcases index with _ | _ | _ | _ | _ | index <;>
        simp [memoryBlock] at hstatement <;>
        subst hstatement <;>
        simp_all [Stmt.variablesRead, Expr.variablesRead, memoryBlock,
          Block.variablesDefinedBefore, Stmt.variablesDefined]
    · simp [memoryBlock, Terminator.variablesRead]

theorem memory_callState (world : World) :
    memoryProgram.callState? memoryEntry (memoryGlobals world) #[] =
      some (memoryInitial world) := by
  simp [Program.callState?, Program.function?, Program.functions, memoryProgram, memoryFunction,
    memoryBlock, memoryInitial, memoryCursor, memoryEntry, memoryBlockId, Block.startPosition,
    Block.absoluteToPosition, Locals.bindParams, Locals.bindValues, bind, Except.bind,
    pure, Except.pure]

theorem memory_lookup_size (world : World) :
    (memoryAtMalloc world).lookup memorySize = .ok (32 : Word) := rfl

theorem memory_lookup_pointer (world : World) :
    (memoryAtStore world).lookup memoryPointer = .ok (0 : Word) := rfl

theorem memory_allocation_valid : MemoryState.empty.IsValidNewAlloc memoryAllocation := by decide

theorem memory_allocation_size : memoryAllocation.size = (32 : Word).toNat := by decide

theorem memory_allocation_bytes :
    memoryAllocation.bytes = ByteArray.mk (Array.replicate (32 : Word).toNat 0) := by
  rw [memory_word_toNat]
  rfl

theorem memory_bump_fits :
    MemoryState.empty.watermark + (32 : Word).toNat ≤ Evm.UInt256.size := by decide

theorem memory_inBounds :
    (MemoryState.empty.push memoryAllocation).InBounds (0 : Word).toNat 32 := by decide

theorem memory_allocation_allowed (world : World) :
    (memoryAtMalloc world).allows 32 memoryAllocation :=
  ⟨memory_allocation_valid, memory_allocation_size⟩

theorem memory_store_in_bounds (world : World) : (memoryAtStore world).inBounds 0 :=
  memory_inBounds

theorem memory_step_size (ctx : CallContext) (world : World) :
    SmallStep memoryProgram ctx (memoryInitial world) [] (memoryAtMalloc world) :=
  SmallStep.evaluate (statement := .assign memorySize (.constant 32)) rfl rfl

theorem memory_step_malloc (ctx : CallContext) (world : World) :
    SmallStep memoryProgram ctx (memoryAtMalloc world) [] (memoryAtValue world) :=
  SmallStep.malloc (size := 32) (allocation := memoryAllocation) rfl (memory_lookup_size world)
    (memory_allocation_allowed world) memory_allocation_bytes

theorem memory_step_value (ctx : CallContext) (world : World) :
    SmallStep memoryProgram ctx (memoryAtValue world) [] (memoryAtStore world) :=
  SmallStep.evaluate (statement := .assign memoryValue (.constant 42)) rfl rfl

theorem memory_step_store (ctx : CallContext) (world : World) :
    SmallStep memoryProgram ctx (memoryAtStore world) [] (memoryAtLoad world) :=
  SmallStep.mstore32 rfl (memory_lookup_pointer world) rfl (memory_store_in_bounds world)

theorem memory_step_load (ctx : CallContext) (world : World) (assumed : Vector UInt8 32) :
    SmallStep memoryProgram ctx (memoryAtLoad world) [] (memoryFinal world assumed) :=
  SmallStep.mload32 (assumed := assumed) rfl rfl

theorem memory_runs (ctx : CallContext) (world : World) (assumed : Vector UInt8 32) :
    Steps memoryProgram ctx (memoryInitial world) [] (memoryFinal world assumed) :=
  .tail (.tail (.tail (.tail (.tail .refl (memory_step_size ctx world))
    (memory_step_malloc ctx world)) (memory_step_value ctx world))
    (memory_step_store ctx world)) (memory_step_load ctx world assumed)

theorem memory_atMalloc_stmt (world : World) {next : Control} {statement : Stmt}
    (hstatement : memoryProgram.AtStmt (memoryAtMalloc world) next statement) :
    statement = .malloc memoryPointer memorySize := by
  have hat : memoryProgram.atStmt (memoryAtMalloc world) =
      some (memoryCursor 2, .malloc memoryPointer memorySize) := rfl
  simp only [Program.AtStmt, hat, Option.some.injEq, Prod.mk.injEq] at hstatement
  exact hstatement.2.symm

theorem memory_atStore_stmt (world : World) {next : Control} {statement : Stmt}
    (hstatement : memoryProgram.AtStmt (memoryAtStore world) next statement) :
    statement = .mstore32 memoryPointer memoryValue := by
  have hat : memoryProgram.atStmt (memoryAtStore world) =
      some (memoryCursor 4, .mstore32 memoryPointer memoryValue) := rfl
  simp only [Program.AtStmt, hat, Option.some.injEq, Prod.mk.injEq] at hstatement
  exact hstatement.2.symm

theorem memory_allocationAvailable (world : World) :
    memoryProgram.AllocationAvailable (memoryAtMalloc world) := by
  refine ⟨?_, ?_⟩
  · intro nextControl result size word hstatement hword
    obtain ⟨rfl, rfl⟩ := Stmt.malloc.inj (memory_atMalloc_stmt world hstatement)
    rw [memory_lookup_size world] at hword
    obtain rfl := Except.ok.inj hword
    exact ⟨memoryAllocation, memory_allocation_valid, memory_allocation_size,
      memory_allocation_bytes⟩
  · intro _ _ _ _ hstatement _
    exact Stmt.noConfusion (memory_atMalloc_stmt world hstatement)

theorem memory_bumpFits (world : World) : memoryProgram.BumpFits (memoryAtMalloc world) := by
  refine ⟨?_, ?_⟩
  · intro nextControl result size word hstatement hword
    obtain ⟨rfl, rfl⟩ := Stmt.malloc.inj (memory_atMalloc_stmt world hstatement)
    rw [memory_lookup_size world] at hword
    obtain rfl := Except.ok.inj hword
    exact memory_bump_fits
  · intro _ _ _ _ hstatement _
    exact Stmt.noConfusion (memory_atMalloc_stmt world hstatement)

theorem memory_storeInBounds (world : World) :
    memoryProgram.StoreInBounds (memoryAtStore world) := by
  intro nextControl offset value word hstatement hword
  obtain ⟨rfl, rfl⟩ := Stmt.mstore32.inj (memory_atStore_stmt world hstatement)
  rw [memory_lookup_pointer world] at hword
  obtain rfl := Except.ok.inj hword
  exact memory_store_in_bounds world

theorem memory_ready_at_malloc (ctx : CallContext) (world : World) :
    memoryProgram.ReadyState ctx (memoryAtMalloc world) :=
  ⟨⟨memoryEntry, memoryGlobals world, #[], [], memoryInitial world, memory_callState world,
      .tail .refl (memory_step_size ctx world)⟩,
    .inl ⟨memoryCursor 2, .malloc memoryPointer memorySize, rfl, by simp⟩,
    .inl (memory_allocationAvailable world),
    fun _ _ _ _ hstatement _ => Stmt.noConfusion (memory_atMalloc_stmt world hstatement)⟩

theorem memory_ready_at_store (ctx : CallContext) (world : World) :
    memoryProgram.ReadyState ctx (memoryAtStore world) :=
  ⟨⟨memoryEntry, memoryGlobals world, #[], [], memoryInitial world, memory_callState world,
      .tail (.tail (.tail .refl (memory_step_size ctx world)) (memory_step_malloc ctx world))
        (memory_step_value ctx world)⟩,
    .inl ⟨memoryCursor 4, .mstore32 memoryPointer memoryValue, rfl, by simp⟩,
    .inr ⟨fun _ _ _ _ hstatement _ => Stmt.noConfusion (memory_atStore_stmt world hstatement),
      fun _ _ _ _ hstatement _ => Stmt.noConfusion (memory_atStore_stmt world hstatement)⟩,
    memory_storeInBounds world⟩

theorem memory_progress_at_malloc (ctx : CallContext) (world : World) :
    ∃ trace state', SmallStep memoryProgram ctx (memoryAtMalloc world) trace state' :=
  memory_wellFormed.progress (memory_ready_at_malloc ctx world)

theorem memory_progress_at_store (ctx : CallContext) (world : World) :
    ∃ trace state', SmallStep memoryProgram ctx (memoryAtStore world) trace state' :=
  memory_wellFormed.progress (memory_ready_at_store ctx world)

end Sir.Vars
