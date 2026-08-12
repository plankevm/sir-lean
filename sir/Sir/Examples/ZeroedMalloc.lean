import Sir.Proofs.Memory
import Sir.Proofs.Steps
import Sir.Spec.Vars

namespace Sir.Examples

def zeroedMallocLoadSize : VarId := ⟨0⟩
def zeroedMallocLoadOffset : VarId := ⟨1⟩
def zeroedMallocLoadResult : VarId := ⟨2⟩
def zeroedMallocLoadBlock : BlockId := ⟨0⟩
def zeroedMallocLoadEntry : FunctionId := ⟨0⟩

def zeroedMallocLoad : Vars.Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[]
        statements := #[
          .assign zeroedMallocLoadSize (.constant 32),
          .malloc zeroedMallocLoadOffset zeroedMallocLoadSize,
          .mload32 zeroedMallocLoadResult zeroedMallocLoadOffset]
        terminator := .halt
        outputs := #[]}]
      entry := zeroedMallocLoadBlock }]
    initEntry := zeroedMallocLoadEntry
    mainEntry := none }

private def zeroedMallocAllocation : Allocation :=
  { offset := 0, bytes := ⟨Array.replicate 32 0⟩ }

private def zeroedMallocControl (position : Machine.BlockPosition) : Machine.MachineControl :=
  .running {
    fn := zeroedMallocLoadEntry
    block := zeroedMallocLoadBlock
    position }

private def zeroedMallocState0 (world : World) : MachineState :=
  { globals := { world }, control := zeroedMallocControl (.statement 0) }

private def zeroedMallocState1 (world : World) : MachineState :=
  { globals := { world }
    locals := Locals.empty.assign zeroedMallocLoadSize 32
    control := zeroedMallocControl (.statement 1) }

private def zeroedMallocState2 (world : World) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push zeroedMallocAllocation }
    locals := (Locals.empty.assign zeroedMallocLoadSize 32).assign zeroedMallocLoadOffset 0
    control := zeroedMallocControl (.statement 2) }

private def zeroedMallocState3 (world : World) : MachineState :=
  { globals := { world, memory := MemoryState.empty.push zeroedMallocAllocation }
    locals := ((Locals.empty.assign zeroedMallocLoadSize 32).assign
      zeroedMallocLoadOffset 0).assign zeroedMallocLoadResult 0
    control := zeroedMallocControl .terminator }

private def zeroedMallocState4 (world : World) : MachineState :=
  { zeroedMallocState3 world with control := .halted }

private theorem zeroedMallocEntry (world : World) :
    zeroedMallocLoad.callState? zeroedMallocLoadEntry { world := world } #[] =
      some (zeroedMallocState0 world) := by
  apply Vars.Program.callState?_eq_some_iff.mpr
  refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
  simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
    Array.toList_zip]
  rfl

private theorem zeroedMallocSteps (ctx : CallContext) (world : World) :
    Vars.Steps zeroedMallocLoad ctx (zeroedMallocState0 world) [] (zeroedMallocState4 world) := by
  have hvalid : MemoryState.empty.IsValidNewAlloc zeroedMallocAllocation := by
    decide
  have hsize : zeroedMallocAllocation.size = (32 : Word).toNat := by
    decide
  have hzero : zeroedMallocAllocation.bytes =
      ByteArray.mk (Array.replicate (32 : Word).toNat 0) := by
    decide
  have hadmissible : Machine.Operation.Admissible Machine.memoryPolicy .malloc
      (zeroedMallocState1 world).globals #[32] zeroedMallocAllocation :=
    ⟨32, rfl, ⟨hvalid, hsize⟩, hvalid, hsize, hzero⟩
  have hfetchEmpty : (#[] : Array VarId).mapM ((zeroedMallocState0 world).locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreSize : Locals.bindValues (zeroedMallocState0 world).locals
      #[zeroedMallocLoadSize] #[32] = .ok (zeroedMallocState1 world).locals := by
    simp only [zeroedMallocState0, zeroedMallocState1, Locals.bindValues,
      ← Array.forIn_toList, Array.toList_zip]
    rfl
  have step01 : Vars.SmallStep zeroedMallocLoad ctx (zeroedMallocState0 world) []
      (zeroedMallocState1 world) := by
    apply step_assign (program := zeroedMallocLoad) (ctx := ctx)
      (result := zeroedMallocLoadSize) (expr := .constant 32)
      (by simp [zeroedMallocLoad, Vars.Program.decodeStmt, Vars.Program.block?, Vars.Program.function?,
        Vars.Function.block?, Vars.Block.absoluteToPosition, zeroedMallocState0,
        zeroedMallocControl, zeroedMallocLoadEntry, zeroedMallocLoadBlock,
        zeroedMallocLoadSize, zeroedMallocLoadOffset, zeroedMallocLoadResult])
    simp only [Vars.decodeExpression, Machine.Instruction.Fires]
    exact fires_of hfetchEmpty (by trivial)
      (Machine.Operation.execute_constant_ok ctx 32 (zeroedMallocState0 world).globals #[])
      hstoreSize
  have hfetchSize : #[zeroedMallocLoadSize].mapM
      ((zeroedMallocState1 world).locals.lookup ·) = .ok #[32] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreOffset : Locals.bindValues (zeroedMallocState1 world).locals
      #[zeroedMallocLoadOffset] #[0] = .ok (zeroedMallocState2 world).locals := by
    simp only [zeroedMallocState1, zeroedMallocState2, Locals.bindValues,
      ← Array.forIn_toList, Array.toList_zip]
    rfl
  have step12 : Vars.SmallStep zeroedMallocLoad ctx (zeroedMallocState1 world) []
      (zeroedMallocState2 world) := by
    apply step_malloc (program := zeroedMallocLoad) (ctx := ctx)
      (result := zeroedMallocLoadOffset) (size := zeroedMallocLoadSize)
      (by simp [zeroedMallocLoad, Vars.Program.decodeStmt, Vars.Program.block?, Vars.Program.function?,
        Vars.Function.block?, Vars.Block.absoluteToPosition, zeroedMallocState1,
        zeroedMallocControl, zeroedMallocLoadEntry, zeroedMallocLoadBlock,
        zeroedMallocLoadSize, zeroedMallocLoadOffset, zeroedMallocLoadResult])
    simp only [Vars.decodeStatement, Machine.Instruction.Fires]
    exact fires_of hfetchSize hadmissible
      (Machine.Operation.execute_malloc_ok ctx zeroedMallocAllocation
        (zeroedMallocState1 world).globals 32 hsize)
      hstoreOffset
  let assumed : Vector UInt8 32 := Vector.replicate 32 0
  have hcontains : zeroedMallocAllocation.Contains (0 : Word).toNat 32 := by
    decide
  have hread : (zeroedMallocState2 world).globals.memory.readBytes
      0 ⟨assumed.toArray⟩ = ByteArray.mk (Array.replicate 32 0) := by
    simpa [zeroedMallocState1, zeroedMallocState2] using
      Machine.Operation.malloc_readBytes_zeroed_word hadmissible hcontains assumed
  have hfetchOffset : #[zeroedMallocLoadOffset].mapM
      ((zeroedMallocState2 world).locals.lookup ·) = .ok #[0] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreResult : Locals.bindValues (zeroedMallocState2 world).locals
      #[zeroedMallocLoadResult] #[0] = .ok (zeroedMallocState3 world).locals := by
    simp only [zeroedMallocState2, zeroedMallocState3, Locals.bindValues,
      ← Array.forIn_toList, Array.toList_zip]
    rfl
  have hexecute : Machine.Operation.execute ctx .mload32 assumed
      (zeroedMallocState2 world).globals #[0] =
        .ok (.next #[0] (zeroedMallocState2 world).globals []) := by
    rw [Machine.Operation.execute_mload32_ok, hread]
    simp only [Evm.fromByteArrayBigEndian, Evm.fromBytesBigEndian, Function.comp_apply]
    rw [show (ByteArray.mk (Array.replicate 32 0)).toList =
      (ByteArray.mk (Array.replicate 32 0)).data.toList by
        exact toList_eq_data_toList _]
    simp [Evm.fromBytes']
    rfl
  have step23 : Vars.SmallStep zeroedMallocLoad ctx (zeroedMallocState2 world) []
      (zeroedMallocState3 world) := by
    apply step_mload32 (program := zeroedMallocLoad) (ctx := ctx)
      (result := zeroedMallocLoadResult) (offset := zeroedMallocLoadOffset)
      (by simp [zeroedMallocLoad, Vars.Program.decodeStmt, Vars.Program.block?, Vars.Program.function?,
        Vars.Function.block?, Vars.Block.absoluteToPosition, zeroedMallocState2,
        zeroedMallocControl, zeroedMallocLoadEntry, zeroedMallocLoadBlock,
        zeroedMallocLoadSize, zeroedMallocLoadOffset, zeroedMallocLoadResult])
    simp only [Vars.decodeStatement, Machine.Instruction.Fires]
    exact fires_of hfetchOffset (by trivial) hexecute hstoreResult
  have step34 : Vars.SmallStep zeroedMallocLoad ctx (zeroedMallocState3 world) []
      (zeroedMallocState4 world) :=
    step_terminator (terminator := .halt)
      (by simp [zeroedMallocLoad, Vars.Program.terminatorAt, Vars.Program.block?, Vars.Program.function?,
        Vars.Function.block?, zeroedMallocState3, zeroedMallocControl,
        zeroedMallocLoadEntry, zeroedMallocLoadBlock])
      (by simp [Vars.evaluateTerminator, zeroedMallocState3, zeroedMallocState4,
        pure, Except.pure])
  exact .tail (.tail (.tail (.tail .refl step01) step12) step23) step34

theorem zeroedMallocLoad_readsZero (ctx : CallContext) (world : World) :
    ∃ state,
      zeroedMallocLoad.RunsFunction ctx zeroedMallocLoadEntry { world := world } #[] [] state ∧
      state.locals.lookup zeroedMallocLoadResult = .ok 0 ∧
      state.control = .halted := by
  refine ⟨zeroedMallocState4 world, ⟨zeroedMallocState0 world,
    zeroedMallocEntry world, zeroedMallocSteps ctx world⟩, ?_, rfl⟩
  simp [zeroedMallocState4, zeroedMallocState3, Locals.lookup, Locals.lookup?,
    Locals.assign]

end Sir.Examples
