import Sir.Vars.Theorems

namespace Sir.Vars

private theorem byteArray_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  rw [ByteArray.toList]
  suffices loop : ∀ index rest,
      ByteArray.toList.loop bytes index rest = rest.reverse ++ bytes.data.toList.drop index by
    simpa using loop 0 []
  intro index rest
  fun_induction ByteArray.toList.loop bytes index rest with
  | case1 index rest hlt ih =>
      have hindex : index < bytes.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hget : bytes.get! index = bytes.data.toList[index]'hindex := by
        obtain ⟨array⟩ := bytes
        simp only [ByteArray.get!]
        rw [getElem!_pos array index hlt]
        rfl
      rw [ih, hget, List.reverse_cons, List.append_assoc]
      congr 1
      rw [List.drop_eq_getElem_cons hindex]
      simp
  | case2 index rest hge =>
      have hlength : bytes.data.toList.length ≤ index := by
        rw [Array.length_toList]; exact Nat.le_of_not_lt hge
      simp [List.drop_eq_nil_of_le hlength]

def nondetOffset : VarId := ⟨0⟩
def nondetResult : VarId := ⟨1⟩
def nondetEntry : FunctionId := ⟨0⟩
def nondetBlockId : BlockId := ⟨0⟩

def nondetBlock : Block :=
  { inputs := #[]
    statements := #[.assign nondetOffset (.constant 0), .mload32 nondetResult nondetOffset]
    terminator := .halt
    outputs := #[] }

def nondetFunction : Function := { entry := nondetBlock, rest := #[] }

def nondetProgram : Program := { init := nondetFunction, main := none, rest := #[] }

def nondetGlobals (world : World) : Globals := { world }

def nondetZeroBytes : Vector UInt8 32 := Vector.replicate 32 0

def nondetOneBytes : Vector UInt8 32 :=
  ⟨(List.replicate 31 (0 : UInt8) ++ [1]).toArray, by simp⟩

def nondetInitial (world : World) : State :=
  { globals := nondetGlobals world, environment := .empty
    control := .running { fn := nondetEntry, block := nondetBlockId, position := .statement 0 } }

def nondetAtLoad (world : World) : State :=
  { globals := nondetGlobals world, environment := Locals.empty.assign nondetOffset 0
    control := .running { fn := nondetEntry, block := nondetBlockId, position := .statement 1 } }

def nondetLoaded (world : World) (assumed : Vector UInt8 32) : State :=
  { globals := nondetGlobals world
    environment := (Locals.empty.assign nondetOffset 0).assign nondetResult
      ((nondetGlobals world).readWord32 0 assumed)
    control := .running { fn := nondetEntry, block := nondetBlockId, position := .terminator } }

theorem nondet_functions {fn : Function} (hfn : fn ∈ nondetProgram.functions) :
    fn = nondetFunction := by
  simpa [nondetProgram] using hfn

theorem nondet_blocks {fn : Function} (hfn : fn ∈ nondetProgram.functions)
    {block : Block} (hblock : block ∈ fn.blocks) : block = nondetBlock := by
  obtain rfl := nondet_functions hfn
  simpa [nondetFunction] using hblock

theorem nondet_hasStmt {statement : Stmt} (hstatement : nondetProgram.HasStmt statement) :
    statement = .assign nondetOffset (.constant 0) ∨
      statement = .mload32 nondetResult nondetOffset := by
  simpa [Program.HasStmt, Function.HasStmt, nondetProgram, nondetFunction, nondetBlock]
    using hstatement

theorem nondet_load_hasStmt : nondetProgram.HasStmt (.mload32 nondetResult nondetOffset) :=
  ⟨nondetFunction, by simp [nondetProgram], nondetBlock, by simp [nondetFunction],
    by simp [nondetBlock]⟩

theorem nondet_no_callEdge (caller callee : FunctionId) :
    ¬ nondetProgram.callEdge caller callee := by
  rintro ⟨_, _, fn, hfn, hstatement⟩
  rcases nondet_hasStmt ⟨fn, Array.mem_of_getElem? hfn, hstatement⟩ with hcase | hcase <;>
    exact Stmt.noConfusion hcase

theorem nondet_no_callCycle (f : FunctionId) :
    ¬ Relation.TransGen nondetProgram.callEdge f f := by
  intro hcycle
  cases hcycle with
  | single hedge => exact nondet_no_callEdge _ _ hedge
  | tail _ hedge => exact nondet_no_callEdge _ _ hedge

theorem nondet_wellFormed : nondetProgram.WellFormed where
  icallArity _ _ _ hstatement := by
    rcases nondet_hasStmt hstatement with hcase | hcase <;> exact Stmt.noConfusion hcase
  iretArity := by
    intro fn hfn block hblock hterminator
    obtain rfl := nondet_blocks hfn hblock
    simp [nondetBlock] at hterminator
  acyclicCalls := nondet_no_callCycle
  entryArity := by
    simp [nondetProgram, nondetFunction, nondetBlock, Function.paramsOf, Function.outputs?,
      Function.blocks]
  validJumpTargets := by
    intro fn hfn block hblock target htarget
    obtain rfl := nondet_blocks hfn hblock
    simp [nondetBlock, Terminator.jumpTargets] at htarget
  variablesDefinedBeforeUse := by
    intro fn hfn block hblock
    obtain rfl := nondet_blocks hfn hblock
    refine ⟨?_, ?_⟩
    · intro index statement hstatement identifier hread
      rcases index with _ | _ | index <;>
        simp [nondetBlock] at hstatement <;>
        subst hstatement <;>
        simp_all [Stmt.variablesRead, Expr.variablesRead, nondetBlock,
          Block.variablesDefinedBefore, Stmt.variablesDefined]
    · simp [nondetBlock, Terminator.variablesRead]

theorem nondet_callState (world : World) :
    nondetProgram.callState? nondetEntry (nondetGlobals world) #[] =
      some (nondetInitial world) := by
  simp [Program.callState?, Program.function?, Program.functions, nondetProgram, nondetFunction,
    nondetBlock, nondetInitial, nondetEntry, nondetBlockId, Block.startPosition,
    Block.absoluteToPosition, Locals.bindParams, Locals.bindValues, bind, Except.bind,
    pure, Except.pure]

theorem nondet_read_zero (world : World) :
    (nondetGlobals world).readWord32 0 nondetZeroBytes = 0 := by
  simp [Globals.readWord32, MemoryState.readBytes, MemoryState.readByte?, nondetGlobals,
    nondetZeroBytes, Evm.fromByteArrayBigEndian, byteArray_toList, List.data_toByteArray]
  decide

theorem nondet_read_one (world : World) :
    (nondetGlobals world).readWord32 0 nondetOneBytes = 1 := by
  simp [Globals.readWord32, MemoryState.readBytes, MemoryState.readByte?, nondetGlobals,
    nondetOneBytes, Evm.fromByteArrayBigEndian, byteArray_toList, List.data_toByteArray]
  decide

theorem nondet_step_offset (ctx : CallContext) (world : World) :
    SmallStep nondetProgram ctx (nondetInitial world) [] (nondetAtLoad world) :=
  SmallStep.evaluate (statement := .assign nondetOffset (.constant 0)) rfl rfl

theorem nondet_step_load (ctx : CallContext) (world : World) (assumed : Vector UInt8 32) :
    SmallStep nondetProgram ctx (nondetAtLoad world) [] (nondetLoaded world assumed) :=
  SmallStep.mload32 (assumed := assumed) rfl rfl

theorem nondet_loaded_differ (world : World) :
    nondetLoaded world nondetZeroBytes ≠ nondetLoaded world nondetOneBytes := by
  intro hequal
  have hvalue := congrArg (fun state => state.environment.lookup? nondetResult) hequal
  simp only [nondetLoaded, Locals.lookup?, Locals.assign, ↓reduceIte] at hvalue
  rw [nondet_read_zero, nondet_read_one] at hvalue
  exact absurd hvalue (by decide)

theorem nondet_two_steps (ctx : CallContext) (world : World) :
    SmallStep nondetProgram ctx (nondetAtLoad world) [] (nondetLoaded world nondetZeroBytes) ∧
      SmallStep nondetProgram ctx (nondetAtLoad world) [] (nondetLoaded world nondetOneBytes) ∧
      nondetLoaded world nondetZeroBytes ≠ nondetLoaded world nondetOneBytes :=
  ⟨nondet_step_load ctx world nondetZeroBytes, nondet_step_load ctx world nondetOneBytes,
    nondet_loaded_differ world⟩

theorem nondet_not_memOracleFree : ¬ nondetProgram.MemOracleFree := fun hfree =>
  hfree (.mload32 nondetResult nondetOffset) nondet_load_hasStmt trivial

theorem nondet_trace_det_fails (ctx : CallContext) (world : World) :
    ¬ ∀ (state first second : State) (trace : Trace),
        SmallStep nondetProgram ctx state trace first →
        SmallStep nondetProgram ctx state trace second → first = second := fun hdet =>
  nondet_loaded_differ world
    (hdet _ _ _ [] (nondet_step_load ctx world nondetZeroBytes)
      (nondet_step_load ctx world nondetOneBytes))

end Sir.Vars
