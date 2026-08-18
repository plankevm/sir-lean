import Sir.Stack.Theorems
import Sir.Vars.Theorems

namespace Sir.Vars

open Sir Machine

def witnessResult : VarId := ⟨0⟩
def witnessEntry : FunctionId := ⟨0⟩
def witnessBlock : BlockId := ⟨0⟩

def witnessProgram : Program :=
  { init :=
      { entry :=
          { inputs := #[]
            statements := #[.assign witnessResult (.constant 7)]
            terminator := .halt
            outputs := #[] }
        rest := #[] }
    main := none
    rest := #[] }

def witnessInitial (globals : Globals) : Vars.State :=
  { globals
    environment := .empty
    control := .running
      { fn := witnessEntry, block := witnessBlock, position := .statement 0 } }

def witnessAfterConstant (globals : Globals) : Vars.State :=
  { globals
    environment := Locals.empty.assign witnessResult 7
    control := .running
      { fn := witnessEntry, block := witnessBlock, position := .terminator } }

def witnessFinal (globals : Globals) : Vars.State :=
  { globals, environment := Locals.empty.assign witnessResult 7, control := .halted }

theorem witness_memOracleFree : witnessProgram.MemOracleFree := by
  intro statement hstatement
  simp [Program.HasStmt, Function.HasStmt, witnessProgram] at hstatement
  subst statement
  simp [Stmt.isMemOracle]

theorem resume_rejects_arity (env : Locals) (next : Machine.MachineControl) :
    resume (.returned #[]) env #[witnessResult] next = none := by
  simp [resume, Locals.bindReturns, Locals.bindValues, Functor.map, Except.map]

theorem witness_step_constant (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessInitial globals) [] (witnessAfterConstant globals) := by
  apply Machine.Step.operation (hdecode := rfl)
  refine ⟨#[], #[7], (), by trivial, ?_, rfl, ?_⟩
  · have hfetch : (#[] : Array VarId).mapM (Locals.empty.lookup ·) = .ok #[] := by
      rw [Array.mapM_eq_mapM_toList]
      rfl
    simpa only [frame, witnessInitial] using hfetch
  · have hstore : Locals.bindValues Locals.empty #[witnessResult] #[7] =
        .ok (Locals.empty.assign witnessResult 7) := by
      simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
      rfl
    simpa only [frame, witnessInitial] using hstore

theorem witness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessAfterConstant globals) [] (witnessFinal globals) := by
  exact Machine.Step.control rfl

theorem witness_runs (ctx : CallContext) (globals : Globals) :
    Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
      (witnessInitial globals) [] (witnessFinal globals) :=
  .tail (.tail .refl (witness_step_constant Machine.memoryPolicy ctx globals))
    (witness_step_halt Machine.memoryPolicy ctx globals)

end Sir.Vars

namespace Sir.Stack

open Sir Machine

def witnessEntry : FunctionId := ⟨0⟩
def witnessBlock : BlockId := ⟨0⟩
def witnessSum : Word := Evm.UInt256.add 3 2

def witnessProgram : Program :=
  { init :=
      { entry :=
          { inputCount := 0
            instructions := #[.op (.constant 2), .op (.constant 3), .op .add]
            terminator := .halt
            outputCount := 1 }
        rest := #[] }
    rest := #[] }

def witnessState (globals : Globals) (stack : List Word) (position : Machine.BlockPosition) :
    Machine.State frame :=
  { globals
    environment := { Environment.empty with stack }
    control := .running { fn := witnessEntry, block := witnessBlock, position } }

theorem witness_memOracleFree : witnessProgram.MemOracleFree := by
  intro instruction hinstruction
  simp [Program.HasInstr, Function.HasInstr, witnessProgram] at hinstruction
  rcases hinstruction with rfl | rfl | rfl
  all_goals simp [Instr.isMemOracle]

theorem witness_step_constant₂ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessState globals [] (.statement 0)) []
      (witnessState globals [2] (.statement 1)) := by
  apply Machine.Step.operation (hdecode := rfl)
  exact ⟨_, _, (), by trivial, rfl, rfl,
    by simp [frame, store, witnessState, Operation.inputCount,
      Operation.outputCount]⟩

theorem witness_step_constant₃ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessState globals [2] (.statement 1)) []
      (witnessState globals [3, 2] (.statement 2)) := by
  apply Machine.Step.operation (hdecode := rfl)
  exact ⟨_, _, (), by trivial, rfl, rfl,
    by simp [frame, store, witnessState, Operation.inputCount,
      Operation.outputCount]⟩

theorem witness_step_add (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessState globals [3, 2] (.statement 2)) []
      (witnessState globals [witnessSum] .terminator) := by
  apply Machine.Step.operation (hdecode := rfl)
  exact ⟨_, _, (), by trivial, rfl, rfl,
    by simp [frame, store, witnessState, Operation.inputCount,
      Operation.outputCount, witnessSum]⟩

theorem witness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    Machine.Step frame (decoder witnessProgram) policy ctx
      (witnessState globals [witnessSum] .terminator) []
      { globals, environment := { Environment.empty with stack := [witnessSum] },
        control := .halted } := by
  exact Machine.Step.control rfl

theorem witness_runs (ctx : CallContext) (globals : Globals) :
    Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
      (witnessState globals [] (.statement 0)) []
      { globals, environment := { Environment.empty with stack := [witnessSum] },
        control := .halted } :=
  .tail
    (.tail
      (.tail
        (.tail .refl (witness_step_constant₂ Machine.memoryPolicy ctx globals))
        (witness_step_constant₃ Machine.memoryPolicy ctx globals))
      (witness_step_add Machine.memoryPolicy ctx globals))
    (witness_step_halt Machine.memoryPolicy ctx globals)

end Sir.Stack

namespace Sir.Vars

open Sir Machine

theorem witness_confluence_consumes_generic (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
        (witnessFinal globals) suffix (witnessFinal globals) ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
        (witnessFinal globals) suffix (witnessFinal globals) ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  steps_confluence_or_queryDivergence witness_memOracleFree
    (witness_runs ctx globals) (witness_runs ctx globals)

end Sir.Vars

namespace Sir.Stack

open Sir Machine

theorem witness_confluence_consumes_generic (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted }
        suffix
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      Machine.Steps frame (decoder witnessProgram) Machine.memoryPolicy ctx
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted }
        suffix
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  Steps.confluence_or_queryDivergence witness_memOracleFree
    (witness_runs ctx globals) (witness_runs ctx globals)

end Sir.Stack
