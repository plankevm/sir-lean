import Sir.Generic.Corollaries

namespace Sir.Generic

open Sir

def sirWitnessResult : VarId := ⟨0⟩
def sirWitnessEntry : FunctionId := ⟨0⟩
def sirWitnessBlock : BlockId := ⟨0⟩

def sirWitnessProgram : Program :=
  { functions := #[
      { blocks := #[
          { inputs := #[]
            statements := #[.assign sirWitnessResult (.constant 7)]
            terminator := .halt
            outputs := #[] }]
        entry := sirWitnessBlock }]
    initEntry := sirWitnessEntry
    mainEntry := none }

def sirWitnessInitial (globals : Globals) : GenState localsFrame :=
  { globals
    env := .empty
    control := .running
      { fn := sirWitnessEntry, block := sirWitnessBlock, position := .statement 0 } }

def sirWitnessAfterConstant (globals : Globals) : GenState localsFrame :=
  { globals
    env := Locals.empty.assign sirWitnessResult 7
    control := .running
      { fn := sirWitnessEntry, block := sirWitnessBlock, position := .terminator } }

def sirWitnessFinal (globals : Globals) : GenState localsFrame :=
  { globals, env := Locals.empty.assign sirWitnessResult 7, control := .halted }

theorem sirWitness_memOracleFree : sirWitnessProgram.MemOracleFree := by
  intro statement hstatement
  simp [Program.HasStmt, Function.HasStmt, sirWitnessProgram] at hstatement
  subst statement
  simp [Stmt.isMemOracle]

theorem sirWitness_step_constant (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep localsFrame (sirDecoder sirWitnessProgram) policy ctx
      (sirWitnessInitial globals) [] (sirWitnessAfterConstant globals) := by
  apply GenStep.op (hdecode := rfl)
  refine OpFrame.Fires.next (oracle := ()) (operands := #[]) (results := #[7])
    (by trivial) ?_ rfl ?_
  · have hfetch : (#[] : Array VarId).mapM (Locals.empty.lookup ·) = .ok #[] := by
      rw [Array.mapM_eq_mapM_toList]
      rfl
    simpa only [localsFrame, sirWitnessInitial] using hfetch
  · have hstore : Locals.bindValues Locals.empty #[sirWitnessResult] #[7] =
        .ok (Locals.empty.assign sirWitnessResult 7) := by
      simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
      rfl
    simpa only [localsFrame, sirWitnessInitial] using hstore

theorem sirWitness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep localsFrame (sirDecoder sirWitnessProgram) policy ctx
      (sirWitnessAfterConstant globals) [] (sirWitnessFinal globals) := by
  exact GenStep.control rfl

theorem sirWitness_runs (ctx : CallContext) (globals : Globals) :
    GenSteps localsFrame (sirDecoder sirWitnessProgram) .empty ctx
      (sirWitnessInitial globals) [] (sirWitnessFinal globals) :=
  .tail (.tail .refl (sirWitness_step_constant .empty ctx globals))
    (sirWitness_step_halt .empty ctx globals)

def cfgWitnessEntry : FunctionId := ⟨0⟩
def cfgWitnessBlock : BlockId := ⟨0⟩
def cfgWitnessSum : Word := Evm.UInt256.add 3 2

def cfgWitnessProgram : CfgProgram :=
  { functions := #[
      { blocks := #[
          { inputCount := 0
            instructions := #[.op (.constant 2), .op (.constant 3), .op .add]
            terminator := .halt
            outputCount := 1 }]
        entry := cfgWitnessBlock }]
    initEntry := cfgWitnessEntry }

def cfgWitnessState (globals : Globals) (stack : List Word) (position : BlockPosition) :
    GenState stackFrame :=
  { globals
    env := { StackEnv.empty with stack }
    control := .running { fn := cfgWitnessEntry, block := cfgWitnessBlock, position } }

theorem cfgWitness_noMload : (cfgDecoder cfgWitnessProgram).NoMload := by
  intro control src dst next hdecode
  cases control with
  | returned results =>
      simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction] at hdecode
  | halted =>
      simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction] at hdecode
  | running cursor =>
      rcases cursor with ⟨⟨functionId⟩, ⟨blockId⟩, position⟩
      cases position with
      | terminator =>
          simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction] at hdecode
      | statement index =>
          rcases functionId with _ | functionId
          · rcases blockId with _ | blockId
            · rcases index with _ | _ | _ | index <;>
                simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction,
                  CfgProgram.block?, CfgProgram.function?, CfgFunction.block?,
                  cfgWitnessProgram] at hdecode
            · simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction,
                CfgProgram.block?, CfgProgram.function?, CfgFunction.block?,
                cfgWitnessProgram] at hdecode
          · simp [cfgDecoder, cfgDecode, CfgProgram.decodeInstruction,
              CfgProgram.block?, CfgProgram.function?, CfgFunction.block?,
              cfgWitnessProgram] at hdecode

theorem cfgWitness_step_constant₂ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [] (.statement 0)) []
      (cfgWitnessState globals [2] (.statement 1)) := by
  apply GenStep.op (hdecode := rfl)
  exact OpFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount])

theorem cfgWitness_step_constant₃ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [2] (.statement 1)) []
      (cfgWitnessState globals [3, 2] (.statement 2)) := by
  apply GenStep.op (hdecode := rfl)
  exact OpFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount])

theorem cfgWitness_step_add (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [3, 2] (.statement 2)) []
      (cfgWitnessState globals [cfgWitnessSum] .terminator) := by
  apply GenStep.op (hdecode := rfl)
  exact OpFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount, cfgWitnessSum])

theorem cfgWitness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [cfgWitnessSum] .terminator) []
      { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
        control := .halted } := by
  exact GenStep.control rfl

theorem cfgWitness_runs (ctx : CallContext) (globals : Globals) :
    GenSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
      (cfgWitnessState globals [] (.statement 0)) []
      { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
        control := .halted } :=
  .tail
    (.tail
      (.tail
        (.tail .refl (cfgWitness_step_constant₂ .empty ctx globals))
        (cfgWitness_step_constant₃ .empty ctx globals))
      (cfgWitness_step_add .empty ctx globals))
    (cfgWitness_step_halt .empty ctx globals)

theorem sirWitness_confluence_consumes_generic (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      GenSteps localsFrame (sirDecoder sirWitnessProgram) .empty ctx
        (sirWitnessFinal globals) suffix (sirWitnessFinal globals) ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      GenSteps localsFrame (sirDecoder sirWitnessProgram) .empty ctx
        (sirWitnessFinal globals) suffix (sirWitnessFinal globals) ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  sir_steps_confluence_or_queryDivergence MemoryPolicy.empty_deterministic
    sirWitness_memOracleFree (sirWitness_runs ctx globals) (sirWitness_runs ctx globals)

theorem cfgWitness_confluence_consumes_generic (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      GenSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
        { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted }
        suffix
        { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      GenSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
        { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted }
        suffix
        { globals, env := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  cfg_steps_confluence_or_queryDivergence MemoryPolicy.empty_deterministic
    cfgWitness_noMload (cfgWitness_runs ctx globals) (cfgWitness_runs ctx globals)

end Sir.Generic
