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

def sirWitnessInitial (globals : Globals) : GenericState localOperandFrame :=
  { globals
    environment := .empty
    control := .running
      { fn := sirWitnessEntry, block := sirWitnessBlock, position := .statement 0 } }

def sirWitnessAfterConstant (globals : Globals) : GenericState localOperandFrame :=
  { globals
    environment := Locals.empty.assign sirWitnessResult 7
    control := .running
      { fn := sirWitnessEntry, block := sirWitnessBlock, position := .terminator } }

def sirWitnessFinal (globals : Globals) : GenericState localOperandFrame :=
  { globals, environment := Locals.empty.assign sirWitnessResult 7, control := .halted }

theorem sirResume_rejects_arity (env : Locals) (next : MachineControl) :
    sirResume (.returned #[]) env #[sirWitnessResult] next = none := by
  simp [sirResume, Locals.bindReturns, Locals.bindValues, Functor.map, Except.map]

theorem sirWitness_step_constant (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep localOperandFrame (sirDecoder sirWitnessProgram) policy ctx
      (sirWitnessInitial globals) [] (sirWitnessAfterConstant globals) := by
  apply GenericStep.operation (hdecode := rfl)
  refine OperandFrame.Fires.next (oracle := ()) (operands := #[]) (results := #[7])
    (by trivial) ?_ rfl ?_
  · have hfetch : (#[] : Array VarId).mapM (Locals.empty.lookup ·) = .ok #[] := by
      rw [Array.mapM_eq_mapM_toList]
      rfl
    simpa only [localOperandFrame, sirWitnessInitial] using hfetch
  · have hstore : Locals.bindValues Locals.empty #[sirWitnessResult] #[7] =
        .ok (Locals.empty.assign sirWitnessResult 7) := by
      simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
      rfl
    simpa only [localOperandFrame, sirWitnessInitial] using hstore

theorem sirWitness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep localOperandFrame (sirDecoder sirWitnessProgram) policy ctx
      (sirWitnessAfterConstant globals) [] (sirWitnessFinal globals) := by
  exact GenericStep.control rfl

theorem sirWitness_runs (ctx : CallContext) (globals : Globals) :
    GenericSteps localOperandFrame (sirDecoder sirWitnessProgram) .empty ctx
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
    GenericState stackFrame :=
  { globals
    environment := { StackEnv.empty with stack }
    control := .running { fn := cfgWitnessEntry, block := cfgWitnessBlock, position } }

theorem cfgWitness_step_constant₂ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [] (.statement 0)) []
      (cfgWitnessState globals [2] (.statement 1)) := by
  apply GenericStep.operation (hdecode := rfl)
  exact OperandFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount])

theorem cfgWitness_step_constant₃ (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [2] (.statement 1)) []
      (cfgWitnessState globals [3, 2] (.statement 2)) := by
  apply GenericStep.operation (hdecode := rfl)
  exact OperandFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount])

theorem cfgWitness_step_add (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [3, 2] (.statement 2)) []
      (cfgWitnessState globals [cfgWitnessSum] .terminator) := by
  apply GenericStep.operation (hdecode := rfl)
  exact OperandFrame.Fires.next (oracle := ()) (by trivial) rfl rfl
    (by simp [stackFrame, stackStore, cfgWitnessState, Operation.inputCount,
      Operation.outputCount, cfgWitnessSum])

theorem cfgWitness_step_halt (policy : MemoryPolicy) (ctx : CallContext)
    (globals : Globals) :
    GenericStep stackFrame (cfgDecoder cfgWitnessProgram) policy ctx
      (cfgWitnessState globals [cfgWitnessSum] .terminator) []
      { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
        control := .halted } := by
  exact GenericStep.control rfl

theorem cfgWitness_runs (ctx : CallContext) (globals : Globals) :
    GenericSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
      (cfgWitnessState globals [] (.statement 0)) []
      { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
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
      GenericSteps localOperandFrame (sirDecoder sirWitnessProgram) .empty ctx
        (sirWitnessFinal globals) suffix (sirWitnessFinal globals) ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      GenericSteps localOperandFrame (sirDecoder sirWitnessProgram) .empty ctx
        (sirWitnessFinal globals) suffix (sirWitnessFinal globals) ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  GenericSteps.confluence_or_queryDivergence (.inl MemoryPolicy.empty_deterministic)
    (sirDecoder_exclusive sirWitnessProgram) (sirDecoder_terminal sirWitnessProgram)
    (sirWitness_runs ctx globals) (sirWitness_runs ctx globals)

theorem cfgWitness_confluence_consumes_generic (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      GenericSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
        { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted }
        suffix
        { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      GenericSteps stackFrame (cfgDecoder cfgWitnessProgram) .empty ctx
        { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted }
        suffix
        { globals, environment := { StackEnv.empty with stack := [cfgWitnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  cfg_steps_confluence_or_queryDivergence MemoryPolicy.empty_deterministic
    (cfgWitness_runs ctx globals) (cfgWitness_runs ctx globals)

end Sir.Generic
