import Sir.Vars.Theorems

namespace Sir.Vars

def jumpSeed : VarId := ⟨0⟩
def jumpParameter : VarId := ⟨1⟩
def jumpDoubled : VarId := ⟨2⟩
def jumpEntry : FunctionId := ⟨0⟩
def jumpSource : BlockId := ⟨0⟩
def jumpTarget : BlockId := ⟨1⟩

def jumpSourceBlock : Block :=
  { inputs := #[]
    statements := #[.assign jumpSeed (.constant 7)]
    terminator := .jump jumpTarget
    outputs := #[jumpSeed] }

def jumpTargetBlock : Block :=
  { inputs := #[jumpParameter]
    statements := #[.assign jumpDoubled (.add jumpParameter jumpParameter)]
    terminator := .halt
    outputs := #[] }

def jumpFunction : Function :=
  { entry := jumpSourceBlock, rest := #[jumpTargetBlock] }

def jumpProgram : Program :=
  { init := jumpFunction, main := none, rest := #[] }

def jumpInitial (globals : Globals) : State :=
  { globals
    environment := .empty
    control := .running { fn := jumpEntry, block := jumpSource, position := .statement 0 } }

def jumpAtJump (globals : Globals) : State :=
  { globals
    environment := Locals.empty.assign jumpSeed 7
    control := .running { fn := jumpEntry, block := jumpSource, position := .terminator } }

def jumpAfterJump (globals : Globals) : State :=
  { globals
    environment := (Locals.empty.assign jumpSeed 7).assign jumpParameter 7
    control := .running { fn := jumpEntry, block := jumpTarget, position := .statement 0 } }

theorem jump_functions {fn : Function} (hfn : fn ∈ jumpProgram.functions) :
    fn = jumpFunction := by
  simpa [jumpProgram] using hfn

theorem jump_blocks {fn : Function} (hfn : fn ∈ jumpProgram.functions)
    {block : Block} (hblock : block ∈ fn.blocks) :
    block = jumpSourceBlock ∨ block = jumpTargetBlock := by
  obtain rfl := jump_functions hfn
  simpa [jumpFunction] using hblock

theorem jump_hasStmt {statement : Stmt} (hstatement : jumpProgram.HasStmt statement) :
    statement = .assign jumpSeed (.constant 7) ∨
      statement = .assign jumpDoubled (.add jumpParameter jumpParameter) := by
  simpa [Program.HasStmt, Function.HasStmt, jumpProgram, jumpFunction, jumpSourceBlock,
    jumpTargetBlock] using hstatement

theorem jump_no_callEdge (caller callee : FunctionId) :
    ¬ jumpProgram.callEdge caller callee := by
  rintro ⟨_, _, fn, hfn, hstatement⟩
  rcases jump_hasStmt ⟨fn, Array.mem_of_getElem? hfn, hstatement⟩ with hcase | hcase <;>
    exact Stmt.noConfusion hcase

theorem jump_no_callCycle (f : FunctionId) :
    ¬ Relation.TransGen jumpProgram.callEdge f f := by
  intro hcycle
  cases hcycle with
  | single hedge => exact jump_no_callEdge _ _ hedge
  | tail _ hedge => exact jump_no_callEdge _ _ hedge

theorem jump_function_target : jumpFunction.block? jumpTarget = some jumpTargetBlock := rfl

theorem jump_program_source :
    jumpProgram.block? { fn := jumpEntry, block := jumpSource, position := .terminator } =
      some jumpSourceBlock := rfl

theorem jump_program_target :
    jumpProgram.block? { fn := jumpEntry, block := jumpTarget, position := .terminator } =
      some jumpTargetBlock := rfl

theorem jump_wellFormed : jumpProgram.WellFormed where
  icallArity _ _ _ hstatement := by
    rcases jump_hasStmt hstatement with hcase | hcase <;> exact Stmt.noConfusion hcase
  iretArity := by
    intro fn hfn block hblock hterminator
    rcases jump_blocks hfn hblock with rfl | rfl <;>
      simp [jumpSourceBlock, jumpTargetBlock] at hterminator
  acyclicCalls := jump_no_callCycle
  entryArity := by
    simp [jumpProgram, jumpFunction, jumpSourceBlock, jumpTargetBlock, Function.paramsOf,
      Function.outputs?, Function.blocks]
  validJumpTargets := by
    intro fn hfn block hblock target htarget
    have hcases := jump_blocks hfn hblock
    obtain rfl := jump_functions hfn
    rcases hcases with rfl | rfl
    · simp [jumpSourceBlock, Terminator.jumpTargets] at htarget
      subst htarget
      exact ⟨jumpTargetBlock, jump_function_target, by simp [jumpSourceBlock, jumpTargetBlock]⟩
    · simp [jumpTargetBlock, Terminator.jumpTargets] at htarget
  variablesDefinedBeforeUse := by
    intro fn hfn block hblock
    rcases jump_blocks hfn hblock with rfl | rfl
    · refine ⟨?_, ?_⟩
      · intro index statement hstatement identifier hread
        rcases index with _ | index <;> simp [jumpSourceBlock] at hstatement
        subst hstatement
        simp [Stmt.variablesRead, Expr.variablesRead] at hread
      · simp [jumpSourceBlock, Terminator.variablesRead, Block.variablesDefinedBefore,
          Stmt.variablesDefined]
    · refine ⟨?_, ?_⟩
      · intro index statement hstatement identifier hread
        rcases index with _ | index <;> simp [jumpTargetBlock] at hstatement
        subst hstatement
        simpa [Stmt.variablesRead, Expr.variablesRead, jumpTargetBlock,
          Block.variablesDefinedBefore] using hread
      · simp [jumpTargetBlock, Terminator.variablesRead]

theorem jump_callState (globals : Globals) :
    jumpProgram.callState? jumpEntry globals #[] = some (jumpInitial globals) := by
  simp [Program.callState?, Program.function?, Program.functions, jumpProgram, jumpFunction,
    jumpSourceBlock, jumpInitial, jumpEntry, jumpSource, Block.startPosition,
    Block.absoluteToPosition, Locals.bindParams, Locals.bindValues, bind, Except.bind,
    pure, Except.pure]

theorem jump_step_seed (ctx : CallContext) (globals : Globals) :
    SmallStep jumpProgram ctx (jumpInitial globals) [] (jumpAtJump globals) :=
  SmallStep.evaluate (statement := .assign jumpSeed (.constant 7)) rfl rfl

theorem jump_outputs (globals : Globals) :
    jumpSourceBlock.outputs.mapM (jumpAtJump globals).environment.lookup = .ok #[(7 : Word)] := by
  rw [Array.mapM_eq_mapM_toList]
  simp [jumpSourceBlock, jumpAtJump, Locals.lookup, Locals.lookup?, Locals.assign,
    Functor.map, Except.map, bind, Except.bind, pure, Except.pure]

theorem jump_evaluates (globals : Globals) :
    evaluateTerminator jumpProgram (jumpAtJump globals).environment
        (jumpAtJump globals).control (.jump jumpTarget) =
      .ok ((jumpAfterJump globals).environment, (jumpAfterJump globals).control) := by
  show jump jumpProgram (jumpAtJump globals).environment
      { fn := jumpEntry, block := jumpSource, position := .terminator } jumpTarget = _
  exact jump_eq_ok jump_program_source jump_program_target (jump_outputs globals) rfl
    (by simp [jumpAtJump, jumpAfterJump, jumpTargetBlock, Locals.bindValues,
      bind, Except.bind, pure, Except.pure])

theorem jump_step_jump (ctx : CallContext) (globals : Globals) :
    SmallStep jumpProgram ctx (jumpAtJump globals) [] (jumpAfterJump globals) :=
  SmallStep.control (terminator := .jump jumpTarget) rfl (jump_evaluates globals)

theorem jump_runs (ctx : CallContext) (globals : Globals) :
    Steps jumpProgram ctx (jumpInitial globals) [] (jumpAfterJump globals) :=
  .tail (.tail .refl (jump_step_seed ctx globals)) (jump_step_jump ctx globals)

theorem jump_no_stmt (globals : Globals) {next : Control} {statement : Stmt} :
    ¬ jumpProgram.AtStmt (jumpAtJump globals) next statement := by
  have hat : jumpProgram.atStmt (jumpAtJump globals) = none := rfl
  simp [Program.AtStmt, hat]

theorem jump_ready (ctx : CallContext) (globals : Globals) :
    jumpProgram.ReadyState ctx (jumpAtJump globals) := by
  refine ⟨⟨jumpEntry, globals, #[], [], jumpInitial globals, jump_callState globals,
      .tail .refl (jump_step_seed ctx globals)⟩,
    .inr ⟨.jump jumpTarget, rfl⟩, .inr ⟨?_, ?_⟩, ?_⟩ <;>
    exact fun _ _ _ _ hstatement _ => absurd hstatement (jump_no_stmt globals)

theorem jump_progress (ctx : CallContext) (globals : Globals) :
    ∃ trace state', SmallStep jumpProgram ctx (jumpAtJump globals) trace state' :=
  jump_wellFormed.progress (jump_ready ctx globals)

end Sir.Vars
