import Sir.Vars.Theorems

namespace Sir.Vars

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

theorem resume_rejects_arity (env : Locals) (next : Control) :
    resume (.returned #[]) env #[witnessResult] next = .error (.blockArityMismatch 0 1) := by
  dsimp (config := {zetaDelta := true}) [resume]
  simp [Locals.bindReturns, Locals.bindValues, bind, Except.bind]

theorem witness_step_constant (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx (witnessInitial globals) [] (witnessAfterConstant globals) := by
  have hstmt : witnessProgram.AtStmt (witnessInitial globals)
      (witnessAfterConstant globals).control (.assign witnessResult (.constant 7)) := rfl
  have heval :
      (witnessInitial globals).evaluate ctx (.assign witnessResult (.constant 7)) =
        .ok (globals, (witnessInitial globals).environment.assign witnessResult 7) := by
    simp [State.evaluate, evalStmt, evalExpr, witnessInitial]
  exact SmallStep.evaluate hstmt heval

theorem witness_step_halt (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx (witnessAfterConstant globals) [] (witnessFinal globals) :=
  SmallStep.control rfl rfl

theorem witness_runs (ctx : CallContext) (globals : Globals) :
    Steps witnessProgram ctx (witnessInitial globals) [] (witnessFinal globals) :=
  .tail (.tail .refl (witness_step_constant ctx globals)) (witness_step_halt ctx globals)

theorem witness_confluence_consumes_export (ctx : CallContext) (globals : Globals) :
    Steps.Extends witnessProgram ctx (witnessFinal globals) [] (witnessFinal globals) [] ∨
    Steps.Extends witnessProgram ctx (witnessFinal globals) [] (witnessFinal globals) [] ∨
    Trace.QueryDivergence [] [] :=
  Steps.confluence_or_queryDivergence witness_memOracleFree
    (witness_runs ctx globals) (witness_runs ctx globals)

theorem witness_hasStmt {statement : Stmt} (hstatement : witnessProgram.HasStmt statement) :
    statement = .assign witnessResult (.constant 7) := by
  simpa [Program.HasStmt, Function.HasStmt, witnessProgram] using hstatement

theorem witness_blocks {fn : Function} (hfn : fn ∈ witnessProgram.functions)
    {block : Block} (hblock : block ∈ fn.blocks) :
    block = witnessProgram.init.entry := by
  simp [Program.functions, witnessProgram] at hfn
  subst hfn
  simpa [Function.blocks, witnessProgram] using hblock

theorem witness_no_callEdge (caller callee : FunctionId) :
    ¬ witnessProgram.callEdge caller callee := by
  rintro ⟨_, _, fn, hfn, hstatement⟩
  exact Stmt.noConfusion (witness_hasStmt ⟨fn, Array.mem_of_getElem? hfn, hstatement⟩)

theorem witness_no_callCycle (f : FunctionId) :
    ¬ Relation.TransGen witnessProgram.callEdge f f := by
  intro hcycle
  cases hcycle with
  | single hedge => exact witness_no_callEdge _ _ hedge
  | tail _ hedge => exact witness_no_callEdge _ _ hedge

theorem witness_wellFormed : witnessProgram.WellFormed where
  icallArity _ _ _ hstatement := Stmt.noConfusion (witness_hasStmt hstatement)
  iretArity := by
    intro fn hfn block hblock hterminator
    have hentry := witness_blocks hfn hblock
    subst hentry
    simp [witnessProgram] at hterminator
  acyclicCalls := witness_no_callCycle
  entryArity := by
    simp [witnessProgram, Function.paramsOf, Function.outputs?, Function.blocks]
  validJumpTargets := by
    intro fn hfn block hblock target htarget
    have hentry := witness_blocks hfn hblock
    subst hentry
    simp [witnessProgram, Terminator.jumpTargets] at htarget
  variablesDefinedBeforeUse := by
    intro fn hfn block hblock
    have hentry := witness_blocks hfn hblock
    subst hentry
    refine ⟨?_, ?_⟩
    · intro index statement hstatement identifier hread
      have hassign := witness_hasStmt
        ⟨fn, hfn, _, hblock, Array.mem_of_getElem? hstatement⟩
      subst hassign
      simp [Stmt.variablesRead, Expr.variablesRead] at hread
    · intro identifier hread
      simp [witnessProgram, Terminator.variablesRead] at hread

theorem witness_atStmt (globals : Globals) {next : Control} {statement : Stmt}
    (hstatement : witnessProgram.AtStmt (witnessInitial globals) next statement) :
    statement = .assign witnessResult (.constant 7) := by
  have hat : witnessProgram.atStmt (witnessInitial globals) =
      some ((witnessAfterConstant globals).control, .assign witnessResult (.constant 7)) := rfl
  simp only [Program.AtStmt, hat, Option.some.injEq, Prod.mk.injEq] at hstatement
  exact hstatement.2.symm

theorem witness_callState (globals : Globals) :
    witnessProgram.callState? witnessEntry globals #[] = some (witnessInitial globals) := by
  simp [Program.callState?, Program.function?, Program.functions, witnessProgram, witnessInitial,
    witnessEntry, witnessBlock, Block.startPosition, Block.absoluteToPosition,
    Locals.bindParams, Locals.bindValues, bind, Except.bind, pure, Except.pure]

theorem witness_ready (ctx : CallContext) (globals : Globals) :
    witnessProgram.ReadyState ctx (witnessInitial globals) := by
  refine ⟨⟨witnessEntry, globals, #[], [], witnessInitial globals,
      witness_callState globals, .refl⟩,
    .inl ⟨(witnessAfterConstant globals).control, .assign witnessResult (.constant 7),
      rfl, by simp⟩,
    .inr ⟨?_, ?_⟩, ?_⟩
  · intro _ _ _ _ hstatement _
    exact absurd (witness_atStmt globals hstatement) (by simp)
  · intro _ _ _ _ hstatement _
    exact absurd (witness_atStmt globals hstatement) (by simp)
  · intro _ _ _ _ hstatement _
    exact absurd (witness_atStmt globals hstatement) (by simp)

theorem witness_progress (ctx : CallContext) (globals : Globals) :
    ∃ trace state', SmallStep witnessProgram ctx (witnessInitial globals) trace state' :=
  witness_wellFormed.progress (witness_ready ctx globals)

end Sir.Vars
