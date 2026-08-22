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
        .ok { witnessInitial globals with
          environment := (witnessInitial globals).environment.assign witnessResult 7 } := by
    simp [State.evaluate, evalStmt, evalExpr]
  exact SmallStep.assign hstmt heval

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

end Sir.Vars
