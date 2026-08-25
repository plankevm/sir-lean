import Sir.Vars.Theorems

namespace Sir.Vars

def icallResult : VarId := ⟨0⟩
def icallSum : VarId := ⟨1⟩
def icallCaller : FunctionId := ⟨0⟩
def icallReturner : FunctionId := ⟨1⟩
def icallHalter : FunctionId := ⟨2⟩
def icallBlockId : BlockId := ⟨0⟩

def icallCallerBlock : Block :=
  { inputs := #[]
    statements := #[.icall icallReturner #[] #[icallResult], .icall icallHalter #[] #[]]
    terminator := .halt
    outputs := #[] }

def icallReturnerBlock : Block :=
  { inputs := #[]
    statements := #[.assign icallSum (.constant 5)]
    terminator := .iret
    outputs := #[icallSum] }

def icallHalterBlock : Block :=
  { inputs := #[], statements := #[], terminator := .halt, outputs := #[] }

def icallCallerFunction : Function := { entry := icallCallerBlock, rest := #[] }
def icallReturnerFunction : Function := { entry := icallReturnerBlock, rest := #[] }
def icallHalterFunction : Function := { entry := icallHalterBlock, rest := #[] }

def icallProgram : Program :=
  { init := icallCallerFunction
    main := none
    rest := #[icallReturnerFunction, icallHalterFunction] }

def icallCallerCursor (index : Nat) : Control :=
  .running { fn := icallCaller, block := icallBlockId, position := .statement index }

def icallInitial (globals : Globals) : State :=
  { globals, environment := .empty, control := icallCallerCursor 0 }

def icallAfterReturn (globals : Globals) : State :=
  { globals, environment := Locals.empty.assign icallResult 5, control := icallCallerCursor 1 }

def icallReturnerInitial (globals : Globals) : State :=
  { globals, environment := .empty
    control := .running { fn := icallReturner, block := icallBlockId, position := .statement 0 } }

def icallReturnerAtIret (globals : Globals) : State :=
  { globals, environment := Locals.empty.assign icallSum 5
    control := .running { fn := icallReturner, block := icallBlockId, position := .terminator } }

def icallReturnerFinal (globals : Globals) : State :=
  { globals, environment := Locals.empty.assign icallSum 5, control := .returned #[5] }

def icallHalterInitial (globals : Globals) : State :=
  { globals, environment := .empty
    control := .running { fn := icallHalter, block := icallBlockId, position := .terminator } }

theorem icall_no_args (state : State) :
    (#[] : Array VarId).mapM state.lookup = .ok (#[] : Array Word) := by
  rw [Array.mapM_eq_mapM_toList]
  simp [Functor.map, Except.map, pure, Except.pure]

theorem icall_returner_outputs? : icallReturnerFunction.outputs? = some 1 := by
  simp [Function.outputs?, Function.blocks, icallReturnerFunction, icallReturnerBlock]

theorem icall_halter_outputs? : icallHalterFunction.outputs? = none := by
  simp [Function.outputs?, Function.blocks, icallHalterFunction, icallHalterBlock]

theorem icall_caller_outputs? : icallCallerFunction.outputs? = none := by
  simp [Function.outputs?, Function.blocks, icallCallerFunction, icallCallerBlock]

theorem icall_function_returner :
    icallProgram.function? icallReturner = some icallReturnerFunction := rfl

theorem icall_function_halter :
    icallProgram.function? icallHalter = some icallHalterFunction := rfl

theorem icall_hasStmt {statement : Stmt} (hstatement : icallProgram.HasStmt statement) :
    statement = .icall icallReturner #[] #[icallResult] ∨
      statement = .icall icallHalter #[] #[] ∨
      statement = .assign icallSum (.constant 5) := by
  simpa [Program.HasStmt, Function.HasStmt, icallProgram, icallCallerFunction,
    icallReturnerFunction, icallHalterFunction, icallCallerBlock, icallReturnerBlock,
    icallHalterBlock, or_assoc] using hstatement

theorem icall_blocks {fn : Function} (hfn : fn ∈ icallProgram.functions)
    {block : Block} (hblock : block ∈ fn.blocks) :
    (fn = icallCallerFunction ∧ block = icallCallerBlock) ∨
      (fn = icallReturnerFunction ∧ block = icallReturnerBlock) ∨
      (fn = icallHalterFunction ∧ block = icallHalterBlock) := by
  simp [icallProgram] at hfn
  rcases hfn with rfl | rfl | rfl
  · exact .inl ⟨rfl, by simpa [icallCallerFunction] using hblock⟩
  · exact .inr (.inl ⟨rfl, by simpa [icallReturnerFunction] using hblock⟩)
  · exact .inr (.inr ⟨rfl, by simpa [icallHalterFunction] using hblock⟩)

theorem icall_callEdge_callee {caller callee : FunctionId}
    (hedge : icallProgram.callEdge caller callee) :
    callee = icallReturner ∨ callee = icallHalter := by
  obtain ⟨args, dests, fn, hfn, hstatement⟩ := hedge
  rcases icall_hasStmt ⟨fn, Array.mem_of_getElem? hfn, hstatement⟩ with hcase | hcase | hcase
  · injection hcase with hcallee
    exact .inl hcallee
  · injection hcase with hcallee
    exact .inr hcallee
  · exact Stmt.noConfusion hcase

theorem icall_no_callEdge_returner (callee : FunctionId) :
    ¬ icallProgram.callEdge icallReturner callee := by
  rintro ⟨args, dests, fn, hfn, hstatement⟩
  rw [icall_function_returner] at hfn
  obtain rfl := Option.some.inj hfn
  simp [Function.HasStmt, Function.blocks, icallReturnerFunction, icallReturnerBlock]
    at hstatement

theorem icall_no_callEdge_halter (callee : FunctionId) :
    ¬ icallProgram.callEdge icallHalter callee := by
  rintro ⟨args, dests, fn, hfn, hstatement⟩
  rw [icall_function_halter] at hfn
  obtain rfl := Option.some.inj hfn
  simp [Function.HasStmt, Function.blocks, icallHalterFunction, icallHalterBlock] at hstatement

theorem icall_no_callCycle (f : FunctionId) :
    ¬ Relation.TransGen icallProgram.callEdge f f := by
  intro hcycle
  have hsource : ∀ {a b : FunctionId}, Relation.TransGen icallProgram.callEdge a b →
      ∃ c, icallProgram.callEdge a c := by
    intro a b h
    induction h with
    | single hedge => exact ⟨_, hedge⟩
    | tail _ _ ih => exact ih
  have htarget : ∀ {a b : FunctionId}, Relation.TransGen icallProgram.callEdge a b →
      b = icallReturner ∨ b = icallHalter := by
    intro a b h
    induction h with
    | single hedge => exact icall_callEdge_callee hedge
    | tail _ hedge _ => exact icall_callEdge_callee hedge
  obtain ⟨c, hedge⟩ := hsource hcycle
  rcases htarget hcycle with rfl | rfl
  · exact icall_no_callEdge_returner c hedge
  · exact icall_no_callEdge_halter c hedge

theorem icall_wellFormed : icallProgram.WellFormed where
  icallArity := by
    intro callee args dests hstatement
    rcases icall_hasStmt hstatement with hcase | hcase | hcase
    · injection hcase with hcallee hargs hdests
      subst hcallee
      subst hargs
      subst hdests
      exact ⟨some 1, ⟨icallReturnerFunction, icall_function_returner, rfl,
        icall_returner_outputs?⟩, rfl⟩
    · injection hcase with hcallee hargs hdests
      subst hcallee
      subst hargs
      subst hdests
      exact ⟨none, ⟨icallHalterFunction, icall_function_halter, rfl,
        icall_halter_outputs?⟩, rfl⟩
    · exact Stmt.noConfusion hcase
  iretArity := by
    intro fn hfn block hblock hterminator
    rcases icall_blocks hfn hblock with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [icallCallerBlock] at hterminator
    · simp [icallReturnerBlock, icall_returner_outputs?]
    · simp [icallHalterBlock] at hterminator
  acyclicCalls := icall_no_callCycle
  entryArity := by
    refine ⟨⟨rfl, icall_caller_outputs?⟩, ?_⟩
    simp [icallProgram]
  validJumpTargets := by
    intro fn hfn block hblock target htarget
    rcases icall_blocks hfn hblock with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [icallCallerBlock, icallReturnerBlock, icallHalterBlock,
        Terminator.jumpTargets] at htarget
  variablesDefinedBeforeUse := by
    intro fn hfn block hblock
    rcases icall_blocks hfn hblock with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨?_, ?_⟩
      · intro index statement hstatement identifier hread
        rcases index with _ | _ | index <;>
          simp [icallCallerBlock] at hstatement <;>
          subst hstatement <;>
          simp [Stmt.variablesRead] at hread
      · simp [icallCallerBlock, Terminator.variablesRead]
    · refine ⟨?_, ?_⟩
      · intro index statement hstatement identifier hread
        rcases index with _ | index
        · simp [icallReturnerBlock] at hstatement
          subst hstatement
          simp [Stmt.variablesRead, Expr.variablesRead] at hread
        · simp [icallReturnerBlock] at hstatement
      · simp [icallReturnerBlock, Terminator.variablesRead, Block.variablesDefinedBefore,
          Stmt.variablesDefined]
    · refine ⟨?_, ?_⟩
      · intro index statement hstatement identifier hread
        simp [icallHalterBlock] at hstatement
      · simp [icallHalterBlock, Terminator.variablesRead]

theorem icall_returner_callState (globals : Globals) :
    icallProgram.callState? icallReturner globals #[] = some (icallReturnerInitial globals) := by
  simp [Program.callState?, icall_function_returner, icallReturnerFunction, icallReturnerBlock,
    icallReturnerInitial, icallBlockId, Block.startPosition, Block.absoluteToPosition,
    Locals.bindParams, Locals.bindValues, bind, Except.bind, pure, Except.pure]

theorem icall_halter_callState (globals : Globals) :
    icallProgram.callState? icallHalter globals #[] = some (icallHalterInitial globals) := by
  simp [Program.callState?, icall_function_halter, icallHalterFunction, icallHalterBlock,
    icallHalterInitial, icallBlockId, Block.startPosition, Block.absoluteToPosition,
    Locals.bindParams, Locals.bindValues, bind, Except.bind, pure, Except.pure]

theorem icall_returner_block :
    icallProgram.block? { fn := icallReturner, block := icallBlockId, position := .terminator } =
      some icallReturnerBlock := rfl

theorem icall_returner_outputs (globals : Globals) :
    icallReturnerBlock.outputs.mapM (icallReturnerAtIret globals).environment.lookup =
      .ok #[(5 : Word)] := by
  rw [Array.mapM_eq_mapM_toList]
  simp [icallReturnerBlock, icallReturnerAtIret, Locals.lookup, Locals.lookup?, Locals.assign,
    Functor.map, Except.map, bind, Except.bind, pure, Except.pure]

theorem icall_returner_step_assign (ctx : CallContext) (globals : Globals) :
    SmallStep icallProgram ctx (icallReturnerInitial globals) [] (icallReturnerAtIret globals) :=
  SmallStep.evaluate (statement := .assign icallSum (.constant 5)) rfl rfl

theorem icall_returner_step_iret (ctx : CallContext) (globals : Globals) :
    SmallStep icallProgram ctx (icallReturnerAtIret globals) [] (icallReturnerFinal globals) :=
  SmallStep.control (terminator := .iret) rfl
    (evaluateTerminator_iret_ok (s := icallReturnerAtIret globals) rfl icall_returner_block
      (icall_returner_outputs globals))

theorem icall_halter_step (ctx : CallContext) (globals : Globals) :
    SmallStep icallProgram ctx (icallHalterInitial globals) [] (State.halted globals) :=
  SmallStep.control (terminator := .halt) rfl rfl

theorem icall_returner_evalFn (ctx : CallContext) (globals : Globals) :
    EvalFn icallProgram ctx icallReturner globals #[] [] globals (.returned #[5]) :=
  EvalFn.exit (icall_returner_callState globals)
    (.tail (.tail .refl (icall_returner_step_assign ctx globals))
      (icall_returner_step_iret ctx globals)) rfl

theorem icall_halter_evalFn (ctx : CallContext) (globals : Globals) :
    EvalFn icallProgram ctx icallHalter globals #[] [] globals .halted :=
  EvalFn.exit (icall_halter_callState globals)
    (.tail .refl (icall_halter_step ctx globals)) rfl

theorem icall_step_returner (ctx : CallContext) (globals : Globals) :
    ∃ locals, SmallStep icallProgram ctx (icallInitial globals) []
      (State.of globals locals (icallCallerCursor 1)) :=
  icall_wellFormed.icall_step rfl (icall_no_args (icallInitial globals))
    (icall_returner_evalFn ctx globals)

theorem icall_returner_arity (ctx : CallContext) (globals : Globals) :
    (icallProgram.function? icallReturner).bind (·.outputs?) = some (#[(5 : Word)]).size :=
  icall_wellFormed.evalFn_arity (icall_returner_evalFn ctx globals)

theorem icall_step_halter (ctx : CallContext) (globals : Globals) :
    SmallStep icallProgram ctx (icallAfterReturn globals) [] (State.halted globals) :=
  Program.icall_halted_step rfl (icall_no_args (icallAfterReturn globals))
    (icall_halter_evalFn ctx globals)

end Sir.Vars
