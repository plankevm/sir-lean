import Sir.Proofs.Vars

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

open Machine

def Machine.State.toMachine (state : Machine.State Vars.frame) : MachineState :=
  ⟨state.globals, state.environment, state.control⟩

theorem MachineState.toState_inj {state₁ state₂ : MachineState}
    (h : state₁.toState = state₂.toState) : state₁ = state₂ := by
  cases state₁
  cases state₂
  cases h
  rfl

namespace Machine.Operation

theorem execute_constant_ok (ctx : CallContext) (value : Word) (globals : Globals)
    (operands : Array Word) :
    execute ctx (.constant value) () globals operands =
      .ok (.next #[value] globals []) := rfl

theorem execute_copy_ok (ctx : CallContext) (value : Word) (globals : Globals) :
    execute ctx .copy () globals #[value] = .ok (.next #[value] globals []) := rfl

theorem execute_add_ok (ctx : CallContext) (lhs rhs : Word) (globals : Globals) :
    execute ctx .add () globals #[lhs, rhs] =
      .ok (.next #[Evm.UInt256.add lhs rhs] globals []) := rfl

theorem execute_lt_ok (ctx : CallContext) (lhs rhs : Word) (globals : Globals) :
    execute ctx .lt () globals #[lhs, rhs] =
      .ok (.next #[Evm.UInt256.lt lhs rhs] globals []) := rfl

theorem execute_sload_ok (ctx : CallContext) (key : Word) (globals : Globals) :
    execute ctx .sload () globals #[key] =
      .ok (.next #[globals.world.loadStorage ctx.self key] globals []) := rfl

theorem execute_sstore_ok (ctx : CallContext) (key value : Word) (globals : Globals) :
    execute ctx .sstore () globals #[key, value] =
      .ok (.next #[]
        { globals with world := globals.world.storeStorage ctx.self key value } []) := rfl

theorem execute_gas_ok (ctx : CallContext) (answer : Word) (globals : Globals)
    (operands : Array Word) :
    execute ctx .gas answer globals operands =
      .ok (.next #[answer] globals [.gas answer]) := rfl

theorem execute_call_ok (ctx : CallContext) (result : CallResult)
    (globals : Globals) (callee gas : Word) :
    execute ctx .call result globals #[callee, gas] =
      .ok (.next #[Evm.UInt256.fromBool result.success]
        { globals with returnData := result.output, world := result.world' }
        [.call {
          input := { target := .ofUInt256 callee, gas := gas, world := globals.world }
          result := result }]) := rfl

theorem execute_mallocUninit_ok (ctx : CallContext) (allocation : Allocation)
    (globals : Globals) (size : Word) (hsize : allocation.size = size.toNat) :
    execute ctx .mallocUninit allocation globals #[size] =
      .ok (.next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []) := by
  simp [execute, hsize, bind, Except.bind, pure, Except.pure]

theorem execute_malloc_ok (ctx : CallContext) (allocation : Allocation)
    (globals : Globals) (size : Word) (hsize : allocation.size = size.toNat) :
    execute ctx .malloc allocation globals #[size] =
      .ok (.next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []) := by
  simp [execute, hsize, bind, Except.bind, pure, Except.pure]

theorem execute_mstore32_ok (ctx : CallContext) (globals : Globals)
    (offset value : Word) (hin : globals.memory.InBounds offset.toNat 32) :
    execute ctx .mstore32 () globals #[offset, value] =
      .ok (.next #[]
        { globals with memory := globals.memory.writeBytes offset value.toByteArray } []) := by
  simp [execute, hin, pure, Except.pure]

theorem execute_mstore32_out_of_bounds (ctx : CallContext) (globals : Globals)
    (offset value : Word) (hout : ¬ globals.memory.InBounds offset.toNat 32) :
    execute ctx .mstore32 () globals #[offset, value] = .error .storeOutOfBounds := by
  simp [execute, hout, throw, throwThe, MonadExceptOf.throw]

theorem execute_mload32_ok (ctx : CallContext) (assumed : Vector UInt8 32)
    (globals : Globals) (offset : Word) :
    execute ctx .mload32 assumed globals #[offset] =
      .ok (.next #[.ofNat (Evm.fromByteArrayBigEndian
        (globals.memory.readBytes offset ⟨assumed.toArray⟩))] globals []) := rfl

end Machine.Operation

theorem fires_of
    {operation : Operation} {src dst : Array VarId} {env env' : Locals}
    {globals globals' : Globals} {operands results : Array Word} {trace : Trace}
    {oracle : operation.Oracle}
    (hfetch : Vars.frame.fetch env src = .ok operands)
    (hadmissible : operation.Admissible Machine.memoryPolicy globals operands oracle)
    (hexecute : operation.execute ctx oracle globals operands =
      .ok (.next results globals' trace))
    (hstore : Vars.frame.store env dst results = .ok env') :
    Vars.frame.Fires Machine.memoryPolicy ctx operation src dst env globals trace env' globals' :=
  .next hadmissible hfetch hexecute hstore

theorem firesHalt_false
    {operation : Operation} {src : Array VarId} {env : Locals}
    {globals globals' : Globals} {trace : Trace}
    (h : Vars.frame.FiresHalt Machine.memoryPolicy ctx operation src env globals trace globals') :
    False := by
  cases h with
  | halted hadmissible hfetch hexecute =>
      cases operation <;> simp only [Machine.Operation.execute] at hexecute
      all_goals repeat' first | split at hexecute
      all_goals simp_all [pure, Except.pure, bind, Except.bind]

def Machine.Instruction.Fires {frame : OperandFrame} (instruction : Instruction frame)
    (policy : MemoryPolicy) (ctx : CallContext) (env : frame.Environment) (globals : Globals)
    (trace : Trace) (env' : frame.Environment) (globals' : Globals) : Prop :=
  match instruction.kind with
  | .primitive operation =>
      frame.Fires policy ctx operation instruction.source instruction.destination
        env globals trace env' globals'
  | .icall _ => False

theorem step_statement
    {state : MachineState} {next : Machine.MachineControl} {statement : Vars.Stmt}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, statement))
    (hfires : (Vars.decodeStatement statement).Fires Machine.memoryPolicy ctx state.locals state.globals
      trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState := by
  generalize hinstruction : Vars.decodeStatement statement = instruction at hfires
  obtain ⟨kind, src, dst⟩ := instruction
  cases kind with
  | primitive operation =>
      exact Machine.Step.operation (operation := operation) (src := src) (dst := dst)
        (by
          change Vars.decode program state.control =
            some (⟨Instruction.Kind.primitive operation, src, dst⟩, next)
          simp [Vars.decode, hdecode, hinstruction]) hfires
  | icall callee => simp [Machine.Instruction.Fires] at hfires

theorem step_assign
    {state : MachineState} {next : Machine.MachineControl} {result : VarId} {expr : Vars.Expr}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .assign result expr))
    (hfires : (Vars.decodeExpression result expr).Fires Machine.memoryPolicy ctx state.locals state.globals
      trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_sstore
    {state : MachineState} {next : Machine.MachineControl} {key value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .sstore key value))
    (hfires : (Vars.decodeStatement (.sstore key value)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_gas
    {state : MachineState} {next : Machine.MachineControl} {result : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .gas result))
    (hfires : (Vars.decodeStatement (.gas result)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_call
    {state : MachineState} {next : Machine.MachineControl} {call : Vars.Call}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .call call))
    (hfires : (Vars.decodeStatement (.call call)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_mallocUninit
    {state : MachineState} {next : Machine.MachineControl} {result size : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mallocUninit result size))
    (hfires : (Vars.decodeStatement (.mallocUninit result size)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_malloc
    {state : MachineState} {next : Machine.MachineControl} {result size : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .malloc result size))
    (hfires : (Vars.decodeStatement (.malloc result size)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_mstore32
    {state : MachineState} {next : Machine.MachineControl} {offset value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mstore32 offset value))
    (hfires : (Vars.decodeStatement (.mstore32 offset value)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_mload32
    {state : MachineState} {next : Machine.MachineControl} {result offset : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mload32 result offset))
    (hfires : (Vars.decodeStatement (.mload32 result offset)).Fires Machine.memoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toState :=
  step_statement hdecode hfires

theorem step_terminator
    {state state' : MachineState} {terminator : Vars.Terminator}
    (hterm : program.terminatorAt state.control = some terminator)
    (heval : (Vars.evaluateTerminator program terminator).run state = .ok ((), state')) :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState [] state'.toState := by
  apply Machine.Step.control
  apply Vars.control_inv.mpr
  exact ⟨terminator, state', hterm, heval, rfl, rfl, rfl, rfl⟩

theorem step_icall
    {state : MachineState} {next : Machine.MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values results : Array Word} {trace : Trace}
    {globals' : Globals} {locals' : Locals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx callee
      state.globals values trace globals' (.returned results))
    (hbind : Locals.bindReturns state.locals dests results = .ok locals') :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      { state with globals := globals', locals := locals', control := next }.toState := by
  apply Machine.Step.internalCall
  · change Vars.decode program state.control =
      some (⟨Instruction.Kind.icall callee, args, dests⟩, next)
    simp [Vars.decode, hdecode, Vars.decodeStatement]
  · exact hargs
  · exact hcallee
  · exact Vars.resume_returned_eq_some_iff.mpr ⟨hbind, rfl⟩

theorem step_icallHalted
    {state : MachineState} {next : Machine.MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values : Array Word} {trace : Trace}
    {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx callee
      state.globals values trace globals' .halted) :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state.toState trace
      ({ globals := globals', control := .halted } : MachineState).toState := by
  apply Machine.Step.internalCall
  · change Vars.decode program state.control =
      some (⟨Instruction.Kind.icall callee, args, dests⟩, next)
    simp [Vars.decode, hdecode, Vars.decodeStatement]
  · exact hargs
  · exact hcallee
  · exact Vars.resume_halted state.locals dests next

theorem Vars.EvalFn.returned
    {function : FunctionId} {globals : Globals} {args results : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      initial.toState trace exit.toState)
    (hreturn : exit.control = .returned results) :
    Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx function globals args
      trace exit.globals (.returned results) :=
  Machine.FunctionEvaluation.returned (initial := initial.toState) (exit := exit.toState)
    (by simp [Vars.entry_eq, hentry]) hrun hreturn

theorem Vars.EvalFn.halted
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      initial.toState trace exit.toState)
    (hhalt : exit.control = .halted) :
    Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx function globals args
      trace exit.globals .halted :=
  Machine.FunctionEvaluation.halted (initial := initial.toState) (exit := exit.toState)
    (by simp [Vars.entry_eq, hentry]) hrun hhalt

@[elab_as_elim]
theorem Vars.Steps.inductionOn {program : Vars.Program} {ctx : CallContext}
    {motive : (state : MachineState) → (trace : Trace) → (final : MachineState) →
      Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        state.toState trace final.toState → Prop}
    (refl : ∀ state, motive state [] state .refl)
    (tail : ∀ {state middle final : MachineState} {trace₁ trace₂ : Trace}
      (start : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        state.toState trace₁ middle.toState)
      (next : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        middle.toState trace₂ final.toState),
      motive state trace₁ middle start →
        motive state (trace₁ ++ trace₂) final (start.tail next))
    {state final : MachineState} {trace : Trace}
    (h : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState) : motive state trace final h := by
  simpa using Machine.Steps.inductionOn
    (motive := fun state trace final h =>
      motive state.toMachine trace final.toMachine h)
    (fun state => refl state.toMachine)
    (fun {state middle final trace₁ trace₂} start next ih =>
      tail (state := state.toMachine) (middle := middle.toMachine)
        (final := final.toMachine) (trace₁ := trace₁) (trace₂ := trace₂)
        (by simpa using start) (by simpa using next) (by simpa using ih)) h

def Stuck (program : Vars.Program) (ctx : CallContext) (state : MachineState) : Prop :=
  Machine.Stuck (Vars.decoder program) Machine.memoryPolicy ctx state.toState

theorem stuck_of_returned
    {state : MachineState} {results : Array Word}
    (hcontrol : state.control = .returned results) :
    Stuck program ctx state :=
  Machine.stuck_of_returned (Vars.decoder_terminal program) hcontrol

theorem stuck_of_halted
    {state : MachineState} (hcontrol : state.control = .halted) :
    Stuck program ctx state :=
  Machine.stuck_of_halted (Vars.decoder_terminal program) hcontrol

theorem Vars.Steps.eq_of_stuck
    {state final : MachineState} {trace : Trace}
    (h : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState)
    (hstuck : Stuck program ctx state) : final = state ∧ trace = [] := by
  obtain ⟨hstate, htrace⟩ := Machine.Steps.eq_of_stuck h hstuck
  exact ⟨MachineState.toState_inj hstate, htrace⟩

theorem stepDialogue_all
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        state.toState trace₂ final₂.toState →
      (trace = trace₂ ∧ final = final₂) ∨
        Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  rcases Machine.Proofs.stepDialogue_all
      (.inr (Vars.decoder_noMalloc hfree))
      (Vars.decoder_exclusive program)
      (Vars.decoder_terminal program)
      (Vars.decoder_noMload hfree) h trace₂ final₂.toState h₂ with
    ⟨htrace, hfinal⟩ | hdiv
  · exact .inl ⟨htrace, MachineState.toState_inj hfinal⟩
  · exact .inr hdiv

theorem runDialogue_all
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        state.toState trace₂ final₂.toState →
      (∃ suffix, Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
          final.toState suffix final₂.toState ∧ trace ++ suffix = trace₂) ∨
      (∃ suffix, Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
          final₂.toState suffix final.toState ∧ trace₂ ++ suffix = trace) ∨
      Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  exact Machine.Proofs.runDialogue_all
    (.inr (Vars.decoder_noMalloc hfree))
    (Vars.decoder_exclusive program)
    (Vars.decoder_terminal program)
    (Vars.decoder_noMload hfree) h trace₂ final₂.toState h₂

theorem fnDialogue_all
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      function globals args trace globals' outcome) :
    ∀ trace₂ globals₂ outcome₂,
      Machine.FunctionEvaluation Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
        function globals args trace₂ globals₂ outcome₂ →
      (trace = trace₂ ∧ globals' = globals₂ ∧ outcome = outcome₂) ∨
        Trace.QueryDivergence trace trace₂ :=
  Machine.Proofs.evalDialogue_all
    (.inr (Vars.decoder_noMalloc hfree))
    (Vars.decoder_exclusive program)
    (Vars.decoder_terminal program)
    (Vars.decoder_noMload hfree) h

theorem Vars.Proofs.Steps.confluence_or_queryDivergence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : MachineState} {trace₁ trace₂ : Trace}
    (h₁ : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace₁ final₁.toState)
    (h₂ : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace₂ final₂.toState) :
    (∃ suffix, Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      final₁.toState suffix final₂.toState ∧ trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      final₂.toState suffix final₁.toState ∧ trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Vars.steps_confluence_or_queryDivergence hfree h₁ h₂

private theorem Vars.jump_control
    {s s' : MachineState} {target : BlockId}
    (h : (Vars.jump program target).run s = .ok ((), s')) :
    ∃ cursor targetBlock, s.control = .running cursor ∧
      program.block? { cursor with block := target } = some targetBlock ∧
      s'.control = .running
        { cursor with block := target, position := targetBlock.startPosition } := by
  cases hctrl : s.control with
  | returned rs =>
    simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hsrc : program.block? cursor with
    | none =>
      simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
        getThe, MonadStateOf.get, hctrl, hsrc, Function.comp, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some sourceBlock =>
      cases htgt : program.block? { cursor with block := target } with
      | none =>
        simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hsrc, htgt, Function.comp, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
      | some targetBlock =>
        refine ⟨cursor, targetBlock, rfl, htgt, ?_⟩
        cases htr : Locals.transfer sourceBlock.outputs targetBlock.inputs s.locals with
        | error e =>
          simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, pure, Except.pure, modify, modifyGet,
            MonadStateOf.modifyGet] at h
        | ok res =>
          obtain ⟨⟨⟩, locals'⟩ := res
          simp only [Vars.jump, StateT.run, bind, StateT.bind, Except.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
            true_and] at h
          rw [← h]

theorem Vars.evaluateTerminator_iret_inv
    {s s' : MachineState}
    (h : (Vars.evaluateTerminator program .iret).run s = .ok ((), s')) :
    ∃ cursor block rs, s.control = .running cursor ∧
      program.block? cursor = some block ∧
      block.outputs.mapM (s.locals.lookup ·) = .ok rs ∧
      s' = { s with control := .returned rs } := by
  cases hctrl : s.control with
  | returned old =>
    simp [Vars.evaluateTerminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [Vars.evaluateTerminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hblock : program.block? cursor with
    | none =>
      simp [Vars.evaluateTerminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
        get, getThe, MonadStateOf.get, hctrl, hblock, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some block =>
      cases hrs : block.outputs.mapM (s.locals.lookup ·) with
      | error e =>
        simp [Vars.evaluateTerminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
          get, getThe, MonadStateOf.get, hctrl, hblock, hrs, liftM, monadLift,
          MonadLift.monadLift, StateT.lift, pure, Except.pure] at h
      | ok rs =>
        refine ⟨cursor, block, rs, rfl, hblock, hrs, ?_⟩
        simp only [Vars.evaluateTerminator, StateT.run, bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hblock, liftM, monadLift,
          MonadLift.monadLift, hrs, StateT.lift, Except.bind, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq, true_and] at h
        exact h.symm

private theorem Vars.evaluateTerminator_preserves_function
    {cursor : Machine.ProgramCursor} {state state' : MachineState} {terminator : Vars.Terminator}
    (hcontrol : state.control = .running cursor)
    (heval : (Vars.evaluateTerminator program terminator).run state = .ok ((), state')) :
    state'.control = .halted ∨ (∃ results, state'.control = .returned results) ∨
      ∃ cursor', state'.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases terminator with
  | halt =>
      have hhalt : (Vars.evaluateTerminator program .halt).run state =
          .ok ((), { state with control := .halted }) := rfl
      rw [hhalt] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      exact .inl rfl
  | jump target =>
      simp only [Vars.evaluateTerminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, -, hcontrol'⟩ :=
        Vars.jump_control heval
      obtain rfl := Machine.MachineControl.running.inj (hsource.symm.trans hcontrol)
      exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | branch condition thenTarget elseTarget =>
      simp only [Vars.evaluateTerminator] at heval
      cases hcondition : state.locals.lookup condition with
      | error error =>
          simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
            MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          simp at heval
      | ok value =>
          simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
            MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          obtain ⟨sourceCursor, targetBlock, hsource, -, hcontrol'⟩ :=
            Vars.jump_control heval
          obtain rfl := Machine.MachineControl.running.inj (hsource.symm.trans hcontrol)
          exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | iret =>
      obtain ⟨_, _, results, -, -, -, rfl⟩ := Vars.evaluateTerminator_iret_inv heval
      exact .inr (.inl ⟨results, rfl⟩)

private theorem Vars.evaluateTerminator_returned_inv
    {state state' : MachineState} {terminator : Vars.Terminator} {results : Array Word}
    (hterm : program.terminatorAt state.control = some terminator)
    (heval : (Vars.evaluateTerminator program terminator).run state = .ok ((), state'))
    (hreturn : state'.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.locals.lookup ·) = .ok results := by
  cases terminator with
  | halt =>
      simp only [Vars.evaluateTerminator] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      cases hreturn
  | jump target =>
      simp only [Vars.evaluateTerminator] at heval
      obtain ⟨_, _, _, -, hcontrol'⟩ := Vars.jump_control heval
      rw [hcontrol'] at hreturn
      cases hreturn
  | branch condition thenTarget elseTarget =>
      simp only [Vars.evaluateTerminator] at heval
      cases hcondition : state.locals.lookup condition with
      | error error =>
          simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
            MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          simp at heval
      | ok value =>
          simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
            MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          obtain ⟨_, _, _, -, hcontrol'⟩ := Vars.jump_control heval
          rw [hcontrol'] at hreturn
          cases hreturn
  | iret =>
      obtain ⟨cursor, block, actual, hcontrol, hblock, houtputs, rfl⟩ :=
        Vars.evaluateTerminator_iret_inv heval
      obtain rfl := Machine.MachineControl.returned.inj hreturn
      cases hposition : cursor.position with
      | statement index => simp [Vars.Program.terminatorAt, hcontrol, hposition] at hterm
      | terminator =>
          have hblockTerminator : block.terminator = .iret := by
            simpa [Vars.Program.terminatorAt, hcontrol, hposition, hblock] using hterm
          exact ⟨cursor, block, hcontrol, hblock, hblockTerminator, houtputs⟩

private theorem genStep_preserves_function
    {cursor : Machine.ProgramCursor} {state final : Machine.State Vars.frame} {trace : Trace}
    (h : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | operation hdecode hfires =>
      change Vars.decode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨position, hnext⟩ := Vars.Program.decodeStmt_next_block hcontrol hstatement
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | operationHalted hdecode hfires => exact .inl rfl
  | internalCall hdecode hfetch hcallee hresume =>
      rename_i callee src dst next values globals' outcome env' control'
      change Vars.decode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨position, hnext⟩ := Vars.Program.decodeStmt_next_block hcontrol hstatement
      change Vars.resume outcome state.environment dst next = some (env', control') at hresume
      cases outcome with
      | returned results =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_returned_eq_some_iff.mp hresume
          subst control'
          exact .inr (.inr ⟨_, hnext, rfl⟩)
      | halted =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_halted_eq_some_iff.mp hresume
          subst control'
          exact .inl rfl
  | control hstep =>
      change Vars.control program state.environment state.globals state.control = _ at hstep
      obtain ⟨terminator, state', -, heval, rfl, rfl, rfl, rfl⟩ :=
        Vars.control_inv.mp hstep
      exact Vars.evaluateTerminator_preserves_function hcontrol heval

theorem Vars.SmallStep.preserves_function
    {cursor : Machine.ProgramCursor} {state final : MachineState} {trace : Trace}
    (h : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  genStep_preserves_function h hcontrol

private theorem genSteps_preserves_function
    {cursor : Machine.ProgramCursor} {state final : Machine.State Vars.frame} {trace : Trace}
    (h : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  exact Machine.Steps.inductionOn
    (motive := fun state _ final _ => state.control = .running cursor →
      final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
        ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn)
    (fun _ hcontrol => .inr (.inr ⟨cursor, hcontrol, rfl⟩))
    (fun _ next ih hcontrol => by
      rcases ih hcontrol with hhalt | ⟨results, hreturn⟩ | ⟨cursor', hcontrol', hfn⟩
      · exact absurd next
          (Machine.stuck_of_halted (Vars.decoder_terminal program) hhalt _ _)
      · exact absurd next
          (Machine.stuck_of_returned (Vars.decoder_terminal program) hreturn _ _)
      · rcases genStep_preserves_function next hcontrol' with
          hhalt | hreturned | ⟨cursor'', hcontrol'', hfn'⟩
        · exact .inl hhalt
        · exact .inr (.inl hreturned)
        · exact .inr (.inr ⟨cursor'', hcontrol'', hfn'.trans hfn⟩))
    h hcontrol

theorem Vars.Proofs.Steps.preserves_function
    {cursor : Machine.ProgramCursor} {state final : MachineState} {trace : Trace}
    (h : Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  genSteps_preserves_function h hcontrol

private theorem genStep_returned_inv
    {state final : Machine.State Vars.frame} {trace : Trace} {results : Array Word}
    (h : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state trace final)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.environment.lookup ·) = .ok results := by
  cases h with
  | operation hdecode hfires =>
      change Vars.decode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨cursor, hnext⟩ := Vars.Program.decodeStmt_next_running hstatement
      rw [hnext] at hreturn
      cases hreturn
  | operationHalted hdecode hfires => cases hreturn
  | internalCall hdecode hfetch hcallee hresume =>
      rename_i callee src dst next values globals' outcome env' control'
      change Vars.decode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨cursor, hnext⟩ := Vars.Program.decodeStmt_next_running hstatement
      change Vars.resume outcome state.environment dst next = some (env', control') at hresume
      cases outcome with
      | returned actual =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_returned_eq_some_iff.mp hresume
          subst control'
          rw [hnext] at hreturn
          cases hreturn
      | halted =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_halted_eq_some_iff.mp hresume
          subst control'
          cases hreturn
  | control hstep =>
      change Vars.control program state.environment state.globals state.control = _ at hstep
      obtain ⟨terminator, state', hterm, heval, rfl, rfl, rfl, rfl⟩ :=
        Vars.control_inv.mp hstep
      exact Vars.evaluateTerminator_returned_inv hterm heval hreturn

theorem Vars.SmallStep.returned_inv
    {state final : MachineState} {trace : Trace} {results : Array Word}
    (h : Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state.toState trace final.toState)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.locals.lookup ·) = .ok results :=
  genStep_returned_inv h hreturn

end Sir
