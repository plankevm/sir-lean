import Sir.Proofs.Decode
import Sir.Generic.Corollaries
import Sir.Spec.WellFormed

namespace Sir

variable {program : Program} {ctx : CallContext}

open Generic

def Generic.GenericState.toMachine (state : GenericState localOperandFrame) : MachineState :=
  ⟨state.globals, state.environment, state.control⟩

theorem MachineState.toGenericState_inj {state₁ state₂ : MachineState}
    (h : state₁.toGenericState = state₂.toGenericState) : state₁ = state₂ := by
  cases state₁
  cases state₂
  cases h
  rfl

namespace Generic.Operation

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

theorem execute_malloc_ok (ctx : CallContext) (allocation : Allocation)
    (globals : Globals) (size : Word) (hsize : allocation.size = size.toNat) :
    execute ctx .mallocUninit allocation globals #[size] =
      .ok (.next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []) := by
  simp [execute, hsize, bind, Except.bind, pure, Except.pure]

theorem execute_mstore32_ok (ctx : CallContext) (globals : Globals)
    (offset value : Word) :
    execute ctx .mstore32 () globals #[offset, value] =
      .ok (.next #[]
        { globals with memory := globals.memory.writeBytes offset value.toByteArray } []) := rfl

theorem execute_mload32_ok (ctx : CallContext) (assumed : Vector UInt8 32)
    (globals : Globals) (offset : Word) :
    execute ctx .mload32 assumed globals #[offset] =
      .ok (.next #[.ofNat (Evm.fromByteArrayBigEndian
        (globals.memory.readBytes offset ⟨assumed.toArray⟩))] globals []) := rfl

end Generic.Operation

theorem fires_of
    {operation : Operation} {src dst : Array VarId} {env env' : Locals}
    {globals globals' : Globals} {operands results : Array Word} {trace : Trace}
    {oracle : operation.Oracle}
    (hfetch : localOperandFrame.fetch env src = .ok operands)
    (hadmissible : operation.Admissible sirMemoryPolicy globals operands oracle)
    (hexecute : operation.execute ctx oracle globals operands =
      .ok (.next results globals' trace))
    (hstore : localOperandFrame.store env dst results = .ok env') :
    localOperandFrame.Fires sirMemoryPolicy ctx operation src dst env globals trace env' globals' :=
  .next hadmissible hfetch hexecute hstore

theorem firesHalt_false
    {operation : Operation} {src : Array VarId} {env : Locals}
    {globals globals' : Globals} {trace : Trace}
    (h : localOperandFrame.FiresHalt sirMemoryPolicy ctx operation src env globals trace globals') :
    False := by
  cases h with
  | halted hadmissible hfetch hexecute =>
      cases operation <;> simp only [Generic.Operation.execute] at hexecute
      all_goals repeat' first | split at hexecute <;>
        simp_all [pure, Except.pure, bind, Except.bind]
      all_goals cases Except.ok.inj hexecute

def Generic.Instruction.Fires {frame : OperandFrame} (instruction : Instruction frame)
    (policy : MemoryPolicy) (ctx : CallContext) (env : frame.Environment) (globals : Globals)
    (trace : Trace) (env' : frame.Environment) (globals' : Globals) : Prop :=
  match instruction.kind with
  | .primitive operation =>
      frame.Fires policy ctx operation instruction.source instruction.destination
        env globals trace env' globals'
  | .icall _ => False

theorem step_statement
    {state : MachineState} {next : MachineControl} {statement : Stmt}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, statement))
    (hfires : (decodeSirStatement statement).Fires sirMemoryPolicy ctx state.locals state.globals
      trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState := by
  generalize hinstruction : decodeSirStatement statement = instruction at hfires
  obtain ⟨kind, src, dst⟩ := instruction
  cases kind with
  | primitive operation =>
      exact GenericStep.operation (operation := operation) (src := src) (dst := dst)
        (by
          change sirDecode program state.control =
            some (⟨Instruction.Kind.primitive operation, src, dst⟩, next)
          simp [sirDecode, hdecode, hinstruction]) hfires
  | icall callee => simp [Generic.Instruction.Fires] at hfires

theorem step_assign
    {state : MachineState} {next : MachineControl} {result : VarId} {expr : Expr}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .assign result expr))
    (hfires : (decodeExpression result expr).Fires sirMemoryPolicy ctx state.locals state.globals
      trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_sstore
    {state : MachineState} {next : MachineControl} {key value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .sstore key value))
    (hfires : (decodeSirStatement (.sstore key value)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_gas
    {state : MachineState} {next : MachineControl} {result : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .gas result))
    (hfires : (decodeSirStatement (.gas result)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_call
    {state : MachineState} {next : MachineControl} {call : Call}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .call call))
    (hfires : (decodeSirStatement (.call call)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_mallocUninit
    {state : MachineState} {next : MachineControl} {result size : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mallocUninit result size))
    (hfires : (decodeSirStatement (.mallocUninit result size)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_mstore32
    {state : MachineState} {next : MachineControl} {offset value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mstore32 offset value))
    (hfires : (decodeSirStatement (.mstore32 offset value)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_mload32
    {state : MachineState} {next : MachineControl} {result offset : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mload32 result offset))
    (hfires : (decodeSirStatement (.mload32 result offset)).Fires sirMemoryPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', locals := locals', control := next } : MachineState).toGenericState :=
  step_statement hdecode hfires

theorem step_terminator
    {state state' : MachineState} {terminator : Terminator}
    (hterm : program.terminatorAt state.control = some terminator)
    (heval : (eval_terminator program terminator).run state = .ok ((), state')) :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState [] state'.toGenericState := by
  apply GenericStep.control
  apply sirControl_inv.mpr
  exact ⟨terminator, state', hterm, heval, rfl, rfl, rfl, rfl⟩

theorem step_icall
    {state : MachineState} {next : MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values results : Array Word} {trace : Trace}
    {globals' : Globals} {locals' : Locals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx callee
      state.globals values trace globals' (.returned results))
    (hbind : Locals.bindReturns state.locals dests results = .ok locals') :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      { state with globals := globals', locals := locals', control := next }.toGenericState := by
  apply GenericStep.internalCall
  · change sirDecode program state.control =
      some (⟨Instruction.Kind.icall callee, args, dests⟩, next)
    simp [sirDecode, hdecode, decodeSirStatement]
  · exact hargs
  · exact hcallee
  · exact sirResume_returned_eq_some_iff.mpr ⟨hbind, rfl⟩

theorem step_icallHalted
    {state : MachineState} {next : MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values : Array Word} {trace : Trace}
    {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx callee
      state.globals values trace globals' .halted) :
    GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state.toGenericState trace
      ({ globals := globals', control := .halted } : MachineState).toGenericState := by
  apply GenericStep.internalCall
  · change sirDecode program state.control =
      some (⟨Instruction.Kind.icall callee, args, dests⟩, next)
    simp [sirDecode, hdecode, decodeSirStatement]
  · exact hargs
  · exact hcallee
  · exact sirResume_halted state.locals dests next

theorem EvalFn.returned
    {function : FunctionId} {globals : Globals} {args results : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      initial.toGenericState trace exit.toGenericState)
    (hreturn : exit.control = .returned results) :
    GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx function globals args
      trace exit.globals (.returned results) :=
  GenericFunctionEvaluation.returned (initial := initial.toGenericState) (exit := exit.toGenericState)
    (by simp [sirEntry_eq, hentry]) hrun hreturn

theorem EvalFn.halted
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      initial.toGenericState trace exit.toGenericState)
    (hhalt : exit.control = .halted) :
    GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx function globals args
      trace exit.globals .halted :=
  GenericFunctionEvaluation.halted (initial := initial.toGenericState) (exit := exit.toGenericState)
    (by simp [sirEntry_eq, hentry]) hrun hhalt

@[elab_as_elim]
theorem Steps.inductionOn {program : Program} {ctx : CallContext}
    {motive : (state : MachineState) → (trace : Trace) → (final : MachineState) →
      GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        state.toGenericState trace final.toGenericState → Prop}
    (refl : ∀ state, motive state [] state .refl)
    (tail : ∀ {state middle final : MachineState} {trace₁ trace₂ : Trace}
      (start : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        state.toGenericState trace₁ middle.toGenericState)
      (next : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        middle.toGenericState trace₂ final.toGenericState),
      motive state trace₁ middle start →
        motive state (trace₁ ++ trace₂) final (start.tail next))
    {state final : MachineState} {trace : Trace}
    (h : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState) : motive state trace final h := by
  simpa using Generic.GenericSteps.inductionOn
    (motive := fun state trace final h =>
      motive state.toMachine trace final.toMachine h)
    (fun state => refl state.toMachine)
    (fun {state middle final trace₁ trace₂} start next ih =>
      tail (state := state.toMachine) (middle := middle.toMachine)
        (final := final.toMachine) (trace₁ := trace₁) (trace₂ := trace₂)
        (by simpa using start) (by simpa using next) (by simpa using ih)) h

def Stuck (program : Program) (ctx : CallContext) (state : MachineState) : Prop :=
  Generic.Stuck (sirDecoder program) sirMemoryPolicy ctx state.toGenericState

theorem stuck_of_returned
    {state : MachineState} {results : Array Word}
    (hcontrol : state.control = .returned results) :
    Stuck program ctx state :=
  Generic.stuck_of_returned (Generic.sirDecoder_terminal program) hcontrol

theorem stuck_of_halted
    {state : MachineState} (hcontrol : state.control = .halted) :
    Stuck program ctx state :=
  Generic.stuck_of_halted (Generic.sirDecoder_terminal program) hcontrol

theorem Steps.eq_of_stuck
    {state final : MachineState} {trace : Trace}
    (h : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState)
    (hstuck : Stuck program ctx state) : final = state ∧ trace = [] := by
  obtain ⟨hstate, htrace⟩ := Generic.GenericSteps.eq_of_stuck h hstuck
  exact ⟨MachineState.toGenericState_inj hstate, htrace⟩

theorem stepDialogue_all
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        state.toGenericState trace₂ final₂.toGenericState →
      (trace = trace₂ ∧ final = final₂) ∨
        Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  rcases Generic.stepDialogue_all
      (.inr (Generic.sirDecoder_noMalloc hfree))
      (Generic.sirDecoder_exclusive program)
      (Generic.sirDecoder_terminal program)
      (Generic.sirDecoder_noMload hfree) h trace₂ final₂.toGenericState h₂ with
    ⟨htrace, hfinal⟩ | hdiv
  · exact .inl ⟨htrace, MachineState.toGenericState_inj hfinal⟩
  · exact .inr hdiv

theorem runDialogue_all
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        state.toGenericState trace₂ final₂.toGenericState →
      (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
          final.toGenericState suffix final₂.toGenericState ∧ trace ++ suffix = trace₂) ∨
      (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
          final₂.toGenericState suffix final.toGenericState ∧ trace₂ ++ suffix = trace) ∨
      Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  exact Generic.runDialogue_all
    (.inr (Generic.sirDecoder_noMalloc hfree))
    (Generic.sirDecoder_exclusive program)
    (Generic.sirDecoder_terminal program)
    (Generic.sirDecoder_noMload hfree) h trace₂ final₂.toGenericState h₂

theorem fnDialogue_all
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      function globals args trace globals' outcome) :
    ∀ trace₂ globals₂ outcome₂,
      GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
        function globals args trace₂ globals₂ outcome₂ →
      (trace = trace₂ ∧ globals' = globals₂ ∧ outcome = outcome₂) ∨
        Trace.QueryDivergence trace trace₂ :=
  Generic.evalDialogue_all
    (.inr (Generic.sirDecoder_noMalloc hfree))
    (Generic.sirDecoder_exclusive program)
    (Generic.sirDecoder_terminal program)
    (Generic.sirDecoder_noMload hfree) h

theorem Steps.confluence_or_queryDivergence_proof
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : MachineState} {trace₁ trace₂ : Trace}
    (h₁ : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace₁ final₁.toGenericState)
    (h₂ : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace₂ final₂.toGenericState) :
    (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      final₁.toGenericState suffix final₂.toGenericState ∧ trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      final₂.toGenericState suffix final₁.toGenericState ∧ trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Generic.sir_steps_confluence_or_queryDivergence hfree h₁ h₂

private theorem eval_jump_control
    {s s' : MachineState} {target : BlockId}
    (h : (eval_jump program target).run s = .ok ((), s')) :
    ∃ cursor targetBlock, s.control = .running cursor ∧
      program.block? { cursor with block := target } = some targetBlock ∧
      s'.control = .running
        { cursor with block := target, position := targetBlock.startPosition } := by
  cases hctrl : s.control with
  | returned rs =>
    simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hsrc : program.block? cursor with
    | none =>
      simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
        getThe, MonadStateOf.get, hctrl, hsrc, Function.comp, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some sourceBlock =>
      cases htgt : program.block? { cursor with block := target } with
      | none =>
        simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hsrc, htgt, Function.comp, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
      | some targetBlock =>
        refine ⟨cursor, targetBlock, rfl, htgt, ?_⟩
        cases htr : Locals.transfer sourceBlock.outputs targetBlock.inputs s.locals with
        | error e =>
          simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, pure, Except.pure, modify, modifyGet,
            MonadStateOf.modifyGet] at h
        | ok res =>
          obtain ⟨⟨⟩, locals'⟩ := res
          simp only [eval_jump, StateT.run, bind, StateT.bind, Except.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
            true_and] at h
          rw [← h]

theorem eval_terminator_iret_inv
    {s s' : MachineState}
    (h : (eval_terminator program .iret).run s = .ok ((), s')) :
    ∃ cursor block rs, s.control = .running cursor ∧
      program.block? cursor = some block ∧
      block.outputs.mapM (s.locals.lookup ·) = .ok rs ∧
      s' = { s with control := .returned rs } := by
  cases hctrl : s.control with
  | returned old =>
    simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hblock : program.block? cursor with
    | none =>
      simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
        get, getThe, MonadStateOf.get, hctrl, hblock, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some block =>
      cases hrs : block.outputs.mapM (s.locals.lookup ·) with
      | error e =>
        simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
          get, getThe, MonadStateOf.get, hctrl, hblock, hrs, liftM, monadLift,
          MonadLift.monadLift, StateT.lift, pure, Except.pure] at h
      | ok rs =>
        refine ⟨cursor, block, rs, rfl, hblock, hrs, ?_⟩
        simp only [eval_terminator, StateT.run, bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hblock, liftM, monadLift,
          MonadLift.monadLift, hrs, StateT.lift, Except.bind, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq, true_and] at h
        exact h.symm

private theorem eval_terminator_preserves_function
    {cursor : ProgramCursor} {state state' : MachineState} {terminator : Terminator}
    (hcontrol : state.control = .running cursor)
    (heval : (eval_terminator program terminator).run state = .ok ((), state')) :
    state'.control = .halted ∨ (∃ results, state'.control = .returned results) ∨
      ∃ cursor', state'.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases terminator with
  | halt =>
      have hhalt : (eval_terminator program .halt).run state =
          .ok ((), { state with control := .halted }) := rfl
      rw [hhalt] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      exact .inl rfl
  | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, -, hcontrol'⟩ :=
        eval_jump_control heval
      obtain rfl := MachineControl.running.inj (hsource.symm.trans hcontrol)
      exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
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
            eval_jump_control heval
          obtain rfl := MachineControl.running.inj (hsource.symm.trans hcontrol)
          exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | iret =>
      obtain ⟨_, _, results, -, -, -, rfl⟩ := eval_terminator_iret_inv heval
      exact .inr (.inl ⟨results, rfl⟩)

private theorem eval_terminator_returned_inv
    {state state' : MachineState} {terminator : Terminator} {results : Array Word}
    (hterm : program.terminatorAt state.control = some terminator)
    (heval : (eval_terminator program terminator).run state = .ok ((), state'))
    (hreturn : state'.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.locals.lookup ·) = .ok results := by
  cases terminator with
  | halt =>
      simp only [eval_terminator] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      cases hreturn
  | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨_, _, _, -, hcontrol'⟩ := eval_jump_control heval
      rw [hcontrol'] at hreturn
      cases hreturn
  | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
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
          obtain ⟨_, _, _, -, hcontrol'⟩ := eval_jump_control heval
          rw [hcontrol'] at hreturn
          cases hreturn
  | iret =>
      obtain ⟨cursor, block, actual, hcontrol, hblock, houtputs, rfl⟩ :=
        eval_terminator_iret_inv heval
      obtain rfl := MachineControl.returned.inj hreturn
      cases hposition : cursor.position with
      | statement index => simp [Program.terminatorAt, hcontrol, hposition] at hterm
      | terminator =>
          have hblockTerminator : block.terminator = .iret := by
            simpa [Program.terminatorAt, hcontrol, hposition, hblock] using hterm
          exact ⟨cursor, block, hcontrol, hblock, hblockTerminator, houtputs⟩

private theorem genStep_preserves_function
    {cursor : ProgramCursor} {state final : GenericState localOperandFrame} {trace : Trace}
    (h : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | operation hdecode hfires =>
      change sirDecode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := sirDecode_inv.mp hdecode
      obtain ⟨position, hnext⟩ := Program.decodeStmt_next_block hcontrol hstatement
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | operationHalted hdecode hfires => exact .inl rfl
  | internalCall hdecode hfetch hcallee hresume =>
      rename_i callee src dst next values globals' outcome env' control'
      change sirDecode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := sirDecode_inv.mp hdecode
      obtain ⟨position, hnext⟩ := Program.decodeStmt_next_block hcontrol hstatement
      change sirResume outcome state.environment dst next = some (env', control') at hresume
      cases outcome with
      | returned results =>
          obtain ⟨-, hcontrol'⟩ := sirResume_returned_eq_some_iff.mp hresume
          subst control'
          exact .inr (.inr ⟨_, hnext, rfl⟩)
      | halted =>
          obtain ⟨-, hcontrol'⟩ := sirResume_halted_eq_some_iff.mp hresume
          subst control'
          exact .inl rfl
  | control hstep =>
      change sirControl program state.environment state.globals state.control = _ at hstep
      obtain ⟨terminator, state', -, heval, rfl, rfl, rfl, rfl⟩ :=
        sirControl_inv.mp hstep
      exact eval_terminator_preserves_function hcontrol heval

theorem SmallStep.preserves_function
    {cursor : ProgramCursor} {state final : MachineState} {trace : Trace}
    (h : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  genStep_preserves_function h hcontrol

private theorem genSteps_preserves_function
    {cursor : ProgramCursor} {state final : GenericState localOperandFrame} {trace : Trace}
    (h : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  exact Generic.GenericSteps.inductionOn
    (motive := fun state _ final _ => state.control = .running cursor →
      final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
        ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn)
    (fun _ hcontrol => .inr (.inr ⟨cursor, hcontrol, rfl⟩))
    (fun _ next ih hcontrol => by
      rcases ih hcontrol with hhalt | ⟨results, hreturn⟩ | ⟨cursor', hcontrol', hfn⟩
      · exact absurd next
          (Generic.stuck_of_halted (Generic.sirDecoder_terminal program) hhalt _ _)
      · exact absurd next
          (Generic.stuck_of_returned (Generic.sirDecoder_terminal program) hreturn _ _)
      · rcases genStep_preserves_function next hcontrol' with
          hhalt | hreturned | ⟨cursor'', hcontrol'', hfn'⟩
        · exact .inl hhalt
        · exact .inr (.inl hreturned)
        · exact .inr (.inr ⟨cursor'', hcontrol'', hfn'.trans hfn⟩))
    h hcontrol

theorem Steps.preserves_function_proof
    {cursor : ProgramCursor} {state final : MachineState} {trace : Trace}
    (h : GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  genSteps_preserves_function h hcontrol

private theorem genStep_returned_inv
    {state final : GenericState localOperandFrame} {trace : Trace} {results : Array Word}
    (h : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx state trace final)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.environment.lookup ·) = .ok results := by
  cases h with
  | operation hdecode hfires =>
      change sirDecode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := sirDecode_inv.mp hdecode
      obtain ⟨cursor, hnext⟩ := Program.decodeStmt_next_running hstatement
      rw [hnext] at hreturn
      cases hreturn
  | operationHalted hdecode hfires => cases hreturn
  | internalCall hdecode hfetch hcallee hresume =>
      rename_i callee src dst next values globals' outcome env' control'
      change sirDecode program state.control = _ at hdecode
      obtain ⟨statement, hstatement, -⟩ := sirDecode_inv.mp hdecode
      obtain ⟨cursor, hnext⟩ := Program.decodeStmt_next_running hstatement
      change sirResume outcome state.environment dst next = some (env', control') at hresume
      cases outcome with
      | returned actual =>
          obtain ⟨-, hcontrol'⟩ := sirResume_returned_eq_some_iff.mp hresume
          subst control'
          rw [hnext] at hreturn
          cases hreturn
      | halted =>
          obtain ⟨-, hcontrol'⟩ := sirResume_halted_eq_some_iff.mp hresume
          subst control'
          cases hreturn
  | control hstep =>
      change sirControl program state.environment state.globals state.control = _ at hstep
      obtain ⟨terminator, state', hterm, heval, rfl, rfl, rfl, rfl⟩ :=
        sirControl_inv.mp hstep
      exact eval_terminator_returned_inv hterm heval hreturn

theorem SmallStep.returned_inv
    {state final : MachineState} {trace : Trace} {results : Array Word}
    (h : GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.locals.lookup ·) = .ok results :=
  genStep_returned_inv h hreturn

end Sir
