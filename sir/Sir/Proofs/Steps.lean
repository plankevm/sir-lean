import Sir.Proofs.Decode
import Sir.Generic.Corollaries
import Sir.Spec.WellFormed

namespace Sir

variable {program : Program} {ctx : CallContext}

open Generic

def Generic.GenState.toMachine (state : GenState localsFrame) : MachineState :=
  ⟨state.globals, state.env, state.control⟩

@[simp]
theorem MachineState.gen_globals (state : MachineState) : state.gen.globals = state.globals := rfl

@[simp]
theorem MachineState.gen_env (state : MachineState) : state.gen.env = state.locals := rfl

@[simp]
theorem MachineState.gen_control (state : MachineState) : state.gen.control = state.control := rfl

theorem MachineState.gen_inj {state₁ state₂ : MachineState}
    (h : state₁.gen = state₂.gen) : state₁ = state₂ := by
  cases state₁
  cases state₂
  cases h
  rfl

@[simp]
theorem toMachine_gen (state : MachineState) : state.gen.toMachine = state := rfl

@[simp]
theorem gen_toMachine (state : GenState localsFrame) : state.toMachine.gen = state := rfl

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

theorem execute_constant_inv
    {ctx : CallContext} {value : Word} {globals : Globals} {operands : Array Word}
    {outcome : Outcome}
    (h : execute ctx (.constant value) () globals operands = .ok outcome) :
    outcome = .next #[value] globals [] :=
  (Except.ok.inj h).symm

theorem execute_copy_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .copy () globals operands = .ok outcome) :
    ∃ value, operands[0]? = some value ∧ outcome = .next #[value] globals [] := by
  change (do
    let some value := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 1)
    return Outcome.next #[value] globals []) = Except.ok outcome at h
  split at h
  next value hvalue => exact ⟨value, hvalue, (Except.ok.inj h).symm⟩
  next => contradiction

theorem execute_add_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .add () globals operands = .ok outcome) :
    ∃ lhs rhs, operands[0]? = some lhs ∧ operands[1]? = some rhs ∧
      outcome = .next #[Evm.UInt256.add lhs rhs] globals [] := by
  change (do
    let some lhs := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some rhs := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    return Outcome.next #[Evm.UInt256.add lhs rhs] globals []) = Except.ok outcome at h
  split at h
  next lhs hlhs =>
    split at h
    next rhs hrhs => exact ⟨lhs, rhs, hlhs, hrhs, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_lt_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .lt () globals operands = .ok outcome) :
    ∃ lhs rhs, operands[0]? = some lhs ∧ operands[1]? = some rhs ∧
      outcome = .next #[Evm.UInt256.lt lhs rhs] globals [] := by
  change (do
    let some lhs := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some rhs := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    return Outcome.next #[Evm.UInt256.lt lhs rhs] globals []) = Except.ok outcome at h
  split at h
  next lhs hlhs =>
    split at h
    next rhs hrhs => exact ⟨lhs, rhs, hlhs, hrhs, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_sload_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .sload () globals operands = .ok outcome) :
    ∃ key, operands[0]? = some key ∧
      outcome = .next #[globals.world.loadStorage ctx.self key] globals [] := by
  change (do
    let some key := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 1)
    return Outcome.next #[globals.world.loadStorage ctx.self key] globals []) =
      Except.ok outcome at h
  split at h
  next key hkey => exact ⟨key, hkey, (Except.ok.inj h).symm⟩
  next => contradiction

theorem execute_sstore_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .sstore () globals operands = .ok outcome) :
    ∃ key value, operands[0]? = some key ∧ operands[1]? = some value ∧
      outcome = .next #[]
        { globals with world := globals.world.storeStorage ctx.self key value } [] := by
  change (do
    let some key := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some value := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    return Outcome.next #[]
      { globals with world := globals.world.storeStorage ctx.self key value } []) =
      Except.ok outcome at h
  split at h
  next key hkey =>
    split at h
    next value hvalue => exact ⟨key, value, hkey, hvalue, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_gas_inv
    {ctx : CallContext} {answer : Word} {globals : Globals} {operands : Array Word}
    {outcome : Outcome} (h : execute ctx .gas answer globals operands = .ok outcome) :
    outcome = .next #[answer] globals [.gas answer] :=
  (Except.ok.inj h).symm

theorem execute_call_inv
    {ctx : CallContext} {result : CallResult} {globals : Globals}
    {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .call result globals operands = .ok outcome) :
    ∃ callee gas,
      operands[0]? = some callee ∧ operands[1]? = some gas ∧
      outcome = .next #[Evm.UInt256.fromBool result.success]
        { globals with returnData := result.output, world := result.world' }
        [.call {
          input := { target := .ofUInt256 callee, gas := gas, world := globals.world }
          result := result }] := by
  change (do
    let some callee := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some gasValue := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let input : CallInput :=
      { target := .ofUInt256 callee, gas := gasValue, world := globals.world }
    let record : CallRecord := { input, result }
    return Outcome.next #[Evm.UInt256.fromBool result.success]
      { globals with returnData := result.output, world := result.world' }
      [.call record]) = Except.ok outcome at h
  split at h
  next callee hcallee =>
    split at h
    next gasValue hgas =>
      exact ⟨callee, gasValue, hcallee, hgas, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_malloc_inv
    {ctx : CallContext} {allocation : Allocation} {globals : Globals}
    {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .mallocUninit allocation globals operands = .ok outcome) :
    ∃ size, operands[0]? = some size ∧ allocation.size = size.toNat ∧
      outcome = .next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } [] := by
  change (do
    let some size := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 1)
    if allocation.size ≠ size.toNat then
      throw IRError.invalidAlloc
    return Outcome.next #[allocation.offset]
      { globals with memory := globals.memory.push allocation } []) = Except.ok outcome at h
  split at h
  next size hsize =>
    split at h
    next => contradiction
    next hvalid =>
      exact ⟨size, hsize, not_ne_iff.mp hvalid, (Except.ok.inj h).symm⟩
  next => contradiction

theorem execute_mstore32_inv
    {ctx : CallContext} {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .mstore32 () globals operands = .ok outcome) :
    ∃ offset value, operands[0]? = some offset ∧ operands[1]? = some value ∧
      outcome = .next #[]
        { globals with memory := globals.memory.writeBytes offset value.toByteArray } [] := by
  change (do
    let some offset := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some value := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    return Outcome.next #[]
      { globals with memory := globals.memory.writeBytes offset value.toByteArray } []) =
      Except.ok outcome at h
  split at h
  next offset hoffset =>
    split at h
    next value hvalue => exact ⟨offset, value, hoffset, hvalue, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_mload32_inv
    {ctx : CallContext} {assumed : Vector UInt8 32} {globals : Globals}
    {operands : Array Word} {outcome : Outcome}
    (h : execute ctx .mload32 assumed globals operands = .ok outcome) :
    ∃ offset, operands[0]? = some offset ∧
      outcome = .next #[.ofNat (Evm.fromByteArrayBigEndian
        (globals.memory.readBytes offset ⟨assumed.toArray⟩))] globals [] := by
  change (do
    let some offset := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 1)
    let bytes := globals.memory.readBytes offset ⟨assumed.toArray⟩
    return Outcome.next #[.ofNat (Evm.fromByteArrayBigEndian bytes)] globals []) =
      Except.ok outcome at h
  split at h
  next offset hoffset => exact ⟨offset, hoffset, (Except.ok.inj h).symm⟩
  next => contradiction

end Generic.Operation

theorem fires_of
    {operation : Operation} {src dst : Array VarId} {env env' : Locals}
    {globals globals' : Globals} {operands results : Array Word} {trace : Trace}
    {oracle : operation.Oracle}
    (hfetch : localsFrame.fetch env src = .ok operands)
    (hadmissible : operation.Admissible sirPolicy globals operands oracle)
    (hexecute : operation.execute ctx oracle globals operands =
      .ok (.next results globals' trace))
    (hstore : localsFrame.store env dst results = .ok env') :
    localsFrame.Fires sirPolicy ctx operation src dst env globals trace env' globals' :=
  .next hadmissible hfetch hexecute hstore

def Generic.Instr.Fires {frame : OpFrame} (instruction : Instr frame)
    (policy : MemoryPolicy) (ctx : CallContext) (env : frame.Env) (globals : Globals)
    (trace : Trace) (env' : frame.Env) (globals' : Globals) : Prop :=
  match instruction.kind with
  | .primitive operation =>
      frame.Fires policy ctx operation instruction.src instruction.dst
        env globals trace env' globals'
  | .icall _ => False

theorem step_statement_gen
    {state : MachineState} {next : MachineControl} {statement : Stmt}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, statement))
    (hfires : (decodeSirStmt statement).Fires sirPolicy ctx state.locals state.globals
      trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen := by
  generalize hinstruction : decodeSirStmt statement = instruction at hfires
  obtain ⟨kind, src, dst⟩ := instruction
  cases kind with
  | primitive operation =>
      exact GenStep.op (operation := operation) (src := src) (dst := dst)
        (by
          change sirDecode program state.control =
            some (⟨Instr.Kind.primitive operation, src, dst⟩, next)
          simp [sirDecode, hdecode, hinstruction]) hfires
  | icall callee => simp [Generic.Instr.Fires] at hfires

theorem step_assign_gen
    {state : MachineState} {next : MachineControl} {result : VarId} {expr : Expr}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .assign result expr))
    (hfires : (decodeExpr result expr).Fires sirPolicy ctx state.locals state.globals
      trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_sstore_gen
    {state : MachineState} {next : MachineControl} {key value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .sstore key value))
    (hfires : (decodeSirStmt (.sstore key value)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_gas_gen
    {state : MachineState} {next : MachineControl} {result : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .gas result))
    (hfires : (decodeSirStmt (.gas result)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_call_gen
    {state : MachineState} {next : MachineControl} {call : Call}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .call call))
    (hfires : (decodeSirStmt (.call call)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_mallocUninit_gen
    {state : MachineState} {next : MachineControl} {result size : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mallocUninit result size))
    (hfires : (decodeSirStmt (.mallocUninit result size)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_mstore32_gen
    {state : MachineState} {next : MachineControl} {offset value : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mstore32 offset value))
    (hfires : (decodeSirStmt (.mstore32 offset value)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_mload32_gen
    {state : MachineState} {next : MachineControl} {result offset : VarId}
    {trace : Trace} {locals' : Locals} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .mload32 result offset))
    (hfires : (decodeSirStmt (.mload32 result offset)).Fires sirPolicy ctx
      state.locals state.globals trace locals' globals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', locals := locals', control := next } : MachineState).gen :=
  step_statement_gen hdecode hfires

theorem step_terminator_gen
    {state state' : MachineState} {terminator : Terminator}
    (hterm : program.terminatorAt state.control = some terminator)
    (heval : (eval_terminator program terminator).run state = .ok ((), state')) :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen [] state'.gen := by
  apply GenStep.control
  apply sirControl_inv.mpr
  exact ⟨terminator, state', hterm, heval, rfl, rfl, rfl, rfl⟩

theorem step_icall_gen
    {state : MachineState} {next : MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values results : Array Word} {trace : Trace}
    {globals' : Globals} {locals' : Locals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx callee
      state.globals values trace globals' (.returned results))
    (hbind : Locals.bindReturns state.locals dests results = .ok locals') :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      { state with globals := globals', locals := locals', control := next }.gen := by
  apply GenStep.icall
  · change sirDecode program state.control =
      some (⟨Instr.Kind.icall callee, args, dests⟩, next)
    simp [sirDecode, hdecode, decodeSirStmt]
  · exact hargs
  · exact hcallee
  · exact sirResume_returned_eq_some_iff.mpr ⟨hbind, rfl⟩

theorem step_icallHalted_gen
    {state : MachineState} {next : MachineControl} {callee : FunctionId}
    {args dests : Array VarId} {values : Array Word} {trace : Trace}
    {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx callee
      state.globals values trace globals' .halted) :
    GenStep localsFrame (sirDecoder program) sirPolicy ctx state.gen trace
      ({ globals := globals', control := .halted } : MachineState).gen := by
  apply GenStep.icall
  · change sirDecode program state.control =
      some (⟨Instr.Kind.icall callee, args, dests⟩, next)
    simp [sirDecode, hdecode, decodeSirStmt]
  · exact hargs
  · exact hcallee
  · exact sirResume_halted state.locals dests next

theorem evalFn_returned_gen
    {function : FunctionId} {globals : Globals} {args results : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      initial.gen trace exit.gen)
    (hreturn : exit.control = .returned results) :
    GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx function globals args
      trace exit.globals (.returned results) :=
  GenEvalFn.returned (initial := initial.gen) (exit := exit.gen)
    (by simp [sirEntry_eq, hentry]) hrun hreturn

theorem evalFn_halted_gen
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace : Trace} {initial exit : MachineState}
    (hentry : program.callState? function globals args = some initial)
    (hrun : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      initial.gen trace exit.gen)
    (hhalt : exit.control = .halted) :
    GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx function globals args
      trace exit.globals .halted :=
  GenEvalFn.halted (initial := initial.gen) (exit := exit.gen)
    (by simp [sirEntry_eq, hentry]) hrun hhalt

@[elab_as_elim]
theorem Steps.inductionOn_gen {program : Program} {ctx : CallContext}
    {motive : (state : MachineState) → (trace : Trace) → (final : MachineState) →
      GenSteps localsFrame (sirDecoder program) sirPolicy ctx
        state.gen trace final.gen → Prop}
    (refl : ∀ state, motive state [] state .refl)
    (tail : ∀ {state middle final : MachineState} {trace₁ trace₂ : Trace}
      (start : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
        state.gen trace₁ middle.gen)
      (next : GenStep localsFrame (sirDecoder program) sirPolicy ctx
        middle.gen trace₂ final.gen),
      motive state trace₁ middle start →
        motive state (trace₁ ++ trace₂) final (start.tail next))
    {state final : MachineState} {trace : Trace}
    (h : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen) : motive state trace final h := by
  simpa using Generic.GenSteps.inductionOn
    (motive := fun state trace final h =>
      motive state.toMachine trace final.toMachine h)
    (fun state => refl state.toMachine)
    (fun {state middle final trace₁ trace₂} start next ih =>
      tail (state := state.toMachine) (middle := middle.toMachine)
        (final := final.toMachine) (trace₁ := trace₁) (trace₂ := trace₂)
        (by simpa using start) (by simpa using next) (by simpa using ih)) h

theorem Steps.single_gen
    {state final : MachineState} {trace : Trace}
    (step : GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen) :
    GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen :=
  Generic.GenSteps.single step

theorem Steps.trans_gen
    {state middle final : MachineState} {trace₁ trace₂ : Trace}
    (h₁ : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace₁ middle.gen)
    (h₂ : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      middle.gen trace₂ final.gen) :
    GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen (trace₁ ++ trace₂) final.gen := by
  refine (Generic.GenSteps.inductionOn
    (motive := fun start trace₂ final _ => start = middle.gen →
      GenSteps localsFrame (sirDecoder program) sirPolicy ctx
        state.gen (trace₁ ++ trace₂) final)
    (fun start hstart => by
      subst start
      simpa using h₁)
    (fun _ next ih hstart => by
      simpa [List.append_assoc] using Generic.GenSteps.tail (ih hstart) next)
    h₂) rfl

theorem Steps.head_gen
    {state middle final : MachineState} {trace₁ trace₂ : Trace}
    (step : GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace₁ middle.gen)
    (rest : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      middle.gen trace₂ final.gen) :
    GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen (trace₁ ++ trace₂) final.gen :=
  Steps.trans_gen (Steps.single_gen step) rest

def Stuck_gen (program : Program) (ctx : CallContext) (state : MachineState) : Prop :=
  Generic.Stuck (sirDecoder program) sirPolicy ctx state.gen

theorem stuck_of_returned_gen
    {state : MachineState} {results : Array Word}
    (hcontrol : state.control = .returned results) :
    Stuck_gen program ctx state :=
  Generic.stuck_of_returned (Generic.sirDecoder_terminal program) hcontrol

theorem stuck_of_halted_gen
    {state : MachineState} (hcontrol : state.control = .halted) :
    Stuck_gen program ctx state :=
  Generic.stuck_of_halted (Generic.sirDecoder_terminal program) hcontrol

theorem Steps.head_decomp_gen
    {state final : MachineState} {trace : Trace}
    (h : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen) :
    (state = final ∧ trace = []) ∨
      ∃ (middle : MachineState) (trace₁ trace₂ : Trace),
        GenStep localsFrame (sirDecoder program) sirPolicy ctx
          state.gen trace₁ middle.gen ∧
        GenSteps localsFrame (sirDecoder program) sirPolicy ctx
          middle.gen trace₂ final.gen ∧
        trace = trace₁ ++ trace₂ := by
  rcases Generic.GenSteps.headDecomp h with ⟨hstate, htrace⟩ |
      ⟨middle, trace₁, trace₂, step, rest, htrace⟩
  · exact .inl ⟨MachineState.gen_inj hstate, htrace⟩
  · exact .inr ⟨middle.toMachine, trace₁, trace₂, step, rest, htrace⟩

theorem Steps.eq_of_stuck_gen
    {state final : MachineState} {trace : Trace}
    (h : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen)
    (hstuck : Stuck_gen program ctx state) : final = state ∧ trace = [] := by
  obtain ⟨hstate, htrace⟩ := Generic.GenSteps.eq_of_stuck h hstuck
  exact ⟨MachineState.gen_inj hstate, htrace⟩

theorem stepDialogue_all_gen
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      GenStep localsFrame (sirDecoder program) sirPolicy ctx
        state.gen trace₂ final₂.gen →
      (trace = trace₂ ∧ final = final₂) ∨
        Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  rcases Generic.stepDialogue_all
      (.inr (Generic.sirDecoder_noMalloc hfree))
      (Generic.sirDecoder_exclusive program)
      (Generic.sirDecoder_terminal program)
      (Generic.sirDecoder_noMload hfree) h trace₂ final₂.gen h₂ with
    ⟨htrace, hfinal⟩ | hdiv
  · exact .inl ⟨htrace, MachineState.gen_inj hfinal⟩
  · exact .inr hdiv

theorem runDialogue_all_gen
    (hfree : program.MemOracleFree)
    {state final : MachineState} {trace : Trace}
    (h : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen) :
    ∀ (trace₂ : Trace) (final₂ : MachineState),
      GenSteps localsFrame (sirDecoder program) sirPolicy ctx
        state.gen trace₂ final₂.gen →
      (∃ suffix, GenSteps localsFrame (sirDecoder program) sirPolicy ctx
          final.gen suffix final₂.gen ∧ trace ++ suffix = trace₂) ∨
      (∃ suffix, GenSteps localsFrame (sirDecoder program) sirPolicy ctx
          final₂.gen suffix final.gen ∧ trace₂ ++ suffix = trace) ∨
      Trace.QueryDivergence trace trace₂ := by
  intro trace₂ final₂ h₂
  exact Generic.runDialogue_all
    (.inr (Generic.sirDecoder_noMalloc hfree))
    (Generic.sirDecoder_exclusive program)
    (Generic.sirDecoder_terminal program)
    (Generic.sirDecoder_noMload hfree) h trace₂ final₂.gen h₂

theorem fnDialogue_all_gen
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx
      function globals args trace globals' outcome) :
    ∀ trace₂ globals₂ outcome₂,
      GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx
        function globals args trace₂ globals₂ outcome₂ →
      (trace = trace₂ ∧ globals' = globals₂ ∧ outcome = outcome₂) ∨
        Trace.QueryDivergence trace trace₂ :=
  Generic.evalDialogue_all
    (.inr (Generic.sirDecoder_noMalloc hfree))
    (Generic.sirDecoder_exclusive program)
    (Generic.sirDecoder_terminal program)
    (Generic.sirDecoder_noMload hfree) h

theorem Steps.confluence_or_queryDivergence_proof_gen
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : MachineState} {trace₁ trace₂ : Trace}
    (h₁ : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace₁ final₁.gen)
    (h₂ : GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace₂ final₂.gen) :
    (∃ suffix, GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      final₁.gen suffix final₂.gen ∧ trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, GenSteps localsFrame (sirDecoder program) sirPolicy ctx
      final₂.gen suffix final₁.gen ∧ trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Generic.sir_steps_confluence_or_queryDivergence hfree h₁ h₂

@[elab_as_elim]
theorem Steps.inductionOn {program : Program} {ctx : CallContext}
    {motive : (s : MachineState) → (t : Trace) → (e : MachineState) →
      Steps program ctx s t e → Prop}
    (refl : ∀ s, motive s [] s .refl)
    (tail : ∀ {s mid s' : MachineState} {t₁ t₂ : Trace}
      (start : Steps program ctx s t₁ mid) (next : SmallStep program ctx mid t₂ s'),
      motive s t₁ mid start → motive s (t₁ ++ t₂) s' (start.tail next))
    {s : MachineState} {t : Trace} {e : MachineState}
    (h : Steps program ctx s t e) : motive s t e h := by
  refine Steps.rec (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun a ta b hh => motive a ta b hh)
      (motive_3 := fun _ _ _ _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?refl ?tail ?_ ?_ h
  case refl => intro a; exact refl a
  case tail => intro a m b ta tb start next ih _; exact tail start next ih
  all_goals intros; trivial

theorem Steps.single {program : Program} {ctx : CallContext}
    {s s' : MachineState} {t : Trace}
    (step : SmallStep program ctx s t s') : Steps program ctx s t s' :=
  Steps.tail Steps.refl step

theorem Steps.trans {program : Program} {ctx : CallContext}
    {s mid s' : MachineState} {t₁ t₂ : Trace}
    (h₁ : Steps program ctx s t₁ mid) (h₂ : Steps program ctx mid t₂ s') :
    Steps program ctx s (t₁ ++ t₂) s' := by
  induction h₂ using Steps.inductionOn with
  | refl => simpa using h₁
  | tail start next ih => simpa [List.append_assoc] using Steps.tail (ih h₁) next

theorem Steps.head {program : Program} {ctx : CallContext}
    {s mid s' : MachineState} {t₁ t₂ : Trace}
    (step : SmallStep program ctx s t₁ mid) (rest : Steps program ctx mid t₂ s') :
    Steps program ctx s (t₁ ++ t₂) s' :=
  Steps.trans (Steps.single step) rest
def Stuck (program : Program) (ctx : CallContext) (s : MachineState) : Prop :=
  ∀ t s', ¬ SmallStep program ctx s t s'

theorem stuck_of_returned
    {state : MachineState} {rs : Array Word} (hctrl : state.control = .returned rs) :
    Stuck program ctx state := by
  intro t s' hstep
  cases hstep <;> simp_all [Program.decodeStmt, Program.terminatorAt]

theorem stuck_of_halted
    {state : MachineState} (hctrl : state.control = .halted) :
    Stuck program ctx state := by
  intro t s' hstep
  cases hstep <;> simp_all [Program.decodeStmt, Program.terminatorAt]

theorem Steps.head_decomp
    {s e : MachineState} {t : Trace} (h : Steps program ctx s t e) :
    (s = e ∧ t = []) ∨
      ∃ mid t₁ t₂, SmallStep program ctx s t₁ mid ∧ Steps program ctx mid t₂ e ∧
        t = t₁ ++ t₂ := by
  induction h using Steps.inductionOn with
  | refl => exact .inl ⟨rfl, rfl⟩
  | tail start next ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨mid, u₁, u₂, step, rest, rfl⟩
    · exact .inr ⟨_, _, [], next, .refl, by simp⟩
    · exact .inr ⟨mid, u₁, u₂ ++ _, step, rest.tail next, by simp⟩

theorem Steps.eq_of_stuck
    {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e) (hs : Stuck program ctx s) : e = s ∧ t = [] := by
  rcases h.head_decomp with ⟨rfl, rfl⟩ | ⟨mid, t₁, t₂, step, -, -⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd step (hs t₁ mid)

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

theorem SmallStep.preserves_function
    {cursor : ProgramCursor} {s s' : MachineState} {t : Trace}
    (h : SmallStep program ctx s t s')
    (hctrl : s.control = .running cursor) :
    s'.control = .halted ∨ (∃ rs, s'.control = .returned rs) ∨
      ∃ cursor', s'.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | assign hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | sstore hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | gas hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | call hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mallocUninit hstmt halloc heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mstore32 hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mload32 hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | icall hstmt hargs hcallee hbind =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | icallHalted hstmt hargs hcallee => exact .inl rfl
  | terminator hterm heval =>
    rename_i term
    have hsrc := Program.terminatorAt_inv hctrl hterm
    cases term with
    | halt =>
      have hh : (eval_terminator program .halt).run s =
          .ok ((), { s with control := .halted }) := rfl
      rw [hh] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      exact .inl rfl
    | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
      obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
      exact .inr (.inr ⟨_, hctrl', rfl⟩)
    | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
      cases hcond : s.locals.lookup condition with
      | error e =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        simp at heval
      | ok w =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        by_cases hw : w = 0
        · rw [if_pos hw] at heval
          obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
          obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
          exact .inr (.inr ⟨_, hctrl', rfl⟩)
        · rw [if_neg hw] at heval
          obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
          obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
          exact .inr (.inr ⟨_, hctrl', rfl⟩)
    | iret =>
      obtain ⟨cursor, block, rs, hs, hb, hrs, rfl⟩ := eval_terminator_iret_inv heval
      exact .inr (.inl ⟨rs, rfl⟩)

theorem Steps.preserves_function_proof
    {cursor : ProgramCursor} {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e)
    (hctrl : s.control = .running cursor) :
    e.control = .halted ∨ (∃ rs, e.control = .returned rs) ∨
      ∃ cursor', e.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  induction h using Steps.inductionOn with
  | refl => exact .inr (.inr ⟨cursor, hctrl, rfl⟩)
  | tail start next ih =>
    rcases ih hctrl with hmid | ⟨rs, hmid⟩ | ⟨cursor', hctrl', hfn⟩
    · exact absurd next (stuck_of_halted hmid _ _)
    · exact absurd next (stuck_of_returned hmid _ _)
    · rcases next.preserves_function hctrl' with hhalt | hreturned | ⟨cursor'', hctrl'', hfn'⟩
      · exact .inl hhalt
      · exact .inr (.inl hreturned)
      · exact .inr (.inr ⟨cursor'', hctrl'', hfn'.trans hfn⟩)

theorem SmallStep.returned_inv
    {s s' : MachineState} {t : Trace} {rs : Array Word}
    (h : SmallStep program ctx s t s') (hret : s'.control = .returned rs) :
    ∃ cursor block, s.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (s.locals.lookup ·) = .ok rs := by
  cases h with
  | assign hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | sstore hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | gas hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | call hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mallocUninit hstmt halloc heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mstore32 hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mload32 hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | icall hstmt hargs hcallee hbind =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | icallHalted hstmt hargs hcallee => cases hret
  | terminator hterm heval =>
    rename_i term
    cases term with
    | halt =>
      simp only [eval_terminator] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      cases hret
    | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
      rw [hctrl'] at hret
      cases hret
    | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
      cases hcond : s.locals.lookup condition with
      | error e =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        simp at heval
      | ok w =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
        rw [hctrl'] at hret
        cases hret
    | iret =>
      obtain ⟨cursor, block, actual, hctrl, hblock, houtputs, rfl⟩ :=
        eval_terminator_iret_inv heval
      obtain rfl := MachineControl.returned.inj hret
      cases hpos : cursor.position with
      | statement index => simp [Program.terminatorAt, hctrl, hpos] at hterm
      | terminator =>
        have hblockTerm : block.terminator = .iret := by
          simpa [Program.terminatorAt, hctrl, hpos, hblock] using hterm
        exact ⟨cursor, block, hctrl, hblock, hblockTerm, houtputs⟩

end Sir
