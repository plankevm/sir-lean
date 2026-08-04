import Sir.Proofs.WellFormed

namespace Sir

variable {program : Program} {ctx : CallContext}

def Locals.Defined (locals : Locals) (var : VarId) : Prop :=
  ∃ w, locals.lookup var = .ok w

def Locals.ExprReady (locals : Locals) : Expr → Prop
  | .constant _ => True
  | .var v => locals.Defined v
  | .add a b | .lt a b => locals.Defined a ∧ locals.Defined b
  | .sload k => locals.Defined k

def MachineState.StmtReady (s : MachineState) : Stmt → Prop
  | .assign _ e => s.locals.ExprReady e
  | .sstore key value => s.locals.Defined key ∧ s.locals.Defined value
  | .gas _ => True
  | .call c => s.locals.Defined c.callee ∧ s.locals.Defined c.gas
  | .mallocUninit _ size =>
      ∃ w alloc, s.locals.lookup size = .ok w ∧
        s.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = w.toNat
  | .mstore32 offset value =>
      ∃ w, s.locals.lookup offset = .ok w ∧ s.locals.Defined value ∧
        s.globals.memory.InBounds w.toNat 32
  | .mload32 _ offset => s.locals.Defined offset
  | .icall _ _ _ => False

def Program.JumpReady (program : Program) (fn : FunctionId) (s : MachineState)
    (src : BasicBlock) (target : BlockId) : Prop :=
  (∃ vs, src.outputs.mapM (s.locals.lookup ·) = .ok vs) ∧
    ∃ targetBlock,
      program.block? { fn := fn, block := target, position := .terminator } = some targetBlock ∧
      targetBlock.inputs.size = src.outputs.size

def Program.TerminatorReady (program : Program) (fn : FunctionId) (s : MachineState)
    (src : BasicBlock) : Prop :=
  match src.terminator with
  | .halt => True
  | .jump target => program.JumpReady fn s src target
  | .branch condition thenTarget elseTarget =>
      ∃ w, s.locals.lookup condition = .ok w ∧
        program.JumpReady fn s src (if w = 0 then elseTarget else thenTarget)
  | .iret => ∃ rs, src.outputs.mapM (s.locals.lookup ·) = .ok rs

theorem eval_terminator_halt_ok (s : MachineState) :
    (eval_terminator program .halt).run s =
      .ok ((), { s with control := .halted }) := rfl

theorem eval_terminator_iret_ok
    {s : MachineState} {cursor : ProgramCursor} {block : BasicBlock}
    {rs : Array Word}
    (hctrl : s.control = .running cursor)
    (hblock : program.block? cursor = some block)
    (houtputs : block.outputs.mapM (s.locals.lookup ·) = .ok rs) :
    (eval_terminator program .iret).run s =
      .ok ((), { s with control := .returned rs }) := by
  simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
    get, getThe, MonadStateOf.get, hctrl, hblock, houtputs, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Except.pure]

private theorem eval_jump_ok
    {s : MachineState} {cursor : ProgramCursor} {target : BlockId}
    {sourceBlock targetBlock : BasicBlock} {vs : Array Word}
    (hctrl : s.control = .running cursor)
    (hsrc : program.block? cursor = some sourceBlock)
    (htgt : program.block? { cursor with block := target } = some targetBlock)
    (houts : sourceBlock.outputs.mapM (s.locals.lookup ·) = .ok vs)
    (harity : targetBlock.inputs.size = vs.size) :
    ∃ s', (eval_jump program target).run s = .ok ((), s') := by
  obtain ⟨l', hbind⟩ := Locals.bindValues_total s.locals harity
  refine ⟨{ s with locals := l',
                   control := .running
                     { cursor with block := target, position := targetBlock.startPosition } }, ?_⟩
  simp [eval_jump, StateT.run, Locals.transfer, bind, Except.bind, StateT.bind,
    hctrl, hsrc, htgt, houts, hbind, StateT.get, get, getThe, MonadStateOf.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftM, monadLift,
    MonadLift.monadLift, pure, Except.pure]

theorem progress_stmt_proof
    {state : MachineState} {next : MachineControl} {statement : Stmt}
    (hdecode : program.decodeStmt state.control = some (next, statement))
    (hready : state.StmtReady statement) :
    ∃ (trace : Trace) (final : MachineState),
      Generic.GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState trace final.toGenericState := by
  cases statement with
  | assign result expr =>
      cases expr with
      | constant value =>
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[value]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign hdecode ?_⟩
          simp only [decodeExpression, Generic.Instruction.Fires]
          apply fires_of (operation := .constant value) (oracle := ())
            (operands := #[]) (results := #[value])
          · change (#[] : Array VarId).mapM (state.locals.lookup ·) = .ok #[]
            rw [Array.mapM_eq_mapM_toList]
            rfl
          · trivial
          · exact Generic.Operation.execute_constant_ok ctx value state.globals #[]
          · exact hstore
      | var v =>
          obtain ⟨value, hvalue⟩ := hready
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[value]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign hdecode ?_⟩
          simp only [decodeExpression, Generic.Instruction.Fires]
          apply fires_of (operation := .copy) (oracle := ())
            (operands := #[value]) (results := #[value])
          · simp [Array.mapM_eq_mapM_toList, hvalue, bind, Except.bind,
              Functor.map, Except.map, pure, Except.pure]
          · trivial
          · exact Generic.Operation.execute_copy_ok ctx value state.globals
          · exact hstore
      | add lhs rhs =>
          obtain ⟨⟨lhsValue, hlhs⟩, rhsValue, hrhs⟩ := hready
          let resultValue := Evm.UInt256.add lhsValue rhsValue
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[resultValue]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign hdecode ?_⟩
          simp only [decodeExpression, Generic.Instruction.Fires]
          apply fires_of (operation := .add) (oracle := ())
            (operands := #[lhsValue, rhsValue])
            (results := #[resultValue])
          · simp [Array.mapM_eq_mapM_toList, hlhs, hrhs, bind, Except.bind,
              Functor.map, Except.map, pure, Except.pure]
          · trivial
          · exact Generic.Operation.execute_add_ok ctx lhsValue rhsValue state.globals
          · exact hstore
      | lt lhs rhs =>
          obtain ⟨⟨lhsValue, hlhs⟩, rhsValue, hrhs⟩ := hready
          let resultValue := Evm.UInt256.lt lhsValue rhsValue
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[resultValue]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign hdecode ?_⟩
          simp only [decodeExpression, Generic.Instruction.Fires]
          apply fires_of (operation := .lt) (oracle := ())
            (operands := #[lhsValue, rhsValue])
            (results := #[resultValue])
          · simp [Array.mapM_eq_mapM_toList, hlhs, hrhs, bind, Except.bind,
              Functor.map, Except.map, pure, Except.pure]
          · trivial
          · exact Generic.Operation.execute_lt_ok ctx lhsValue rhsValue state.globals
          · exact hstore
      | sload key =>
          obtain ⟨keyValue, hkey⟩ := hready
          let resultValue := state.globals.world.loadStorage ctx.self keyValue
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[resultValue]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign hdecode ?_⟩
          simp only [decodeExpression, Generic.Instruction.Fires]
          apply fires_of (operation := .sload) (oracle := ()) (operands := #[keyValue])
            (results := #[resultValue])
          · simp [Array.mapM_eq_mapM_toList, hkey, bind, Except.bind,
              Functor.map, Except.map, pure, Except.pure]
          · trivial
          · exact Generic.Operation.execute_sload_ok ctx keyValue state.globals
          · exact hstore
  | sstore key value =>
      obtain ⟨⟨keyValue, hkey⟩, valueValue, hvalue⟩ := hready
      let globals' := { state.globals with
        world := state.globals.world.storeStorage ctx.self keyValue valueValue }
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[]) (vs := #[]) rfl
      refine ⟨[], ⟨globals', locals', next⟩, step_sstore hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .sstore) (oracle := ())
        (operands := #[keyValue, valueValue]) (results := #[])
      · simp [Array.mapM_eq_mapM_toList, hkey, hvalue, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_sstore_ok ctx keyValue valueValue state.globals
      · exact hstore
  | gas result =>
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[result]) (vs := #[(0 : Word)]) rfl
      refine ⟨[.gas 0], ⟨state.globals, locals', next⟩, step_gas hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .gas) (oracle := (0 : Word))
        (operands := #[]) (results := #[0])
      · change (#[] : Array VarId).mapM (state.locals.lookup ·) = .ok #[]
        rw [Array.mapM_eq_mapM_toList]
        rfl
      · trivial
      · exact Generic.Operation.execute_gas_ok ctx 0 state.globals #[]
      · exact hstore
  | call call =>
      obtain ⟨⟨callee, hcallee⟩, gas, hgas⟩ := hready
      let result : CallResult :=
        { world' := state.globals.world, success := true, output := ByteArray.empty }
      let globals' := { state.globals with
        returnData := result.output, world := result.world' }
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[call.result])
        (vs := #[Evm.UInt256.fromBool result.success]) rfl
      let record : CallRecord :=
        { input := { target := .ofUInt256 callee, gas, world := state.globals.world }, result }
      refine ⟨[.call record], ⟨globals', locals', next⟩, step_call hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .call) (oracle := result) (operands := #[callee, gas])
        (results := #[Evm.UInt256.fromBool result.success])
      · simp [Array.mapM_eq_mapM_toList, hcallee, hgas, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_call_ok ctx result state.globals callee gas
      · exact hstore
  | mallocUninit result size =>
      obtain ⟨sizeValue, allocation, hsizeValue, hvalid, hsize⟩ := hready
      let globals' := { state.globals with memory := state.globals.memory.push allocation }
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[result]) (vs := #[allocation.offset]) rfl
      refine ⟨[], ⟨globals', locals', next⟩, step_mallocUninit hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .mallocUninit) (oracle := allocation)
        (operands := #[sizeValue])
        (results := #[allocation.offset])
      · simp [Array.mapM_eq_mapM_toList, hsizeValue, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · exact ⟨sizeValue, rfl, ⟨hvalid, hsize⟩, hvalid, hsize⟩
      · exact Generic.Operation.execute_malloc_ok ctx allocation state.globals sizeValue hsize
      · exact hstore
  | mstore32 offset value =>
      obtain ⟨offsetValue, hoffset, ⟨valueValue, hvalue⟩, hin⟩ := hready
      let globals' := { state.globals with
        memory := state.globals.memory.writeBytes offsetValue valueValue.toByteArray }
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[]) (vs := #[]) rfl
      refine ⟨[], ⟨globals', locals', next⟩, step_mstore32 hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .mstore32) (oracle := ())
        (operands := #[offsetValue, valueValue]) (results := #[])
      · simp [Array.mapM_eq_mapM_toList, hoffset, hvalue, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_mstore32_ok ctx state.globals offsetValue valueValue hin
      · exact hstore
  | mload32 result offset =>
      obtain ⟨offsetValue, hoffset⟩ := hready
      let resultValue : Word := .ofNat (Evm.fromByteArrayBigEndian
        (state.globals.memory.readBytes offsetValue 32))
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[result]) (vs := #[resultValue]) rfl
      refine ⟨[], ⟨state.globals, locals', next⟩, step_mload32 hdecode ?_⟩
      simp only [decodeSirStatement, Generic.Instruction.Fires]
      apply fires_of (operation := .mload32) (oracle := ()) (operands := #[offsetValue])
        (results := #[resultValue])
      · simp [Array.mapM_eq_mapM_toList, hoffset, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_mload32_ok ctx state.globals offsetValue
      · exact hstore
  | icall callee args dests => exact hready.elim

theorem progress_terminator_proof
    {state : MachineState} {cursor : ProgramCursor} {source : BasicBlock}
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hsource : program.block? cursor = some source)
    (hready : program.TerminatorReady cursor.fn state source) :
    ∃ (final : MachineState),
      Generic.GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
      state.toGenericState [] final.toGenericState := by
  have hterm : program.terminatorAt state.control = some source.terminator := by
    simp [Program.terminatorAt, hcontrol, hposition, hsource]
  unfold Program.TerminatorReady at hready
  cases hcase : source.terminator with
  | halt =>
      rw [hcase] at hterm
      exact ⟨_, step_terminator hterm (eval_terminator_halt_ok state)⟩
  | jump target =>
      rw [hcase] at hterm hready
      obtain ⟨⟨values, houtputs⟩, targetBlock, htarget, harity⟩ := hready
      obtain ⟨final, hfinal⟩ := eval_jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      exact ⟨final, step_terminator hterm hfinal⟩
  | branch condition thenTarget elseTarget =>
      rw [hcase] at hterm hready
      obtain ⟨value, hcondition, ⟨values, houtputs⟩, targetBlock, htarget, harity⟩ :=
        hready
      obtain ⟨final, hfinal⟩ := eval_jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      refine ⟨final, step_terminator hterm ?_⟩
      simp only [eval_terminator, StateT.run, bind, StateT.bind, Locals.lookupM,
        liftM, monadLift, MonadLift.monadLift, StateT.get, Except.bind, StateT.lift,
        pure, Except.pure, hcondition]
      exact hfinal
  | iret =>
      rw [hcase] at hterm hready
      obtain ⟨results, houtputs⟩ := hready
      exact ⟨_, step_terminator hterm
        (eval_terminator_iret_ok hcontrol hsource houtputs)⟩

theorem progress_nonIcall_proof {s : MachineState}
    (h : (∃ nextControl stmt,
            program.decodeStmt s.control = some (nextControl, stmt) ∧
            s.StmtReady stmt) ∨
         (∃ cursor src, s.control = .running cursor ∧
            cursor.position = .terminator ∧
            program.block? cursor = some src ∧
            program.TerminatorReady cursor.fn s src)) :
    ∃ t s', SmallStep program ctx s t s' := by
  rcases h with ⟨nextControl, stmt, hstmt, hready⟩ |
    ⟨cursor, src, hctrl, hpos, hsrc, hready⟩
  · exact progress_stmt_proof hstmt hready
  · obtain ⟨s', hs'⟩ := progress_terminator_proof hctrl hpos hsrc hready
    exact ⟨[], s', hs'⟩

end Sir
