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
  | .mstore32 offset value => s.locals.Defined offset ∧ s.locals.Defined value
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

theorem Expr.eval_total {s : MachineState} {e : Expr}
    (h : s.locals.ExprReady e) : ∃ w, Expr.eval ctx s e = .ok w := by
  cases e with
  | constant v => exact ⟨v, rfl⟩
  | var v => exact h.imp fun w hw => by simp [Expr.eval, hw]
  | add a b =>
    obtain ⟨⟨wa, ha⟩, wb, hb⟩ := h
    exact ⟨Evm.UInt256.add wa wb, by simp [Expr.eval, ha, hb, bind, Except.bind]; rfl⟩
  | lt a b =>
    obtain ⟨⟨wa, ha⟩, wb, hb⟩ := h
    exact ⟨Evm.UInt256.lt wa wb, by simp [Expr.eval, ha, hb, bind, Except.bind]; rfl⟩
  | sload k =>
    obtain ⟨wk, hk⟩ := h
    exact ⟨s.globals.world.loadStorage ctx.self wk,
      by simp [Expr.eval, hk, bind, Except.bind]; rfl⟩

theorem eval_assign_ok {s : MachineState} {result : VarId} {expr : Expr} {w : Word}
    (h : Expr.eval ctx s expr = .ok w) :
    eval_assign ctx s result expr = .ok { s with locals := s.locals.assign result w } := by
  simp [eval_assign, h, bind, Except.bind]

theorem eval_sstore_ok {s : MachineState} {key value : VarId} {w₁ w₂ : Word}
    (h₁ : s.locals.lookup key = .ok w₁) (h₂ : s.locals.lookup value = .ok w₂) :
    eval_sstore ctx s key value = .ok { s with globals :=
      { s.globals with world := s.globals.world.storeStorage ctx.self w₁ w₂ } } := by
  simp [eval_sstore, h₁, h₂, bind, Except.bind, pure, Except.pure]

theorem eval_gas_ok (result : VarId) (g : Word) (s : MachineState) :
    (eval_gas result g).run s =
      .ok ((), { s with locals := s.locals.assign result g }) := rfl

theorem eval_malloc_uninit_ok {s : MachineState} {alloc : Allocation}
    {result size : VarId} {w : Word}
    (h : s.locals.lookup size = .ok w) (hsz : alloc.size = w.toNat) :
    (eval_malloc_uninit alloc result size).run s =
      .ok ((), { s with
        locals := s.locals.assign result alloc.offset
        globals := { s.globals with memory := s.globals.memory.push alloc } }) := by
  simp [eval_malloc_uninit, StateT.run, Locals.lookupM, bind, Except.bind, StateT.bind,
    h, hsz, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift, Locals.assignM,
    pure, Except.pure, StateT.pure]

theorem eval_mstore32_ok {s : MachineState} {offset value : VarId} {w₁ w₂ : Word}
    (h₁ : s.locals.lookup offset = .ok w₁) (h₂ : s.locals.lookup value = .ok w₂) :
    (eval_mstore32 offset value).run s =
      .ok ((), { s with globals :=
        { s.globals with memory := s.globals.memory.writeBytes w₁ w₂.toByteArray } }) := by
  simp [eval_mstore32, StateT.run, Locals.lookupM, bind, Except.bind, StateT.bind,
    h₁, h₂, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift, pure, Except.pure]

theorem eval_mload32_ok {s : MachineState} {result offset : VarId} {w : Word}
    {assumed : ByteArray} (h : s.locals.lookup offset = .ok w) :
    (eval_mload32 assumed result offset).run s =
      .ok ((), { s with locals := s.locals.assign result
                          (.ofNat (Evm.fromByteArrayBigEndian
                            (s.globals.memory.readBytes w assumed))) }) := by
  simp [eval_mload32, StateT.run, Locals.lookupM, bind, Except.bind, StateT.bind,
    h, StateT.get, get, getThe, MonadStateOf.get, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, liftM, monadLift, MonadLift.monadLift,
    StateT.lift, Locals.assignM, pure, Except.pure]

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
    {s : MachineState} {nextControl : MachineControl} {stmt : Stmt}
    (hstmt : program.decodeStmt s.control = some (nextControl, stmt))
    (hready : s.StmtReady stmt) :
    ∃ t s', SmallStep program ctx s t s' := by
  cases stmt with
  | assign result expr =>
    obtain ⟨w, hw⟩ := Expr.eval_total hready
    exact ⟨_, _, .assign hstmt (eval_assign_ok hw)⟩
  | sstore key value =>
    obtain ⟨⟨w₁, h₁⟩, w₂, h₂⟩ := hready
    exact ⟨_, _, .sstore hstmt (eval_sstore_ok h₁ h₂)⟩
  | gas result =>
    exact ⟨_, _, .gas hstmt (eval_gas_ok result 0 s)⟩
  | call c =>
    obtain ⟨⟨w₁, h₁⟩, w₂, h₂⟩ := hready
    exact ⟨_, _, .call hstmt
      (eval_call_ok c { world' := s.globals.world, success := true,
                        output := ByteArray.empty } s w₁ w₂ h₁ h₂)⟩
  | mallocUninit result size =>
    obtain ⟨w, alloc, h, hvalid, hsz⟩ := hready
    exact ⟨_, _, .mallocUninit hstmt hvalid (eval_malloc_uninit_ok h hsz)⟩
  | mstore32 offset value =>
    obtain ⟨⟨w₁, h₁⟩, w₂, h₂⟩ := hready
    exact ⟨_, _, .mstore32 hstmt (eval_mstore32_ok h₁ h₂)⟩
  | mload32 result offset =>
    obtain ⟨w, h⟩ := hready
    exact ⟨_, _, .mload32 (assumed := Vector.replicate 32 0) hstmt (eval_mload32_ok h)⟩
  | icall callee args dests => exact hready.elim

theorem progress_terminator_proof
    {s : MachineState} {cursor : ProgramCursor} {src : BasicBlock}
    (hctrl : s.control = .running cursor)
    (hpos : cursor.position = .terminator)
    (hsrc : program.block? cursor = some src)
    (hready : program.TerminatorReady cursor.fn s src) :
    ∃ s', SmallStep program ctx s [] s' := by
  have hterm : program.terminatorAt s.control = some src.terminator := by
    simp [Program.terminatorAt, hctrl, hpos, hsrc]
  unfold Program.TerminatorReady at hready
  cases hcase : src.terminator with
  | halt =>
    rw [hcase] at hterm
    exact ⟨_, .terminator hterm (eval_terminator_halt_ok s)⟩
  | jump target =>
    rw [hcase] at hterm hready
    obtain ⟨⟨vs, houts⟩, targetBlock, htgt, harity⟩ := hready
    obtain ⟨s', hs'⟩ :=
      eval_jump_ok hctrl hsrc htgt houts (harity.trans (mapM_ok_size houts).symm)
    exact ⟨s', .terminator hterm hs'⟩
  | branch condition thenTarget elseTarget =>
    rw [hcase] at hterm hready
    obtain ⟨w, hcond, ⟨vs, houts⟩, targetBlock, htgt, harity⟩ := hready
    obtain ⟨s', hs'⟩ :=
      eval_jump_ok hctrl hsrc htgt houts (harity.trans (mapM_ok_size houts).symm)
    refine ⟨s', .terminator hterm ?_⟩
    simp only [eval_terminator]
    simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
      MonadLift.monadLift, StateT.get, Except.bind, StateT.lift,
      pure, Except.pure, hcond]
    exact hs'
  | iret =>
    rw [hcase] at hterm hready
    obtain ⟨rs, houtputs⟩ := hready
    exact ⟨_, .terminator hterm (eval_terminator_iret_ok hctrl hsrc houtputs)⟩

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

theorem progress_stmt_proof_gen
    {state : MachineState} {next : MachineControl} {statement : Stmt}
    (hdecode : program.decodeStmt state.control = some (next, statement))
    (hready : state.StmtReady statement) :
    ∃ (trace : Trace) (final : MachineState),
      Generic.GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen := by
  cases statement with
  | assign result expr =>
      cases expr with
      | constant value =>
          obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
            (targetVars := #[result]) (vs := #[value]) rfl
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign_gen hdecode ?_⟩
          simp only [decodeExpr, Generic.Instr.Fires]
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
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign_gen hdecode ?_⟩
          simp only [decodeExpr, Generic.Instr.Fires]
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
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign_gen hdecode ?_⟩
          simp only [decodeExpr, Generic.Instr.Fires]
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
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign_gen hdecode ?_⟩
          simp only [decodeExpr, Generic.Instr.Fires]
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
          refine ⟨[], ⟨state.globals, locals', next⟩, step_assign_gen hdecode ?_⟩
          simp only [decodeExpr, Generic.Instr.Fires]
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
      refine ⟨[], ⟨globals', locals', next⟩, step_sstore_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
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
      refine ⟨[.gas 0], ⟨state.globals, locals', next⟩, step_gas_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
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
      refine ⟨[.call record], ⟨globals', locals', next⟩, step_call_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
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
      refine ⟨[], ⟨globals', locals', next⟩, step_mallocUninit_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
      apply fires_of (operation := .mallocUninit) (oracle := allocation)
        (operands := #[sizeValue])
        (results := #[allocation.offset])
      · simp [Array.mapM_eq_mapM_toList, hsizeValue, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · exact ⟨sizeValue, rfl, ⟨hvalid, hsize⟩, hvalid, hsize⟩
      · exact Generic.Operation.execute_malloc_ok ctx allocation state.globals sizeValue hsize
      · exact hstore
  | mstore32 offset value =>
      obtain ⟨⟨offsetValue, hoffset⟩, valueValue, hvalue⟩ := hready
      let globals' := { state.globals with
        memory := state.globals.memory.writeBytes offsetValue valueValue.toByteArray }
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[]) (vs := #[]) rfl
      refine ⟨[], ⟨globals', locals', next⟩, step_mstore32_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
      apply fires_of (operation := .mstore32) (oracle := ())
        (operands := #[offsetValue, valueValue]) (results := #[])
      · simp [Array.mapM_eq_mapM_toList, hoffset, hvalue, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_mstore32_ok ctx state.globals offsetValue valueValue
      · exact hstore
  | mload32 result offset =>
      obtain ⟨offsetValue, hoffset⟩ := hready
      let assumed : Vector UInt8 32 := Vector.replicate 32 0
      let resultValue : Word := .ofNat (Evm.fromByteArrayBigEndian
        (state.globals.memory.readBytes offsetValue ⟨assumed.toArray⟩))
      obtain ⟨locals', hstore⟩ := Locals.bindValues_total state.locals
        (targetVars := #[result]) (vs := #[resultValue]) rfl
      refine ⟨[], ⟨state.globals, locals', next⟩, step_mload32_gen hdecode ?_⟩
      simp only [decodeSirStmt, Generic.Instr.Fires]
      apply fires_of (operation := .mload32) (oracle := assumed) (operands := #[offsetValue])
        (results := #[resultValue])
      · simp [Array.mapM_eq_mapM_toList, hoffset, bind, Except.bind,
          Functor.map, Except.map, pure, Except.pure]
      · trivial
      · exact Generic.Operation.execute_mload32_ok ctx assumed state.globals offsetValue
      · exact hstore
  | icall callee args dests => exact hready.elim

theorem progress_terminator_proof_gen
    {state : MachineState} {cursor : ProgramCursor} {source : BasicBlock}
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hsource : program.block? cursor = some source)
    (hready : program.TerminatorReady cursor.fn state source) :
    ∃ (final : MachineState),
      Generic.GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen [] final.gen := by
  have hterm : program.terminatorAt state.control = some source.terminator := by
    simp [Program.terminatorAt, hcontrol, hposition, hsource]
  unfold Program.TerminatorReady at hready
  cases hcase : source.terminator with
  | halt =>
      rw [hcase] at hterm
      exact ⟨_, step_terminator_gen hterm (eval_terminator_halt_ok state)⟩
  | jump target =>
      rw [hcase] at hterm hready
      obtain ⟨⟨values, houtputs⟩, targetBlock, htarget, harity⟩ := hready
      obtain ⟨final, hfinal⟩ := eval_jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      exact ⟨final, step_terminator_gen hterm hfinal⟩
  | branch condition thenTarget elseTarget =>
      rw [hcase] at hterm hready
      obtain ⟨value, hcondition, ⟨values, houtputs⟩, targetBlock, htarget, harity⟩ :=
        hready
      obtain ⟨final, hfinal⟩ := eval_jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      refine ⟨final, step_terminator_gen hterm ?_⟩
      simp only [eval_terminator, StateT.run, bind, StateT.bind, Locals.lookupM,
        liftM, monadLift, MonadLift.monadLift, StateT.get, Except.bind, StateT.lift,
        pure, Except.pure, hcondition]
      exact hfinal
  | iret =>
      rw [hcase] at hterm hready
      obtain ⟨results, houtputs⟩ := hready
      exact ⟨_, step_terminator_gen hterm
        (eval_terminator_iret_ok hcontrol hsource houtputs)⟩

theorem progress_nonIcall_proof_gen {state : MachineState}
    (h : (∃ next statement,
            program.decodeStmt state.control = some (next, statement) ∧
            state.StmtReady statement) ∨
         (∃ cursor source, state.control = .running cursor ∧
            cursor.position = .terminator ∧
            program.block? cursor = some source ∧
            program.TerminatorReady cursor.fn state source)) :
    ∃ (trace : Trace) (final : MachineState),
      Generic.GenStep localsFrame (sirDecoder program) sirPolicy ctx
      state.gen trace final.gen := by
  rcases h with ⟨next, statement, hdecode, hready⟩ |
    ⟨cursor, source, hcontrol, hposition, hsource, hready⟩
  · exact progress_stmt_proof_gen hdecode hready
  · obtain ⟨final, hfinal⟩ :=
      progress_terminator_proof_gen hcontrol hposition hsource hready
    exact ⟨[], final, hfinal⟩
end Sir
