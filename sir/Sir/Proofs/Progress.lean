import Sir.Proofs.WellFormed

namespace Sir

variable {program : Program} {ctx : CallContext}

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
end Sir
