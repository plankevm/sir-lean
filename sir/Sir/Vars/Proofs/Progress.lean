import Sir.Vars.Proofs.Statics

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

def Locals.Defined (locals : Locals) (var : VarId) : Prop :=
  ∃ w, locals.lookup var = .ok w

def Locals.ExprReady (locals : Locals) : Vars.Expr → Prop
  | .constant _ => True
  | .var v => locals.Defined v
  | .add a b | .lt a b => locals.Defined a ∧ locals.Defined b
  | .sload k => locals.Defined k

def Vars.State.StmtReady (s : Vars.State) : Vars.Stmt → Prop
  | .assign _ e => s.environment.ExprReady e
  | .sstore key value => s.environment.Defined key ∧ s.environment.Defined value
  | .gas _ => True
  | .call c => s.environment.Defined c.callee ∧ s.environment.Defined c.gas
  | .malloc _ size =>
      ∃ w alloc, s.lookup size = .ok w ∧
        s.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = w.toNat ∧
        alloc.bytes = ByteArray.mk (Array.replicate w.toNat 0)
  | .mallocUninit _ size =>
      ∃ w alloc, s.lookup size = .ok w ∧
        s.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = w.toNat
  | .mstore32 offset value =>
      ∃ w, s.lookup offset = .ok w ∧ s.environment.Defined value ∧ s.inBounds w
  | .mload32 _ offset => s.environment.Defined offset
  | .icall _ _ _ => False

def Vars.Program.JumpReady (program : Vars.Program) (fn : FunctionId) (s : Vars.State)
    (src : Vars.Block) (target : BlockId) : Prop :=
  (∃ vs, src.outputs.mapM (s.environment.lookup ·) = .ok vs) ∧
    ∃ targetBlock,
      program.block? { fn := fn, block := target, position := .terminator } = some targetBlock ∧
      targetBlock.inputs.size = src.outputs.size

def Vars.Program.TerminatorReady (program : Vars.Program) (fn : FunctionId) (s : Vars.State)
    (src : Vars.Block) : Prop :=
  match src.terminator with
  | .halt => True
  | .jump target => program.JumpReady fn s src target
  | .branch condition thenTarget elseTarget =>
      ∃ w, s.environment.lookup condition = .ok w ∧
        program.JumpReady fn s src (if w = 0 then elseTarget else thenTarget)
  | .iret => ∃ rs, src.outputs.mapM (s.environment.lookup ·) = .ok rs

theorem Vars.evaluateTerminator_halt_ok (s : Vars.State) :
    Vars.evaluateTerminator program s.environment s.control .halt =
      .ok (s.environment, .halted) := rfl

theorem Vars.evaluateTerminator_iret_ok
    {s : Vars.State} {cursor : ProgramCursor} {block : Vars.Block}
    {rs : Array Word}
    (_hctrl : s.control = .running cursor)
    (hblock : program.block? cursor = some block)
    (houtputs : block.outputs.mapM (s.environment.lookup ·) = .ok rs) :
    Vars.evaluateTerminator program s.environment s.control .iret =
      .ok (s.environment, .returned rs) := by
  simp [Vars.evaluateTerminator, _hctrl, hblock, houtputs, bind, Except.bind]

private theorem Vars.jump_ok
    {s : Vars.State} {cursor : ProgramCursor} {target : BlockId}
    {sourceBlock targetBlock : Vars.Block} {vs : Array Word}
    (_hctrl : s.control = .running cursor)
    (hsrc : program.block? cursor = some sourceBlock)
    (htgt : program.block? { cursor with block := target } = some targetBlock)
    (houts : sourceBlock.outputs.mapM (s.environment.lookup ·) = .ok vs)
    (harity : targetBlock.inputs.size = vs.size) :
    ∃ locals,
      Vars.jump program s.environment cursor target =
        .ok (locals, .running
          { cursor with block := target, position := targetBlock.startPosition }) := by
  obtain ⟨l', hbind⟩ := Locals.bindValues_total s.environment harity
  refine ⟨l', ?_⟩
  exact Vars.jump_eq_ok hsrc htgt houts harity.symm hbind

theorem Vars.Proofs.progress_stmt
    {state : Vars.State} {next : Control} {statement : Vars.Stmt}
    (hstmt : program.atStmt state = some (next, statement))
    (hready : state.StmtReady statement) :
    ∃ (trace : Trace) (final : Vars.State),
      Vars.SmallStep program ctx state trace final := by
  cases statement with
  | assign result expression =>
      cases expression with
      | constant value =>
          exact ⟨[], _, .evaluate (globals := state.globals)
              (environment := state.environment.assign result value)
            hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, Vars.evalExpr])⟩
      | var identifier =>
          obtain ⟨value, hvalue⟩ := hready
          exact ⟨[], _, .evaluate (globals := state.globals)
              (environment := state.environment.assign result value)
            hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, Vars.evalExpr, hvalue])⟩
      | add left right =>
          obtain ⟨⟨leftValue, hleft⟩, rightValue, hright⟩ := hready
          let value := Evm.UInt256.add leftValue rightValue
          exact ⟨[], _, .evaluate (globals := state.globals)
              (environment := state.environment.assign result value)
            hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, Vars.evalExpr, hleft, hright,
              value, bind, Except.bind, pure, Except.pure])⟩
      | lt left right =>
          obtain ⟨⟨leftValue, hleft⟩, rightValue, hright⟩ := hready
          let value := Evm.UInt256.lt leftValue rightValue
          exact ⟨[], _, .evaluate (globals := state.globals)
              (environment := state.environment.assign result value)
            hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, Vars.evalExpr, hleft, hright,
              value, bind, Except.bind, pure, Except.pure])⟩
      | sload key =>
          obtain ⟨keyValue, hkey⟩ := hready
          let value := state.globals.world.loadStorage ctx.self keyValue
          exact ⟨[], _, .evaluate (globals := state.globals)
              (environment := state.environment.assign result value)
            hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, Vars.evalExpr, hkey, value])⟩
  | sstore key value =>
      obtain ⟨⟨keyWord, hkey⟩, valueWord, hvalue⟩ := hready
      exact ⟨[], _, .evaluate (globals := state.globals.storeStorage ctx keyWord valueWord)
        (environment := state.environment)
        hstmt (by simp [Vars.State.evaluate, Vars.evalStmt, hkey, hvalue, bind, Except.bind,
          pure, Except.pure])⟩
  | gas result => exact ⟨[.gas 0], _, .gas hstmt⟩
  | call call =>
      obtain ⟨⟨target, htarget⟩, gas, hgas⟩ := hready
      let answer : CallResult :=
        { world' := state.globals.world, success := true, output := ByteArray.empty }
      exact ⟨[Event.call { input := state.globals.callInput target gas, result := answer }],
        _, .call hstmt htarget hgas⟩
  | malloc result size =>
      obtain ⟨word, allocation, hword, hvalid, hsize, hbytes⟩ := hready
      exact ⟨[], _, .malloc hstmt hword ⟨hvalid, hsize⟩ hbytes⟩
  | mallocUninit result size =>
      obtain ⟨word, allocation, hword, hvalid, hsize⟩ := hready
      exact ⟨[], _, .mallocUninit hstmt hword ⟨hvalid, hsize⟩⟩
  | mstore32 offset value =>
      obtain ⟨offsetWord, hoffset, ⟨valueWord, hvalue⟩, hbound⟩ := hready
      exact ⟨[], _, .mstore32 hstmt hoffset hvalue hbound⟩
  | mload32 result offset =>
      obtain ⟨offsetWord, hoffset⟩ := hready
      exact ⟨[], _, .mload32 (assumed := ⟨Array.replicate 32 0, by simp⟩) hstmt hoffset⟩
  | icall callee args dests => exact False.elim hready

theorem Vars.Proofs.progress_terminator
    {state : Vars.State} {cursor : ProgramCursor} {source : Vars.Block}
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hsource : program.block? cursor = some source)
    (hready : program.TerminatorReady cursor.fn state source) :
    ∃ (final : Vars.State),
      Vars.SmallStep program ctx state [] final := by
  have hterm : program.atTerm state = some source.terminator := by
    simp [Vars.Program.atTerm, Vars.Program.terminatorAt, hcontrol, hposition, hsource]
  unfold Vars.Program.TerminatorReady at hready
  cases hcase : source.terminator with
  | halt =>
      rw [hcase] at hterm
      exact ⟨_, .control hterm (Vars.evaluateTerminator_halt_ok state)⟩
  | jump target =>
      rw [hcase] at hterm hready
      obtain ⟨⟨values, houtputs⟩, targetBlock, htarget, harity⟩ := hready
      obtain ⟨locals, hjump⟩ := Vars.jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      exact ⟨_, .control hterm (by
        simp [Vars.evaluateTerminator, hcontrol]
        exact hjump)⟩
  | branch condition thenTarget elseTarget =>
      rw [hcase] at hterm hready
      obtain ⟨value, hcondition, ⟨values, houtputs⟩, targetBlock, htarget, harity⟩ :=
        hready
      obtain ⟨locals, hjump⟩ := Vars.jump_ok hcontrol hsource htarget houtputs
        (harity.trans (mapM_ok_size houtputs).symm)
      exact ⟨_, .control hterm (by
        simp [Vars.evaluateTerminator, hcontrol, hcondition]
        exact hjump)⟩
  | iret =>
      rw [hcase] at hterm hready
      obtain ⟨results, houtputs⟩ := hready
      exact ⟨_, .control hterm
        (Vars.evaluateTerminator_iret_ok hcontrol hsource houtputs)⟩

theorem Vars.Proofs.progress_nonIcall {s : Vars.State}
    (h : (∃ nextControl stmt,
            program.atStmt s = some (nextControl, stmt) ∧
            s.StmtReady stmt) ∨
         (∃ cursor src, s.control = .running cursor ∧
            cursor.position = .terminator ∧
            program.block? cursor = some src ∧
            program.TerminatorReady cursor.fn s src)) :
    ∃ t s', Vars.SmallStep program ctx s t s' := by
  rcases h with ⟨nextControl, stmt, hstmt, hready⟩ |
    ⟨cursor, src, hctrl, hpos, hsrc, hready⟩
  · exact Vars.Proofs.progress_stmt hstmt hready
  · obtain ⟨s', hs'⟩ := Vars.Proofs.progress_terminator hctrl hpos hsrc hready
    exact ⟨[], s', hs'⟩



end Sir
