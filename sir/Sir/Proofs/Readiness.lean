import Sir.Proofs.Progress

namespace Sir

variable {program : Program} {ctx : CallContext}

def BasicBlock.variablesDefinedAtPosition
    (block : BasicBlock) : BlockPosition → List VarId
  | .statement index => block.variablesDefinedBefore index
  | .terminator => block.variablesDefinedBefore block.statements.size

def Locals.CoversVariables (locals : Locals) (identifiers : List VarId) : Prop :=
  ∀ identifier ∈ identifiers, locals.Defined identifier

def MachineState.LocalsCoverCursor (program : Program) (state : MachineState) : Prop :=
  match state.control with
  | .running cursor =>
      ∃ block, program.block? cursor = some block ∧
        state.locals.CoversVariables (block.variablesDefinedAtPosition cursor.position)
  | .returned _ | .halted => True

theorem Locals.defined_assign (locals : Locals) (identifier : VarId) (value : Word) :
    (locals.assign identifier value).Defined identifier := by
  exact ⟨value, by simp [Locals.lookup, Locals.lookup?,
    Locals.assign]⟩

theorem Locals.defined_assign_of_defined
    {locals : Locals} {identifier assigned : VarId} {value : Word}
    (h : locals.Defined identifier) :
    (locals.assign assigned value).Defined identifier := by
  obtain ⟨word, hword⟩ := h
  by_cases heq : identifier = assigned
  · subst identifier
    exact Locals.defined_assign locals assigned value
  · exact ⟨word, by
      simp only [Locals.lookup, Locals.lookup?, Locals.assign, heq, ↓reduceIte]
      simpa [Locals.lookup, Locals.lookup?] using hword⟩

def Locals.assignPairs (locals : Locals) :
    List (VarId × Word) → Locals
  | [] => locals
  | (identifier, value) :: rest =>
      (locals.assign identifier value).assignPairs rest

theorem Locals.assignPairs_preserves
    {locals : Locals} {pairs : List (VarId × Word)} {identifier : VarId}
    (h : locals.Defined identifier) :
    (locals.assignPairs pairs).Defined identifier := by
  induction pairs generalizing locals with
  | nil => exact h
  | cons pair rest ih =>
      obtain ⟨assigned, value⟩ := pair
      exact ih (Locals.defined_assign_of_defined h)

theorem Locals.assignPairs_zip_defines
    {locals : Locals} {identifiers : List VarId} {values : List Word}
    (hsize : identifiers.length = values.length) :
    locals.assignPairs (identifiers.zip values) |>.CoversVariables identifiers := by
  induction identifiers generalizing locals values with
  | nil => simp [Locals.CoversVariables]
  | cons identifier identifiers ih =>
      cases values with
      | nil => simp at hsize
      | cons value values =>
          simp at hsize
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with heq | hcandidate
          · subst candidate
            change ((locals.assign identifier value).assignPairs
              (identifiers.zip values)).Defined identifier
            exact Locals.assignPairs_preserves
              (Locals.defined_assign locals identifier value)
          · exact ih hsize candidate hcandidate

theorem Locals.assignPairs_eq_foldl
    (locals : Locals) (pairs : List (VarId × Word)) :
    locals.assignPairs pairs =
      pairs.foldl (fun result pair => result.assign pair.1 pair.2) locals := by
  induction pairs generalizing locals with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨identifier, value⟩ := pair
      exact ih (locals.assign identifier value)

private theorem Locals.bindValues_assignPairs
    {locals : Locals} {identifiers : Array VarId} {values : Array Word}
    (hsize : identifiers.size = values.size) :
    Locals.bindValues locals identifiers values =
      .ok (locals.assignPairs (identifiers.toList.zip values.toList)) := by
  simp only [Locals.bindValues, hsize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    ← Array.forIn_toList, Array.toList_zip]
  simp only [bind, Except.bind, pure, Except.pure]
  change ((forIn (identifiers.toList.zip values.toList) locals
      fun (pair : VarId × Word) (result : Locals) => pure (ForInStep.yield
        (result.assign pair.1 pair.2))) >>= pure) =
    Except.ok (locals.assignPairs (identifiers.toList.zip values.toList))
  rw [bind_pure]
  rw [List.forIn_pure_yield_eq_foldl]
  simp [Locals.assignPairs_eq_foldl, pure, Except.pure]

theorem Locals.bindValues_covers
    {locals result : Locals} {identifiers : Array VarId} {values : Array Word}
    (hbind : Locals.bindValues locals identifiers values = .ok result) :
    result.CoversVariables identifiers.toList := by
  have hsize : identifiers.size = values.size := by
    by_contra hne
    have hbne : (identifiers.size != values.size) = true :=
      bne_iff_ne.mpr hne
    simp [Locals.bindValues, hbne, bind, Except.bind] at hbind
  rw [Locals.bindValues_assignPairs hsize] at hbind
  obtain rfl := Except.ok.inj hbind
  apply Locals.assignPairs_zip_defines
  simpa using hsize

theorem Locals.bindValues_preserves
    {locals result : Locals} {identifiers : Array VarId} {values : Array Word}
    (hbind : Locals.bindValues locals identifiers values = .ok result)
    {identifier : VarId} (h : locals.Defined identifier) :
    result.Defined identifier := by
  have hsize : identifiers.size = values.size := by
    by_contra hne
    have hbne : (identifiers.size != values.size) = true :=
      bne_iff_ne.mpr hne
    simp [Locals.bindValues, hbne, bind, Except.bind] at hbind
  rw [Locals.bindValues_assignPairs hsize] at hbind
  obtain rfl := Except.ok.inj hbind
  exact Locals.assignPairs_preserves h

theorem Locals.bindParams_covers
    {inputs : Array VarId} {values : Array Word} {locals : Locals}
    (hbind : Locals.bindParams inputs values = .ok locals) :
    locals.CoversVariables inputs.toList :=
  Locals.bindValues_covers hbind

theorem Locals.lookupArray_total
    {locals : Locals} {identifiers : Array VarId}
    (h : locals.CoversVariables identifiers.toList) :
    ∃ values, identifiers.mapM (locals.lookup ·) = .ok values := by
  have lookupListTotal :
      ∀ (list : List VarId), locals.CoversVariables list →
        ∃ values, list.mapM (locals.lookup ·) = .ok values := by
    intro list hlist
    induction list with
    | nil => exact ⟨[], rfl⟩
    | cons identifier identifiers ih =>
        obtain ⟨value, hvalue⟩ := hlist identifier (by simp)
        obtain ⟨values, hvalues⟩ := ih (fun candidate hcandidate =>
          hlist candidate (by simp [hcandidate]))
        exact ⟨value :: values, by
          simp [hvalue, hvalues, bind, Except.bind, pure, Except.pure]⟩
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨values, hvalues⟩ := lookupListTotal identifiers.toList h
  exact ⟨values.toArray, by simp [hvalues, Functor.map, Except.map]⟩

theorem Locals.coversVariables_append
    {locals : Locals} {first second : List VarId}
    (hfirst : locals.CoversVariables first)
    (hsecond : locals.CoversVariables second) :
    locals.CoversVariables (first ++ second) := by
  intro identifier hidentifier
  rcases List.mem_append.mp hidentifier with hidentifier | hidentifier
  · exact hfirst identifier hidentifier
  · exact hsecond identifier hidentifier

theorem BasicBlock.variablesDefinedAtPosition_start (block : BasicBlock) :
    block.variablesDefinedAtPosition block.startPosition = block.inputs.toList := by
  cases hsize : block.statements.size with
  | zero =>
      simp [BasicBlock.startPosition, BasicBlock.absoluteToPosition,
        BasicBlock.variablesDefinedAtPosition, BasicBlock.variablesDefinedBefore,
        hsize]
  | succ size =>
      simp [BasicBlock.startPosition, BasicBlock.absoluteToPosition,
        BasicBlock.variablesDefinedAtPosition, BasicBlock.variablesDefinedBefore,
        hsize]

theorem BasicBlock.variablesDefinedAtPosition_next
    {block : BasicBlock} {index : Nat} {statement : Stmt}
    (hstatement : block.statements[index]? = some statement) :
    block.variablesDefinedAtPosition (block.absoluteToPosition (index + 1)) =
      block.variablesDefinedBefore index ++ statement.variablesDefined := by
  have hindex : index < block.statements.size :=
    (Array.getElem?_eq_some_iff.mp hstatement).choose
  have hbefore :
      block.variablesDefinedBefore (index + 1) =
        block.variablesDefinedBefore index ++ statement.variablesDefined := by
    simp [BasicBlock.variablesDefinedBefore, hstatement]
  by_cases hnext : index + 1 < block.statements.size
  · simp [BasicBlock.absoluteToPosition, hnext,
      BasicBlock.variablesDefinedAtPosition, hbefore]
  · have hsize : block.statements.size = index + 1 := by omega
    simp [BasicBlock.absoluteToPosition,
      BasicBlock.variablesDefinedAtPosition, hsize, hbefore]

theorem Program.block?_function
    {cursor : ProgramCursor} {block : BasicBlock}
    (hblock : program.block? cursor = some block) :
    ∃ fn, program.function? cursor.fn = some fn ∧ block ∈ fn.blocks := by
  cases hfn : program.function? cursor.fn with
  | none => simp [Program.block?, hfn] at hblock
  | some fn =>
      have hlocal : fn.block? cursor.block = some block := by
        simpa [Program.block?, hfn] using hblock
      exact ⟨fn, rfl, Array.mem_of_getElem? hlocal⟩

theorem Program.callState?_localsCoverCursor
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {state : MachineState}
    (hentry : program.callState? function globals args = some state) :
    state.LocalsCoverCursor program := by
  obtain ⟨fn, block, locals, hfn, hblock, hbind, rfl⟩ :=
    Program.callState?_eq_some_iff.mp hentry
  refine ⟨block, ?_, ?_⟩
  · simp [Program.block?, hfn, hblock]
  · rw [BasicBlock.variablesDefinedAtPosition_start]
    exact Locals.bindParams_covers hbind

theorem Locals.exprReady_of_coversVariables
    {locals : Locals} {expression : Expr}
    (h : locals.CoversVariables expression.variablesRead) :
    locals.ExprReady expression := by
  cases expression with
  | constant value => trivial
  | var identifier => exact h identifier (by simp [Expr.variablesRead])
  | add lhs rhs | lt lhs rhs =>
      exact ⟨h lhs (by simp [Expr.variablesRead]),
        h rhs (by simp [Expr.variablesRead])⟩
  | sload key => exact h key (by simp [Expr.variablesRead])

theorem MachineState.stmtReady_of_coversVariables
    {state : MachineState} {statement : Stmt}
    (h : state.locals.CoversVariables statement.variablesRead)
    (halloc : ∀ result size, statement = .mallocUninit result size →
      ∃ word alloc, state.locals.lookup size = .ok word ∧
        state.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = word.toNat)
    (hnonIcall : ∀ callee args dests, statement ≠ .icall callee args dests) :
    state.StmtReady statement := by
  cases statement with
  | assign result expression =>
      exact Locals.exprReady_of_coversVariables h
  | sstore key value | mstore32 key value =>
      exact ⟨h key (by simp [Stmt.variablesRead]),
        h value (by simp [Stmt.variablesRead])⟩
  | gas result => trivial
  | call callData =>
      exact ⟨h callData.callee (by simp [Stmt.variablesRead]),
        h callData.gas (by simp [Stmt.variablesRead])⟩
  | mallocUninit result size => exact halloc result size rfl
  | mload32 result offset => exact h offset (by simp [Stmt.variablesRead])
  | icall callee args dests => exact (hnonIcall callee args dests rfl).elim

theorem Program.decodeStmt_cursor
    {control nextControl : MachineControl} {statement : Stmt}
    (hdecode : program.decodeStmt control = some (nextControl, statement)) :
    ∃ cursor block index,
      control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.statements[index]? = some statement ∧
      nextControl = .running
        { cursor with position := block.absoluteToPosition (index + 1) } := by
  cases control with
  | returned values => simp [Program.decodeStmt] at hdecode
  | halted => simp [Program.decodeStmt] at hdecode
  | running cursor =>
      cases hposition : cursor.position with
      | terminator => simp [Program.decodeStmt, hposition] at hdecode
      | statement index =>
          cases hblock : program.block? cursor with
          | none => simp [Program.decodeStmt, hposition, hblock] at hdecode
          | some block =>
              cases hstatement : block.statements[index]? with
              | none =>
                  simp [Program.decodeStmt, hposition, hblock, hstatement] at hdecode
              | some found =>
                  simp [Program.decodeStmt, hposition, hblock, hstatement] at hdecode
                  obtain ⟨rfl, rfl⟩ := hdecode
                  exact ⟨cursor, block, index, rfl, hposition, hblock, hstatement, rfl⟩

theorem Program.terminatorAt_cursor
    {control : MachineControl} {terminator : Terminator}
    (hterminator : program.terminatorAt control = some terminator) :
    ∃ cursor block, control = .running cursor ∧ cursor.position = .terminator ∧
      program.block? cursor = some block ∧ block.terminator = terminator := by
  cases control with
  | returned values => simp [Program.terminatorAt] at hterminator
  | halted => simp [Program.terminatorAt] at hterminator
  | running cursor =>
      cases hposition : cursor.position with
      | statement index => simp [Program.terminatorAt, hposition] at hterminator
      | terminator =>
          cases hblock : program.block? cursor with
          | none => simp [Program.terminatorAt, hposition, hblock] at hterminator
          | some block =>
              simp [Program.terminatorAt, hposition, hblock] at hterminator
              subst terminator
              exact ⟨cursor, block, rfl, hposition, hblock, rfl⟩

theorem Program.WellFormed.decodeStmt_covers
    (hwf : program.WellFormed) {state : MachineState}
    {nextControl : MachineControl} {statement : Stmt}
    (hinvariant : state.LocalsCoverCursor program)
    (hdecode : program.decodeStmt state.control = some (nextControl, statement)) :
    ∃ cursor block index,
      state.control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.statements[index]? = some statement ∧
      nextControl = .running
        { cursor with position := block.absoluteToPosition (index + 1) } ∧
      state.locals.CoversVariables (block.variablesDefinedBefore index) ∧
      state.locals.CoversVariables statement.variablesRead := by
  obtain ⟨cursor, block, index, hcontrol, hposition, hblock, hstatement, hnext⟩ :=
    Program.decodeStmt_cursor hdecode
  unfold MachineState.LocalsCoverCursor at hinvariant
  rw [hcontrol] at hinvariant
  obtain ⟨coveredBlock, hcoveredBlock, hcover⟩ := hinvariant
  have hsame : coveredBlock = block := by
    exact Option.some.inj (hcoveredBlock.symm.trans hblock)
  subst coveredBlock
  rw [hposition] at hcover
  obtain ⟨fn, hfn, hmembership⟩ := Program.block?_function hblock
  have hstatic :=
    (hwf.variablesDefinedBeforeUse cursor.fn fn hfn block hmembership).1
      index statement hstatement
  refine ⟨cursor, block, index, hcontrol, hposition, hblock, hstatement,
    hnext, hcover, ?_⟩
  exact fun identifier hidentifier =>
    hcover identifier (hstatic identifier hidentifier)

theorem MachineState.localsCoverCursor_after_statement
    {state evaluated : MachineState} {nextControl : MachineControl}
    {statement : Stmt} {cursor : ProgramCursor} {block : BasicBlock} {index : Nat}
    (hblock : program.block? cursor = some block)
    (hstatement : block.statements[index]? = some statement)
    (hnext : nextControl = .running
      { cursor with position := block.absoluteToPosition (index + 1) })
    (hbefore : state.locals.CoversVariables (block.variablesDefinedBefore index))
    (hpreserves : ∀ identifier, state.locals.Defined identifier →
      evaluated.locals.Defined identifier)
    (hdefines : evaluated.locals.CoversVariables statement.variablesDefined) :
    ({ evaluated with control := nextControl } : MachineState).LocalsCoverCursor program := by
  subst nextControl
  refine ⟨block, ?_, ?_⟩
  · simpa [Program.block?] using hblock
  · rw [BasicBlock.variablesDefinedAtPosition_next hstatement]
    exact Locals.coversVariables_append
      (fun identifier hidentifier => hpreserves identifier
        (hbefore identifier hidentifier))
      hdefines

theorem Program.WellFormed.terminatorReady_of_localsCoverCursor
    (hwf : program.WellFormed) {state : MachineState}
    {cursor : ProgramCursor} {block : BasicBlock}
    (hinvariant : state.LocalsCoverCursor program)
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hblock : program.block? cursor = some block) :
    program.TerminatorReady cursor.fn state block := by
  unfold MachineState.LocalsCoverCursor at hinvariant
  rw [hcontrol] at hinvariant
  obtain ⟨coveredBlock, hcoveredBlock, hcover⟩ := hinvariant
  have hsame : coveredBlock = block :=
    Option.some.inj (hcoveredBlock.symm.trans hblock)
  subst coveredBlock
  rw [hposition] at hcover
  obtain ⟨fn, hfn, hmembership⟩ := Program.block?_function hblock
  have hstatic :=
    (hwf.variablesDefinedBeforeUse cursor.fn fn hfn block hmembership).2
  have hcoverStatic :
      state.locals.CoversVariables
        (block.terminator.variablesRead ++ block.outputs.toList) :=
    fun identifier hidentifier => hcover identifier (hstatic identifier hidentifier)
  have houtputs :
      state.locals.CoversVariables block.outputs.toList :=
    fun identifier hidentifier =>
      hcoverStatic identifier (List.mem_append_right _ hidentifier)
  have jumpReady (target : BlockId)
      (htarget : target ∈ block.terminator.jumpTargets) :
      program.JumpReady cursor.fn state block target := by
    obtain ⟨values, hvalues⟩ := Locals.lookupArray_total houtputs
    obtain ⟨targetBlock, htargetBlock, harity⟩ :=
      hwf.validJumpTargets cursor.fn fn hfn block hmembership target htarget
    refine ⟨⟨values, hvalues⟩, targetBlock, ?_, harity⟩
    simp [Program.block?, hfn, htargetBlock]
  unfold Program.TerminatorReady
  cases hterminator : block.terminator with
  | halt => trivial
  | jump target =>
      exact jumpReady target (by simp [hterminator, Terminator.jumpTargets])
  | branch condition thenTarget elseTarget =>
      have hcondition : state.locals.Defined condition :=
        hcoverStatic condition (by simp [hterminator, Terminator.variablesRead])
      obtain ⟨word, hword⟩ := hcondition
      refine ⟨word, hword, jumpReady _ ?_⟩
      by_cases hzero : word = 0
      · simp [hzero, hterminator, Terminator.jumpTargets]
      · simp [hzero, hterminator, Terminator.jumpTargets]
  | iret =>
      exact Locals.lookupArray_total houtputs

theorem Program.WellFormed.localsCoverCursor_step
    (hwf : program.WellFormed) {state state' : MachineState} {trace : Trace}
    (hinvariant : state.LocalsCoverCursor program)
    (hstep : SmallStep program ctx state trace state') :
    state'.LocalsCoverCursor program := by
  cases hstep with
  | assign hdecode heval =>
      rename_i evaluated nextControl result expression
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      obtain ⟨word, hword⟩ :=
        Expr.eval_total (Locals.exprReady_of_coversVariables hreads)
      rw [eval_assign_ok hword] at heval
      obtain rfl := Except.ok.inj heval
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign state.locals result word
  | sstore hdecode heval =>
      rename_i evaluated nextControl key value
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      have hready : state.locals.Defined key ∧ state.locals.Defined value :=
        ⟨hreads key (by simp [Stmt.variablesRead]),
          hreads value (by simp [Stmt.variablesRead])⟩
      obtain ⟨⟨keyWord, hkey⟩, valueWord, hvalue⟩ := hready
      rw [eval_sstore_ok hkey hvalue] at heval
      obtain rfl := Except.ok.inj heval
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun _ hdefined => hdefined
      · simp [Locals.CoversVariables, Stmt.variablesDefined]
  | gas hdecode heval =>
      rename_i evaluated nextControl result gas
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, -⟩ := hwf.decodeStmt_covers hinvariant hdecode
      rw [eval_gas_ok result gas state] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign state.locals result gas
  | call hdecode heval =>
      rename_i evaluated nextControl callData result record
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      obtain ⟨callee, hcallee⟩ :=
        hreads callData.callee (by simp [Stmt.variablesRead])
      obtain ⟨gas, hgas⟩ :=
        hreads callData.gas (by simp [Stmt.variablesRead])
      rw [eval_call_ok callData result state callee gas hcallee hgas] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign state.locals callData.result
          (Evm.UInt256.fromBool result.success)
  | mallocUninit hdecode hvalid heval =>
      rename_i evaluated nextControl allocation result size
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      obtain ⟨word, hword⟩ := hreads size (by simp [Stmt.variablesRead])
      have hsize : allocation.size = word.toNat := by
        by_contra hne
        simp [eval_malloc_uninit, StateT.run, Locals.lookupM, bind, Except.bind,
          StateT.bind, hword, hne, StateT.get,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          liftM, monadLift, MonadLift.monadLift, StateT.lift, Locals.assignM,
          throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at heval
      rw [eval_malloc_uninit_ok hword hsize] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign state.locals result allocation.offset
  | mstore32 hdecode heval =>
      rename_i evaluated nextControl offset value
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      obtain ⟨offsetWord, hoffset⟩ :=
        hreads offset (by simp [Stmt.variablesRead])
      obtain ⟨valueWord, hvalue⟩ :=
        hreads value (by simp [Stmt.variablesRead])
      rw [eval_mstore32_ok hoffset hvalue] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun _ hdefined => hdefined
      · simp [Locals.CoversVariables, Stmt.variablesDefined]
  | mload32 hdecode heval =>
      rename_i evaluated nextControl assumed result offset
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
      obtain ⟨offsetWord, hoffset⟩ :=
        hreads offset (by simp [Stmt.variablesRead])
      rw [eval_mload32_ok (assumed := ⟨assumed.toArray⟩) hoffset] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      apply MachineState.localsCoverCursor_after_statement
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign state.locals result _
  | icall hdecode hargs hcallee hbind =>
      rename_i globals' locals'
      obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
          hbefore, -⟩ := hwf.decodeStmt_covers hinvariant hdecode
      apply MachineState.localsCoverCursor_after_statement
        (evaluated := { state with globals := globals', locals := locals' })
        hblock hstatement hnext hbefore
      · exact fun identifier hdefined =>
          Locals.bindValues_preserves hbind hdefined
      · exact Locals.bindValues_covers hbind
  | icallHalted hdecode hargs hcallee =>
      trivial
  | terminator hterminator heval =>
      rename_i terminator
      obtain ⟨cursor, block, hcontrol, hposition, hblock, hblockTerminator⟩ :=
        Program.terminatorAt_cursor hterminator
      have hready := hwf.terminatorReady_of_localsCoverCursor
        hinvariant hcontrol hposition hblock
      have jumpPreserves {target : BlockId}
          (hjump : (eval_jump program target).run state = .ok ((), state'))
          (hjumpReady : program.JumpReady cursor.fn state block target) :
          state'.LocalsCoverCursor program := by
        obtain ⟨⟨values, hvalues⟩, targetBlock, htarget, harity⟩ := hjumpReady
        obtain ⟨locals', hbind⟩ := Locals.bindValues_total state.locals
          (harity.trans (mapM_ok_size hvalues).symm)
        have htarget' :
            program.block? { cursor with block := target } = some targetBlock := by
          simpa [Program.block?] using htarget
        have hexact : (eval_jump program target).run state =
            .ok ((), { state with
              locals := locals'
              control := .running
                { cursor with block := target, position := targetBlock.startPosition } }) := by
          simp [eval_jump, StateT.run, Locals.transfer, bind, Except.bind, StateT.bind,
            hcontrol, hblock, htarget', hvalues, hbind, StateT.get, get, getThe,
            MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, liftM, monadLift, MonadLift.monadLift,
            pure, Except.pure]
        rw [hexact] at hjump
        obtain rfl := (Prod.mk.inj (Except.ok.inj hjump)).2
        refine ⟨targetBlock, ?_, ?_⟩
        · simpa [Program.block?] using htarget
        · rw [BasicBlock.variablesDefinedAtPosition_start]
          exact Locals.bindValues_covers hbind
      unfold Program.TerminatorReady at hready
      cases terminator with
      | halt =>
          rw [hblockTerminator] at hready
          simp only [eval_terminator] at heval
          obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
          trivial
      | jump target =>
          rw [hblockTerminator] at hready
          exact jumpPreserves heval hready
      | branch condition thenTarget elseTarget =>
          rw [hblockTerminator] at hready
          obtain ⟨word, hword, hjumpReady⟩ := hready
          simp only [eval_terminator, StateT.run, bind, StateT.bind,
            Locals.lookupM, liftM, monadLift, MonadLift.monadLift,
            StateT.get, Except.bind, StateT.lift, pure, Except.pure, hword] at heval
          exact jumpPreserves heval hjumpReady
      | iret =>
          rw [hblockTerminator] at hready
          obtain ⟨values, hvalues⟩ := hready
          rw [eval_terminator_iret_ok hcontrol hblock hvalues] at heval
          obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
          trivial

theorem Program.WellFormed.localsCoverCursor_steps
    (hwf : program.WellFormed) {initial state : MachineState} {trace : Trace}
    (hinitial : initial.LocalsCoverCursor program)
    (hsteps : Steps program ctx initial trace state) :
    state.LocalsCoverCursor program := by
  induction hsteps using Steps.inductionOn with
  | refl => exact hinitial
  | tail start next ih => exact hwf.localsCoverCursor_step (ih hinitial) next

theorem Program.WellFormed.localsCoverCursor_runsFn
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {trace : Trace} {state : MachineState}
    (hrun : program.RunsFunction ctx function globals args trace state) :
    state.LocalsCoverCursor program := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  exact hwf.localsCoverCursor_steps
    (Program.callState?_localsCoverCursor hentry) hsteps

theorem Program.WellFormed.progress_reachable_nonIcall_proof
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol :
      (∃ nextControl statement,
        program.decodeStmt state.control = some (nextControl, statement) ∧
        ∀ callee callArgs destinations,
          statement ≠ .icall callee callArgs destinations) ∨
      ∃ terminator, program.terminatorAt state.control = some terminator)
    (hfreshAllocation :
      ∀ nextControl result size word,
        program.decodeStmt state.control =
            some (nextControl, .mallocUninit result size) →
        state.locals.lookup size = .ok word →
        ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
          allocation.size = word.toNat) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  have hinvariant := hwf.localsCoverCursor_runsFn hrun
  rcases hcontrol with
    ⟨nextControl, statement, hdecode, hnonIcall⟩ | ⟨terminator, hterminator⟩
  · obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
        hbefore, hreads⟩ := hwf.decodeStmt_covers hinvariant hdecode
    have hready : state.StmtReady statement := by
      apply MachineState.stmtReady_of_coversVariables hreads
      · intro result size heq
        subst statement
        obtain ⟨word, hword⟩ := hreads size (by simp [Stmt.variablesRead])
        obtain ⟨allocation, hvalid, hsize⟩ :=
          hfreshAllocation nextControl result size word hdecode hword
        exact ⟨word, allocation, hword, hvalid, hsize⟩
      · exact hnonIcall
    exact progress_stmt_proof hdecode hready
  · obtain ⟨cursor, block, hstateControl, hposition, hblock, -⟩ :=
      Program.terminatorAt_cursor hterminator
    have hready := hwf.terminatorReady_of_localsCoverCursor
      hinvariant hstateControl hposition hblock
    obtain ⟨state', hstep⟩ :=
      progress_terminator_proof hstateControl hposition hblock hready
    exact ⟨[], state', hstep⟩

end Sir
