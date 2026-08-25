import Sir.Vars.Proofs.Progress

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

def Vars.Block.variablesDefinedAtPosition
    (block : Vars.Block) : BlockPosition → List VarId
  | .statement index => block.variablesDefinedBefore index
  | .terminator => block.variablesDefinedBefore block.statements.size

def Locals.CoversVariables (locals : Locals) (identifiers : List VarId) : Prop :=
  ∀ identifier ∈ identifiers, locals.Defined identifier

def Vars.State.LocalsCoverCursor (program : Vars.Program) (state : Vars.State) : Prop :=
  match state.control with
  | .running cursor =>
      ∃ block, program.block? cursor = some block ∧
        state.environment.CoversVariables (block.variablesDefinedAtPosition cursor.position)
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

theorem Locals.bindValues_eq_assignPairs
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
  rw [Locals.bindValues_eq_assignPairs hsize] at hbind
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
  rw [Locals.bindValues_eq_assignPairs hsize] at hbind
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

theorem Vars.Block.variablesDefinedAtPosition_start (block : Vars.Block) :
    block.variablesDefinedAtPosition block.startPosition = block.inputs.toList := by
  cases hsize : block.statements.size with
  | zero =>
      simp [Vars.Block.startPosition, Vars.Block.absoluteToPosition,
        Vars.Block.variablesDefinedAtPosition, Vars.Block.variablesDefinedBefore,
        hsize]
  | succ size =>
      simp [Vars.Block.startPosition, Vars.Block.absoluteToPosition,
        Vars.Block.variablesDefinedAtPosition, Vars.Block.variablesDefinedBefore,
        hsize]

theorem Vars.Block.variablesDefinedAtPosition_next
    {block : Vars.Block} {index : Nat} {statement : Vars.Stmt}
    (hstatement : block.statements[index]? = some statement) :
    block.variablesDefinedAtPosition (block.absoluteToPosition (index + 1)) =
      block.variablesDefinedBefore index ++ statement.variablesDefined := by
  have hindex : index < block.statements.size :=
    (Array.getElem?_eq_some_iff.mp hstatement).choose
  have hbefore :
      block.variablesDefinedBefore (index + 1) =
        block.variablesDefinedBefore index ++ statement.variablesDefined := by
    simp [Vars.Block.variablesDefinedBefore, hstatement]
  by_cases hnext : index + 1 < block.statements.size
  · simp [Vars.Block.absoluteToPosition, hnext,
      Vars.Block.variablesDefinedAtPosition, hbefore]
  · have hsize : block.statements.size = index + 1 := by omega
    simp [Vars.Block.absoluteToPosition,
      Vars.Block.variablesDefinedAtPosition, hsize, hbefore]

theorem Vars.Program.block?_function
    {cursor : ProgramCursor} {block : Vars.Block}
    (hblock : program.block? cursor = some block) :
    ∃ fn, program.function? cursor.fn = some fn ∧ block ∈ fn.blocks := by
  cases hfn : program.function? cursor.fn with
  | none => simp [Vars.Program.block?, hfn] at hblock
  | some fn =>
      have hlocal : fn.block? cursor.block = some block := by
        simpa [Vars.Program.block?, hfn] using hblock
      exact ⟨fn, rfl, Array.mem_of_getElem? hlocal⟩

theorem Vars.Program.callState?_localsCoverCursor
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {state : Vars.State}
    (hentry : program.callState? function globals args = some state) :
    state.LocalsCoverCursor program := by
  obtain ⟨fn, locals, hfn, hbind, rfl⟩ :=
    Vars.Program.callState?_eq_some_iff.mp hentry
  refine ⟨fn.entry, ?_, ?_⟩
  · simp [Vars.Program.block?, hfn]
  · rw [Vars.Block.variablesDefinedAtPosition_start]
    exact Locals.bindParams_covers hbind

theorem Locals.exprReady_of_coversVariables
    {locals : Locals} {expression : Vars.Expr}
    (h : locals.CoversVariables expression.variablesRead) :
    locals.ExprReady expression := by
  cases expression with
  | constant value => trivial
  | var identifier => exact h identifier (by simp [Vars.Expr.variablesRead])
  | add lhs rhs | lt lhs rhs =>
      exact ⟨h lhs (by simp [Vars.Expr.variablesRead]),
        h rhs (by simp [Vars.Expr.variablesRead])⟩
  | sload key => exact h key (by simp [Vars.Expr.variablesRead])

theorem Vars.State.stmtReady_of_coversVariables
    {state : Vars.State} {statement : Vars.Stmt}
    (h : state.environment.CoversVariables statement.variablesRead)
    (hmalloc : ∀ result size, statement = .malloc result size →
      ∃ word alloc, state.environment.lookup size = .ok word ∧
        state.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = word.toNat ∧
        alloc.bytes = ByteArray.mk (Array.replicate word.toNat 0))
    (halloc : ∀ result size, statement = .mallocUninit result size →
      ∃ word alloc, state.environment.lookup size = .ok word ∧
        state.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = word.toNat)
    (hstore : ∀ offset value, statement = .mstore32 offset value →
      ∃ word, state.environment.lookup offset = .ok word ∧
        state.globals.memory.InBounds word.toNat 32)
    (hnonIcall : ∀ callee args dests, statement ≠ .icall callee args dests) :
    state.StmtReady statement := by
  cases statement with
  | assign result expression =>
      exact Locals.exprReady_of_coversVariables h
  | sstore key value =>
      exact ⟨h key (by simp [Vars.Stmt.variablesRead]),
        h value (by simp [Vars.Stmt.variablesRead])⟩
  | gas result => trivial
  | call callData =>
      exact ⟨h callData.callee (by simp [Vars.Stmt.variablesRead]),
        h callData.gas (by simp [Vars.Stmt.variablesRead])⟩
  | malloc result size => exact hmalloc result size rfl
  | mallocUninit result size => exact halloc result size rfl
  | mstore32 offset value =>
      obtain ⟨word, hword, hin⟩ := hstore offset value rfl
      exact ⟨word, hword, h value (by simp [Vars.Stmt.variablesRead]), hin⟩
  | mload32 result offset => exact h offset (by simp [Vars.Stmt.variablesRead])
  | icall callee args dests => exact (hnonIcall callee args dests rfl).elim

theorem Vars.Program.WellFormed.statementAt_covers
    (hwf : program.WellFormed) {state : Vars.State}
    {nextControl : Control} {statement : Vars.Stmt}
    (hinvariant : state.LocalsCoverCursor program)
    (hstmt : program.atStmt state = some (nextControl, statement)) :
    ∃ cursor block index,
      state.control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.statements[index]? = some statement ∧
      nextControl = .running
        { cursor with position := block.absoluteToPosition (index + 1) } ∧
      state.environment.CoversVariables (block.variablesDefinedBefore index) ∧
      state.environment.CoversVariables statement.variablesRead := by
  obtain ⟨cursor, block, index, hcontrol, hposition, hblock, hstatement, hnext⟩ :=
    Vars.Program.statementAt_cursor hstmt
  unfold Vars.State.LocalsCoverCursor at hinvariant
  rw [hcontrol] at hinvariant
  obtain ⟨coveredBlock, hcoveredBlock, hcover⟩ := hinvariant
  have hsame : coveredBlock = block := by
    exact Option.some.inj (hcoveredBlock.symm.trans hblock)
  subst coveredBlock
  rw [hposition] at hcover
  obtain ⟨fn, hfn, hmembership⟩ := Vars.Program.block?_function hblock
  have hstatic :=
    (hwf.variablesDefinedBeforeUse fn (Vars.Program.mem_functions_of_function? hfn) block hmembership).1
      index statement hstatement
  refine ⟨cursor, block, index, hcontrol, hposition, hblock, hstatement,
    hnext, hcover, ?_⟩
  exact fun identifier hidentifier =>
    hcover identifier (hstatic identifier hidentifier)

theorem Vars.State.localsCoverCursor_after_statement
    {state evaluated : Vars.State} {nextControl : Control}
    {statement : Vars.Stmt} {cursor : ProgramCursor} {block : Vars.Block} {index : Nat}
    (hblock : program.block? cursor = some block)
    (hstatement : block.statements[index]? = some statement)
    (hnext : nextControl = .running
      { cursor with position := block.absoluteToPosition (index + 1) })
    (hbefore : state.environment.CoversVariables (block.variablesDefinedBefore index))
    (hpreserves : ∀ identifier, state.environment.Defined identifier →
      evaluated.environment.Defined identifier)
    (hdefines : evaluated.environment.CoversVariables statement.variablesDefined) :
    Vars.State.LocalsCoverCursor program { evaluated with control := nextControl } := by
  subst nextControl
  refine ⟨block, ?_, ?_⟩
  · simpa [Vars.Program.block?] using hblock
  · rw [Vars.Block.variablesDefinedAtPosition_next hstatement]
    exact Locals.coversVariables_append
      (fun identifier hidentifier => hpreserves identifier
        (hbefore identifier hidentifier))
      hdefines

theorem Vars.Program.WellFormed.terminatorReady_of_localsCoverCursor
    (hwf : program.WellFormed) {state : Vars.State}
    {cursor : ProgramCursor} {block : Vars.Block}
    (hinvariant : state.LocalsCoverCursor program)
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hblock : program.block? cursor = some block) :
    program.TerminatorReady cursor.fn state block := by
  unfold Vars.State.LocalsCoverCursor at hinvariant
  rw [hcontrol] at hinvariant
  obtain ⟨coveredBlock, hcoveredBlock, hcover⟩ := hinvariant
  have hsame : coveredBlock = block :=
    Option.some.inj (hcoveredBlock.symm.trans hblock)
  subst coveredBlock
  rw [hposition] at hcover
  obtain ⟨fn, hfn, hmembership⟩ := Vars.Program.block?_function hblock
  have hstatic :=
    (hwf.variablesDefinedBeforeUse fn (Vars.Program.mem_functions_of_function? hfn) block hmembership).2
  have hcoverStatic :
      state.environment.CoversVariables
        (block.terminator.variablesRead ++ block.outputs.toList) :=
    fun identifier hidentifier => hcover identifier (hstatic identifier hidentifier)
  have houtputs :
      state.environment.CoversVariables block.outputs.toList :=
    fun identifier hidentifier =>
      hcoverStatic identifier (List.mem_append_right _ hidentifier)
  have jumpReady (target : BlockId)
      (htarget : target ∈ block.terminator.jumpTargets) :
      program.JumpReady cursor.fn state block target := by
    obtain ⟨values, hvalues⟩ := Locals.lookupArray_total houtputs
    obtain ⟨targetBlock, htargetBlock, harity⟩ :=
      hwf.validJumpTargets fn (Vars.Program.mem_functions_of_function? hfn) block hmembership target htarget
    refine ⟨⟨values, hvalues⟩, targetBlock, ?_, harity⟩
    simp [Vars.Program.block?, hfn, htargetBlock]
  unfold Vars.Program.TerminatorReady
  cases hterminator : block.terminator with
  | halt => trivial
  | jump target =>
      exact jumpReady target (by simp [hterminator, Vars.Terminator.jumpTargets])
  | branch condition thenTarget elseTarget =>
      have hcondition : state.environment.Defined condition :=
        hcoverStatic condition (by simp [hterminator, Vars.Terminator.variablesRead])
      obtain ⟨word, hword⟩ := hcondition
      refine ⟨word, hword, jumpReady _ ?_⟩
      by_cases hzero : word = 0
      · simp [hzero, hterminator, Vars.Terminator.jumpTargets]
      · simp [hzero, hterminator, Vars.Terminator.jumpTargets]
  | iret =>
      exact Locals.lookupArray_total houtputs

private theorem Vars.Program.WellFormed.localsCoverCursor_terminator
    (hwf : program.WellFormed) {state : Vars.State} {terminator : Vars.Terminator}
    {environment : Locals} {finalControl : Control}
    (hinvariant : state.LocalsCoverCursor program)
    (hterminator : program.atTerm state = some terminator)
    (heval : Vars.evaluateTerminator program state.environment state.control terminator =
      .ok (environment, finalControl)) :
    (State.of state.globals environment finalControl).LocalsCoverCursor program := by
  obtain ⟨cursor, block, hcontrol, hposition, hblock, hblockTerminator⟩ :=
    Vars.Program.terminatorAt_cursor hterminator
  have hready := hwf.terminatorReady_of_localsCoverCursor
    hinvariant hcontrol hposition hblock
  have jumpPreserves {target : BlockId} {locals : Locals} {control : Control}
      (hjump : Vars.jump program state.environment cursor target = .ok (locals, control))
      (hjumpReady : program.JumpReady cursor.fn state block target)
      (hfinal : environment = locals ∧ finalControl = control) :
      (State.of state.globals environment finalControl).LocalsCoverCursor program := by
    obtain ⟨⟨values, hvalues⟩, targetBlock, htarget, harity⟩ := hjumpReady
    obtain ⟨locals', hbind⟩ := Locals.bindValues_total state.environment
      (harity.trans (mapM_ok_size hvalues).symm)
    have htarget' :
        program.block? { cursor with block := target } = some targetBlock := by
      simpa [Vars.Program.block?] using htarget
    have hexact :
        Vars.jump program state.environment cursor target =
          .ok (locals', .running
            { cursor with block := target, position := targetBlock.startPosition }) := by
      apply Vars.jump_eq_ok hblock htarget' hvalues
        ((mapM_ok_size hvalues).trans harity.symm) hbind
    rw [hexact] at hjump
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hjump)
    obtain ⟨rfl, rfl⟩ := hfinal
    refine ⟨targetBlock, ?_, ?_⟩
    · simpa [Vars.Program.block?, State.of] using htarget
    · rw [Vars.Block.variablesDefinedAtPosition_start]
      exact Locals.bindValues_covers hbind
  unfold Vars.Program.TerminatorReady at hready
  cases terminator with
  | halt =>
      rw [hblockTerminator] at hready
      simp [Vars.evaluateTerminator] at heval
      obtain ⟨rfl, rfl⟩ := heval
      trivial
  | jump target =>
      rw [hblockTerminator] at hready
      simp [Vars.evaluateTerminator, hcontrol] at heval
      exact jumpPreserves heval hready ⟨rfl, rfl⟩
  | branch condition thenTarget elseTarget =>
      rw [hblockTerminator] at hready
      obtain ⟨word, hword, hjumpReady⟩ := hready
      simp [Vars.evaluateTerminator, hcontrol, hword] at heval
      exact jumpPreserves heval hjumpReady ⟨rfl, rfl⟩
  | iret =>
      rw [hblockTerminator] at hready
      obtain ⟨values, hvalues⟩ := hready
      rw [Vars.evaluateTerminator_iret_ok hcontrol hblock hvalues] at heval
      obtain ⟨rfl, rfl⟩ := heval
      trivial

theorem Vars.State.evaluate_covers
    {state : Vars.State} {statement : Vars.Stmt} {globals : Globals} {environment : Locals}
    (h : state.evaluate ctx statement = .ok (globals, environment)) :
    (∀ identifier, state.environment.Defined identifier → environment.Defined identifier) ∧
      environment.CoversVariables statement.variablesDefined := by
  cases statement with
  | assign result expression =>
      cases hexpr : Vars.evalExpr ctx state.environment state.globals expression with
      | error _ => simp [Vars.State.evaluate, Vars.evalStmt, hexpr] at h
      | ok value =>
          simp [Vars.State.evaluate, Vars.evalStmt, hexpr] at h
          obtain ⟨-, rfl⟩ := h
          refine ⟨fun _ hdefined => Locals.defined_assign_of_defined hdefined, ?_⟩
          intro identifier hidentifier
          simp [Vars.Stmt.variablesDefined] at hidentifier
          subst identifier
          exact Locals.defined_assign _ _ _
  | sstore keyVar valueVar =>
      cases hkey : state.lookup keyVar with
      | error _ => simp [Vars.State.evaluate, Vars.evalStmt, hkey, bind, Except.bind] at h
      | ok key =>
          cases hvalue : state.lookup valueVar with
          | error _ =>
              simp [Vars.State.evaluate, Vars.evalStmt, hkey, hvalue, bind, Except.bind] at h
          | ok value =>
              simp [Vars.State.evaluate, Vars.evalStmt, hkey, hvalue, bind, Except.bind] at h
              obtain ⟨-, rfl⟩ := h
              exact ⟨fun _ hdefined => hdefined, by
                simp [Locals.CoversVariables, Vars.Stmt.variablesDefined]⟩
  | gas _ | call _ | malloc _ _ | mallocUninit _ _ | mstore32 _ _ | mload32 _ _
  | icall _ _ _ =>
      simp [Vars.State.evaluate, Vars.evalStmt] at h

theorem Vars.Program.WellFormed.localsCoverCursor_step
    (hwf : program.WellFormed) {state final : Vars.State} {trace : Trace}
    (hinvariant : state.LocalsCoverCursor program)
    (hstep : Vars.SmallStep program ctx state trace final) :
    final.LocalsCoverCursor program := by
  cases hstep with
  | evaluate hstmt heval =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      obtain ⟨hpreserves, hdefines⟩ := Vars.State.evaluate_covers heval
      exact Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨_, _, state.control⟩)
        hblock hstatementAt hnext hbefore hpreserves hdefines
  | gas hstmt =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      apply Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨state.globals, state.environment.assign _ _, state.control⟩)
        hblock hstatementAt hnext hbefore
      · exact fun identifier hdefined => Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Vars.Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign _ _ _
  | call hstmt =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      apply Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨state.globals, state.environment.assign _ _, state.control⟩)
        hblock hstatementAt hnext hbefore
      · exact fun identifier hdefined => Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Vars.Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign _ _ _
  | malloc hstmt _ _ =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      apply Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨state.globals, state.environment.assign _ _, state.control⟩)
        hblock hstatementAt hnext hbefore
      · exact fun identifier hdefined => Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Vars.Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign _ _ _
  | mallocUninit hstmt _ =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      apply Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨state.globals, state.environment.assign _ _, state.control⟩)
        hblock hstatementAt hnext hbefore
      · exact fun identifier hdefined => Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Vars.Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign _ _ _
  | mstore32 hstmt _ =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      have hcover := Vars.State.localsCoverCursor_after_statement
        (evaluated := state) hblock hstatementAt hnext hbefore
        (fun _ h => h) (by simp [Locals.CoversVariables, Vars.Stmt.variablesDefined])
      simpa [Vars.State.LocalsCoverCursor] using hcover
  | mload32 hstmt =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext, hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      apply Vars.State.localsCoverCursor_after_statement
        (evaluated := ⟨state.globals, state.environment.assign _ _, state.control⟩)
        hblock hstatementAt hnext hbefore
      · exact fun identifier hdefined => Locals.defined_assign_of_defined hdefined
      · intro identifier hidentifier
        simp [Vars.Stmt.variablesDefined] at hidentifier
        subst identifier
        exact Locals.defined_assign _ _ _
  | icall hstmt hfetch hcallee hresume =>
      obtain ⟨cursor, block, index, -, -, hblock, hstatementAt, hnext,
          hbefore, -⟩ :=
        hwf.statementAt_covers hinvariant hstmt
      cases ‹FunctionOutcome› with
      | returned results =>
          obtain ⟨hbind, hcontrol'⟩ := Vars.resume_returned_eq_ok_iff.mp hresume
          subst_vars
          apply Vars.State.localsCoverCursor_after_statement
            (evaluated := ⟨_, _, state.control⟩)
            hblock hstatementAt rfl hbefore
          · exact fun identifier hdefined =>
              Locals.bindValues_preserves hbind hdefined
          · simpa [Vars.Stmt.variablesDefined] using Locals.bindValues_covers hbind
      | halted =>
          obtain ⟨rfl, rfl⟩ := Vars.resume_halted_eq_ok_iff.mp hresume
          trivial
  | control hterminator heval =>
      exact hwf.localsCoverCursor_terminator hinvariant hterminator heval

theorem Vars.Program.WellFormed.localsCoverCursor_steps
    (hwf : program.WellFormed) {initial final : Vars.State} {trace : Trace}
    (hinitial : initial.LocalsCoverCursor program)
    (hsteps : Vars.Steps program ctx initial trace final) :
    final.LocalsCoverCursor program := by
  exact Vars.Steps.inductionOn
    (motive := fun initial _ final _ =>
      Vars.State.LocalsCoverCursor program initial →
        Vars.State.LocalsCoverCursor program final)
    (fun _ hinvariant => hinvariant)
    (fun _ next ih hinvariant =>
      hwf.localsCoverCursor_step (ih hinvariant) next)
    hsteps hinitial

theorem Vars.Program.WellFormed.localsCoverCursor_runsFn
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {trace : Trace} {state : Vars.State}
    (hrun : program.RunsFunction ctx function globals args trace state) :
    state.LocalsCoverCursor program := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  exact hwf.localsCoverCursor_steps
    (Vars.Program.callState?_localsCoverCursor hentry) hsteps

theorem Vars.Proofs.Program.WellFormed.progress_reachable_nonIcall
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : Vars.State}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hfreshAllocation : program.AllocationAvailable state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', Vars.SmallStep program ctx state trace state' := by
  have hinvariant := hwf.localsCoverCursor_runsFn hrun
  rcases hcontrol with
    ⟨nextControl, statement, hstmt, hnonIcall⟩ | ⟨terminator, hterminator⟩
  · obtain ⟨cursor, block, index, -, -, hblock, hstatement, hnext,
        hbefore, hreads⟩ := hwf.statementAt_covers hinvariant hstmt
    have hready : state.StmtReady statement := by
      apply Vars.State.stmtReady_of_coversVariables hreads
      · intro result size heq
        subst statement
        obtain ⟨word, hword⟩ := hreads size (by simp [Vars.Stmt.variablesRead])
        obtain ⟨allocation, hvalid, hsize, hzero⟩ :=
          hfreshAllocation.1 nextControl result size word hstmt hword
        exact ⟨word, allocation, hword, hvalid, hsize, hzero⟩
      · intro result size heq
        subst statement
        obtain ⟨word, hword⟩ := hreads size (by simp [Vars.Stmt.variablesRead])
        obtain ⟨allocation, hvalid, hsize⟩ :=
          hfreshAllocation.2 nextControl result size word hstmt hword
        exact ⟨word, allocation, hword, hvalid, hsize⟩
      · intro offset value heq
        subst statement
        obtain ⟨word, hword⟩ := hreads offset (by simp [Vars.Stmt.variablesRead])
        exact ⟨word, hword, hstore nextControl offset value word hstmt hword⟩
      · exact hnonIcall
    exact Vars.Proofs.progress_stmt hstmt hready
  · obtain ⟨cursor, block, hstateControl, hposition, hblock, -⟩ :=
      Vars.Program.terminatorAt_cursor hterminator
    have hready := hwf.terminatorReady_of_localsCoverCursor
      hinvariant hstateControl hposition hblock
    obtain ⟨state', hstep⟩ :=
      Vars.Proofs.progress_terminator hstateControl hposition hblock hready
    exact ⟨[], state', hstep⟩

end Sir
