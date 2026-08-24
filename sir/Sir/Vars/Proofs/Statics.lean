import Sir.Vars.Proofs.Dialogue

namespace Sir

variable {program : Vars.Program}

@[simp]
theorem Vars.Function.mem_blocks {fn : Vars.Function} {b : Vars.Block} :
    b ∈ fn.blocks ↔ b = fn.entry ∨ b ∈ fn.rest := by
  simp [Vars.Function.blocks]

@[simp]
theorem Vars.Function.block?_zero (fn : Vars.Function) : fn.block? ⟨0⟩ = some fn.entry := by
  simp [Vars.Function.block?, Vars.Function.blocks]

@[simp]
theorem Vars.Function.block?_succ (fn : Vars.Function) (n : Nat) :
    fn.block? ⟨n + 1⟩ = fn.rest[n]? := by
  simp [Vars.Function.block?, Vars.Function.blocks, Array.getElem?_append_right]

@[simp]
theorem Vars.Program.mem_functions {p : Vars.Program} {fn : Vars.Function} :
    fn ∈ p.functions ↔ fn = p.init ∨ p.main = some fn ∨ fn ∈ p.rest := by
  simp [Vars.Program.functions, Option.mem_toArray]

@[simp]
theorem Vars.Program.function?_initId (p : Vars.Program) :
    p.function? p.initId = some p.init := by
  simp [Vars.Program.function?, Vars.Program.functions, Vars.Program.initId]

theorem Vars.Program.function?_mainId {p : Vars.Program} {f : FunctionId}
    (h : p.mainId? = some f) : ∃ m, p.main = some m ∧ p.function? f = some m := by
  cases hmain : p.main with
  | none => simp [Vars.Program.mainId?, hmain] at h
  | some m =>
    refine ⟨m, rfl, ?_⟩
    simp [Vars.Program.mainId?, hmain] at h
    subst h
    simp [Vars.Program.function?, Vars.Program.functions, hmain, Array.getElem?_append]

theorem Vars.Program.callState?_eq_some_iff
    {p : Vars.Program} {f : FunctionId} {g : Globals} {args : Array Word}
    {s : Vars.State} :
    p.callState? f g args = some s ↔
      ∃ fn locals₀, p.function? f = some fn ∧
        Locals.bindParams fn.entry.inputs args = .ok locals₀ ∧
        s = ⟨g, locals₀,
          .running { fn := f, block := ⟨0⟩, position := fn.entry.startPosition }⟩ := by
  constructor
  · intro h
    cases hfn : p.function? f with
    | none => simp [Vars.Program.callState?, hfn] at h
    | some fn =>
      cases hbind : Locals.bindParams fn.entry.inputs args with
      | error e => simp [Vars.Program.callState?, hfn, hbind] at h
      | ok locals₀ =>
        have hs : ⟨g, locals₀, .running {
            fn := f, block := ⟨0⟩, position := fn.entry.startPosition }⟩ = s := by
          simpa [Vars.Program.callState?, hfn, hbind] using h
        exact ⟨fn, locals₀, rfl, hbind, hs.symm⟩
  · rintro ⟨fn, locals₀, hfn, hbind, rfl⟩
    simp [Vars.Program.callState?, hfn, hbind]

theorem Vars.Program.statementAt_next_block
    {control next : Control} {stmt : Vars.Stmt} {cursor : ProgramCursor}
    (hctrl : control = .running cursor)
    (h : program.statementAt control = some (next, stmt)) :
    ∃ pos, next = .running { cursor with position := pos } := by
  subst hctrl
  obtain ⟨fid, blk, pos⟩ := cursor
  cases pos with
  | terminator => simp [Vars.Program.statementAt] at h
  | statement index =>
    simp only [Vars.Program.statementAt, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨block, hblock, stmt', hstmt', hnext, -⟩ := h
    exact ⟨_, hnext.symm⟩

theorem Vars.Program.statementAt_next_running
    {control next : Control} {stmt : Vars.Stmt}
    (h : program.statementAt control = some (next, stmt)) :
    ∃ cursor, next = .running cursor := by
  cases control with
  | returned rs => simp [Vars.Program.statementAt] at h
  | halted => simp [Vars.Program.statementAt] at h
  | running cursor =>
    obtain ⟨pos, hnext⟩ := Vars.Program.statementAt_next_block rfl h
    exact ⟨_, hnext⟩

def Vars.Function.terminatorOf (fn : Vars.Function) (block : BlockId) : Option Vars.Terminator :=
  (fn.block? block).map (·.terminator)

def Vars.Program.terminatorOf (program : Vars.Program) (cursor : ProgramCursor) : Option Vars.Terminator :=
  (program.block? cursor).map (·.terminator)

theorem Vars.Program.terminatorAt_inv
    {control : Control} {cursor : ProgramCursor} {term : Vars.Terminator}
    (hctrl : control = .running cursor)
    (h : program.terminatorAt control = some term) :
    program.terminatorOf cursor = some term := by
  subst hctrl
  obtain ⟨fid, blk, pos⟩ := cursor
  cases pos with
  | statement index => simp [Vars.Program.terminatorAt] at h
  | terminator =>
    cases hb : program.block? { fn := fid, block := blk, position := .terminator } with
    | none => simp [Vars.Program.terminatorAt, hb] at h
    | some bb =>
      simp only [Vars.Program.terminatorAt, hb] at h
      simpa [Vars.Program.terminatorOf, hb] using h

theorem Vars.Program.statementAt_cursor
    {control nextControl : Control} {statement : Vars.Stmt}
    (hstmt : program.statementAt control = some (nextControl, statement)) :
    ∃ cursor block index,
      control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.statements[index]? = some statement ∧
      nextControl = .running
        { cursor with position := block.absoluteToPosition (index + 1) } := by
  cases control with
  | returned values => simp [Vars.Program.statementAt] at hstmt
  | halted => simp [Vars.Program.statementAt] at hstmt
  | running cursor =>
      cases hposition : cursor.position with
      | terminator => simp [Vars.Program.statementAt, hposition] at hstmt
      | statement index =>
          cases hblock : program.block? cursor with
          | none => simp [Vars.Program.statementAt, hposition, hblock] at hstmt
          | some block =>
              cases hstatement : block.statements[index]? with
              | none =>
                  simp [Vars.Program.statementAt, hposition, hblock, hstatement] at hstmt
              | some found =>
                  simp [Vars.Program.statementAt, hposition, hblock, hstatement] at hstmt
                  obtain ⟨rfl, rfl⟩ := hstmt
                  exact ⟨cursor, block, index, rfl, hposition, hblock, hstatement, rfl⟩

theorem Vars.Program.terminatorAt_cursor
    {control : Control} {terminator : Vars.Terminator}
    (hterminator : program.terminatorAt control = some terminator) :
    ∃ cursor block, control = .running cursor ∧ cursor.position = .terminator ∧
      program.block? cursor = some block ∧ block.terminator = terminator := by
  cases control with
  | returned values => simp [Vars.Program.terminatorAt] at hterminator
  | halted => simp [Vars.Program.terminatorAt] at hterminator
  | running cursor =>
      cases hposition : cursor.position with
      | statement index => simp [Vars.Program.terminatorAt, hposition] at hterminator
      | terminator =>
          cases hblock : program.block? cursor with
          | none => simp [Vars.Program.terminatorAt, hposition, hblock] at hterminator
          | some block =>
              simp [Vars.Program.terminatorAt, hposition, hblock] at hterminator
              subst terminator
              exact ⟨cursor, block, rfl, hposition, hblock, rfl⟩

@[simp]
theorem Vars.Program.statementAt_returned (results : Array Word) :
    program.statementAt (.returned results) = none := rfl

@[simp]
theorem Vars.Program.statementAt_halted : program.statementAt .halted = none := rfl

@[simp]
theorem Vars.Program.terminatorAt_returned (results : Array Word) :
    program.terminatorAt (.returned results) = none := rfl

@[simp]
theorem Vars.Program.terminatorAt_halted : program.terminatorAt .halted = none := rfl

@[simp]
theorem Vars.resume_returned_eq_ok_iff
    {results : Array Word} {env env' : Locals} {dst : Array VarId}
    {next control' : Control} :
    Vars.resume (.returned results) env dst next = .ok (env', control') ↔
      Locals.bindReturns env dst results = .ok env' ∧ control' = next := by
  cases hbind : Locals.bindReturns env dst results <;>
    simp [Vars.resume, hbind, bind, Except.bind, eq_comm]

@[simp]
theorem Vars.resume_halted (env : Locals) (dst : Array VarId) (next : Control) :
    Vars.resume .halted env dst next = .ok (.empty, .halted) := rfl

@[simp]
theorem Vars.resume_halted_eq_ok_iff
    {env env' : Locals} {dst : Array VarId} {next control' : Control} :
    Vars.resume .halted env dst next = .ok (env', control') ↔
      env' = .empty ∧ control' = .halted := by
  simp [Vars.resume, eq_comm]

end Sir
namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

theorem Vars.jump_eq_ok
    {locals nextLocals : Locals} {cursor : ProgramCursor} {target : BlockId}
    {sourceBlock targetBlock : Vars.Block} {values : Array Word}
    (hsource : program.block? cursor = some sourceBlock)
    (htarget : program.block? { cursor with block := target } = some targetBlock)
    (houtputs : sourceBlock.outputs.mapM locals.lookup = .ok values)
    (harity : values.size = targetBlock.inputs.size)
    (hbind : Locals.bindValues locals targetBlock.inputs values = .ok nextLocals) :
    Vars.jump program locals cursor target = .ok (nextLocals, .running
      { cursor with block := target, position := targetBlock.startPosition }) := by
  simp [Vars.jump, hsource, htarget, houtputs, bind, Except.bind, pure, Except.pure,
    harity, hbind]

private theorem Vars.jump_control
    {locals : Locals} {cursor : ProgramCursor} {target : BlockId}
    {nextLocals : Locals} {control : Control}
    (h : Vars.jump program locals cursor target = .ok (nextLocals, control)) :
    ∃ targetBlock,
      program.block? { cursor with block := target } = some targetBlock ∧
      control = .running
        { cursor with block := target, position := targetBlock.startPosition } := by
  dsimp (config := {zetaDelta := true}) [Vars.jump] at h
  cases hsrc : program.block? cursor with
  | none => simp [hsrc] at h
  | some sourceBlock =>
      cases htgt : program.block? { cursor with block := target } with
      | none => simp [hsrc, htgt] at h
      | some targetBlock =>
          simp [hsrc, htgt] at h
          refine ⟨targetBlock, rfl, ?_⟩
          cases hmap : sourceBlock.outputs.mapM locals.lookup with
          | error e => simp [hmap, bind, Except.bind] at h
          | ok values =>
              simp [hmap] at h
              simp only [bind, Except.bind] at h
              split_ifs at h with hsize
              · cases hbind : Locals.bindValues locals targetBlock.inputs values with
                | error e => simp [hbind] at h
                | ok _ => simp [hbind] at h; exact h.2.symm

theorem Vars.evaluateTerminator_iret_inv
    {s : Vars.State} {locals : Locals} {control : Control}
    (h : Vars.evaluateTerminator program s.environment s.control .iret =
      .ok (locals, control)) :
    ∃ cursor block rs, s.control = .running cursor ∧
      program.block? cursor = some block ∧
      block.outputs.mapM (s.environment.lookup ·) = .ok rs ∧
      locals = s.environment ∧ control = .returned rs := by
  cases hctrl : s.control with
  | returned _ | halted => simp [Vars.evaluateTerminator, hctrl] at h
  | running cursor =>
      cases hblock : program.block? cursor with
      | none => simp [Vars.evaluateTerminator, hctrl, hblock] at h
      | some block =>
          cases hrs : block.outputs.mapM (s.environment.lookup ·) with
          | error _ => simp [Vars.evaluateTerminator, hctrl, hblock, hrs, bind, Except.bind] at h
          | ok rs =>
              simp [Vars.evaluateTerminator, hctrl, hblock, hrs] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨cursor, block, rs, rfl, hblock, hrs, rfl, rfl⟩

private theorem Vars.evaluateTerminator_preserves_function
    {cursor : ProgramCursor} {state : Vars.State} {terminator : Vars.Terminator}
    {locals : Locals} {finalControl : Control}
    (hcontrol : state.control = .running cursor)
    (heval : Vars.evaluateTerminator program state.environment state.control terminator =
      .ok (locals, finalControl)) :
    finalControl = .halted ∨ (∃ results, finalControl = .returned results) ∨
      ∃ cursor', finalControl = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases terminator with
  | halt =>
      simp [Vars.evaluateTerminator] at heval
      obtain ⟨rfl, rfl⟩ := heval
      exact .inl rfl
  | jump target =>
      simp [Vars.evaluateTerminator, hcontrol] at heval
      obtain ⟨targetBlock, -, hcontrol'⟩ := Vars.jump_control heval
      exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | branch condition thenTarget elseTarget =>
      simp [Vars.evaluateTerminator, hcontrol] at heval
      cases hcondition : state.environment.lookup condition with
      | error _ => simp [hcondition, bind, Except.bind] at heval
      | ok value =>
          simp [hcondition, bind, Except.bind] at heval
          obtain ⟨targetBlock, -, hcontrol'⟩ := Vars.jump_control heval
          exact .inr (.inr ⟨_, hcontrol', rfl⟩)
  | iret =>
      obtain ⟨_, _, results, -, -, -, -, rfl⟩ := Vars.evaluateTerminator_iret_inv heval
      exact .inr (.inl ⟨results, rfl⟩)

private theorem Vars.evaluateTerminator_returned_inv
    {state : Vars.State} {terminator : Vars.Terminator} {results : Array Word}
    {locals : Locals} {finalControl : Control}
    (hterm : program.atTerm state = some terminator)
    (heval : Vars.evaluateTerminator program state.environment state.control terminator =
      .ok (locals, finalControl))
    (hreturn : finalControl = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.environment.lookup ·) = .ok results := by
  cases terminator with
  | halt =>
      simp [Vars.evaluateTerminator] at heval
      obtain ⟨rfl, rfl⟩ := heval
      cases hreturn
  | jump target =>
      simp [Vars.evaluateTerminator] at heval
      cases hctrl : state.control with
      | returned _ | halted => simp [hctrl] at heval
      | running cursor =>
          simp [hctrl] at heval
          obtain ⟨_, -, hcontrol'⟩ := Vars.jump_control heval
          rw [hcontrol'] at hreturn
          cases hreturn
  | branch condition thenTarget elseTarget =>
      simp [Vars.evaluateTerminator] at heval
      cases hctrl : state.control with
      | returned _ | halted => simp [hctrl] at heval
      | running cursor =>
          simp [hctrl] at heval
          cases hcondition : state.environment.lookup condition with
          | error _ => simp [hcondition, bind, Except.bind] at heval
          | ok value =>
              simp [hcondition, bind, Except.bind] at heval
              obtain ⟨_, -, hcontrol'⟩ := Vars.jump_control heval
              rw [hcontrol'] at hreturn
              cases hreturn
  | iret =>
      obtain ⟨cursor, block, actual, hcontrol, hblock, houtputs, -, rfl⟩ :=
        Vars.evaluateTerminator_iret_inv heval
      obtain rfl := Control.returned.inj hreturn
      cases hposition : cursor.position with
      | statement index =>
          simp [Vars.Program.atTerm, Vars.Program.terminatorAt, hcontrol, hposition] at hterm
      | terminator =>
          have hblockTerminator : block.terminator = .iret := by
            simpa [Vars.Program.atTerm, Vars.Program.terminatorAt, hcontrol, hposition,
              hblock] using hterm
          exact ⟨cursor, block, hcontrol, hblock, hblockTerminator, houtputs⟩

theorem Vars.SmallStep.preserves_function
    {cursor : ProgramCursor} {state final : Vars.State} {trace : Trace}
    (h : Vars.SmallStep program ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | evaluate hstmt _ =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | gas hstmt =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | call hstmt =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | malloc hstmt _ _ =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mallocUninit hstmt _ =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mstore32 hstmt _ =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mload32 hstmt =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | icall hstmt hargs hcallee hresume =>
      obtain ⟨position, hnext⟩ := Vars.Program.statementAt_next_block hcontrol hstmt
      cases ‹FunctionOutcome› with
      | returned results =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_returned_eq_ok_iff.mp hresume
          subst hcontrol'
          exact .inr (.inr ⟨_, hnext, rfl⟩)
      | halted =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_halted_eq_ok_iff.mp hresume
          subst hcontrol'
          exact .inl rfl
  | control hterm heval =>
      simpa [State.of] using Vars.evaluateTerminator_preserves_function hcontrol heval

theorem Vars.Proofs.Steps.preserves_function
    {cursor : ProgramCursor} {state final : Vars.State} {trace : Trace}
    (h : Vars.Steps program ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  exact Vars.Steps.inductionOn
    (motive := fun state _ final _ => state.control = .running cursor →
      final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
        ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn)
    (fun _ hcontrol => .inr (.inr ⟨cursor, hcontrol, rfl⟩))
    (fun _ next ih hcontrol => by
      rcases ih hcontrol with hhalt | ⟨results, hreturn⟩ | ⟨cursor', hcontrol', hfn⟩
      · exact absurd next (stuck_of_exit (outcome := .halted) hhalt _ _)
      · exact absurd next (stuck_of_exit (outcome := .returned _) hreturn _ _)
      · rcases Vars.SmallStep.preserves_function next hcontrol' with
          hhalt | hreturned | ⟨cursor'', hcontrol'', hfn'⟩
        · exact .inl hhalt
        · exact .inr (.inl hreturned)
        · exact .inr (.inr ⟨cursor'', hcontrol'', hfn'.trans hfn⟩))
    h hcontrol

theorem Vars.SmallStep.returned_inv
    {state final : Vars.State} {trace : Trace} {results : Array Word}
    (h : Vars.SmallStep program ctx state trace final)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (state.environment.lookup ·) = .ok results := by
  cases h with
  | evaluate hstmt _ =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | gas hstmt =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | call hstmt =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | malloc hstmt _ _ =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | mallocUninit hstmt _ =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | mstore32 hstmt _ =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | mload32 hstmt =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      rw [hnext] at hreturn
      cases hreturn
  | icall hstmt hargs hcallee hresume =>
      obtain ⟨cursor, hnext⟩ := Vars.Program.statementAt_next_running hstmt
      cases ‹FunctionOutcome› with
      | returned actual =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_returned_eq_ok_iff.mp hresume
          subst hcontrol'
          rw [hnext] at hreturn
          cases hreturn
      | halted =>
          obtain ⟨-, hcontrol'⟩ := Vars.resume_halted_eq_ok_iff.mp hresume
          subst hcontrol'
          cases hreturn
  | control hterm heval =>
      exact Vars.evaluateTerminator_returned_inv hterm heval (by
        simp [State.of] at hreturn; exact hreturn)

end Sir

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

def Vars.Program.paramsOf (program : Vars.Program) (function : FunctionId) : Option (Array VarId) :=
  (program.function? function).map (·.paramsOf)

theorem Vars.Program.mem_functions_of_function? {p : Vars.Program} {f : FunctionId} {fn : Vars.Function}
    (h : p.function? f = some fn) : fn ∈ p.functions :=
  Array.mem_of_getElem? h

theorem Vars.Program.functionInputOutputArity_iff
    {p : Vars.Program} {inputCount : Nat} {outputCount : Option Nat}
    {functionId : FunctionId} :
    p.FunctionInputOutputArity inputCount outputCount functionId ↔
      ∃ fn, p.function? functionId = some fn ∧
        fn.paramsOf.size = inputCount ∧ fn.outputs? = outputCount := by
  rfl

theorem Vars.Program.WellFormed.callEdge_wellFounded
    (hwf : program.WellFormed) : WellFounded (Function.swap program.callEdge) := by
  classical
  let validFunctions := (Finset.range program.functions.size).image FunctionId.mk
  let ancestors (f : FunctionId) := validFunctions.filter fun predecessor =>
    Relation.TransGen (Function.swap program.callEdge) predecessor f
  let rank (f : FunctionId) :=
    if f.id < program.functions.size then (ancestors f).card + 1 else 0
  apply Subrelation.wf (r := fun predecessor caller => rank predecessor < rank caller) _
    (measure rank).wf
  intro predecessor caller hEdge
  have callerValid : caller.id < program.functions.size := by
    rcases hEdge with ⟨args, dests, fn, hfn, hstmt⟩
    exact (Array.getElem?_eq_some_iff.mp hfn).1
  by_cases predecessorValid : predecessor.id < program.functions.size
  · have ancestorsSubset : ancestors predecessor ⊆ ancestors caller := by
      intro f hf
      simp only [ancestors, Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.tail hEdge⟩
    have predecessorMem : predecessor ∈ ancestors caller := by
      simp only [ancestors, Finset.mem_filter, validFunctions, Finset.mem_image,
        Finset.mem_range]
      exact ⟨⟨predecessor.id, predecessorValid, rfl⟩,
        Relation.TransGen.single hEdge⟩
    have predecessorNotMem : predecessor ∉ ancestors predecessor := by
      intro h
      exact hwf.acyclicCalls predecessor (Finset.mem_filter.mp h).2.swap
    have ancestorsStrict : ancestors predecessor ⊂ ancestors caller :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨ancestorsSubset, fun h => predecessorNotMem (h ▸ predecessorMem)⟩
    simp only [rank, predecessorValid, callerValid, ↓reduceIte]
    exact Nat.add_lt_add_right (Finset.card_lt_card ancestorsStrict) 1
  · simp [rank, predecessorValid, callerValid]

private theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = .ok bs → bs.length = l.length
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      simp [← h]
  | a :: l, bs, h => by
      simp only [List.mapM_cons] at h
      cases hfa : f a with
      | error e => simp [hfa, bind, Except.bind] at h
      | ok b =>
        cases hml : l.mapM f with
        | error e => simp [hfa, hml, bind, Except.bind] at h
        | ok bs' =>
          simp only [hfa, hml, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at h
          simp [← h, mapM_ok_length hml]

theorem mapM_ok_size {α β ε : Type} {f : α → Except ε β}
    {as : Array α} {bs : Array β} (h : as.mapM f = .ok bs) : bs.size = as.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hml : as.toList.mapM f with
  | error e => simp [hml, Functor.map, Except.map] at h
  | ok l =>
    simp only [hml, Functor.map, Except.map, Except.ok.injEq] at h
    simpa [← h] using mapM_ok_length hml

theorem Locals.bindValues_total (dst : Locals) {targetVars : Array VarId}
    {vs : Array Word} (h : targetVars.size = vs.size) :
    ∃ l', Locals.bindValues dst targetVars vs = .ok l' :=
  ⟨_, by simp [Locals.bindValues, h]; rfl⟩

theorem Vars.Program.WellFormed.icall_paramsOf
    (hwf : program.WellFormed) {control nextControl : Control}
    {callee : FunctionId} {args dests : Array VarId}
    (hstmt : program.statementAt control = some (nextControl, .icall callee args dests)) :
    (∃ ps, program.paramsOf callee = some ps ∧ ps.size = args.size) ∧
      ((program.function? callee).bind (·.outputs?)).getD 0 = dests.size := by
  obtain ⟨outputs, harity, hdests⟩ :=
    hwf.icallArity callee args dests (Vars.Program.statementAt_mem hstmt)
  rcases Vars.Program.functionInputOutputArity_iff.mp harity with
    ⟨fn, hfn, hparams, houtputs⟩
  refine ⟨⟨fn.paramsOf, ?_, hparams⟩, ?_⟩
  · simp [Vars.Program.paramsOf, hfn]
  · simp [hfn, houtputs, hdests]

theorem Vars.Program.WellFormed.icall_bindParams
    (hwf : program.WellFormed) {s : Vars.State} {nextControl : Control}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    (hstmt : program.atStmt s = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.environment.lookup ·) = .ok vs) :
    ∃ ps locals₀, program.paramsOf callee = some ps ∧
      Locals.bindParams ps vs = .ok locals₀ := by
  obtain ⟨⟨ps, hps, hsize⟩, -⟩ := hwf.icall_paramsOf hstmt
  obtain ⟨locals₀, hbind⟩ :=
    Locals.bindValues_total Locals.empty (hsize.trans (mapM_ok_size hargs).symm)
  exact ⟨ps, locals₀, hps, hbind⟩

theorem Vars.Proofs.Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {function : FunctionId} {globals globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hrun : Vars.EvalFn program ctx
      function globals args trace globals' (.returned results)) :
    (program.function? function).bind (·.outputs?) = some results.size := by
  cases hrun with
  | exit hentry hsteps hreturn =>
      obtain ⟨fn, locals₀, hfn, hbind, rfl⟩ :=
        Vars.Program.callState?_eq_some_iff.mp hentry
      cases hsteps with
      | refl => cases hreturn
      | tail start next =>
          have hinv := Vars.SmallStep.returned_inv next hreturn
          obtain ⟨cursor, block, hcontrol, hblock, hterm, houtputs⟩ := hinv
          rcases Vars.Proofs.Steps.preserves_function
              (cursor := ⟨function, ⟨0⟩, fn.entry.startPosition⟩)
              (state := (⟨globals, locals₀,
                .running ⟨function, ⟨0⟩, fn.entry.startPosition⟩⟩ : Vars.State))
              start rfl with
            hhalt | ⟨returnedValues, hreturned⟩ | ⟨cursor', hcontrol', hcursorFn⟩
          · exact absurd next
              (stuck_of_exit (outcome := .halted) hhalt _ _)
          · exact absurd next
              (stuck_of_exit (outcome := .returned _) hreturned _ _)
          · have hsame : cursor' = cursor :=
              Control.running.inj (hcontrol'.symm.trans hcontrol)
            subst cursor'
            change cursor.fn = function at hcursorFn
            simp only [Vars.Program.block?, hcursorFn, hfn] at hblock
            have harity := hwf.iretArity fn (Vars.Program.mem_functions_of_function? hfn)
              block (Array.mem_of_getElem? hblock) hterm
            rw [hfn]
            simp only [Option.bind_some]
            rw [← harity, mapM_ok_size houtputs]

theorem Vars.Proofs.Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initId ∨ program.mainId? = some entry)
    (hrun : Vars.EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False := by
  obtain ⟨fn, hfn, houtputs⟩ :
      ∃ fn, program.function? entry = some fn ∧ fn.outputs? = none := by
    rcases hentry with rfl | hmain
    · exact ⟨program.init, Vars.Program.function?_initId program, hwf.entryArity.1.2⟩
    · obtain ⟨m, hmain', hfn⟩ := Vars.Program.function?_mainId hmain
      exact ⟨m, hfn, (hwf.entryArity.2 m hmain').2⟩
  have hreturn := Vars.Proofs.Program.WellFormed.evalFn_arity hwf hrun
  rw [hfn] at hreturn
  simp [houtputs] at hreturn

theorem Vars.Program.WellFormed.icall_bindReturns
    (hwf : program.WellFormed) {s : Vars.State} {nextControl : Control}
    {callee : FunctionId} {args dests : Array VarId}
    {g g' : Globals} {vs rs : Array Word} {t : Trace}
    (hstmt : program.atStmt s = some (nextControl, .icall callee args dests))
    (hcallee : Vars.EvalFn program ctx callee g vs t g' (.returned rs)) :
    ∃ locals', Locals.bindReturns s.environment dests rs = .ok locals' := by
  obtain ⟨-, houtputs⟩ := hwf.icall_paramsOf hstmt
  rw [Vars.Proofs.Program.WellFormed.evalFn_arity hwf hcallee, Option.getD_some] at houtputs
  exact Locals.bindValues_total s.environment houtputs.symm

theorem Vars.Proofs.Program.WellFormed.icall_step
    (hwf : program.WellFormed) {state : Vars.State} {next : Control}
    {callee : FunctionId} {args dests : Array VarId} {values results : Array Word}
    {trace : Trace} {globals' : Globals}
    (hstmt : program.AtStmt state next (.icall callee args dests))
    (hargs : args.mapM state.lookup = .ok values)
    (hcallee : Vars.EvalFn program ctx
      callee state.globals values trace globals' (.returned results)) :
    ∃ locals', Vars.SmallStep program ctx state trace
        (State.of globals' locals' next) := by
  obtain ⟨locals', hbind⟩ := hwf.icall_bindReturns hstmt hcallee
  exact ⟨locals', Vars.SmallStep.icall hstmt hargs hcallee
    (Vars.resume_returned_eq_ok_iff.mpr ⟨hbind, rfl⟩)⟩

theorem Vars.Proofs.Program.icall_halted_step
    {state : Vars.State} {next : Control}
    {callee : FunctionId} {args dests : Array VarId} {values : Array Word}
    {trace : Trace} {globals' : Globals}
    (hstmt : program.AtStmt state next (.icall callee args dests))
    (hargs : args.mapM state.lookup = .ok values)
    (hcallee : Vars.EvalFn program ctx
      callee state.globals values trace globals' .halted) :
    Vars.SmallStep program ctx state trace (State.halted globals') :=
  Vars.SmallStep.icall hstmt hargs hcallee
    (Vars.resume_halted state.environment dests next)


end Sir
