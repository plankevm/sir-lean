import Sir.Spec.Step
import Sir.Spec.Observation

namespace Sir

variable {program : Program}

theorem Program.callState?_eq_some_iff
    {p : Program} {f : FunctionId} {g : Globals} {args : Array Word}
    {s : MachineState} :
    p.callState? f g args = some s ↔
      ∃ fn bb locals₀, p.function? f = some fn ∧
        fn.block? fn.entry = some bb ∧
        Locals.bindParams bb.inputs args = .ok locals₀ ∧
        s = ⟨g, locals₀,
          .running { fn := f, block := fn.entry, position := bb.startPosition }⟩ := by
  constructor
  · intro h
    cases hfn : p.function? f with
    | none => simp [Program.callState?, hfn] at h
    | some fn =>
      cases hbb : fn.block? fn.entry with
      | none => simp [Program.callState?, hfn, hbb] at h
      | some bb =>
        cases hbind : Locals.bindParams bb.inputs args with
        | error e => simp [Program.callState?, hfn, hbb, hbind] at h
        | ok locals₀ =>
          have hs : ⟨g, locals₀, .running {
              fn := f, block := fn.entry, position := bb.startPosition }⟩ = s := by
            simpa [Program.callState?, hfn, hbb, hbind] using h
          exact ⟨fn, bb, locals₀, rfl, hbb, hbind, hs.symm⟩
  · rintro ⟨fn, bb, locals₀, hfn, hbb, hbind, rfl⟩
    simp [Program.callState?, hfn, hbb, hbind]

theorem decodeStmt_terminatorAt_exclusive
    {control nextControl : MachineControl} {stmt : Stmt} {term : Terminator}
    (hstmt : program.decodeStmt control = some (nextControl, stmt))
    (hterm : program.terminatorAt control = some term) : False := by
  cases control with
  | halted => simp [Program.decodeStmt] at hstmt
  | returned rs => simp [Program.decodeStmt] at hstmt
  | running cursor =>
    cases hpos : cursor.position <;>
      simp [Program.decodeStmt, Program.terminatorAt, hpos] at hstmt hterm

theorem Program.decodeStmt_mem
    {control nextControl : MachineControl} {stmt : Stmt}
    (h : program.decodeStmt control = some (nextControl, stmt)) :
    program.HasStmt stmt := by
  cases control with
  | halted => simp [Program.decodeStmt] at h
  | returned rs => simp [Program.decodeStmt] at h
  | running cursor =>
    obtain ⟨fid, blk, pos⟩ := cursor
    cases pos with
    | terminator => simp [Program.decodeStmt] at h
    | statement index =>
      cases hfn : program.function? fid with
      | none => simp [Program.decodeStmt, Program.block?, hfn] at h
      | some fn =>
        cases hblock : fn.block? blk with
        | none => simp [Program.decodeStmt, Program.block?, hfn, hblock] at h
        | some block =>
          cases hstmt : block.statements[index]? with
          | none => simp [Program.decodeStmt, Program.block?, hfn, hblock, hstmt] at h
          | some found =>
            simp [Program.decodeStmt, Program.block?, hfn, hblock, hstmt] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨fn, Array.mem_of_getElem? hfn, block,
              Array.mem_of_getElem? hblock, Array.mem_of_getElem? hstmt⟩

theorem Program.MemOracleFree.not_mallocUninit
    (hfree : program.MemOracleFree)
    {control nextControl : MachineControl} {result size : VarId}
    (h : program.decodeStmt control = some (nextControl, .mallocUninit result size)) :
    False := by
  exact hfree _ (Program.decodeStmt_mem h) trivial

theorem Program.MemOracleFree.not_mload32
    (hfree : program.MemOracleFree)
    {control nextControl : MachineControl} {result offset : VarId}
    (h : program.decodeStmt control = some (nextControl, .mload32 result offset)) :
    False := by
  exact hfree _ (Program.decodeStmt_mem h) trivial

theorem Program.decodeStmt_next_block
    {control next : MachineControl} {stmt : Stmt} {cursor : ProgramCursor}
    (hctrl : control = .running cursor)
    (h : program.decodeStmt control = some (next, stmt)) :
    ∃ pos, next = .running { cursor with position := pos } := by
  subst hctrl
  obtain ⟨fid, blk, pos⟩ := cursor
  cases pos with
  | terminator => simp [Program.decodeStmt] at h
  | statement index =>
    simp only [Program.decodeStmt, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨block, hblock, stmt', hstmt', hnext, -⟩ := h
    exact ⟨_, hnext.symm⟩

theorem Program.decodeStmt_next_running
    {control next : MachineControl} {stmt : Stmt}
    (h : program.decodeStmt control = some (next, stmt)) :
    ∃ cursor, next = .running cursor := by
  cases control with
  | returned rs => simp [Program.decodeStmt] at h
  | halted => simp [Program.decodeStmt] at h
  | running cursor =>
    obtain ⟨pos, hnext⟩ := Program.decodeStmt_next_block rfl h
    exact ⟨_, hnext⟩

def Function.terminatorOf (fn : Function) (block : BlockId) : Option Terminator :=
  (fn.block? block).map (·.terminator)

def Program.terminatorOf (program : Program) (cursor : ProgramCursor) : Option Terminator :=
  (program.block? cursor).map (·.terminator)

theorem Program.terminatorAt_inv
    {control : MachineControl} {cursor : ProgramCursor} {term : Terminator}
    (hctrl : control = .running cursor)
    (h : program.terminatorAt control = some term) :
    program.terminatorOf cursor = some term := by
  subst hctrl
  obtain ⟨fid, blk, pos⟩ := cursor
  cases pos with
  | statement index => simp [Program.terminatorAt] at h
  | terminator =>
    cases hb : program.block? { fn := fid, block := blk, position := .terminator } with
    | none => simp [Program.terminatorAt, hb] at h
    | some bb =>
      simp only [Program.terminatorAt, hb] at h
      simpa [Program.terminatorOf, hb] using h

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

theorem sirDecode_inv
    {control next : MachineControl} {instruction : Generic.Instr localsFrame} :
    sirDecode program control = some (instruction, next) ↔
      ∃ statement, program.decodeStmt control = some (next, statement) ∧
        decodeSirStmt statement = instruction := by
  simp [sirDecode, Option.map_eq_some_iff]

@[simp]
theorem sirEntry_eq (function : FunctionId) (globals : Globals) (args : Array Word) :
    (sirDecoder program).entry function globals args =
      (program.callState? function globals args).map MachineState.gen := rfl

theorem sirControl_inv
    {env env' : Locals} {globals globals' : Globals}
    {control control' : MachineControl} {trace : Trace} :
    sirControl program env globals control = some (trace, env', globals', control') ↔
      ∃ terminator state',
        program.terminatorAt control = some terminator ∧
        (eval_terminator program terminator).run
            { globals := globals, locals := env, control := control } = .ok ((), state') ∧
        trace = [] ∧ env' = state'.locals ∧ globals' = state'.globals ∧
        control' = state'.control := by
  constructor
  · intro h
    change ((program.terminatorAt control).bind fun terminator =>
      match (eval_terminator program terminator).run
          { globals := globals, locals := env, control := control } with
      | .ok ((), state') => some ([], state'.locals, state'.globals, state'.control)
      | _ => none) = some (trace, env', globals', control') at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨terminator, hterminator, h⟩ := h
    cases heval : (eval_terminator program terminator).run
        { globals := globals, locals := env, control := control } with
    | error error => simp [heval] at h
    | ok result =>
      obtain ⟨resultUnit, state'⟩ := result
      cases resultUnit
      simp only [heval, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨terminator, state', hterminator, heval, rfl, rfl, rfl, rfl⟩
  · rintro ⟨terminator, state', hterminator, heval, rfl, rfl, rfl, rfl⟩
    change ((program.terminatorAt control).bind fun terminator =>
      match (eval_terminator program terminator).run
          { globals := globals, locals := env, control := control } with
      | .ok ((), state') => some ([], state'.locals, state'.globals, state'.control)
      | _ => none) = some ([], state'.locals, state'.globals, state'.control)
    rw [Option.bind_eq_some_iff]
    exact ⟨terminator, hterminator, by simp [heval]⟩

@[simp]
theorem sirResume_returned_eq_some_iff
    {results : Array Word} {env env' : Locals} {dst : Array VarId}
    {next control' : MachineControl} :
    sirResume (.returned results) env dst next = some (env', control') ↔
      Locals.bindReturns env dst results = .ok env' ∧ control' = next := by
  cases hbind : Locals.bindReturns env dst results <;>
    simp [sirResume, hbind, eq_comm]

@[simp]
theorem sirResume_halted (env : Locals) (dst : Array VarId) (next : MachineControl) :
    sirResume .halted env dst next = some (.empty, .halted) := rfl

@[simp]
theorem sirResume_halted_eq_some_iff
    {env env' : Locals} {dst : Array VarId} {next control' : MachineControl} :
    sirResume .halted env dst next = some (env', control') ↔
      env' = .empty ∧ control' = .halted := by
  simp [sirResume, eq_comm]

end Sir
