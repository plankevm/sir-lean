import Sir.Vars.Spec

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

theorem decodeStmt_terminatorAt_exclusive
    {control nextControl : Machine.MachineControl} {stmt : Vars.Stmt} {term : Vars.Terminator}
    (hstmt : program.decodeStmt control = some (nextControl, stmt))
    (hterm : program.terminatorAt control = some term) : False := by
  cases control with
  | halted => simp [Vars.Program.decodeStmt] at hstmt
  | returned rs => simp [Vars.Program.decodeStmt] at hstmt
  | running cursor =>
    cases hpos : cursor.position <;>
      simp [Vars.Program.decodeStmt, Vars.Program.terminatorAt, hpos] at hstmt hterm

theorem Vars.Program.decodeStmt_mem
    {control nextControl : Machine.MachineControl} {stmt : Vars.Stmt}
    (h : program.decodeStmt control = some (nextControl, stmt)) :
    program.HasStmt stmt := by
  cases control with
  | halted => simp [Vars.Program.decodeStmt] at h
  | returned rs => simp [Vars.Program.decodeStmt] at h
  | running cursor =>
    obtain ⟨fid, blk, pos⟩ := cursor
    cases pos with
    | terminator => simp [Vars.Program.decodeStmt] at h
    | statement index =>
      cases hfn : program.function? fid with
      | none => simp [Vars.Program.decodeStmt, Vars.Program.block?, hfn] at h
      | some fn =>
        cases hblock : fn.block? blk with
        | none => simp [Vars.Program.decodeStmt, Vars.Program.block?, hfn, hblock] at h
        | some block =>
          cases hstmt : block.statements[index]? with
          | none => simp [Vars.Program.decodeStmt, Vars.Program.block?, hfn, hblock, hstmt] at h
          | some found =>
            simp [Vars.Program.decodeStmt, Vars.Program.block?, hfn, hblock, hstmt] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨fn, Array.mem_of_getElem? hfn, block,
              Array.mem_of_getElem? hblock, Array.mem_of_getElem? hstmt⟩

theorem Vars.Program.MemOracleFree.not_mallocUninit
    (hfree : program.MemOracleFree)
    {control nextControl : Machine.MachineControl} {result size : VarId}
    (h : program.decodeStmt control = some (nextControl, .mallocUninit result size)) :
    False := by
  exact hfree _ (Vars.Program.decodeStmt_mem h) trivial

theorem Vars.Program.MemOracleFree.not_malloc
    (hfree : program.MemOracleFree)
    {control nextControl : Machine.MachineControl} {result size : VarId}
    (h : program.decodeStmt control = some (nextControl, .malloc result size)) :
    False := by
  exact hfree _ (Vars.Program.decodeStmt_mem h) trivial

theorem Vars.Program.MemOracleFree.not_mload32
    (hfree : program.MemOracleFree)
    {control nextControl : Machine.MachineControl} {result offset : VarId}
    (h : program.decodeStmt control = some (nextControl, .mload32 result offset)) :
    False := by
  exact hfree _ (Vars.Program.decodeStmt_mem h) trivial

theorem Vars.Program.decodeStmt_next_block
    {control next : Machine.MachineControl} {stmt : Vars.Stmt} {cursor : Machine.ProgramCursor}
    (hctrl : control = .running cursor)
    (h : program.decodeStmt control = some (next, stmt)) :
    ∃ pos, next = .running { cursor with position := pos } := by
  subst hctrl
  obtain ⟨fid, blk, pos⟩ := cursor
  cases pos with
  | terminator => simp [Vars.Program.decodeStmt] at h
  | statement index =>
    simp only [Vars.Program.decodeStmt, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨block, hblock, stmt', hstmt', hnext, -⟩ := h
    exact ⟨_, hnext.symm⟩

theorem Vars.Program.decodeStmt_next_running
    {control next : Machine.MachineControl} {stmt : Vars.Stmt}
    (h : program.decodeStmt control = some (next, stmt)) :
    ∃ cursor, next = .running cursor := by
  cases control with
  | returned rs => simp [Vars.Program.decodeStmt] at h
  | halted => simp [Vars.Program.decodeStmt] at h
  | running cursor =>
    obtain ⟨pos, hnext⟩ := Vars.Program.decodeStmt_next_block rfl h
    exact ⟨_, hnext⟩

def Vars.Function.terminatorOf (fn : Vars.Function) (block : BlockId) : Option Vars.Terminator :=
  (fn.block? block).map (·.terminator)

def Vars.Program.terminatorOf (program : Vars.Program) (cursor : Machine.ProgramCursor) : Option Vars.Terminator :=
  (program.block? cursor).map (·.terminator)

theorem Vars.Program.terminatorAt_inv
    {control : Machine.MachineControl} {cursor : Machine.ProgramCursor} {term : Vars.Terminator}
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

theorem Vars.Program.decodeStmt_cursor
    {control nextControl : Machine.MachineControl} {statement : Vars.Stmt}
    (hdecode : program.decodeStmt control = some (nextControl, statement)) :
    ∃ cursor block index,
      control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.statements[index]? = some statement ∧
      nextControl = .running
        { cursor with position := block.absoluteToPosition (index + 1) } := by
  cases control with
  | returned values => simp [Vars.Program.decodeStmt] at hdecode
  | halted => simp [Vars.Program.decodeStmt] at hdecode
  | running cursor =>
      cases hposition : cursor.position with
      | terminator => simp [Vars.Program.decodeStmt, hposition] at hdecode
      | statement index =>
          cases hblock : program.block? cursor with
          | none => simp [Vars.Program.decodeStmt, hposition, hblock] at hdecode
          | some block =>
              cases hstatement : block.statements[index]? with
              | none =>
                  simp [Vars.Program.decodeStmt, hposition, hblock, hstatement] at hdecode
              | some found =>
                  simp [Vars.Program.decodeStmt, hposition, hblock, hstatement] at hdecode
                  obtain ⟨rfl, rfl⟩ := hdecode
                  exact ⟨cursor, block, index, rfl, hposition, hblock, hstatement, rfl⟩

theorem Vars.Program.terminatorAt_cursor
    {control : Machine.MachineControl} {terminator : Vars.Terminator}
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

theorem Vars.decode_inv
    {control next : Machine.MachineControl} {instruction : Machine.Instruction Vars.frame} :
    Vars.decode program control = some (instruction, next) ↔
      ∃ statement, program.decodeStmt control = some (next, statement) ∧
        Vars.decodeStatement statement = instruction := by
  simp [Vars.decode, Option.map_eq_some_iff]

@[simp]
theorem Vars.entry_eq (function : FunctionId) (globals : Globals) (args : Array Word) :
    (Vars.decoder program).entry function globals args =
      program.callState? function globals args := rfl

theorem Vars.control_inv
    {env env' : Locals} {globals globals' : Globals}
    {control control' : Machine.MachineControl} {trace : Trace} :
    Vars.control program env globals control = some (trace, env', globals', control') ↔
      ∃ terminator state',
        program.terminatorAt control = some terminator ∧
        (Vars.evaluateTerminator program terminator).run
            { globals := globals, environment := env, control := control } = .ok ((), state') ∧
        trace = [] ∧ env' = state'.environment ∧ globals' = state'.globals ∧
        control' = state'.control := by
  constructor
  · intro h
    change ((program.terminatorAt control).bind fun terminator =>
      match (Vars.evaluateTerminator program terminator).run
          { globals := globals, environment := env, control := control } with
      | .ok ((), state') => some ([], state'.environment, state'.globals, state'.control)
      | _ => none) = some (trace, env', globals', control') at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨terminator, hterminator, h⟩ := h
    cases heval : (Vars.evaluateTerminator program terminator).run
        { globals := globals, environment := env, control := control } with
    | error error => simp [heval] at h
    | ok result =>
      obtain ⟨resultUnit, state'⟩ := result
      cases resultUnit
      simp only [heval, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨terminator, state', hterminator, heval, rfl, rfl, rfl, rfl⟩
  · rintro ⟨terminator, state', hterminator, heval, rfl, rfl, rfl, rfl⟩
    change ((program.terminatorAt control).bind fun terminator =>
      match (Vars.evaluateTerminator program terminator).run
          { globals := globals, environment := env, control := control } with
      | .ok ((), state') => some ([], state'.environment, state'.globals, state'.control)
      | _ => none) = some ([], state'.environment, state'.globals, state'.control)
    rw [Option.bind_eq_some_iff]
    exact ⟨terminator, hterminator, by simp [heval]⟩

@[simp]
theorem Vars.resume_returned_eq_some_iff
    {results : Array Word} {env env' : Locals} {dst : Array VarId}
    {next control' : Machine.MachineControl} :
    Vars.resume (.returned results) env dst next = some (env', control') ↔
      Locals.bindReturns env dst results = .ok env' ∧ control' = next := by
  cases hbind : Locals.bindReturns env dst results <;>
    simp [Vars.resume, hbind, eq_comm]

@[simp]
theorem Vars.resume_halted (env : Locals) (dst : Array VarId) (next : Machine.MachineControl) :
    Vars.resume .halted env dst next = some (.empty, .halted) := rfl

@[simp]
theorem Vars.resume_halted_eq_some_iff
    {env env' : Locals} {dst : Array VarId} {next control' : Machine.MachineControl} :
    Vars.resume .halted env dst next = some (env', control') ↔
      env' = .empty ∧ control' = .halted := by
  simp [Vars.resume, eq_comm]

end Sir
