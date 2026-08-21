import Sir.Vars.Spec
import Sir.Core.Proofs

namespace Sir.Vars

theorem Program.statementAt_terminatorAt_exclusive {program : Program}
    {control next : Control} {statement : Stmt} {terminator : Terminator}
    (hstatement : program.statementAt control = some (next, statement)) :
    program.terminatorAt control ≠ some terminator := by
  cases control with
  | halted => simp [Program.statementAt] at hstatement
  | returned results => simp [Program.statementAt] at hstatement
  | running cursor =>
      obtain ⟨functionId, blockId, position⟩ := cursor
      cases position <;> simp [Program.statementAt, Program.terminatorAt] at hstatement ⊢

theorem Program.statementAt_mem {program : Program} {control next : Control}
    {statement : Stmt}
    (h : program.statementAt control = some (next, statement)) :
    program.HasStmt statement := by
  cases control with
  | halted => simp [Program.statementAt] at h
  | returned results => simp [Program.statementAt] at h
  | running cursor =>
      obtain ⟨functionId, blockId, position⟩ := cursor
      cases position with
      | terminator => simp [Program.statementAt] at h
      | statement index =>
          cases hfunction : program.function? functionId with
          | none => simp [Program.statementAt, Program.block?, hfunction] at h
          | some function =>
              cases hblock : function.block? blockId with
              | none => simp [Program.statementAt, Program.block?, hfunction, hblock] at h
              | some block =>
                  cases hstatement : block.statements[index]? with
                  | none =>
                      simp [Program.statementAt, Program.block?, hfunction, hblock,
                        hstatement] at h
                  | some found =>
                      simp [Program.statementAt, Program.block?, hfunction, hblock,
                        hstatement] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨function, Array.mem_of_getElem? hfunction, block,
                        Array.mem_of_getElem? hblock, Array.mem_of_getElem? hstatement⟩

theorem Program.memOracleFree_statement {program : Program}
    (hfree : program.MemOracleFree) {control next : Control} {statement : Stmt}
    (hstatement : program.statementAt control = some (next, statement)) :
    ¬ statement.isMemOracle :=
  hfree statement (program.statementAt_mem hstatement)

theorem Program.memOracleFree_not_malloc {program : Program}
    (hfree : program.MemOracleFree) {control next : Control} {result size : VarId} :
    program.statementAt control ≠ some (next, .malloc result size) := by
  intro h
  exact program.memOracleFree_statement hfree h trivial

theorem Program.memOracleFree_not_mallocUninit {program : Program}
    (hfree : program.MemOracleFree) {control next : Control} {result size : VarId} :
    program.statementAt control ≠ some (next, .mallocUninit result size) := by
  intro h
  exact program.memOracleFree_statement hfree h trivial

theorem Program.memOracleFree_not_mload32 {program : Program}
    (hfree : program.MemOracleFree) {control next : Control} {result offset : VarId} :
    program.statementAt control ≠ some (next, .mload32 result offset) := by
  intro h
  exact program.memOracleFree_statement hfree h trivial

theorem Program.At.mk1 {program : Program} {state : State} {next : Control}
    {stmt : Stmt} {var : VarId} {value : Word}
    (hstmt : program.atStmt state = some (next, stmt))
    (hvar : state.lookup var = .ok value) :
    program.At state next stmt [(var, value)] :=
  ⟨hstmt, by simp [hvar, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem Program.At.mk2 {program : Program} {state : State} {next : Control}
    {stmt : Stmt} {var₁ var₂ : VarId} {value₁ value₂ : Word}
    (hstmt : program.atStmt state = some (next, stmt))
    (h₁ : state.lookup var₁ = .ok value₁)
    (h₂ : state.lookup var₂ = .ok value₂) :
    program.At state next stmt [(var₁, value₁), (var₂, value₂)] :=
  ⟨hstmt, by simp [h₁, h₂, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

end Sir.Vars
