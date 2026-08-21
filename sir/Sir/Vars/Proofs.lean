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

theorem Program.AtStmt.unique {program : Program} {state : State}
    {next₁ next₂ : Control} {stmt₁ stmt₂ : Stmt}
    (h₁ : program.AtStmt state next₁ stmt₁) (h₂ : program.AtStmt state next₂ stmt₂) :
    next₁ = next₂ ∧ stmt₁ = stmt₂ :=
  Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

theorem Program.AtTerm.unique {program : Program} {state : State}
    {terminator₁ terminator₂ : Terminator}
    (h₁ : program.AtTerm state terminator₁) (h₂ : program.AtTerm state terminator₂) :
    terminator₁ = terminator₂ :=
  Option.some.inj (h₁.symm.trans h₂)

theorem Program.AtStmt_AtTerm_exclusive {program : Program} {state : State}
    {next : Control} {statement : Stmt} {terminator : Terminator}
    (hstmt : program.AtStmt state next statement)
    (hterm : program.AtTerm state terminator) : False :=
  program.statementAt_terminatorAt_exclusive hstmt hterm

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



end Sir.Vars
