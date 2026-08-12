import Sir.Machine.Proofs
import Sir.Vars.Proofs.Decode

namespace Sir.Vars

open Sir Machine

theorem decoder_exclusive (program : Program) : (decoder program).Exclusive := by
  intro env globals control instruction next hdecode
  cases hstmt : program.decodeStmt control with
  | none => simp [decoder, decode, hstmt] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, stmt⟩
      have hterm : program.terminatorAt control = none := by
        cases h : program.terminatorAt control with
        | none => rfl
        | some terminator =>
            exact False.elim (decodeStmt_terminatorAt_exclusive hstmt h)
      simp [Vars.decoder, Vars.control, hterm]

theorem decoder_terminal (program : Program) : (decoder program).Terminal := by
  constructor
  · intro env globals results
    simp [Vars.decoder, Vars.decode, Vars.control, Program.decodeStmt, Program.terminatorAt]
  · intro env globals
    simp [Vars.decoder, Vars.decode, Vars.control, Program.decodeStmt, Program.terminatorAt]

theorem decoder_noMload {program : Program} (hfree : program.MemOracleFree) :
    (decoder program).NoMload := by
  intro control src dst next hdecode
  cases hstmt : program.decodeStmt control with
  | none => simp [decoder, decode, hstmt] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, stmt⟩
      have hmem := Program.decodeStmt_mem hstmt
      cases stmt with
      | assign result expr =>
          cases expr <;> simp [decoder, decode, hstmt, decodeStatement, decodeExpression] at hdecode
      | sstore => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | gas => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | call => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | malloc => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | mallocUninit => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | mstore32 => simp [decoder, decode, hstmt, decodeStatement] at hdecode
      | mload32 => exact hfree _ hmem (by simp [Stmt.isMemOracle])
      | icall => simp [decoder, decode, hstmt, decodeStatement] at hdecode

theorem decoder_noMalloc {program : Program} (hfree : program.MemOracleFree) :
    (decoder program).NoMalloc := by
  constructor
  · intro control src dst next hdecode
    cases hstmt : program.decodeStmt control with
    | none => simp [decoder, decode, hstmt] at hdecode
    | some decoded =>
        rcases decoded with ⟨nextControl, stmt⟩
        have hmem := Program.decodeStmt_mem hstmt
        cases stmt with
        | assign result expr =>
            cases expr <;>
              simp [decoder, decode, hstmt, decodeStatement, decodeExpression] at hdecode
        | sstore => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | gas => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | call => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | malloc => exact hfree _ hmem (by simp [Stmt.isMemOracle])
        | mallocUninit => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | mstore32 => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | mload32 => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | icall => simp [decoder, decode, hstmt, decodeStatement] at hdecode
  · intro control src dst next hdecode
    cases hstmt : program.decodeStmt control with
    | none => simp [decoder, decode, hstmt] at hdecode
    | some decoded =>
        rcases decoded with ⟨nextControl, stmt⟩
        have hmem := Program.decodeStmt_mem hstmt
        cases stmt with
        | assign result expr =>
            cases expr <;>
              simp [decoder, decode, hstmt, decodeStatement, decodeExpression] at hdecode
        | sstore => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | gas => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | call => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | malloc => exact hfree _ hmem (by simp [Stmt.isMemOracle])
        | mallocUninit => exact hfree _ hmem (by simp [Stmt.isMemOracle])
        | mstore32 => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | mload32 => simp [decoder, decode, hstmt, decodeStatement] at hdecode
        | icall => simp [decoder, decode, hstmt, decodeStatement] at hdecode

end Sir.Vars

namespace Sir.Vars

open Sir Machine

theorem steps_confluence_or_queryDivergence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ : Trace}
    (h₁ : Machine.Steps frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Steps frame (decoder program) policy ctx state trace₂ final₂) :
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Machine.Proofs.Steps.confluence_or_queryDivergence (.inr (decoder_noMalloc hfree))
    (decoder_exclusive program)
    (decoder_terminal program) (decoder_noMload hfree) h₁ h₂

end Sir.Vars
