import Sir.Generic.Cfg
import Sir.Generic.Dialogue
import Sir.Proofs.Decode

namespace Sir.Generic

open Sir

theorem sirDecoder_exclusive (program : Program) : (sirDecoder program).Exclusive := by
  intro env globals control instruction next hdecode
  cases hstmt : program.decodeStmt control with
  | none => simp [sirDecoder, sirDecode, hstmt] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, stmt⟩
      have hterm : program.terminatorAt control = none := by
        cases h : program.terminatorAt control with
        | none => rfl
        | some terminator =>
            exact False.elim (decodeStmt_terminatorAt_exclusive hstmt h)
      simp [sirDecoder, sirControl, hterm]

theorem sirDecoder_terminal (program : Program) : (sirDecoder program).Terminal := by
  constructor
  · intro env globals results
    simp [sirDecoder, sirDecode, sirControl, Program.decodeStmt, Program.terminatorAt]
  · intro env globals
    simp [sirDecoder, sirDecode, sirControl, Program.decodeStmt, Program.terminatorAt]

theorem sirDecoder_noMalloc {program : Program} (hfree : program.MemOracleFree) :
    (sirDecoder program).NoMalloc := by
  intro control src dst next hdecode
  cases hstmt : program.decodeStmt control with
  | none => simp [sirDecoder, sirDecode, hstmt] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, stmt⟩
      have hmem := Program.decodeStmt_mem hstmt
      cases stmt with
      | assign result expr =>
          cases expr <;> simp [sirDecoder, sirDecode, hstmt, decodeSirStatement, decodeExpression] at hdecode
      | sstore => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode
      | gas => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode
      | call => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode
      | mallocUninit => exact hfree _ hmem (by simp [Stmt.isMemOracle])
      | mstore32 => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode
      | mload32 => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode
      | icall => simp [sirDecoder, sirDecode, hstmt, decodeSirStatement] at hdecode

theorem cfgDecoder_exclusive (program : CfgProgram) : (cfgDecoder program).Exclusive := by
  intro env globals control instruction next hdecode
  cases hstatement : program.decodeInstruction control with
  | none => simp [cfgDecoder, cfgDecode, hstatement] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, statement⟩
      cases statement <;>
        simp [cfgDecoder, cfgDecode, cfgControl, hstatement] at hdecode ⊢

theorem cfgDecoder_terminal (program : CfgProgram) : (cfgDecoder program).Terminal := by
  constructor
  · intro env globals results
    simp [cfgDecoder, cfgDecode, cfgControl, CfgProgram.decodeInstruction]
  · intro env globals
    simp [cfgDecoder, cfgDecode, cfgControl, CfgProgram.decodeInstruction]

theorem sir_steps_confluence_or_queryDivergence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : policy.Deterministic)
    {state final₁ final₂ : GenericState localOperandFrame} {trace₁ trace₂ : Trace}
    (h₁ : GenericSteps localOperandFrame (sirDecoder program) policy ctx state trace₁ final₁)
    (h₂ : GenericSteps localOperandFrame (sirDecoder program) policy ctx state trace₂ final₂) :
    (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, GenericSteps localOperandFrame (sirDecoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  GenericSteps.confluence_or_queryDivergence (.inl hdet)
    (sirDecoder_exclusive program)
    (sirDecoder_terminal program) h₁ h₂

theorem cfg_steps_confluence_or_queryDivergence
    {program : CfgProgram} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : policy.Deterministic)
    {state final₁ final₂ : GenericState stackFrame} {trace₁ trace₂ : Trace}
    (h₁ : GenericSteps stackFrame (cfgDecoder program) policy ctx state trace₁ final₁)
    (h₂ : GenericSteps stackFrame (cfgDecoder program) policy ctx state trace₂ final₂) :
    (∃ suffix, GenericSteps stackFrame (cfgDecoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, GenericSteps stackFrame (cfgDecoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  GenericSteps.confluence_or_queryDivergence (.inl hdet) (cfgDecoder_exclusive program)
    (cfgDecoder_terminal program) h₁ h₂

end Sir.Generic
