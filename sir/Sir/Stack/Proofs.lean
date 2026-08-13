import Sir.Machine.Proofs
import Sir.Stack.Spec

namespace Sir.Stack

open Sir Machine

namespace Proofs

theorem decoder_exclusive (program : Program) : (decoder program).Exclusive := by
  intro env globals control instruction next hdecode
  cases hstatement : program.decodeInstruction control with
  | none => simp [Stack.decoder, Stack.decode, hstatement] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, statement⟩
      cases statement <;>
        simp [Stack.decoder, Stack.decode, Stack.control, hstatement] at hdecode ⊢

theorem decoder_terminal (program : Program) : (decoder program).Terminal := by
  constructor
  · intro env globals results
    simp [Stack.decoder, Stack.decode, Stack.control, Program.decodeInstruction]
  · intro env globals
    simp [Stack.decoder, Stack.decode, Stack.control, Program.decodeInstruction]

private theorem Program.decodeInstruction_mem
    {program : Program} {control next : Machine.MachineControl} {instruction : Instr}
    (h : program.decodeInstruction control = some (next, instruction)) :
    program.HasInstr instruction := by
  cases control with
  | halted => simp [Program.decodeInstruction] at h
  | returned results => simp [Program.decodeInstruction] at h
  | running cursor =>
      obtain ⟨functionId, blockId, position⟩ := cursor
      cases position with
      | terminator => simp [Program.decodeInstruction] at h
      | statement index =>
          cases hfunction : program.function? functionId with
          | none => simp [Program.decodeInstruction, Program.block?, hfunction] at h
          | some function =>
              cases hblock : function.block? blockId with
              | none =>
                  simp [Program.decodeInstruction, Program.block?, hfunction, hblock] at h
              | some block =>
                  cases hinstruction : block.instructions[index]? with
                  | none =>
                      simp [Program.decodeInstruction, Program.block?, hfunction, hblock,
                        hinstruction] at h
                  | some found =>
                      simp [Program.decodeInstruction, Program.block?, hfunction, hblock,
                        hinstruction] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨function, Array.mem_of_getElem? hfunction, block,
                        Array.mem_of_getElem? hblock, Array.mem_of_getElem? hinstruction⟩

theorem decoder_noMload {program : Program} (hfree : program.MemOracleFree) :
    (decoder program).NoMload := by
  intro control src dst next hdecode
  cases hstatement : program.decodeInstruction control with
  | none => simp [decoder, decode, hstatement] at hdecode
  | some decoded =>
      rcases decoded with ⟨nextControl, instruction⟩
      have hmem := Program.decodeInstruction_mem hstatement
      cases instruction <;> simp [decoder, decode, hstatement] at hdecode
      case op operation =>
        cases operation <;> simp at hdecode
        exact hfree _ hmem (by simp [Instr.isMemOracle])
      case flippedOp operation => cases operation <;> simp at hdecode

theorem decoder_noMalloc {program : Program} (hfree : program.MemOracleFree) :
    (decoder program).NoMalloc := by
  constructor <;> intro control src dst next hdecode <;>
    cases hstatement : program.decodeInstruction control with
    | none => simp [decoder, decode, hstatement] at hdecode
    | some decoded =>
        rcases decoded with ⟨nextControl, instruction⟩
        have hmem := Program.decodeInstruction_mem hstatement
        cases instruction <;> simp [decoder, decode, hstatement] at hdecode
        case op operation =>
          cases operation <;> simp at hdecode
          exact hfree _ hmem (by simp [Instr.isMemOracle])
        case flippedOp operation => cases operation <;> simp at hdecode

theorem steps_confluence_or_queryDivergence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : policy.Deterministic) (hnomload : (decoder program).NoMload)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ : Trace}
    (h₁ : Machine.Steps frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Steps frame (decoder program) policy ctx state trace₂ final₂) :
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Machine.Proofs.Steps.confluence_or_queryDivergence (.inl hdet) (decoder_exclusive program)
    (decoder_terminal program) hnomload h₁ h₂

end Proofs

end Sir.Stack
