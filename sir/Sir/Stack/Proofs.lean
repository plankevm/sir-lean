import Sir.Stack.Spec
import Sir.Core.Proofs

namespace Sir.Stack

theorem Program.instructionAt_terminatorAt_exclusive {program : Program}
    {control next : Control} {instruction : Instr} {terminator : Terminator}
    (hinstruction : program.instructionAt control = some (next, instruction))
    (hterminator : program.terminatorAt control = some terminator) : False := by
  cases control with
  | halted => simp [Program.instructionAt] at hinstruction
  | returned results => simp [Program.instructionAt] at hinstruction
  | running cursor =>
      obtain ⟨function, block, position⟩ := cursor
      cases position <;> simp_all [Program.instructionAt, Program.terminatorAt]

theorem Program.AtInstr.unique {program : Program} {state : State}
    {next₁ next₂ : Control} {instr₁ instr₂ : Instr}
    (h₁ : program.AtInstr state next₁ instr₁) (h₂ : program.AtInstr state next₂ instr₂) :
    next₁ = next₂ ∧ instr₁ = instr₂ :=
  Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

theorem Program.AtTerm.unique {program : Program} {state : State}
    {terminator₁ terminator₂ : Terminator}
    (h₁ : program.AtTerm state terminator₁) (h₂ : program.AtTerm state terminator₂) :
    terminator₁ = terminator₂ :=
  Option.some.inj (h₁.symm.trans h₂)

theorem Program.AtInstr_AtTerm_exclusive {program : Program} {state : State}
    {next : Control} {instruction : Instr} {terminator : Terminator}
    (hinstr : program.AtInstr state next instruction)
    (hterm : program.AtTerm state terminator) : False :=
  program.instructionAt_terminatorAt_exclusive hinstr hterm

theorem Program.instructionAt_mem {program : Program} {control next : Control}
    {instruction : Instr}
    (h : program.instructionAt control = some (next, instruction)) :
    program.HasInstr instruction := by
  cases control with
  | halted => simp [Program.instructionAt] at h
  | returned results => simp [Program.instructionAt] at h
  | running cursor =>
      obtain ⟨functionId, blockId, position⟩ := cursor
      cases position with
      | terminator => simp [Program.instructionAt] at h
      | statement index =>
          cases hfunction : program.function? functionId with
          | none => simp [Program.instructionAt, Program.block?, hfunction] at h
          | some function =>
              cases hblock : function.block? blockId with
              | none => simp [Program.instructionAt, Program.block?, hfunction, hblock] at h
              | some block =>
                  cases hinstruction : block.instructions[index]? with
                  | none =>
                      simp [Program.instructionAt, Program.block?, hfunction, hblock,
                        hinstruction] at h
                  | some found =>
                      simp [Program.instructionAt, Program.block?, hfunction, hblock,
                        hinstruction] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨function, Array.mem_of_getElem? hfunction, block,
                        Array.mem_of_getElem? hblock, Array.mem_of_getElem? hinstruction⟩

theorem Program.memOracleFree_instruction {program : Program}
    (hfree : program.MemOracleFree) {control next : Control} {instruction : Instr}
    (hinstruction : program.instructionAt control = some (next, instruction)) :
    ¬ instruction.isMemOracle :=
  hfree instruction (program.instructionAt_mem hinstruction)

theorem Program.memOracleFree_not_malloc {program : Program}
    (hfree : program.MemOracleFree) {control next : Control}
    (hinstruction : program.instructionAt control = some (next, .op .malloc)) : False :=
  program.memOracleFree_instruction hfree hinstruction (by simp [Instr.isMemOracle])

theorem Program.memOracleFree_not_mallocUninit {program : Program}
    (hfree : program.MemOracleFree) {control next : Control}
    (hinstruction : program.instructionAt control = some (next, .op .mallocUninit)) : False :=
  program.memOracleFree_instruction hfree hinstruction (by simp [Instr.isMemOracle])

theorem Program.memOracleFree_not_mload32 {program : Program}
    (hfree : program.MemOracleFree) {control next : Control}
    (hinstruction : program.instructionAt control = some (next, .op .mload32)) : False :=
  program.memOracleFree_instruction hfree hinstruction (by simp [Instr.isMemOracle])

end Sir.Stack
