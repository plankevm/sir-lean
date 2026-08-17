import Sir.Machine.Proofs
import Sir.Stack.Spec

namespace Sir.Stack

open Sir Machine

@[simp]
theorem Function.mem_blocks {function : Function} {block : Block} :
    block ∈ function.blocks ↔ block = function.entry ∨ block ∈ function.rest := by
  simp [Function.blocks]

@[simp]
theorem Function.block?_zero (function : Function) :
    function.block? ⟨0⟩ = some function.entry := by
  simp [Function.block?, Function.blocks]

@[simp]
theorem Function.block?_succ (function : Function) (n : Nat) :
    function.block? ⟨n + 1⟩ = function.rest[n]? := by
  simp [Function.block?, Function.blocks, Array.getElem?_append_right]

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

theorem Steps.confluence_or_queryDivergence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : (policy.Deterministic ∧ (decoder program).NoMload) ∨ program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ : Trace}
    (h₁ : Machine.Steps frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Steps frame (decoder program) policy ctx state trace₂ final₂) :
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Machine.Proofs.Steps.confluence_or_queryDivergence
    (hdet.elim (fun h => .inl h.1) (fun h => .inr (decoder_noMalloc h)))
    (decoder_exclusive program) (decoder_terminal program)
    (hdet.elim (fun h => h.2) decoder_noMload) h₁ h₂

private theorem queryDivergence_ne {trace₁ trace₂ : Trace}
    (h : Trace.QueryDivergence trace₁ trace₂) : trace₁ ≠ trace₂ := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, -⟩ := h
  intro heq
  exact hne (List.cons.inj (List.append_cancel_left heq)).1

theorem Steps.prefix_confluence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : (policy.Deterministic ∧ (decoder program).NoMload) ∨ program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : Machine.Steps frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Steps frame (decoder program) policy ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) := by
  rcases Steps.confluence_or_queryDivergence hdet h₁ h₂ with h₁₂ | h₂₁ | hdiv
  · exact .inl h₁₂
  · exact .inr h₂₁
  · exact (queryDivergence_ne (hdiv.extend rest₁ rest₂) htrace).elim

theorem SmallStep.prefix_det
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : (policy.Deterministic ∧ (decoder program).NoMload) ∨ program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : Machine.Step frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Step frame (decoder program) policy ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ final₁ = final₂ := by
  rcases Machine.Proofs.stepDialogue_all
      (hdet.elim (fun h => .inl h.1) (fun h => .inr (decoder_noMalloc h)))
      (decoder_exclusive program) (decoder_terminal program)
      (hdet.elim (fun h => h.2) decoder_noMload) h₁ trace₂ final₂ h₂ with heq | hdiv
  · exact heq
  · exact (queryDivergence_ne (hdiv.extend rest₁ rest₂) htrace).elim

theorem SmallStep.trace_det
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hdet : (policy.Deterministic ∧ (decoder program).NoMload) ∨ program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace : Trace}
    (h₁ : Machine.Step frame (decoder program) policy ctx state trace final₁)
    (h₂ : Machine.Step frame (decoder program) policy ctx state trace final₂) :
    final₁ = final₂ :=
  (SmallStep.prefix_det hdet h₁ h₂ (rest₁ := []) (rest₂ := []) rfl).2

theorem EvalFn.prefix_det
    {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ := by
  rcases Machine.Proofs.evalDialogue_all (.inr (decoder_noMalloc hfree))
      (decoder_exclusive program) (decoder_terminal program) (decoder_noMload hfree)
      h₁ trace₂ finalGlobals₂ outcome₂ h₂ with heq | hdiv
  · exact heq
  · exact (queryDivergence_ne (hdiv.extend rest₁ rest₂) htrace).elim

theorem EvalFn.trace_det
    {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome} {trace : Trace}
    (h₁ : EvalFn program ctx function globals args trace finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace finalGlobals₂ outcome₂) :
    finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  (EvalFn.prefix_det hfree h₁ h₂ (rest₁ := []) (rest₂ := []) rfl).2

end Proofs

end Sir.Stack
