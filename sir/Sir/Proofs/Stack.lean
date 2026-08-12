import Sir.Proofs.Machine
import Sir.Spec.Stack

namespace Sir.Stack

open Sir Machine

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
  Machine.Steps.confluence_or_queryDivergence (.inl hdet) (decoder_exclusive program)
    (decoder_terminal program) hnomload h₁ h₂

end Sir.Stack
