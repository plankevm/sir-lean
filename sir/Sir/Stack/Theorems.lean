import Sir.Stack.Proofs

namespace Sir.Stack

open Sir Machine

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
  Proofs.steps_confluence_or_queryDivergence hdet hnomload h₁ h₂

end Sir.Stack
