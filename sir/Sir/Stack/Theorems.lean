import Sir.Stack.Proofs

namespace Sir.Stack

open Sir Machine

theorem Steps.confluence_or_queryDivergence
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
  Proofs.Steps.confluence_or_queryDivergence (.inr hfree) h₁ h₂

theorem Steps.prefix_confluence
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : Machine.Steps frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Steps frame (decoder program) policy ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Machine.Steps frame (decoder program) policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) :=
  Proofs.Steps.prefix_confluence (.inr hfree) h₁ h₂ htrace

theorem SmallStep.prefix_det
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : Machine.Step frame (decoder program) policy ctx state trace₁ final₁)
    (h₂ : Machine.Step frame (decoder program) policy ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ final₁ = final₂ :=
  Proofs.SmallStep.prefix_det (.inr hfree) h₁ h₂ htrace

theorem SmallStep.trace_det
    {program : Program} {policy : MemoryPolicy} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : Machine.State frame} {trace : Trace}
    (h₁ : Machine.Step frame (decoder program) policy ctx state trace final₁)
    (h₂ : Machine.Step frame (decoder program) policy ctx state trace final₂) :
    final₁ = final₂ :=
  Proofs.SmallStep.trace_det (.inr hfree) h₁ h₂

theorem EvalFn.prefix_det
    {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  Proofs.EvalFn.prefix_det hfree h₁ h₂ htrace

theorem EvalFn.trace_det
    {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome} {trace : Trace}
    (h₁ : EvalFn program ctx function globals args trace finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace finalGlobals₂ outcome₂) :
    finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  Proofs.EvalFn.trace_det hfree h₁ h₂

end Sir.Stack
