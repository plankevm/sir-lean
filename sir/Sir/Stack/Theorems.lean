import Sir.Stack.Proofs.Determinism

namespace Sir.Stack

open Sir

variable {program : Program} {ctx : CallContext}

local notation:50 s " =[" t "]=>* " f => Steps program ctx s t f

local notation:50 s " =[" t "]=> " f => SmallStep program ctx s t f

theorem Steps.confluence_or_queryDivergence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ : Trace}
    (h₁ : state =[trace₁]=>* final₁) (h₂ : state =[trace₂]=>* final₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends program ctx final₂ trace₂ final₁ trace₁ ∨
        Trace.QueryDivergence trace₁ trace₂ :=
  Proofs.Steps.confluence_or_queryDivergence hfree h₁ h₂

theorem Steps.prefix_confluence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : state =[trace₁]=>* final₁) (h₂ : state =[trace₂]=>* final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends program ctx final₂ trace₂ final₁ trace₁ :=
  Proofs.Steps.prefix_confluence hfree h₁ h₂ htrace

theorem SmallStep.prefix_det
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : state =[trace₁]=> final₁) (h₂ : state =[trace₂]=> final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ final₁ = final₂ :=
  Proofs.SmallStep.prefix_det hfree h₁ h₂ htrace

theorem SmallStep.trace_det
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace : Trace}
    (h₁ : state =[trace]=> final₁) (h₂ : state =[trace]=> final₂) :
    final₁ = final₂ :=
  Proofs.SmallStep.trace_det hfree h₁ h₂

theorem EvalFn.prefix_det
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
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome} {trace : Trace}
    (h₁ : EvalFn program ctx function globals args trace finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace finalGlobals₂ outcome₂) :
    finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  Proofs.EvalFn.trace_det hfree h₁ h₂

end Sir.Stack
