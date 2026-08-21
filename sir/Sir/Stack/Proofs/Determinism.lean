import Sir.Stack.Proofs.Dialogue

namespace Sir.Stack

private theorem Trace.QueryDivergence.ne {t₁ t₂ : Trace}
    (h : Trace.QueryDivergence t₁ t₂) : t₁ ≠ t₂ := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, -⟩ := h
  intro heq
  exact hne (List.cons.inj (List.append_cancel_left heq)).1

theorem Proofs.SmallStep.prefix_det {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {state final₁ final₂ : State}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : SmallStep program ctx state trace₁ final₁)
    (h₂ : SmallStep program ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) : trace₁ = trace₂ ∧ final₁ = final₂ := by
  rcases Proofs.stepDialogue_all hfree h₁ trace₂ final₂ h₂ with heq | hdiv
  · exact heq
  · exact Trace.QueryDivergence.ne (hdiv.extend rest₁ rest₂) htrace |>.elim

theorem Proofs.Steps.prefix_confluence {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {state final₁ final₂ : State}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : Steps program ctx state trace₁ final₁)
    (h₂ : Steps program ctx state trace₂ final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends program ctx final₂ trace₂ final₁ trace₁ := by
  rcases Proofs.Steps.confluence_or_queryDivergence hfree h₁ h₂ with h₁₂ | h₂₁ | hdiv
  · exact .inl h₁₂
  · exact .inr h₂₁
  · exact Trace.QueryDivergence.ne (hdiv.extend rest₁ rest₂) htrace |>.elim

theorem Proofs.EvalFn.prefix_det {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ := by
  rcases Proofs.evalDialogue_all hfree h₁ trace₂ finalGlobals₂ outcome₂ h₂ with heq | hdiv
  · exact heq
  · exact Trace.QueryDivergence.ne (hdiv.extend rest₁ rest₂) htrace |>.elim

theorem Proofs.SmallStep.trace_det {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {state final₁ final₂ : State} {trace : Trace}
    (h₁ : SmallStep program ctx state trace final₁)
    (h₂ : SmallStep program ctx state trace final₂) : final₁ = final₂ :=
  (Proofs.SmallStep.prefix_det hfree h₁ h₂ (rest₁ := []) (rest₂ := []) rfl).2

theorem Proofs.EvalFn.trace_det {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome} {trace : Trace}
    (h₁ : EvalFn program ctx function globals args trace finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace finalGlobals₂ outcome₂) :
    finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  (Proofs.EvalFn.prefix_det hfree h₁ h₂ (rest₁ := []) (rest₂ := []) rfl).2

end Sir.Stack
