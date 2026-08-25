import Sir.Stack.Proofs.Dialogue

namespace Sir.Stack

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

theorem Steps.stuck_trace_det {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : State} {t : Trace}
    (h₁ : Steps program ctx s t e₁) (hs₁ : Stuck program ctx e₁)
    (h₂ : Steps program ctx s t e₂) (hs₂ : Stuck program ctx e₂) : e₁ = e₂ := by
  rcases Proofs.Steps.prefix_confluence hfree h₁ h₂ (rest₁ := []) (rest₂ := []) rfl with
    h₁₂ | h₂₁
  · obtain ⟨u, hu, -⟩ := h₁₂
    exact (Steps.eq_of_stuck hu hs₁).1.symm
  · obtain ⟨u, hu, -⟩ := h₂₁
    exact (Steps.eq_of_stuck hu hs₂).1

variable {program : Program} {ctx : CallContext}

theorem Proofs.Program.RunsTo.trace_det
    (hfree : program.MemOracleFree)
    {entry : FunctionId} {world₀ : World} {t : Trace} {final₁ final₂ : State}
    (h₁ : program.RunsTo ctx entry world₀ t final₁)
    (h₂ : program.RunsTo ctx entry world₀ t final₂) : final₁ = final₂ := by
  rcases h₁ with ⟨⟨initial₁, hentry₁, hsteps₁⟩, hhalt₁⟩
  rcases h₂ with ⟨⟨initial₂, hentry₂, hsteps₂⟩, hhalt₂⟩
  have : initial₁ = initial₂ := Option.some.inj (hentry₁.symm.trans hentry₂)
  subst initial₂
  exact Steps.stuck_trace_det hfree hsteps₁ (stuck_of_exit (outcome := .halted) hhalt₁)
    hsteps₂ (stuck_of_exit (outcome := .halted) hhalt₂)

theorem Proofs.Program.RunsTo.unique_or_queryDivergence
    {entry : FunctionId} {world₀ : World}
    {t₁ t₂ : Trace} {final₁ final₂ : State}
    (hfree : program.MemOracleFree)
    (h₁ : program.RunsTo ctx entry world₀ t₁ final₁)
    (h₂ : program.RunsTo ctx entry world₀ t₂ final₂) :
    (t₁ = t₂ ∧ final₁ = final₂) ∨ Trace.QueryDivergence t₁ t₂ := by
  rcases h₁ with ⟨⟨initial₁, hentry₁, hrun₁⟩, hhalt₁⟩
  rcases h₂ with ⟨⟨initial₂, hentry₂, hrun₂⟩, hhalt₂⟩
  have : initial₁ = initial₂ := Option.some.inj (hentry₁.symm.trans hentry₂)
  subst initial₂
  rcases Proofs.Steps.confluence_or_queryDivergence hfree hrun₁ hrun₂ with
    ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
  · obtain ⟨rfl, rfl⟩ := Steps.eq_of_stuck hu (stuck_of_exit (outcome := .halted) hhalt₁)
    exact .inl ⟨by simpa using htu, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Steps.eq_of_stuck hu (stuck_of_exit (outcome := .halted) hhalt₂)
    exact .inl ⟨by simpa using htu.symm, rfl⟩
  · exact .inr hdiv

private theorem Program.RunsFunction.query_eq_at
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {t₁ t₂ history : Trace} {state₁ state₂ : State}
    {event₁ event₂ : Event} {rest₁ rest₂ : Trace}
    (h₁ : program.RunsFunction ctx function globals args t₁ state₁)
    (h₂ : program.RunsFunction ctx function globals args t₂ state₂)
    (ht₁ : t₁ = history ++ event₁ :: rest₁)
    (ht₂ : t₂ = history ++ event₂ :: rest₂) :
    event₁.query = event₂.query := by
  obtain ⟨initial₁, hentry₁, hrun₁⟩ := h₁
  obtain ⟨initial₂, hentry₂, hrun₂⟩ := h₂
  obtain rfl := Option.some.inj (hentry₁.symm.trans hentry₂)
  have get₁ : t₁[history.length]? = some event₁ := by
    rw [ht₁]; exact Trace.getElem?_append_cons ..
  have get₂ : t₂[history.length]? = some event₂ := by
    rw [ht₂]; exact Trace.getElem?_append_cons ..
  rcases Proofs.Steps.confluence_or_queryDivergence hfree hrun₁ hrun₂ with
    ⟨u, -, htu⟩ | ⟨u, -, htu⟩ | hdiv
  · have hlt : history.length < t₁.length := by rw [ht₁]; simp
    have getEq : t₂[history.length]? = t₁[history.length]? := by
      rw [← htu]; exact List.getElem?_append_left hlt
    obtain rfl : event₁ = event₂ :=
      Option.some.inj (get₁.symm.trans (getEq.symm.trans get₂))
    rfl
  · have hlt : history.length < t₂.length := by rw [ht₂]; simp
    have getEq : t₁[history.length]? = t₂[history.length]? := by
      rw [← htu]; exact List.getElem?_append_left hlt
    obtain rfl : event₁ = event₂ :=
      Option.some.inj (get₁.symm.trans (getEq.trans get₂))
    rfl
  · exact Trace.QueryDivergence.query_eq hdiv ht₁ ht₂

private theorem terminalSteps_no_event
    (hfree : program.MemOracleFree)
    {initial exit state : State} {history trace rest : Trace} {event : Event}
    (hterm : Steps program ctx initial history exit)
    (hstuck : Stuck program ctx exit)
    (hsteps : Steps program ctx initial trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  rcases Proofs.Steps.confluence_or_queryDivergence hfree hterm hsteps with
    ⟨u, hu, htu⟩ | ⟨u, -, htu⟩ | hdiv
  · obtain ⟨-, rfl⟩ := Steps.eq_of_stuck hu hstuck
    have hlen := congrArg List.length (htu.trans htrace)
    simp at hlen
  · rw [htrace] at htu
    have hlen := congrArg List.length htu
    simp at hlen
  · obtain ⟨p, a, ra, b, rb, ha, hb, hne, -⟩ := hdiv
    have : ¬ history <+: trace := by
      rintro ⟨u, hu⟩
      rw [ha, hb, List.append_assoc] at hu
      exact hne (List.cons.inj (List.append_cancel_left hu)).1
    exact this ⟨event :: rest, htrace.symm⟩

private theorem EvalFn.runsFunction_no_event
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals : Globals} {args : Array Word}
    {history trace rest : Trace} {outcome : FunctionOutcome} {event : Event}
    {state : State}
    (heval : EvalFn program ctx function globals args history finalGlobals outcome)
    (hrun : program.RunsFunction ctx function globals args trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  cases heval with
  | exit hentry₂ hrun₂ hexit =>
      obtain rfl := Option.some.inj (hentry.symm.trans hentry₂)
      exact terminalSteps_no_event hfree hrun₂ (stuck_of_exit hexit) hsteps htrace

theorem Proofs.Program.functionDeterministicFrom_of_memOracleFree
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args := by
  intro history outcome₁ outcome₂ h₁ h₂
  cases outcome₁ <;> cases outcome₂
  · rfl
  · rcases h₁ with ⟨gas, t₁, r₁, s₁, run₁, ht₁⟩
    rcases h₂ with ⟨call, t₂, r₂, s₂, -, run₂, ht₂⟩
    have hquery := Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rcases h₁ with ⟨gas, t, rest, s, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨gas, t, rest, s, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨call, t₁, r₁, s₁, -, run₁, ht₁⟩
    rcases h₂ with ⟨gas, t₂, r₂, s₂, run₂, ht₂⟩
    have hquery := Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rename_i input₁ input₂
    rcases h₁ with ⟨call₁, t₁, r₁, s₁, hin₁, run₁, ht₁⟩
    rcases h₂ with ⟨call₂, t₂, r₂, s₂, hin₂, run₂, ht₂⟩
    have hquery := Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    have : input₁ = input₂ := by
      simpa [Event.query, hin₁, hin₂] using Query.call.inj hquery
    exact congrArg FunctionObservableOutcome.call this
  · rcases h₁ with ⟨call, t, rest, s, -, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨call, t, rest, s, -, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨gas, t, rest, s, run, ht⟩
    exact (EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨call, t, rest, s, -, run, ht⟩
    exact (EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rename_i world₁ world₂
    rcases h₁ with ⟨globals₁, run₁, worldEq₁⟩
    rcases h₂ with ⟨globals₂, run₂, worldEq₂⟩
    rcases Proofs.evalDialogue_all hfree run₁ _ _ _ run₂ with ⟨-, hglobals, -⟩ | hdiv
    · subst globals₂
      exact congrArg FunctionObservableOutcome.halt (worldEq₁.symm.trans worldEq₂)
    · exact (Trace.QueryDivergence.ne hdiv rfl).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    rcases Proofs.evalDialogue_all hfree haltRun _ _ _ returnRun with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact (Trace.QueryDivergence.ne hdiv rfl).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨gas, t, rest, s, run, ht⟩
    exact (EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨call, t, rest, s, -, run, ht⟩
    exact (EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    rcases Proofs.evalDialogue_all hfree returnRun _ _ _ haltRun with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact (Trace.QueryDivergence.ne hdiv rfl).elim
  · rename_i world₁ values₁ world₂ values₂
    rcases h₁ with ⟨globals₁, run₁, worldEq₁⟩
    rcases h₂ with ⟨globals₂, run₂, worldEq₂⟩
    rcases Proofs.evalDialogue_all hfree run₁ _ _ _ run₂ with
      ⟨-, hglobals, houtcome⟩ | hdiv
    · subst globals₂
      obtain rfl := FunctionOutcome.returned.inj houtcome
      exact congrArg (FunctionObservableOutcome.returned · values₁)
        (worldEq₁.symm.trans worldEq₂)
    · exact (Trace.QueryDivergence.ne hdiv rfl).elim

theorem Proofs.Program.MemOracleFree.deterministicFrom
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ := by
  intro history outcome₁ outcome₂ h₁ h₂
  have h := Proofs.Program.functionDeterministicFrom_of_memOracleFree hfree
    ctx entry { world := world₀ } #[] history outcome₁.functionOutcome
      outcome₂.functionOutcome h₁ h₂
  cases outcome₁ <;> cases outcome₂ <;> simp_all [ObservableOutcome.functionOutcome]

theorem Proofs.Program.functionDeterministic_of_memOracleFree
    (hfree : program.MemOracleFree) (function : FunctionId) :
    program.FunctionDeterministic function := by
  intro ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂
    heval₁ heval₂
  exact Proofs.evalDialogue_all hfree heval₁ trace₂ finalGlobals₂ outcome₂ heval₂

theorem Proofs.Program.deterministic_of_memOracleFree
    (hfree : program.MemOracleFree) : program.Deterministic :=
  fun ctx world₀ =>
    ⟨Proofs.Program.MemOracleFree.deterministicFrom hfree ctx program.initId world₀,
      fun entry _ => Proofs.Program.MemOracleFree.deterministicFrom hfree ctx entry world₀⟩

end Sir.Stack
