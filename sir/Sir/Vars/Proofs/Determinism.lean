import Sir.Vars.Proofs.Steps

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

private theorem Trace.QueryDivergence.ne {t₁ t₂ : Trace}
    (h : Trace.QueryDivergence t₁ t₂) : t₁ ≠ t₂ := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, -⟩ := h
  intro he
  exact hne (List.cons.inj (List.append_cancel_left he)).1

theorem Vars.Proofs.SmallStep.prefix_det
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Vars.SmallStep program ctx s t₁ s₁)
    (h₂ : Vars.SmallStep program ctx s t₂ s₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  rcases stepDialogue_all hfree h₁ t₂ s₂ h₂ with hdet | hdiv
  · exact hdet
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem Vars.Proofs.Steps.prefix_confluence
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Vars.Steps program ctx s t₁ e₁)
    (h₂ : Vars.Steps program ctx s t₂ e₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    (∃ u, Vars.Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Vars.Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) := by
  rcases Vars.Proofs.Steps.confluence_or_queryDivergence hfree h₁ h₂ with h₁₂ | h₂₁ | hdiv
  · exact .inl h₁₂
  · exact .inr h₂₁
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem Vars.Proofs.EvalFn.prefix_det
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome}
    {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Vars.EvalFn program ctx f g args t₁ g₁ outcome₁)
    (h₂ : Vars.EvalFn program ctx f g args t₂ g₂ outcome₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ g₁ = g₂ ∧ outcome₁ = outcome₂ := by
  rcases fnDialogue_all hfree h₁ t₂ g₂ outcome₂ h₂ with hdet | hdiv
  · exact hdet
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem Vars.Proofs.SmallStep.trace_det
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : MachineState} {t : Trace}
    (h₁ : Vars.SmallStep program ctx s t s₁)
    (h₂ : Vars.SmallStep program ctx s t s₂) : s₁ = s₂ :=
  (Vars.Proofs.SmallStep.prefix_det hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl).2

theorem Vars.Proofs.EvalFn.trace_det
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome} {t : Trace}
    (h₁ : Vars.EvalFn program ctx f g args t g₁ outcome₁)
    (h₂ : Vars.EvalFn program ctx f g args t g₂ outcome₂) :
    g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  (Vars.Proofs.EvalFn.prefix_det hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl).2

theorem Vars.Steps.stuck_trace_det
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t : Trace}
    (h₁ : Vars.Steps program ctx s t e₁) (hs₁ : Stuck program ctx e₁)
    (h₂ : Vars.Steps program ctx s t e₂) (hs₂ : Stuck program ctx e₂) : e₁ = e₂ := by
  rcases Vars.Proofs.Steps.prefix_confluence hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl with
    ⟨u, hu, -⟩ | ⟨u, hu, -⟩
  · exact (Vars.Steps.eq_of_stuck hu hs₁).1.symm
  · exact (Vars.Steps.eq_of_stuck hu hs₂).1

theorem Vars.Proofs.Program.RunsTo.trace_det
    (hfree : program.MemOracleFree)
    {entry : FunctionId} {world₀ : World} {t : Trace}
    {final₁ final₂ : MachineState}
    (h₁ : program.RunsTo ctx entry world₀ t final₁)
    (h₂ : program.RunsTo ctx entry world₀ t final₂) : final₁ = final₂ :=
  by
    rcases h₁ with ⟨⟨initial₁, hentry₁, hsteps₁⟩, hhalt₁⟩
    rcases h₂ with ⟨⟨initial₂, hentry₂, hsteps₂⟩, hhalt₂⟩
    have : initial₁ = initial₂ := Option.some.inj (hentry₁.symm.trans hentry₂)
    subst initial₂
    exact Vars.Steps.stuck_trace_det hfree hsteps₁ (stuck_of_halted hhalt₁)
      hsteps₂ (stuck_of_halted hhalt₂)


variable {program : Vars.Program} {ctx : CallContext}

private theorem Trace.QueryDivergence.not_prefix {t₁ t₂ : Trace}
    (h : Trace.QueryDivergence t₁ t₂) : ¬ t₁ <+: t₂ := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, -⟩ := h
  rintro ⟨u, hu⟩
  rw [List.append_assoc] at hu
  exact hne (List.cons.inj (List.append_cancel_left hu)).1

private theorem getElem?_append_cons (l : Trace) (x : Event) (r : Trace) :
    (l ++ x :: r)[l.length]? = some x := by
  simp

private theorem Trace.QueryDivergence.query_eq {t₁ t₂ : Trace}
    (hdiv : Trace.QueryDivergence t₁ t₂)
    {pre : Trace} {e₁ e₂ : Event} {r₁ r₂ : Trace}
    (h₁ : t₁ = pre ++ e₁ :: r₁) (h₂ : t₂ = pre ++ e₂ :: r₂) :
    e₁.query = e₂.query := by
  obtain ⟨p, a, ra, b, rb, hpa, hpb, hne, hq⟩ := hdiv
  have gA1 : t₁[pre.length]? = some e₁ := by rw [h₁]; exact getElem?_append_cons ..
  have gA2 : t₁[p.length]? = some a := by rw [hpa]; exact getElem?_append_cons ..
  have gB1 : t₂[pre.length]? = some e₂ := by rw [h₂]; exact getElem?_append_cons ..
  have gB2 : t₂[p.length]? = some b := by rw [hpb]; exact getElem?_append_cons ..
  rcases Nat.lt_trichotomy pre.length p.length with hlt | hlen | hgt
  · have c₁ : t₁[pre.length]? = p[pre.length]? := by
      rw [hpa]; exact List.getElem?_append_left hlt
    have c₂ : t₂[pre.length]? = p[pre.length]? := by
      rw [hpb]; exact List.getElem?_append_left hlt
    obtain rfl : e₁ = e₂ :=
      Option.some.inj ((c₁.symm.trans gA1).symm.trans (c₂.symm.trans gB1))
    rfl
  · obtain rfl : e₁ = a := Option.some.inj ((hlen ▸ gA1).symm.trans gA2)
    obtain rfl : e₂ = b := Option.some.inj ((hlen ▸ gB1).symm.trans gB2)
    exact hq
  · have c₁ : t₁[p.length]? = pre[p.length]? := by
      rw [h₁]; exact List.getElem?_append_left hgt
    have c₂ : t₂[p.length]? = pre[p.length]? := by
      rw [h₂]; exact List.getElem?_append_left hgt
    exact absurd
      (Option.some.inj ((c₁.symm.trans gA2).symm.trans (c₂.symm.trans gB2))) hne

theorem Vars.Proofs.Program.RunsTo.unique_or_queryDivergence
    {entry : FunctionId} {world₀ : World}
    {t₁ t₂ : Trace} {final₁ final₂ : MachineState}
    (hfree : program.MemOracleFree)
    (h₁ : program.RunsTo ctx entry world₀ t₁ final₁)
    (h₂ : program.RunsTo ctx entry world₀ t₂ final₂) :
    (t₁ = t₂ ∧ final₁ = final₂) ∨ Trace.QueryDivergence t₁ t₂ := by
  rcases h₁ with ⟨⟨initial₁, hentry₁, hrun₁⟩, hhalt₁⟩
  rcases h₂ with ⟨⟨initial₂, hentry₂, hrun₂⟩, hhalt₂⟩
  have : initial₁ = initial₂ := Option.some.inj (hentry₁.symm.trans hentry₂)
  subst initial₂
  rcases Vars.Proofs.Steps.confluence_or_queryDivergence hfree hrun₁ hrun₂ with
    ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
  · obtain ⟨rfl, rfl⟩ := Vars.Steps.eq_of_stuck hu (stuck_of_halted hhalt₁)
    exact .inl ⟨by simpa using htu, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Vars.Steps.eq_of_stuck hu (stuck_of_halted hhalt₂)
    exact .inl ⟨by simpa using htu.symm, rfl⟩
  · exact .inr hdiv

private theorem Vars.Program.RunsFunction.query_eq_at
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {t₁ t₂ history : Trace} {state₁ state₂ : MachineState}
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
    rw [ht₁]
    exact getElem?_append_cons ..
  have get₂ : t₂[history.length]? = some event₂ := by
    rw [ht₂]
    exact getElem?_append_cons ..
  rcases Vars.Proofs.Steps.confluence_or_queryDivergence hfree hrun₁ hrun₂ with
    ⟨u, -, htu⟩ | ⟨u, -, htu⟩ | hdiv
  · have hlt : history.length < t₁.length := by rw [ht₁]; simp
    have getEq : t₂[history.length]? = t₁[history.length]? := by
      rw [← htu]
      exact List.getElem?_append_left hlt
    obtain rfl : event₁ = event₂ :=
      Option.some.inj (get₁.symm.trans (getEq.symm.trans get₂))
    rfl
  · have hlt : history.length < t₂.length := by rw [ht₂]; simp
    have getEq : t₁[history.length]? = t₂[history.length]? := by
      rw [← htu]
      exact List.getElem?_append_left hlt
    obtain rfl : event₁ = event₂ :=
      Option.some.inj (get₁.symm.trans (getEq.trans get₂))
    rfl
  · exact hdiv.query_eq ht₁ ht₂

private theorem terminalSteps_no_event
    (hfree : program.MemOracleFree)
    {initial exit state : MachineState} {history trace rest : Trace} {event : Event}
    (hterm : Vars.Steps program ctx initial history exit)
    (hstuck : Stuck program ctx exit)
    (hsteps : Vars.Steps program ctx initial trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  rcases Vars.Proofs.Steps.confluence_or_queryDivergence hfree hterm hsteps with
    ⟨u, hu, htu⟩ | ⟨u, -, htu⟩ | hdiv
  · obtain ⟨-, rfl⟩ := Vars.Steps.eq_of_stuck hu hstuck
    have hlen := congrArg List.length (htu.trans htrace)
    simp at hlen
  · rw [htrace] at htu
    have hlen := congrArg List.length htu
    simp at hlen
  · exact hdiv.not_prefix ⟨event :: rest, htrace.symm⟩

private theorem Vars.EvalFn.runsFunction_no_event
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals : Globals} {args : Array Word}
    {history trace rest : Trace} {outcome : FunctionOutcome} {event : Event}
    {state : MachineState}
    (heval : Vars.EvalFn program ctx function globals args history finalGlobals outcome)
    (hrun : program.RunsFunction ctx function globals args trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  cases heval with
  | returned hentry₂ hrun₂ hret =>
      rename_i results initialGen exit
      rw [Vars.entry_eq] at hentry₂
      obtain ⟨initial₂, hcallState₂, rfl⟩ := Option.map_eq_some_iff.mp hentry₂
      obtain rfl := Option.some.inj (hentry.symm.trans hcallState₂)
      have hrun₂' : Vars.Steps program ctx initial history exit.toMachine := by
        change Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
          initial.toState history exit.toMachine.toState
        simpa using hrun₂
      exact terminalSteps_no_event hfree hrun₂'
        (stuck_of_returned hret) hsteps htrace
  | halted hentry₂ hrun₂ hhalt =>
      rename_i initialGen exit
      rw [Vars.entry_eq] at hentry₂
      obtain ⟨initial₂, hcallState₂, rfl⟩ := Option.map_eq_some_iff.mp hentry₂
      obtain rfl := Option.some.inj (hentry.symm.trans hcallState₂)
      have hrun₂' : Vars.Steps program ctx initial history exit.toMachine := by
        change Machine.Steps Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
          initial.toState history exit.toMachine.toState
        simpa using hrun₂
      exact terminalSteps_no_event hfree hrun₂'
        (stuck_of_halted hhalt) hsteps htrace

theorem Vars.Proofs.Program.functionDeterministicFrom_of_memOracleFree
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args := by
  intro history outcome₁ outcome₂ h₁ h₂
  cases outcome₁ <;> cases outcome₂
  · rfl
  · rcases h₁ with ⟨gas, t₁, r₁, s₁, run₁, ht₁⟩
    rcases h₂ with ⟨call, t₂, r₂, s₂, -, run₂, ht₂⟩
    have hquery := Vars.Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rcases h₁ with ⟨gas, t, rest, s, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨gas, t, rest, s, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨call, t₁, r₁, s₁, -, run₁, ht₁⟩
    rcases h₂ with ⟨gas, t₂, r₂, s₂, run₂, ht₂⟩
    have hquery := Vars.Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rename_i input₁ input₂
    rcases h₁ with ⟨call₁, t₁, r₁, s₁, hin₁, run₁, ht₁⟩
    rcases h₂ with ⟨call₂, t₂, r₂, s₂, hin₂, run₂, ht₂⟩
    have hquery := Vars.Program.RunsFunction.query_eq_at hfree run₁ run₂ ht₁ ht₂
    have : input₁ = input₂ := by
      simpa [Event.query, hin₁, hin₂] using Query.call.inj hquery
    exact congrArg FunctionObservableOutcome.call this
  · rcases h₁ with ⟨call, t, rest, s, -, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨call, t, rest, s, -, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨gas, t, rest, s, run, ht⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨call, t, rest, s, -, run, ht⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree haltRun run ht).elim
  · rename_i world₁ world₂
    rcases h₁ with ⟨globals₁, run₁, worldEq₁⟩
    rcases h₂ with ⟨globals₂, run₂, worldEq₂⟩
    rcases fnDialogue_all hfree run₁ _ _ _ run₂ with ⟨-, hglobals, -⟩ | hdiv
    · subst globals₂
      exact congrArg FunctionObservableOutcome.halt (worldEq₁.symm.trans worldEq₂)
    · exact (hdiv.ne rfl).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    rcases fnDialogue_all hfree haltRun _ _ _ returnRun with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact (hdiv.ne rfl).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨gas, t, rest, s, run, ht⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨call, t, rest, s, -, run, ht⟩
    exact (Vars.EvalFn.runsFunction_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    rcases fnDialogue_all hfree returnRun _ _ _ haltRun with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact (hdiv.ne rfl).elim
  · rename_i world₁ values₁ world₂ values₂
    rcases h₁ with ⟨globals₁, run₁, worldEq₁⟩
    rcases h₂ with ⟨globals₂, run₂, worldEq₂⟩
    rcases fnDialogue_all hfree run₁ _ _ _ run₂ with
      ⟨-, hglobals, houtcome⟩ | hdiv
    · subst globals₂
      obtain rfl := FunctionOutcome.returned.inj houtcome
      exact congrArg (FunctionObservableOutcome.returned · values₁)
        (worldEq₁.symm.trans worldEq₂)
    · exact (hdiv.ne rfl).elim

theorem Vars.Proofs.Program.MemOracleFree.deterministicFrom
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ := by
  intro history outcome₁ outcome₂ h₁ h₂
  have h := Vars.Proofs.Program.functionDeterministicFrom_of_memOracleFree hfree
    ctx entry { world := world₀ } #[] history outcome₁.functionOutcome
      outcome₂.functionOutcome h₁ h₂
  cases outcome₁ <;> cases outcome₂ <;> simp_all [ObservableOutcome.functionOutcome]

theorem Vars.Proofs.Program.functionDeterministic_of_memOracleFree
    (hfree : program.MemOracleFree) (function : FunctionId) :
    program.FunctionDeterministic function := by
  intro ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂
    heval₁ heval₂
  exact fnDialogue_all hfree heval₁ trace₂ finalGlobals₂ outcome₂ heval₂

theorem Vars.Proofs.Program.deterministic_of_memOracleFree
    (hfree : program.MemOracleFree) : program.Deterministic :=
  fun ctx world₀ =>
    ⟨Vars.Proofs.Program.MemOracleFree.deterministicFrom hfree ctx program.initEntry world₀,
      fun entry _ => Vars.Proofs.Program.MemOracleFree.deterministicFrom hfree ctx entry world₀⟩

end Sir
