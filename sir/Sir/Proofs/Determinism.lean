import Sir.Proofs.Dialogue

namespace Sir

variable {program : Program} {ctx : CallContext}

private theorem Trace.QueryDivergence.ne {t₁ t₂ : Trace}
    (h : Trace.QueryDivergence t₁ t₂) : t₁ ≠ t₂ := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, -⟩ := h
  intro he
  exact hne (List.cons.inj (List.append_cancel_left he)).1

theorem SmallStep.prefix_det_proof
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : SmallStep program ctx s t₁ s₁)
    (h₂ : SmallStep program ctx s t₂ s₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  rcases stepDialogue_all hfree h₁ t₂ s₂ h₂ with hdet | hdiv
  · exact hdet
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem Steps.prefix_confluence_proof
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Steps program ctx s t₁ e₁)
    (h₂ : Steps program ctx s t₂ e₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    (∃ u, Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) := by
  rcases Steps.confluence_or_queryDivergence_proof hfree h₁ h₂ with h₁₂ | h₂₁ | hdiv
  · exact .inl h₁₂
  · exact .inr h₂₁
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem EvalFn.prefix_det_proof
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome}
    {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : EvalFn program ctx f g args t₁ g₁ outcome₁)
    (h₂ : EvalFn program ctx f g args t₂ g₂ outcome₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ g₁ = g₂ ∧ outcome₁ = outcome₂ := by
  rcases fnDialogue_all hfree h₁ t₂ g₂ outcome₂ h₂ with hdet | hdiv
  · exact hdet
  · exact ((hdiv.extend r₁ r₂).ne htr).elim

theorem SmallStep.trace_det_proof
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : MachineState} {t : Trace}
    (h₁ : SmallStep program ctx s t s₁)
    (h₂ : SmallStep program ctx s t s₂) : s₁ = s₂ :=
  (SmallStep.prefix_det_proof hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl).2

theorem EvalFn.trace_det_proof
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome} {t : Trace}
    (h₁ : EvalFn program ctx f g args t g₁ outcome₁)
    (h₂ : EvalFn program ctx f g args t g₂ outcome₂) :
    g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  (EvalFn.prefix_det_proof hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl).2

theorem Steps.stuck_trace_det
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t : Trace}
    (h₁ : Steps program ctx s t e₁) (hs₁ : Stuck program ctx e₁)
    (h₂ : Steps program ctx s t e₂) (hs₂ : Stuck program ctx e₂) : e₁ = e₂ := by
  rcases Steps.prefix_confluence_proof hfree h₁ h₂ (r₁ := []) (r₂ := []) rfl with
    ⟨u, hu, -⟩ | ⟨u, hu, -⟩
  · exact (hu.eq_of_stuck hs₁).1.symm
  · exact (hu.eq_of_stuck hs₂).1

theorem Program.RunsTo.trace_det_proof
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
    exact Steps.stuck_trace_det hfree hsteps₁ (stuck_of_halted hhalt₁)
      hsteps₂ (stuck_of_halted hhalt₂)


variable {program : Program} {ctx : CallContext}

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

theorem Program.RunsTo.unique_or_queryDivergence_proof
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
  rcases Steps.confluence_or_queryDivergence_proof hfree hrun₁ hrun₂ with
    ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
  · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_halted hhalt₁)
    exact .inl ⟨by simpa using htu, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_halted hhalt₂)
    exact .inl ⟨by simpa using htu.symm, rfl⟩
  · exact .inr hdiv

private theorem FnPrefix.query_eq_at
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {t₁ t₂ history : Trace}
    {event₁ event₂ : Event} {rest₁ rest₂ : Trace}
    (h₁ : FnPrefix program ctx function globals args t₁)
    (h₂ : FnPrefix program ctx function globals args t₂)
    (ht₁ : t₁ = history ++ event₁ :: rest₁)
    (ht₂ : t₂ = history ++ event₂ :: rest₂) :
    event₁.query = event₂.query := by
  have get₁ : t₁[history.length]? = some event₁ := by
    rw [ht₁]
    exact getElem?_append_cons ..
  have get₂ : t₂[history.length]? = some event₂ := by
    rw [ht₂]
    exact getElem?_append_cons ..
  rcases fnPrefixDialogue_all hfree h₁ h₂ with
    ⟨u, htu⟩ | ⟨u, htu⟩ | hdiv
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

private theorem EvalFn.fnPrefix_no_event
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals : Globals} {args : Array Word}
    {history trace rest : Trace} {outcome : FunctionOutcome} {event : Event}
    (heval : EvalFn program ctx function globals args history finalGlobals outcome)
    (hprefix : FnPrefix program ctx function globals args trace)
    (htrace : trace = history ++ event :: rest) : False := by
  rcases evalFn_fnPrefixDialogue hfree heval hprefix with ⟨u, htu⟩ | hdiv
  · have hlen := congrArg List.length
      ((congrArg (· ++ u) htrace).symm.trans htu)
    simp at hlen
  · exact hdiv.not_prefix ⟨event :: rest, htrace.symm⟩

theorem Program.functionDeterministicFrom_of_memOracleFree_proof
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args := by
  intro history outcome₁ outcome₂ h₁ h₂
  cases outcome₁ <;> cases outcome₂
  · rfl
  · rcases h₁ with ⟨gas, t₁, r₁, run₁, ht₁⟩
    rcases h₂ with ⟨call, t₂, r₂, -, run₂, ht₂⟩
    have hquery := FnPrefix.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rcases h₁ with ⟨gas, t, rest, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (EvalFn.fnPrefix_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨gas, t, rest, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (EvalFn.fnPrefix_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨call, t₁, r₁, -, run₁, ht₁⟩
    rcases h₂ with ⟨gas, t₂, r₂, run₂, ht₂⟩
    have hquery := FnPrefix.query_eq_at hfree run₁ run₂ ht₁ ht₂
    cases hquery
  · rename_i input₁ input₂
    rcases h₁ with ⟨call₁, t₁, r₁, hin₁, run₁, ht₁⟩
    rcases h₂ with ⟨call₂, t₂, r₂, hin₂, run₂, ht₂⟩
    have hquery := FnPrefix.query_eq_at hfree run₁ run₂ ht₁ ht₂
    have : input₁ = input₂ := by
      simpa [Event.query, hin₁, hin₂] using Query.call.inj hquery
    exact congrArg FunctionObservableOutcome.call this
  · rcases h₁ with ⟨call, t, rest, -, run, ht⟩
    rcases h₂ with ⟨_, haltRun, -⟩
    exact (EvalFn.fnPrefix_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨call, t, rest, -, run, ht⟩
    rcases h₂ with ⟨_, returnRun, -⟩
    exact (EvalFn.fnPrefix_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨gas, t, rest, run, ht⟩
    exact (EvalFn.fnPrefix_no_event hfree haltRun run ht).elim
  · rcases h₁ with ⟨_, haltRun, -⟩
    rcases h₂ with ⟨call, t, rest, -, run, ht⟩
    exact (EvalFn.fnPrefix_no_event hfree haltRun run ht).elim
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
    rcases h₂ with ⟨gas, t, rest, run, ht⟩
    exact (EvalFn.fnPrefix_no_event hfree returnRun run ht).elim
  · rcases h₁ with ⟨_, returnRun, -⟩
    rcases h₂ with ⟨call, t, rest, -, run, ht⟩
    exact (EvalFn.fnPrefix_no_event hfree returnRun run ht).elim
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

theorem Program.MemOracleFree.deterministicFrom_proof
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ := by
  intro history outcome₁ outcome₂ h₁ h₂
  have h := Program.functionDeterministicFrom_of_memOracleFree_proof hfree
    ctx entry { world := world₀ } #[] history outcome₁.functionOutcome
      outcome₂.functionOutcome h₁ h₂
  cases outcome₁ <;> cases outcome₂ <;> simp_all [ObservableOutcome.functionOutcome]

theorem Program.functionDeterministic_of_memOracleFree_proof
    (hfree : program.MemOracleFree) (function : FunctionId) :
    program.FunctionDeterministic function := by
  intro ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂
    heval₁ heval₂
  exact fnDialogue_all hfree heval₁ trace₂ finalGlobals₂ outcome₂ heval₂

theorem Program.deterministic_of_memOracleFree_proof
    (hfree : program.MemOracleFree) : program.Deterministic :=
  fun ctx world₀ =>
    ⟨hfree.deterministicFrom_proof ctx program.initEntry world₀,
      fun entry _ => hfree.deterministicFrom_proof ctx entry world₀⟩

end Sir
