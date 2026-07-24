import Sir.Proofs.StepDet

namespace Sir

variable {program : Program} {ctx : CallContext}

theorem Trace.QueryDivergence.extend {t₁ t₂ : Trace} (u₁ u₂ : Trace)
    (h : Trace.QueryDivergence t₁ t₂) :
    Trace.QueryDivergence (t₁ ++ u₁) (t₂ ++ u₂) := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, hq⟩ := h
  exact ⟨p, a, ra ++ u₁, b, rb ++ u₂, by simp, by simp, hne, hq⟩

private theorem Trace.QueryDivergence.append_left {t₁ t₂ : Trace} (pre : Trace)
    (h : Trace.QueryDivergence t₁ t₂) :
    Trace.QueryDivergence (pre ++ t₁) (pre ++ t₂) := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, hq⟩ := h
  exact ⟨pre ++ p, a, ra, b, rb, by simp, by simp, hne, hq⟩

private theorem Trace.QueryDivergence.symm {t₁ t₂ : Trace}
    (h : Trace.QueryDivergence t₁ t₂) : Trace.QueryDivergence t₂ t₁ := by
  obtain ⟨p, a, ra, b, rb, ht₁, ht₂, hne, hq⟩ := h
  exact ⟨p, b, rb, a, ra, ht₂, ht₁, Ne.symm hne, hq.symm⟩

private abbrev StepDialogue (program : Program) (ctx : CallContext)
    (s : MachineState) (t : Trace) (s' : MachineState) : Prop :=
  ∀ t₂ s₂, SmallStep program ctx s t₂ s₂ →
    (t = t₂ ∧ s' = s₂) ∨ Trace.QueryDivergence t t₂

private abbrev RunDialogue (program : Program) (ctx : CallContext)
    (s : MachineState) (t : Trace) (e : MachineState) : Prop :=
  ∀ t₂ e₂, Steps program ctx s t₂ e₂ →
    (∃ u, Steps program ctx e u e₂ ∧ t ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e ∧ t₂ ++ u = t) ∨ Trace.QueryDivergence t t₂

private abbrev FnDialogue (program : Program) (ctx : CallContext)
    (f : FunctionId) (g : Globals) (args : Array Word) (t : Trace)
    (g' : Globals) (outcome : FunctionOutcome) : Prop :=
  ∀ t₂ g₂ outcome₂, EvalFn program ctx f g args t₂ g₂ outcome₂ →
    (t = t₂ ∧ g' = g₂ ∧ outcome = outcome₂) ∨ Trace.QueryDivergence t t₂

private theorem dialogue_assign
    {state state' : MachineState} {nextControl : MachineControl}
    {result : VarId} {expr : Expr}
    (hstmt : program.decodeStmt state.control = some (nextControl, .assign result expr))
    (heval : eval_assign ctx state result expr = .ok state') :
    StepDialogue program ctx state [] { state' with control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case assign =>
    rename_i hstmt₂ heval₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hr, he⟩ := Stmt.assign.inj hs
    subst hnc hr he
    exact .inl ⟨rfl, by rw [smallStep_assign_det heval heval₂]⟩
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_sstore
    {state state' : MachineState} {nextControl : MachineControl}
    {key value : VarId}
    (hstmt : program.decodeStmt state.control = some (nextControl, .sstore key value))
    (heval : eval_sstore ctx state key value = .ok state') :
    StepDialogue program ctx state [] { state' with control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case sstore =>
    rename_i hstmt₂ heval₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hk, hv⟩ := Stmt.sstore.inj hs
    subst hnc hk hv
    exact .inl ⟨rfl, by rw [smallStep_sstore_det heval heval₂]⟩
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_mstore32
    {state state' : MachineState} {nextControl : MachineControl}
    {offset value : VarId}
    (hstmt : program.decodeStmt state.control = some (nextControl, .mstore32 offset value))
    (heval : (eval_mstore32 offset value).run state = .ok ((), state')) :
    StepDialogue program ctx state [] { state' with control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case mstore32 =>
    rename_i hstmt₂ heval₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨ho, hv⟩ := Stmt.mstore32.inj hs
    subst hnc ho hv
    exact .inl ⟨rfl, by rw [smallStep_mstore32_det heval heval₂]⟩
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_terminator
    {state state' : MachineState} {term : Terminator}
    (hterm : program.terminatorAt state.control = some term)
    (heval : (eval_terminator program term).run state = .ok ((), state')) :
    StepDialogue program ctx state [] state' := by
  intro t₂ s₂ h₂
  cases h₂
  case terminator =>
    rename_i hterm₂ heval₂
    obtain rfl := Option.some.inj (hterm.symm.trans hterm₂)
    exact .inl ⟨rfl, smallStep_terminator_det heval heval₂⟩
  all_goals first
    | (exfalso; rename_i hstmt _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | (exfalso; rename_i hstmt _ _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | (exfalso; rename_i hstmt _ _ _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)

private theorem dialogue_gas
    {state state' : MachineState} {nextControl : MachineControl}
    {result : VarId} {g : Word}
    (hstmt : program.decodeStmt state.control = some (nextControl, .gas result))
    (heval : (eval_gas result g).run state = .ok ((), state')) :
    StepDialogue program ctx state [.gas g] { state' with control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case gas =>
    rename_i g₂ hstmt₂ heval₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain rfl := Stmt.gas.inj hs
    subst hnc
    by_cases hg : g = g₂
    · subst hg
      exact .inl ⟨rfl, by rw [smallStep_gas_det rfl heval heval₂]⟩
    · exact .inr ⟨[], .gas g, [], .gas g₂, [], rfl, rfl,
        fun h => hg (Event.gas.inj h), rfl⟩
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_call
    {state state' : MachineState} {nextControl : MachineControl}
    {call : Call} {result : CallResult} {record : CallRecord}
    (hstmt : program.decodeStmt state.control = some (nextControl, .call call))
    (heval : (eval_call call result).run state = .ok (record, state')) :
    StepDialogue program ctx state [.call record] { state' with control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case call =>
    rename_i record₂ hstmt₂ heval₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain rfl := Stmt.call.inj hs
    subst hnc
    by_cases hrec : record = record₂
    · subst hrec
      exact .inl ⟨rfl, smallStep_call_constructor_det hstmt heval hstmt₂ heval₂ rfl⟩
    · obtain ⟨c₁, gas₁, hc₁, hg₁, hi₁⟩ := eval_call_record_input heval
      obtain ⟨c₂, gas₂, hc₂, hg₂, hi₂⟩ := eval_call_record_input heval₂
      rw [hc₁] at hc₂
      obtain rfl := Except.ok.inj hc₂
      rw [hg₁] at hg₂
      obtain rfl := Except.ok.inj hg₂
      exact .inr ⟨[], .call record, [], .call record₂, [], rfl, rfl,
        fun h => hrec (Event.call.inj h), by simp [Event.query, hi₁, hi₂]⟩
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_icall
    {state : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs rs : Array Word}
    {t : Trace} {g' : Globals} {locals' : Locals}
    (hstmt : program.decodeStmt state.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok vs)
    (hbind : Locals.bindReturns state.locals dests rs = .ok locals')
    (ih : FnDialogue program ctx callee state.globals vs t g' (.returned rs)) :
    StepDialogue program ctx state t
      { state with globals := g', locals := locals', control := nextControl } := by
  intro t₂ s₂ h₂
  cases h₂
  case icall =>
    rename_i hstmt₂ hargs₂ hbind₂ hcallee₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hc, ha, hd⟩ := Stmt.icall.inj hs
    subst hnc hc ha hd
    rw [hargs] at hargs₂
    obtain rfl := Except.ok.inj hargs₂
    rcases ih _ _ _ hcallee₂ with ⟨rfl, rfl, houtcome⟩ | hdiv
    · obtain rfl := FunctionOutcome.returned.inj houtcome
      rw [hbind] at hbind₂
      obtain rfl := Except.ok.inj hbind₂
      exact .inl ⟨rfl, rfl⟩
    · exact .inr hdiv
  case icallHalted =>
    rename_i hstmt₂ hargs₂ hcallee₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hc, ha, hd⟩ := Stmt.icall.inj hs
    subst hnc hc ha hd
    rw [hargs] at hargs₂
    obtain rfl := Except.ok.inj hargs₂
    rcases ih _ _ _ hcallee₂ with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact .inr hdiv
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem dialogue_icallHalted
    {state : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt state.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok vs)
    (ih : FnDialogue program ctx callee state.globals vs t g' .halted) :
    StepDialogue program ctx state t { globals := g', control := .halted } := by
  intro t₂ s₂ h₂
  cases h₂
  case icall =>
    rename_i hstmt₂ hargs₂ hbind₂ hcallee₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hc, ha, hd⟩ := Stmt.icall.inj hs
    subst hnc hc ha hd
    rw [hargs] at hargs₂
    obtain rfl := Except.ok.inj hargs₂
    rcases ih _ _ _ hcallee₂ with ⟨-, -, h⟩ | hdiv
    · cases h
    · exact .inr hdiv
  case icallHalted =>
    rename_i hstmt₂ hargs₂ hcallee₂
    obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
    obtain ⟨hc, ha, hd⟩ := Stmt.icall.inj hs
    subst hnc hc ha hd
    rw [hargs] at hargs₂
    obtain rfl := Except.ok.inj hargs₂
    rcases ih _ _ _ hcallee₂ with ⟨rfl, rfl, -⟩ | hdiv
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr hdiv
  all_goals first
    | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
    | simp_all

private theorem runDialogue_refl {s : MachineState} : RunDialogue program ctx s [] s :=
  fun t₂ _ h₂ => .inl ⟨t₂, h₂, rfl⟩

private theorem runDialogue_tail
    {s mid e : MachineState} {ta tb : Trace}
    (next : SmallStep program ctx mid tb e)
    (ihs : RunDialogue program ctx s ta mid)
    (ihn : StepDialogue program ctx mid tb e) :
    RunDialogue program ctx s (ta ++ tb) e := by
  intro tc ec hc
  rcases ihs tc ec hc with ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
  · rcases hu.head_decomp with ⟨rfl, rfl⟩ | ⟨m', u₁, u₂, stepH, restH, rfl⟩
    · exact .inr (.inl ⟨tb, Steps.single next, by simp [← htu]⟩)
    · rcases ihn u₁ m' stepH with ⟨rfl, rfl⟩ | hdiv
      · exact .inl ⟨u₂, restH, by simp [← htu]⟩
      · exact .inr (.inr (by simpa [htu] using (hdiv.extend [] u₂).append_left ta))
  · exact .inr (.inl ⟨u ++ tb, hu.tail next, by simp [← htu]⟩)
  · exact .inr (.inr (by simpa using hdiv.extend tb []))

private theorem fnDialogue_returned
    {f : FunctionId} {g : Globals} {args rs : Array Word} {t : Trace}
    {s₀ exit : MachineState}
    (hentry : program.callState? f g args = some s₀)
    (hret : exit.control = .returned rs)
    (ihr : RunDialogue program ctx s₀ t exit) :
    FnDialogue program ctx f g args t exit.globals (.returned rs) := by
  obtain ⟨fn, entryBB, locals₀, hfn, hbb, hbind, rfl⟩ :=
    Program.callState?_eq_some_iff.mp hentry
  intro t₂ g₂ outcome₂ h₂
  cases h₂ with
  | returned hentry₂ hrun₂ hret₂ =>
    obtain ⟨fn₂, entryBB₂, locals₂, hfn₂, hbb₂, hbind₂, rfl⟩ :=
      Program.callState?_eq_some_iff.mp hentry₂
    rw [hfn] at hfn₂
    obtain rfl := Option.some.inj hfn₂
    rw [hbb] at hbb₂
    obtain rfl := Option.some.inj hbb₂
    rw [hbind] at hbind₂
    obtain rfl := Except.ok.inj hbind₂
    rcases ihr _ _ hrun₂ with ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
    · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_returned hret)
      obtain rfl := MachineControl.returned.inj (hret.symm.trans hret₂)
      exact .inl ⟨by simpa using htu, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_returned hret₂)
      obtain rfl := MachineControl.returned.inj (hret.symm.trans hret₂)
      exact .inl ⟨by simpa using htu.symm, rfl, rfl⟩
    · exact .inr hdiv
  | halted hentry₂ hrun₂ hhalt₂ =>
    obtain ⟨fn₂, entryBB₂, locals₂, hfn₂, hbb₂, hbind₂, rfl⟩ :=
      Program.callState?_eq_some_iff.mp hentry₂
    rw [hfn] at hfn₂
    obtain rfl := Option.some.inj hfn₂
    rw [hbb] at hbb₂
    obtain rfl := Option.some.inj hbb₂
    rw [hbind] at hbind₂
    obtain rfl := Except.ok.inj hbind₂
    rcases ihr _ _ hrun₂ with ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
    · obtain ⟨rfl, -⟩ := hu.eq_of_stuck (stuck_of_returned hret)
      cases hret.symm.trans hhalt₂
    · obtain ⟨rfl, -⟩ := hu.eq_of_stuck (stuck_of_halted hhalt₂)
      cases hret.symm.trans hhalt₂
    · exact .inr hdiv

private theorem fnDialogue_halted
    {f : FunctionId} {g : Globals} {args : Array Word} {t : Trace}
    {s₀ exit : MachineState}
    (hentry : program.callState? f g args = some s₀)
    (hhalt : exit.control = .halted)
    (ihr : RunDialogue program ctx s₀ t exit) :
    FnDialogue program ctx f g args t exit.globals .halted := by
  obtain ⟨fn, entryBB, locals₀, hfn, hbb, hbind, rfl⟩ :=
    Program.callState?_eq_some_iff.mp hentry
  intro t₂ g₂ outcome₂ h₂
  cases h₂ with
  | returned hentry₂ hrun₂ hret₂ =>
    obtain ⟨fn₂, entryBB₂, locals₂, hfn₂, hbb₂, hbind₂, rfl⟩ :=
      Program.callState?_eq_some_iff.mp hentry₂
    rw [hfn] at hfn₂
    obtain rfl := Option.some.inj hfn₂
    rw [hbb] at hbb₂
    obtain rfl := Option.some.inj hbb₂
    rw [hbind] at hbind₂
    obtain rfl := Except.ok.inj hbind₂
    rcases ihr _ _ hrun₂ with ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
    · obtain ⟨rfl, -⟩ := hu.eq_of_stuck (stuck_of_halted hhalt)
      cases hhalt.symm.trans hret₂
    · obtain ⟨rfl, -⟩ := hu.eq_of_stuck (stuck_of_returned hret₂)
      cases hhalt.symm.trans hret₂
    · exact .inr hdiv
  | halted hentry₂ hrun₂ hhalt₂ =>
    obtain ⟨fn₂, entryBB₂, locals₂, hfn₂, hbb₂, hbind₂, rfl⟩ :=
      Program.callState?_eq_some_iff.mp hentry₂
    rw [hfn] at hfn₂
    obtain rfl := Option.some.inj hfn₂
    rw [hbb] at hbb₂
    obtain rfl := Option.some.inj hbb₂
    rw [hbind] at hbind₂
    obtain rfl := Except.ok.inj hbind₂
    rcases ihr _ _ hrun₂ with ⟨u, hu, htu⟩ | ⟨u, hu, htu⟩ | hdiv
    · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_halted hhalt)
      exact .inl ⟨by simpa using htu, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck (stuck_of_halted hhalt₂)
      exact .inl ⟨by simpa using htu.symm, rfl, rfl⟩
    · exact .inr hdiv

theorem stepDialogue_all
    (hfree : program.MemOracleFree)
    {s s' : MachineState} {t : Trace}
    (h : SmallStep program ctx s t s') : StepDialogue program ctx s t s' := by
  refine SmallStep.rec (motive_1 := fun a ta b _ => StepDialogue program ctx a ta b)
      (motive_2 := fun a ta b _ => RunDialogue program ctx a ta b)
      (motive_3 := fun f g args ta g' outcome _ =>
        FnDialogue program ctx f g args ta g' outcome)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 h
  case c1 => intro _ _ _ _ _ hstmt heval; exact dialogue_assign hstmt heval
  case c2 => intro _ _ _ _ _ hstmt heval; exact dialogue_sstore hstmt heval
  case c3 => intro _ _ _ _ _ hstmt heval; exact dialogue_gas hstmt heval
  case c4 => intro _ _ _ _ _ _ hstmt heval; exact dialogue_call hstmt heval
  case c5 => intro _ _ _ _ _ _ hstmt _ _; exact (hfree.not_mallocUninit hstmt).elim
  case c6 => intro _ _ _ _ _ hstmt heval; exact dialogue_mstore32 hstmt heval
  case c7 => intro _ _ _ _ _ _ hstmt _; exact (hfree.not_mload32 hstmt).elim
  case c8 => intro _ _ _ hterm heval; exact dialogue_terminator hterm heval
  case c9 => intro _ _ _ _ _ _ _ _ _ _ hstmt hargs _ hbind ih; exact dialogue_icall hstmt hargs hbind ih
  case c10 => intro _ _ _ _ _ _ _ _ hstmt hargs _ ih; exact dialogue_icallHalted hstmt hargs ih
  case c11 => intro _; exact runDialogue_refl
  case c12 => intro _ _ _ _ _ _ next ihs ihn; exact runDialogue_tail next ihs ihn
  case c13 =>
    intro _ _ _ _ _ _ _ hentry _ hret ihr
    exact fnDialogue_returned hentry hret ihr
  case c14 =>
    intro _ _ _ _ _ _ hentry _ hhalt ihr
    exact fnDialogue_halted hentry hhalt ihr

private theorem runDialogue_all
    (hfree : program.MemOracleFree)
    {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e) : RunDialogue program ctx s t e := by
  induction h using Steps.inductionOn with
  | refl => exact runDialogue_refl
  | tail _ next ihs => exact runDialogue_tail next ihs (stepDialogue_all hfree next)

theorem fnDialogue_all
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g' : Globals} {args : Array Word} {t : Trace}
    {outcome : FunctionOutcome}
    (h : EvalFn program ctx f g args t g' outcome) :
    FnDialogue program ctx f g args t g' outcome := by
  cases h with
  | returned hentry hrun hret =>
    exact fnDialogue_returned hentry hret (runDialogue_all hfree hrun)
  | halted hentry hrun hhalt =>
    exact fnDialogue_halted hentry hhalt (runDialogue_all hfree hrun)

private theorem terminalSteps_fnPrefixDialogue
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {initial exit : MachineState} {completed partialTrace : Trace}
    (hentry : program.callState? function globals args = some initial)
    (hrun : Steps program ctx initial completed exit)
    (hstuck : Stuck program ctx exit)
    (hdecode : program.decodeStmt exit.control = none)
    (hprefix : FnPrefix program ctx function globals args partialTrace) :
    partialTrace <+: completed ∨ Trace.QueryDivergence completed partialTrace := by
  induction hprefix generalizing initial exit completed with
  | steps hentry₂ hrun₂ =>
      obtain rfl := Option.some.inj (hentry.symm.trans hentry₂)
      rcases runDialogue_all hfree hrun₂ completed exit hrun with
        ⟨u, hu, htrace⟩ | ⟨u, hu, htrace⟩ | hdiv
      · exact .inl ⟨u, htrace⟩
      · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck hstuck
        exact .inl ⟨[], by simpa using htrace.symm⟩
      · exact .inr hdiv.symm
  | descend hentry₂ hrun₂ hstmt hargs hinner ih =>
      rename_i function₂ callee₂ globals₂ args₂ values₂ outerTrace innerTrace
        initial₂ state₂ nextControl₂ callArgs₂ destinations₂
      obtain rfl := Option.some.inj (hentry.symm.trans hentry₂)
      rcases runDialogue_all hfree hrun₂ completed exit hrun with
        ⟨u, hu, htrace⟩ | ⟨u, hu, htrace⟩ | hdiv
      · rcases hu.head_decomp with
          ⟨rfl, rfl⟩ | ⟨after, callTrace, restTrace, callStep, restRun, rfl⟩
        · rw [hdecode] at hstmt
          cases hstmt
        · cases callStep
          case icall hstmt₂ hargs₂ hbind hcallee =>
            obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
            obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
            subst hnc hcalleeId hcallArgs hdestinations
            rw [hargs] at hargs₂
            obtain rfl := Except.ok.inj hargs₂
            cases hcallee with
            | returned hcalleeEntry hcalleeRun hreturn =>
                rcases ih hcalleeEntry hcalleeRun (stuck_of_returned hreturn)
                    (by simp [Program.decodeStmt, hreturn]) with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inl ⟨suffix ++ restTrace, ?_⟩
                  calc
                    (outerTrace ++ innerTrace) ++ (suffix ++ restTrace) =
                        outerTrace ++ ((innerTrace ++ suffix) ++ restTrace) := by simp
                    _ = outerTrace ++ (callTrace ++ restTrace) := by rw [hsuffix]
                    _ = completed := htrace
                · exact .inr (by
                    rw [← htrace]
                    simpa only [List.append_assoc, List.append_nil] using
                      (hdiv.extend restTrace []).append_left _)
          case icallHalted hstmt₂ hargs₂ hcallee =>
            obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
            obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
            subst hnc hcalleeId hcallArgs hdestinations
            rw [hargs] at hargs₂
            obtain rfl := Except.ok.inj hargs₂
            cases hcallee with
            | halted hcalleeEntry hcalleeRun hhalt =>
                rcases ih hcalleeEntry hcalleeRun (stuck_of_halted hhalt)
                    (by simp [Program.decodeStmt, hhalt]) with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inl ⟨suffix ++ restTrace, ?_⟩
                  calc
                    (outerTrace ++ innerTrace) ++ (suffix ++ restTrace) =
                        outerTrace ++ ((innerTrace ++ suffix) ++ restTrace) := by simp
                    _ = outerTrace ++ (callTrace ++ restTrace) := by rw [hsuffix]
                    _ = completed := htrace
                · exact .inr (by
                    rw [← htrace]
                    simpa only [List.append_assoc, List.append_nil] using
                      (hdiv.extend restTrace []).append_left _)
          all_goals first
            | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
            | simp_all
      · obtain ⟨rfl, rfl⟩ := hu.eq_of_stuck hstuck
        rw [hdecode] at hstmt
        cases hstmt
      · exact .inr (by simpa using hdiv.symm.extend [] innerTrace)

theorem evalFn_fnPrefixDialogue
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals : Globals}
    {args : Array Word} {completed partialTrace : Trace} {outcome : FunctionOutcome}
    (heval : EvalFn program ctx function globals args completed finalGlobals outcome)
    (hprefix : FnPrefix program ctx function globals args partialTrace) :
    partialTrace <+: completed ∨ Trace.QueryDivergence completed partialTrace := by
  cases heval with
  | returned hentry hrun hreturn =>
      exact terminalSteps_fnPrefixDialogue hfree hentry hrun
        (stuck_of_returned hreturn) (by simp [Program.decodeStmt, hreturn]) hprefix
  | halted hentry hrun hhalt =>
      exact terminalSteps_fnPrefixDialogue hfree hentry hrun
        (stuck_of_halted hhalt) (by simp [Program.decodeStmt, hhalt]) hprefix

private theorem steps_fnPrefixDialogue
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {initial endState : MachineState} {stepsTrace partialTrace : Trace}
    (hentry : program.callState? function globals args = some initial)
    (hsteps : Steps program ctx initial stepsTrace endState)
    (hprefix : FnPrefix program ctx function globals args partialTrace) :
    stepsTrace <+: partialTrace ∨ partialTrace <+: stepsTrace ∨
      Trace.QueryDivergence stepsTrace partialTrace := by
  cases hprefix with
  | steps hentry₂ hrun₂ =>
      obtain rfl := Option.some.inj (hentry.symm.trans hentry₂)
      rcases runDialogue_all hfree hsteps _ _ hrun₂ with
        ⟨u, -, htrace⟩ | ⟨u, -, htrace⟩ | hdiv
      · exact .inl ⟨u, htrace⟩
      · exact .inr (.inl ⟨u, htrace⟩)
      · exact .inr (.inr hdiv)
  | descend hentry₂ hrun₂ hstmt hargs hinner =>
      rename_i values₂ outerTrace innerTrace state₂ nextControl₂ callArgs₂
        destinations₂
      obtain rfl := Option.some.inj (hentry.symm.trans hentry₂)
      rcases runDialogue_all hfree hsteps values₂ state₂ hrun₂ with
        ⟨u, -, htrace⟩ | ⟨u, hu, htrace⟩ | hdiv
      · refine .inl ⟨u ++ outerTrace, ?_⟩
        simpa only [List.append_assoc] using congrArg (· ++ outerTrace) htrace
      · rcases hu.head_decomp with
          ⟨rfl, rfl⟩ | ⟨after, callTrace, restTrace, callStep, restRun, rfl⟩
        · exact .inl ⟨outerTrace, by simpa using congrArg (· ++ outerTrace) htrace.symm⟩
        · cases callStep
          case icall hstmt₂ hargs₂ hbind hcallee =>
            obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
            obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
            subst hnc hcalleeId hcallArgs hdestinations
            rw [hargs] at hargs₂
            obtain rfl := Except.ok.inj hargs₂
            rcases evalFn_fnPrefixDialogue hfree hcallee hinner with hpre | hdiv
            · obtain ⟨suffix, hsuffix⟩ := hpre
              refine .inr (.inl ⟨suffix ++ restTrace, ?_⟩)
              calc
                (values₂ ++ outerTrace) ++ (suffix ++ restTrace) =
                    values₂ ++ ((outerTrace ++ suffix) ++ restTrace) := by simp
                _ = values₂ ++ (callTrace ++ restTrace) := by rw [hsuffix]
                _ = stepsTrace := htrace
            · exact .inr (.inr (by
                rw [← htrace]
                simpa only [List.append_assoc, List.append_nil] using
                  (hdiv.extend restTrace []).append_left values₂))
          case icallHalted hstmt₂ hargs₂ hcallee =>
            obtain ⟨hnc, hs⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
            obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
            subst hnc hcalleeId hcallArgs hdestinations
            rw [hargs] at hargs₂
            obtain rfl := Except.ok.inj hargs₂
            rcases evalFn_fnPrefixDialogue hfree hcallee hinner with hpre | hdiv
            · obtain ⟨suffix, hsuffix⟩ := hpre
              refine .inr (.inl ⟨suffix ++ restTrace, ?_⟩)
              calc
                (values₂ ++ outerTrace) ++ (suffix ++ restTrace) =
                    values₂ ++ ((outerTrace ++ suffix) ++ restTrace) := by simp
                _ = values₂ ++ (callTrace ++ restTrace) := by rw [hsuffix]
                _ = stepsTrace := htrace
            · exact .inr (.inr (by
                rw [← htrace]
                simpa only [List.append_assoc, List.append_nil] using
                  (hdiv.extend restTrace []).append_left values₂))
          all_goals first
            | (exfalso; rename_i hterm _; exact decodeStmt_terminatorAt_exclusive hstmt hterm)
            | simp_all
      · exact .inr (.inr (by simpa using hdiv.extend [] outerTrace))

theorem fnPrefixDialogue_all
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace₁ trace₂ : Trace}
    (h₁ : FnPrefix program ctx function globals args trace₁)
    (h₂ : FnPrefix program ctx function globals args trace₂) :
    trace₁ <+: trace₂ ∨ trace₂ <+: trace₁ ∨ Trace.QueryDivergence trace₁ trace₂ := by
  induction h₁ generalizing trace₂ with
  | steps hentry₁ hrun₁ =>
      exact steps_fnPrefixDialogue hfree hentry₁ hrun₁ h₂
  | descend hentry₁ hrun₁ hstmt₁ hargs₁ hinner₁ ih =>
      rename_i function₁ callee₁ globals₁ args₁ values₁ outerTrace₁ innerTrace₁
        initial₁ state₁ nextControl₁ callArgs₁ destinations₁
      cases h₂ with
      | steps hentry₂ hrun₂ =>
          rcases steps_fnPrefixDialogue hfree hentry₂ hrun₂
              (.descend hentry₁ hrun₁ hstmt₁ hargs₁ hinner₁) with hpre | hpre | hdiv
          · exact .inr (.inl hpre)
          · exact .inl hpre
          · exact .inr (.inr hdiv.symm)
      | descend hentry₂ hrun₂ hstmt₂ hargs₂ hinner₂ =>
          rename_i callee₂ values₂ outerTrace₂ innerTrace₂ initial₂ state₂
            nextControl₂ callArgs₂ destinations₂
          obtain rfl := Option.some.inj (hentry₁.symm.trans hentry₂)
          rcases runDialogue_all hfree hrun₁ outerTrace₂ state₂ hrun₂ with
            ⟨u, hu, htrace⟩ | ⟨u, hu, htrace⟩ | hdiv
          · rcases hu.head_decomp with
              ⟨rfl, rfl⟩ | ⟨after, callTrace, restTrace, callStep, restRun, rfl⟩
            · simp only [List.append_nil] at htrace
              subst outerTrace₂
              obtain ⟨hnc, hs⟩ :=
                Prod.mk.inj (Option.some.inj (hstmt₁.symm.trans hstmt₂))
              obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
              subst hnc hcalleeId hcallArgs hdestinations
              rw [hargs₁] at hargs₂
              obtain rfl := Except.ok.inj hargs₂
              rcases ih hinner₂ with hpre | hpre | hdiv
              · obtain ⟨suffix, hsuffix⟩ := hpre
                exact .inl ⟨suffix, by simp [hsuffix]⟩
              · obtain ⟨suffix, hsuffix⟩ := hpre
                exact .inr (.inl ⟨suffix, by simp [hsuffix]⟩)
              · exact .inr (.inr (hdiv.append_left outerTrace₁))
            · cases callStep
              case icall hstmt hargs hbind hcallee =>
                obtain ⟨hnc, hs⟩ :=
                  Prod.mk.inj (Option.some.inj (hstmt₁.symm.trans hstmt))
                obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
                subst hnc hcalleeId hcallArgs hdestinations
                rw [hargs₁] at hargs
                obtain rfl := Except.ok.inj hargs
                rcases evalFn_fnPrefixDialogue hfree hcallee hinner₁ with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inl ⟨suffix ++ restTrace ++ innerTrace₂, ?_⟩
                  calc
                    (outerTrace₁ ++ innerTrace₁) ++
                        (suffix ++ restTrace ++ innerTrace₂) =
                      outerTrace₁ ++ ((innerTrace₁ ++ suffix) ++
                        restTrace ++ innerTrace₂) := by simp
                    _ = outerTrace₁ ++ (callTrace ++ restTrace ++ innerTrace₂) := by
                      rw [hsuffix]
                    _ = outerTrace₂ ++ innerTrace₂ := by rw [← htrace]; simp
                · exact .inr (.inr (by
                    have h :=
                      ((hdiv.extend restTrace []).append_left outerTrace₁).symm
                    simpa only [List.append_assoc, List.append_nil, htrace] using
                      h.extend [] innerTrace₂))
              case icallHalted hstmt hargs hcallee =>
                obtain ⟨hnc, hs⟩ :=
                  Prod.mk.inj (Option.some.inj (hstmt₁.symm.trans hstmt))
                obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
                subst hnc hcalleeId hcallArgs hdestinations
                rw [hargs₁] at hargs
                obtain rfl := Except.ok.inj hargs
                rcases evalFn_fnPrefixDialogue hfree hcallee hinner₁ with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inl ⟨suffix ++ restTrace ++ innerTrace₂, ?_⟩
                  calc
                    (outerTrace₁ ++ innerTrace₁) ++
                        (suffix ++ restTrace ++ innerTrace₂) =
                      outerTrace₁ ++ ((innerTrace₁ ++ suffix) ++
                        restTrace ++ innerTrace₂) := by simp
                    _ = outerTrace₁ ++ (callTrace ++ restTrace ++ innerTrace₂) := by
                      rw [hsuffix]
                    _ = outerTrace₂ ++ innerTrace₂ := by rw [← htrace]; simp
                · exact .inr (.inr (by
                    have h :=
                      ((hdiv.extend restTrace []).append_left outerTrace₁).symm
                    simpa only [List.append_assoc, List.append_nil, htrace] using
                      h.extend [] innerTrace₂))
              all_goals first
                | (exfalso; rename_i hterm _; exact
                    decodeStmt_terminatorAt_exclusive hstmt₁ hterm)
                | simp_all
          · rcases hu.head_decomp with
              ⟨rfl, rfl⟩ | ⟨after, callTrace, restTrace, callStep, restRun, rfl⟩
            · simp only [List.append_nil] at htrace
              subst outerTrace₁
              obtain ⟨hnc, hs⟩ :=
                Prod.mk.inj (Option.some.inj (hstmt₂.symm.trans hstmt₁))
              obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
              subst hnc hcalleeId hcallArgs hdestinations
              rw [hargs₂] at hargs₁
              obtain rfl := Except.ok.inj hargs₁
              rcases ih hinner₂ with hpre | hpre | hdiv
              · obtain ⟨suffix, hsuffix⟩ := hpre
                exact .inl ⟨suffix, by simp [hsuffix]⟩
              · obtain ⟨suffix, hsuffix⟩ := hpre
                exact .inr (.inl ⟨suffix, by simp [hsuffix]⟩)
              · exact .inr (.inr (hdiv.append_left outerTrace₂))
            · cases callStep
              case icall hstmt hargs hbind hcallee =>
                obtain ⟨hnc, hs⟩ :=
                  Prod.mk.inj (Option.some.inj (hstmt₂.symm.trans hstmt))
                obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
                subst hnc hcalleeId hcallArgs hdestinations
                rw [hargs₂] at hargs
                obtain rfl := Except.ok.inj hargs
                rcases evalFn_fnPrefixDialogue hfree hcallee hinner₂ with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inr (.inl ⟨suffix ++ restTrace ++ innerTrace₁, ?_⟩)
                  calc
                    (outerTrace₂ ++ innerTrace₂) ++
                        (suffix ++ restTrace ++ innerTrace₁) =
                      outerTrace₂ ++ ((innerTrace₂ ++ suffix) ++
                        restTrace ++ innerTrace₁) := by simp
                    _ = outerTrace₂ ++ (callTrace ++ restTrace ++ innerTrace₁) := by
                      rw [hsuffix]
                    _ = outerTrace₁ ++ innerTrace₁ := by rw [← htrace]; simp
                · exact .inr (.inr (by
                    have h := (hdiv.extend restTrace []).append_left outerTrace₂
                    simpa only [List.append_assoc, List.append_nil, htrace] using
                      h.extend innerTrace₁ []))
              case icallHalted hstmt hargs hcallee =>
                obtain ⟨hnc, hs⟩ :=
                  Prod.mk.inj (Option.some.inj (hstmt₂.symm.trans hstmt))
                obtain ⟨hcalleeId, hcallArgs, hdestinations⟩ := Stmt.icall.inj hs
                subst hnc hcalleeId hcallArgs hdestinations
                rw [hargs₂] at hargs
                obtain rfl := Except.ok.inj hargs
                rcases evalFn_fnPrefixDialogue hfree hcallee hinner₂ with hpre | hdiv
                · obtain ⟨suffix, hsuffix⟩ := hpre
                  refine .inr (.inl ⟨suffix ++ restTrace ++ innerTrace₁, ?_⟩)
                  calc
                    (outerTrace₂ ++ innerTrace₂) ++
                        (suffix ++ restTrace ++ innerTrace₁) =
                      outerTrace₂ ++ ((innerTrace₂ ++ suffix) ++
                        restTrace ++ innerTrace₁) := by simp
                    _ = outerTrace₂ ++ (callTrace ++ restTrace ++ innerTrace₁) := by
                      rw [hsuffix]
                    _ = outerTrace₁ ++ innerTrace₁ := by rw [← htrace]; simp
                · exact .inr (.inr (by
                    have h := (hdiv.extend restTrace []).append_left outerTrace₂
                    simpa only [List.append_assoc, List.append_nil, htrace] using
                      h.extend innerTrace₁ []))
              all_goals first
                | (exfalso; rename_i hterm _; exact
                    decodeStmt_terminatorAt_exclusive hstmt₂ hterm)
                | simp_all
          · exact .inr (.inr (by
              simpa only [List.append_assoc] using hdiv.extend innerTrace₁ innerTrace₂))

theorem Steps.confluence_or_queryDivergence_proof
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ : Trace}
    (h₁ : Steps program ctx s t₁ e₁) (h₂ : Steps program ctx s t₂ e₂) :
    (∃ u, Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) ∨
        Trace.QueryDivergence t₁ t₂ :=
  runDialogue_all hfree h₁ t₂ e₂ h₂

end Sir
