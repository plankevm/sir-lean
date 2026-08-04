import Sir.Proofs.StepDet
import Sir.Generic.Dialogue

namespace Sir

variable {program : Program} {ctx : CallContext}

private theorem Trace.QueryDivergence.append_left {t₁ t₂ : Trace} (pre : Trace)
    (h : Trace.QueryDivergence t₁ t₂) :
    Trace.QueryDivergence (pre ++ t₁) (pre ++ t₂) := by
  obtain ⟨p, a, ra, b, rb, rfl, rfl, hne, hq⟩ := h
  exact ⟨pre ++ p, a, ra, b, rb, by simp, by simp, hne, hq⟩

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

theorem Steps.confluence_or_queryDivergence_proof
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ : Trace}
    (h₁ : Steps program ctx s t₁ e₁) (h₂ : Steps program ctx s t₂ e₂) :
    (∃ u, Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) ∨
        Trace.QueryDivergence t₁ t₂ :=
  runDialogue_all hfree h₁ t₂ e₂ h₂

end Sir
