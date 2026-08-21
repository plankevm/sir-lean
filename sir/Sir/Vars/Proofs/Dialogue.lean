import Sir.Vars.Proofs

namespace Sir.Vars

@[elab_as_elim]
theorem Steps.inductionOn {program : Program} {ctx : CallContext}
    {motive : (state : State) → (trace : Trace) → (final : State) →
      Steps program ctx state trace final → Prop}
    (refl : ∀ state, motive state [] state .refl)
    (tail : ∀ {state middle final : State} {trace₁ trace₂ : Trace}
      (start : Steps program ctx state trace₁ middle)
      (next : SmallStep program ctx middle trace₂ final),
      motive state trace₁ middle start →
        motive state (trace₁ ++ trace₂) final (start.tail next))
    {state final : State} {trace : Trace}
    (h : Steps program ctx state trace final) : motive state trace final h := by
  refine Steps.rec (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun state trace final h => motive state trace final h)
      (motive_3 := fun _ _ _ _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?refl ?tail ?_ h
  case refl => intro state; exact refl state
  case tail => intro state middle final trace₁ trace₂ start next ih _
               exact tail start next ih
  all_goals intros; trivial

theorem Steps.trans {program : Program} {ctx : CallContext}
    {start middle final : State} {firstTrace secondTrace : Trace}
    (first : Steps program ctx start firstTrace middle)
    (second : Steps program ctx middle secondTrace final) :
    Steps program ctx start (firstTrace ++ secondTrace) final := by
  exact Steps.inductionOn
    (motive := fun middle secondTrace final _ =>
      ∀ {start firstTrace}, Steps program ctx start firstTrace middle →
        Steps program ctx start (firstTrace ++ secondTrace) final)
    (fun _ => by
      intro start firstTrace first
      simpa using first)
    (fun {state middle final trace₁ trace₂} rest step ih => by
      intro start firstTrace first
      simpa [List.append_assoc] using (ih first).tail step)
    second first

theorem Steps.single {program : Program} {ctx : CallContext} {state final : State}
    {trace : Trace} (h : SmallStep program ctx state trace final) :
    Steps program ctx state trace final :=
  .tail .refl h

theorem Steps.headDecomp {program : Program} {ctx : CallContext} {state final : State}
    {trace : Trace} (h : Steps program ctx state trace final) :
    (state = final ∧ trace = []) ∨
      ∃ middle trace₁ trace₂,
        SmallStep program ctx state trace₁ middle ∧
        Steps program ctx middle trace₂ final ∧
        trace = trace₁ ++ trace₂ := by
  refine Steps.inductionOn (motive := fun state trace final _ =>
      (state = final ∧ trace = []) ∨
        ∃ middle trace₁ trace₂,
          SmallStep program ctx state trace₁ middle ∧
          Steps program ctx middle trace₂ final ∧
          trace = trace₁ ++ trace₂)
    (fun _ => .inl ⟨rfl, rfl⟩)
    (fun start next ih => by
      rcases ih with ⟨rfl, rfl⟩ | ⟨middle, pre, suffix, step, rest, rfl⟩
      · exact .inr ⟨_, _, [], next, .refl, by simp⟩
      · exact .inr ⟨middle, pre, suffix ++ _, step, rest.tail next, by simp⟩)
    h

def StepDialogue (program : Program) (ctx : CallContext)
    (state : State) (trace : Trace) (final : State) : Prop :=
  ∀ trace₂ final₂, SmallStep program ctx state trace₂ final₂ →
    (trace = trace₂ ∧ final = final₂) ∨ Trace.QueryDivergence trace trace₂

def RunDialogue (program : Program) (ctx : CallContext)
    (state : State) (trace : Trace) (final : State) : Prop :=
  ∀ trace₂ final₂, Steps program ctx state trace₂ final₂ →
    Steps.Extends program ctx final trace final₂ trace₂ ∨
    Steps.Extends program ctx final₂ trace₂ final trace ∨
      Trace.QueryDivergence trace trace₂

def EvalDialogue (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (finalGlobals : Globals)
    (outcome : FunctionOutcome) : Prop :=
  ∀ trace₂ finalGlobals₂ outcome₂,
    EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂ →
    (trace = trace₂ ∧ finalGlobals = finalGlobals₂ ∧ outcome = outcome₂) ∨
      Trace.QueryDivergence trace trace₂

end Sir.Vars

namespace Sir

def Stuck (program : Vars.Program) (ctx : CallContext) (state : Vars.State) : Prop :=
  ∀ trace final, ¬ Vars.SmallStep program ctx state trace final

theorem Vars.Steps.eq_of_stuck {program : Vars.Program} {ctx : CallContext}
    {state final : Vars.State} {trace : Trace}
    (h : Vars.Steps program ctx state trace final)
    (hstuck : Stuck program ctx state) : final = state ∧ trace = [] := by
  rcases h.headDecomp with ⟨rfl, rfl⟩ | ⟨middle, trace₁, _, step, _, _⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd step (hstuck trace₁ middle)

theorem stuck_of_exit {program : Vars.Program} {ctx : CallContext}
    {state : Vars.State} {outcome : FunctionOutcome}
    (hcontrol : state.control = outcome.toControl) : Stuck program ctx state := by
  intro trace final hstep
  cases outcome with
  | returned results =>
      cases hstep <;> simp_all [FunctionOutcome.toControl,
        Vars.Program.atStmt, Vars.Program.statementAt, Vars.Program.terminatorAt]
  | halted =>
      cases hstep <;> simp_all [FunctionOutcome.toControl,
        Vars.Program.atStmt, Vars.Program.statementAt, Vars.Program.terminatorAt]

end Sir

namespace Sir.Vars

private theorem dialogue_icall {program : Program} {ctx : CallContext}
    {state : State} {callee : FunctionId} {args dests : Array VarId}
    {next : Control} {values : Array Word} {trace : Trace} {globals' : Globals}
    {outcome : FunctionOutcome} {env' : Locals} {control' : Control}
    (hstmt : program.atStmt state = some (next, .icall callee args dests))
    (hfetch : args.mapM state.lookup = .ok values)
    (hresume : resume outcome state.environment dests next = some (env', control'))
    (ih : EvalDialogue program ctx callee state.globals values trace globals' outcome) :
    StepDialogue program ctx state trace
      { globals := globals', environment := env', control := control' } := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | icall hstmt₂ hfetch₂ hcallee₂ hresume₂ =>
      obtain ⟨hnext, hstmt⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
      obtain ⟨hcallee, hargs, hdests⟩ := Stmt.icall.inj hstmt
      subst hnext
      subst hcallee
      subst hargs
      subst hdests
      rw [hfetch] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases ih _ _ _ hcallee₂ with ⟨rfl, rfl, rfl⟩ | hdiv
      · rw [hresume] at hresume₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hresume₂)
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv
  | control hterm₂ _ =>
      exact (program.statementAt_terminatorAt_exclusive hstmt hterm₂).elim
  | assign hstmt₂ _ =>
      rw [hstmt] at hstmt₂; simp at hstmt₂
  | sstore hstmt₂ _ _ | gas hstmt₂ | call hstmt₂ _ _ | malloc hstmt₂ _ _ _
  | mallocUninit hstmt₂ _ _ | mstore32 hstmt₂ _ _ _ | mload32 hstmt₂ _ =>
      rw [hstmt] at hstmt₂; simp at hstmt₂

private theorem dialogue_control {program : Program} {ctx : CallContext}
    {state state' : State} {terminator : Terminator}
    (hterm : program.atTerm state = some terminator)
    (heval : (evaluateTerminator program terminator).run state = .ok ((), state')) :
    StepDialogue program ctx state [] state' := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | control hterm₂ heval₂ =>
      rw [hterm] at hterm₂
      obtain rfl := Option.some.inj hterm₂
      rw [heval] at heval₂
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval₂)
      exact .inl ⟨rfl, rfl⟩
  | assign hstmt _ | icall hstmt _ _ _ | sstore hstmt _ _ | gas hstmt
  | call hstmt _ _ | malloc hstmt _ _ _ | mallocUninit hstmt _ _
  | mstore32 hstmt _ _ _ | mload32 hstmt _ =>
      exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim

private theorem runDialogue_refl {program : Program} {ctx : CallContext} {state : State} :
    RunDialogue program ctx state [] state :=
  fun trace _ h => .inl ⟨trace, h, rfl⟩

private theorem runDialogue_tail {program : Program} {ctx : CallContext}
    {state middle final : State} {trace₁ trace₂ : Trace}
    (next : SmallStep program ctx middle trace₂ final)
    (ihRun : RunDialogue program ctx state trace₁ middle)
    (ihStep : StepDialogue program ctx middle trace₂ final) :
    RunDialogue program ctx state (trace₁ ++ trace₂) final := by
  intro trace₃ final₃ hrun₃
  rcases ihRun trace₃ final₃ hrun₃ with
      ⟨suffix, hrun, heq⟩ | ⟨suffix, hrun, heq⟩ | hdiv
  · rcases hrun.headDecomp with ⟨rfl, rfl⟩ |
        ⟨middle', prefixTrace, suffixTrace, first, rest, rfl⟩
    · exact .inr (.inl ⟨trace₂, Steps.single next, by simp [← heq]⟩)
    · rcases ihStep prefixTrace middle' first with ⟨rfl, rfl⟩ | hdiv
      · exact .inl ⟨suffixTrace, rest, by simp [← heq]⟩
      · exact .inr (.inr (by
          simpa [heq] using
            (Trace.QueryDivergence.appendLeft trace₁
              (Trace.QueryDivergence.extend [] suffixTrace hdiv))))
  · exact .inr (.inl ⟨suffix ++ trace₂, hrun.tail next, by simp [← heq]⟩)
  · exact .inr (.inr (by
      simpa using Trace.QueryDivergence.extend trace₂ [] hdiv))

private theorem evalDialogue_exit {program : Program} {ctx : CallContext}
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace : Trace} {initial exit : State} {outcome : FunctionOutcome}
    (hentry : program.callState? function globals args = some initial)
    (hexit : exit.control = outcome.toControl)
    (ihRun : RunDialogue program ctx initial trace exit) :
    EvalDialogue program ctx function globals args trace exit.globals outcome := by
  intro trace₂ globals₂ outcome₂ heval₂
  cases heval₂ with
  | exit hentry₂ hrun₂ hexit₂ =>
      rw [hentry] at hentry₂
      obtain rfl := Option.some.inj hentry₂
      rcases ihRun _ _ hrun₂ with ⟨suffix, hrun, heq⟩ |
          ⟨suffix, hrun, heq⟩ | hdiv
      · obtain ⟨rfl, rfl⟩ := hrun.eq_of_stuck (stuck_of_exit hexit)
        exact .inl ⟨by simpa using heq, rfl,
          FunctionOutcome.toControl_inj (hexit.symm.trans hexit₂)⟩
      · obtain ⟨rfl, rfl⟩ := hrun.eq_of_stuck (stuck_of_exit hexit₂)
        exact .inl ⟨by simpa using heq.symm, rfl,
          FunctionOutcome.toControl_inj (hexit.symm.trans hexit₂)⟩
      · exact .inr hdiv

namespace Proofs

theorem stepDialogue_all {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {state final : State} {trace : Trace}
    (h : SmallStep program ctx state trace final) :
    StepDialogue program ctx state trace final := by
  refine SmallStep.rec
    (motive_1 := fun state trace final _ => StepDialogue program ctx state trace final)
    (motive_2 := fun state trace final _ => RunDialogue program ctx state trace final)
    (motive_3 := fun function globals args trace globals' outcome _ =>
      EvalDialogue program ctx function globals args trace globals' outcome)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  case refine_1 =>
    intro state next result expression value hstmt heval
    intro trace₂ final₂ h₂
    cases h₂ with
    | assign hstmt₂ heval₂ =>
        obtain ⟨hnext, hstatement⟩ :=
          Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
        obtain ⟨hresult, hexpression⟩ := Stmt.assign.inj hstatement
        subst hnext
        subst hresult
        subst hexpression
        rw [heval] at heval₂
        obtain rfl := Except.ok.inj heval₂
        exact .inl ⟨rfl, rfl⟩
    | control hterm _ =>
        exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim
    | icall hstmt₂ _ _ _ | sstore hstmt₂ _ _ | gas hstmt₂ | call hstmt₂ _ _
    | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _ | mstore32 hstmt₂ _ _ _
    | mload32 hstmt₂ _ =>
        rw [hstmt] at hstmt₂; simp at hstmt₂
  case refine_2 =>
    intro state next keyVar valueVar key value hstmt hkey hvalue
    intro trace₂ final₂ h₂
    cases h₂ with
    | sstore hstmt₂ hkey₂ hvalue₂ =>
        obtain ⟨rfl, heq⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
        obtain ⟨rfl, rfl⟩ := Stmt.sstore.inj heq
        rw [hkey] at hkey₂
        obtain rfl := Except.ok.inj hkey₂
        rw [hvalue] at hvalue₂
        obtain rfl := Except.ok.inj hvalue₂
        exact .inl ⟨rfl, rfl⟩
    | control hterm _ =>
        exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim
    | assign hstmt₂ _ | icall hstmt₂ _ _ _ | gas hstmt₂ | call hstmt₂ _ _
    | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _ | mstore32 hstmt₂ _ _ _
    | mload32 hstmt₂ _ =>
        rw [hstmt] at hstmt₂; simp at hstmt₂
  case refine_3 =>
    intro state next result answer₁ hstmt
    intro trace₂ final₂ h₂
    cases h₂ with
    | gas hstmt₂ =>
        rename_i answer₂
        obtain ⟨rfl, heq⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
        obtain rfl := Stmt.gas.inj heq
        rcases Globals.gas_dialogue answer₁ answer₂ with rfl | hdiv
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr hdiv
    | control hterm _ =>
        exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim
    | assign hstmt₂ _ | icall hstmt₂ _ _ _ | sstore hstmt₂ _ _ | call hstmt₂ _ _
    | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _ | mstore32 hstmt₂ _ _ _
    | mload32 hstmt₂ _ =>
        rw [hstmt] at hstmt₂; simp at hstmt₂
  case refine_4 =>
    intro state next call target gasLimit answer₁ hstmt htarget hgas
    intro trace₂ final₂ h₂
    cases h₂ with
    | call hstmt₂ htarget₂ hgas₂ =>
        rename_i answer₂
        obtain ⟨rfl, heq⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
        obtain rfl := Stmt.call.inj heq
        rw [htarget] at htarget₂
        obtain rfl := Except.ok.inj htarget₂
        rw [hgas] at hgas₂
        obtain rfl := Except.ok.inj hgas₂
        rcases Globals.call_dialogue _ _ _ answer₁ answer₂ with ⟨rfl, _⟩ | hdiv
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr hdiv
    | control hterm _ =>
        exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim
    | assign hstmt₂ _ | icall hstmt₂ _ _ _ | sstore hstmt₂ _ _ | gas hstmt₂
    | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _ | mstore32 hstmt₂ _ _ _
    | mload32 hstmt₂ _ =>
        rw [hstmt] at hstmt₂; simp at hstmt₂
  case refine_5 =>
    intro _ _ _ _ _ _ hstmt _ _ _
    exact (program.memOracleFree_not_malloc hfree hstmt).elim
  case refine_6 =>
    intro _ _ _ _ _ _ hstmt _ _
    exact (program.memOracleFree_not_mallocUninit hfree hstmt).elim
  case refine_7 =>
    intro state next offsetVar valueVar offset value hstmt hoffset hvalue hbound
    intro trace₂ final₂ h₂
    cases h₂ with
    | mstore32 hstmt₂ hoffset₂ hvalue₂ _ =>
        obtain ⟨rfl, heq⟩ := Prod.mk.inj (Option.some.inj (hstmt.symm.trans hstmt₂))
        obtain ⟨rfl, rfl⟩ := Stmt.mstore32.inj heq
        rw [hoffset] at hoffset₂
        obtain rfl := Except.ok.inj hoffset₂
        rw [hvalue] at hvalue₂
        obtain rfl := Except.ok.inj hvalue₂
        exact .inl ⟨rfl, rfl⟩
    | control hterm _ =>
        exact (program.statementAt_terminatorAt_exclusive hstmt hterm).elim
    | assign hstmt₂ _ | icall hstmt₂ _ _ _ | sstore hstmt₂ _ _ | gas hstmt₂
    | call hstmt₂ _ _ | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _
    | mload32 hstmt₂ _ =>
        rw [hstmt] at hstmt₂; simp at hstmt₂
  case refine_8 =>
    intro _ _ _ _ _ _ hstmt _
    exact (program.memOracleFree_not_mload32 hfree hstmt).elim
  case refine_9 =>
    intros
    apply dialogue_icall <;> assumption
  case refine_10 =>
    intros
    apply dialogue_control <;> assumption
  case refine_11 => intros; exact runDialogue_refl
  case refine_12 => intros; apply runDialogue_tail <;> assumption
  case refine_13 => intros; apply evalDialogue_exit <;> assumption

theorem runDialogue_all {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {state final : State} {trace : Trace}
    (h : Steps program ctx state trace final) :
    RunDialogue program ctx state trace final := by
  refine Steps.inductionOn (motive := fun state trace final _ =>
      RunDialogue program ctx state trace final)
    (fun _ => runDialogue_refl)
    (fun _ next ihRun => runDialogue_tail next ihRun (stepDialogue_all hfree next)) h

theorem evalDialogue_all {program : Program} {ctx : CallContext}
    (hfree : program.MemOracleFree) {function : FunctionId} {globals globals' : Globals}
    {args : Array Word} {trace : Trace} {outcome : FunctionOutcome}
    (h : EvalFn program ctx function globals args trace globals' outcome) :
    EvalDialogue program ctx function globals args trace globals' outcome := by
  cases h with
  | exit hentry hrun hexit =>
      exact evalDialogue_exit hentry hexit (runDialogue_all hfree hrun)

end Proofs

end Sir.Vars

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

theorem stepDialogue_all
    (hfree : program.MemOracleFree)
    {state final : Vars.State} {trace : Trace}
    (h : Vars.SmallStep program ctx state trace final) :
    ∀ trace₂ final₂, Vars.SmallStep program ctx state trace₂ final₂ →
      (trace = trace₂ ∧ final = final₂) ∨ Trace.QueryDivergence trace trace₂ :=
  Vars.Proofs.stepDialogue_all hfree h

theorem runDialogue_all
    (hfree : program.MemOracleFree)
    {state final : Vars.State} {trace : Trace}
    (h : Vars.Steps program ctx state trace final) :
    ∀ trace₂ final₂, Vars.Steps program ctx state trace₂ final₂ →
      Vars.Steps.Extends program ctx final trace final₂ trace₂ ∨
      Vars.Steps.Extends program ctx final₂ trace₂ final trace ∨
      Trace.QueryDivergence trace trace₂ :=
  Vars.Proofs.runDialogue_all hfree h

theorem fnDialogue_all
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : Vars.EvalFn program ctx function globals args trace globals' outcome) :
    ∀ trace₂ globals₂ outcome₂,
      Vars.EvalFn program ctx function globals args trace₂ globals₂ outcome₂ →
      (trace = trace₂ ∧ globals' = globals₂ ∧ outcome = outcome₂) ∨
      Trace.QueryDivergence trace trace₂ :=
  Vars.Proofs.evalDialogue_all hfree h

theorem Vars.Proofs.Steps.confluence_or_queryDivergence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : Vars.State} {trace₁ trace₂ : Trace}
    (h₁ : Vars.Steps program ctx state trace₁ final₁)
    (h₂ : Vars.Steps program ctx state trace₂ final₂) :
    Vars.Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
    Vars.Steps.Extends program ctx final₂ trace₂ final₁ trace₁ ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  runDialogue_all hfree h₁ trace₂ final₂ h₂

end Sir
