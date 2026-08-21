import Sir.Stack.Proofs

namespace Sir.Stack

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
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?refl ?tail ?_ h
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

def Stuck (program : Program) (ctx : CallContext) (state : State) : Prop :=
  ∀ trace final, ¬ SmallStep program ctx state trace final

theorem Steps.eq_of_stuck {program : Program} {ctx : CallContext}
    {state final : State} {trace : Trace}
    (h : Steps program ctx state trace final)
    (hstuck : Stuck program ctx state) : final = state ∧ trace = [] := by
  rcases h.headDecomp with ⟨rfl, rfl⟩ | ⟨middle, trace₁, _, step, _, _⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd step (hstuck trace₁ middle)

theorem stuck_of_exit {program : Program} {ctx : CallContext}
    {state : State} {outcome : FunctionOutcome}
    (hcontrol : state.control = outcome.toControl) : Stuck program ctx state := by
  intro trace final hstep
  cases outcome with
  | returned results =>
      cases hstep <;> simp_all [FunctionOutcome.toControl, Program.AtInstr, Program.AtTerm,
        Program.atInstr, Program.instructionAt, Program.atTerm, Program.terminatorAt]
  | halted =>
      cases hstep <;> simp_all [FunctionOutcome.toControl, Program.AtInstr, Program.AtTerm,
        Program.atInstr, Program.instructionAt, Program.atTerm, Program.terminatorAt]

private theorem dialogue_icall {program : Program} {ctx : CallContext}
    {state : State} {callee : FunctionId} {argumentCount resultCount : Nat}
    {next : Control} {values : Array Word} {trace : Trace} {globals' : Globals}
    {outcome : FunctionOutcome} {env' : Environment} {control' : Control}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hfetch : state.fetch argumentCount = .ok values)
    (hresume : resume outcome state.environment ⟨argumentCount, resultCount⟩ next =
      .ok (env', control'))
    (ih : EvalDialogue program ctx callee state.globals values trace globals' outcome) :
    StepDialogue program ctx state trace
      { globals := globals', environment := env', control := control' } := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | icall hinstr₂ hfetch₂ hcallee₂ hresume₂ =>
      obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hinstr₂
      obtain ⟨rfl, rfl, rfl⟩ := Instr.icall.inj heq
      rw [hfetch] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases ih _ _ _ hcallee₂ with ⟨rfl, rfl, rfl⟩ | hdiv
      · rw [hresume] at hresume₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hresume₂)
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv
  | control hterm₂ _ =>
      exact (Program.AtInstr_AtTerm_exclusive hinstr hterm₂).elim
  | pure hstmt₂ heval₂ =>
      obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hstmt₂
      subst heq
      simp [State.evaluate, evalInstr] at heval₂
  | gas hstmt₂ _ | call hstmt₂ _ _
  | malloc hstmt₂ _ _ _ | mallocUninit hstmt₂ _ _
  | mstore32 hstmt₂ _ _ _ | mload32 hstmt₂ _ =>
      cases (Program.AtInstr.unique hinstr hstmt₂).2

private theorem dialogue_control {program : Program} {ctx : CallContext}
    {state : State} {terminator : Terminator} {environment : Environment}
    {control : Control}
    (hterm : program.AtTerm state terminator)
    (heval : evaluateTerminator program state.environment state.control terminator =
      .ok (environment, control)) :
    StepDialogue program ctx state [] (State.of state.globals environment control) := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | control hterm₂ heval₂ =>
      obtain rfl := Program.AtTerm.unique hterm hterm₂
      rw [heval] at heval₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj heval₂)
      exact .inl ⟨rfl, rfl⟩
  | pure hstmt _ | gas hstmt _ | call hstmt _ _
  | malloc hstmt _ _ _ | mallocUninit hstmt _ _
  | mstore32 hstmt _ _ _ | mload32 hstmt _ | icall hstmt _ _ _ =>
      exact (Program.AtInstr_AtTerm_exclusive hstmt hterm).elim

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
    (hentry : entry program function globals args = some initial)
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  case refine_1 =>
    intro next instruction globals environment state hinstr heval
    intro trace₂ final₂ h₂
    cases h₂ with
    | pure hinstr₂ heval₂ =>
        obtain ⟨rfl, rfl⟩ := Program.AtInstr.unique hinstr hinstr₂
        rw [heval] at heval₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj heval₂)
        exact .inl ⟨rfl, rfl⟩
    | control hterm _ =>
        exact (Program.AtInstr_AtTerm_exclusive hinstr hterm).elim
    | gas hinstr₂ _ | call hinstr₂ _ _
    | malloc hinstr₂ _ _ _ | mallocUninit hinstr₂ _ _
    | mstore32 hinstr₂ _ _ _ | mload32 hinstr₂ _ | icall hinstr₂ _ _ _ =>
        obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hinstr₂
        subst heq
        simp [State.evaluate, evalInstr] at heval
  case refine_2 =>
    intro state next answer₁ environment₁ hinstr hpush₁
    intro trace₂ final₂ h₂
    cases h₂ with
    | @gas state₂ next₂ answer₂ environment₂ hinstr₂ hpush₂ =>
        obtain ⟨rfl, _⟩ := Program.AtInstr.unique hinstr hinstr₂
        rcases Globals.gas_dialogue answer₁ answer₂ with rfl | hdiv
        · rw [hpush₁] at hpush₂
          obtain rfl := Except.ok.inj hpush₂
          exact .inl ⟨rfl, rfl⟩
        · exact .inr hdiv
    | control hterm _ =>
        exact (Program.AtInstr_AtTerm_exclusive hinstr hterm).elim
    | pure hinstr₂ heval₂ =>
        obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hinstr₂
        subst heq
        simp [State.evaluate, evalInstr] at heval₂
    | call hinstr₂ _ _
    | malloc hinstr₂ _ _ _ | mallocUninit hinstr₂ _ _
    | mstore32 hinstr₂ _ _ _ | mload32 hinstr₂ _ | icall hinstr₂ _ _ _ =>
        cases (Program.AtInstr.unique hinstr hinstr₂).2
  case refine_3 =>
    intro state next target gasLimit environment₁ answer₁ hinstr hfetch₁ hpush₁
    intro trace₂ final₂ h₂
    cases h₂ with
    | @call state₂ next₂ target₂ gas₂ environment₂ answer₂ hinstr₂ hfetch₂ hpush₂ =>
        obtain ⟨rfl, _⟩ := Program.AtInstr.unique hinstr hinstr₂
        rw [hfetch₁] at hfetch₂
        have harray := Except.ok.inj hfetch₂
        have htarget := congrArg (fun values => values[0]?) harray
        have hgas := congrArg (fun values => values[1]?) harray
        simp at htarget hgas
        cases htarget
        cases hgas
        rcases Globals.call_dialogue _ _ _ answer₁ answer₂ with ⟨rfl, _⟩ | hdiv
        · rw [hpush₁] at hpush₂
          obtain rfl := Except.ok.inj hpush₂
          exact .inl ⟨rfl, rfl⟩
        · exact .inr hdiv
    | control hterm _ =>
        exact (Program.AtInstr_AtTerm_exclusive hinstr hterm).elim
    | pure hinstr₂ heval₂ =>
        obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hinstr₂
        subst heq
        simp [State.evaluate, evalInstr] at heval₂
    | gas hinstr₂ _
    | malloc hinstr₂ _ _ _ | mallocUninit hinstr₂ _ _
    | mstore32 hinstr₂ _ _ _ | mload32 hinstr₂ _ | icall hinstr₂ _ _ _ =>
        cases (Program.AtInstr.unique hinstr hinstr₂).2
  case refine_4 =>
    intros
    exact (program.memOracleFree_not_malloc hfree ‹_›).elim
  case refine_5 =>
    intros
    exact (program.memOracleFree_not_mallocUninit hfree ‹_›).elim
  case refine_6 =>
    intro next offset value environment state hinstr hfetch hbound hpush
    intro trace₂ final₂ h₂
    cases h₂ with
    | mstore32 hinstr₂ hfetch₂ _ hpush₂ =>
        obtain ⟨rfl, _⟩ := Program.AtInstr.unique hinstr hinstr₂
        rw [hfetch] at hfetch₂
        have harray := Except.ok.inj hfetch₂
        have hoffset := congrArg (fun values => values[0]?) harray
        have hvalue := congrArg (fun values => values[1]?) harray
        simp at hoffset hvalue
        cases hoffset
        cases hvalue
        rw [hpush] at hpush₂
        obtain rfl := Except.ok.inj hpush₂
        exact .inl ⟨rfl, rfl⟩
    | control hterm _ =>
        exact (Program.AtInstr_AtTerm_exclusive hinstr hterm).elim
    | pure hinstr₂ heval₂ =>
        obtain ⟨rfl, heq⟩ := Program.AtInstr.unique hinstr hinstr₂
        subst heq
        simp [State.evaluate, evalInstr] at heval₂
    | gas hinstr₂ _ | call hinstr₂ _ _
    | malloc hinstr₂ _ _ _ | mallocUninit hinstr₂ _ _
    | mload32 hinstr₂ _ | icall hinstr₂ _ _ _ =>
        cases (Program.AtInstr.unique hinstr hinstr₂).2
  case refine_7 =>
    intros
    exact (program.memOracleFree_not_mload32 hfree ‹_›).elim
  case refine_8 =>
    intros
    apply dialogue_icall <;> assumption
  case refine_9 =>
    intros
    apply dialogue_control <;> assumption
  case refine_10 => intros; exact runDialogue_refl
  case refine_11 => intros; apply runDialogue_tail <;> assumption
  case refine_12 => intros; apply evalDialogue_exit <;> assumption

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

theorem Steps.confluence_or_queryDivergence
    {program : Program} {ctx : CallContext} (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ : Trace}
    (h₁ : Steps program ctx state trace₁ final₁)
    (h₂ : Steps program ctx state trace₂ final₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
    Steps.Extends program ctx final₂ trace₂ final₁ trace₁ ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  runDialogue_all hfree h₁ trace₂ final₂ h₂

end Proofs

end Sir.Stack
