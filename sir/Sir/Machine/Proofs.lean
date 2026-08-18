import Sir.Machine.Spec

namespace Sir.Trace.QueryDivergence

theorem extend {trace₁ trace₂ : Trace} (suffix₁ suffix₂ : Trace)
    (h : Trace.QueryDivergence trace₁ trace₂) :
    Trace.QueryDivergence (trace₁ ++ suffix₁) (trace₂ ++ suffix₂) := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, hquery⟩ := h
  exact ⟨pre, event₁, rest₁ ++ suffix₁, event₂, rest₂ ++ suffix₂,
    by simp, by simp, hne, hquery⟩

theorem appendLeft {trace₁ trace₂ : Trace} (pre : Trace)
    (h : Trace.QueryDivergence trace₁ trace₂) :
    Trace.QueryDivergence (pre ++ trace₁) (pre ++ trace₂) := by
  obtain ⟨common, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, hquery⟩ := h
  exact ⟨pre ++ common, event₁, rest₁, event₂, rest₂,
    by simp, by simp, hne, hquery⟩

theorem symmetric {trace₁ trace₂ : Trace}
    (h : Trace.QueryDivergence trace₁ trace₂) :
    Trace.QueryDivergence trace₂ trace₁ := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, htrace₁, htrace₂, hne, hquery⟩ := h
  exact ⟨pre, event₂, rest₂, event₁, rest₁, htrace₂, htrace₁,
    fun heq => hne heq.symm, hquery.symm⟩

end Sir.Trace.QueryDivergence

namespace Sir.FunctionOutcome

theorem toControl_inj {outcome₁ outcome₂ : FunctionOutcome}
    (h : outcome₁.toControl = outcome₂.toControl) : outcome₁ = outcome₂ := by
  cases outcome₁ <;> cases outcome₂ <;> simp_all [toControl]

end Sir.FunctionOutcome

namespace Sir.Machine

open Sir

namespace MemoryPolicy

theorem empty_deterministic : empty.Deterministic := by
  intro _ _ _ _ impossible
  exact False.elim impossible

end MemoryPolicy

namespace Operation

def Outcome.trace : Outcome → Trace
  | .next _ _ trace | .halted _ trace => trace

theorem execute_ne_halted {ctx : CallContext} {operation : Operation}
    {oracle : operation.Oracle} {globals globals' : Globals} {operands : Array Word}
    {trace : Trace} :
    operation.execute ctx oracle globals operands ≠ .ok (.halted globals' trace) := by
  intro h
  cases operation <;> simp only [execute, pure, Except.pure] at h <;>
    (repeat' split at h) <;> cases h

private theorem executeCallInv {ctx : CallContext} {result : CallResult}
    {globals : Globals} {operands : Array Word} {outcome : Outcome}
    (h : @Operation.execute ctx Operation.call result globals operands = .ok outcome) :
    ∃ callee gasValue,
      operands[0]? = some callee ∧ operands[1]? = some gasValue ∧
      outcome = .next #[Evm.UInt256.fromBool result.success]
        { globals with returnData := result.output, world := result.world' }
        [Sir.Event.call
          { input := { target := .ofUInt256 callee, gas := gasValue, world := globals.world },
            result }] := by
  change (do
    let some callee := operands[0]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let some gasValue := operands[1]? |
      throw (IRError.blockArityMismatch operands.size 2)
    let input : CallInput :=
      { target := .ofUInt256 callee, gas := gasValue, world := globals.world }
    let record : CallRecord := { input, result }
    return Outcome.next #[Evm.UInt256.fromBool result.success]
      { globals with returnData := result.output, world := result.world' }
      [Sir.Event.call record] : Except IRError Outcome) = Except.ok outcome at h
  split at h
  next callee hcallee =>
    split at h
    next gasValue hgas =>
      exact ⟨callee, gasValue, hcallee, hgas, (Except.ok.inj h).symm⟩
    next => contradiction
  next => contradiction

theorem execute_dialogue {policy : MemoryPolicy} (ctx : CallContext)
    (operation : Operation)
    (hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic)
    (globals : Globals)
    (operands : Array Word) {oracle₁ oracle₂ : operation.Oracle}
    {outcome₁ outcome₂ : Outcome}
    (hadmissible₁ : operation.Admissible policy globals operands oracle₁)
    (hadmissible₂ : operation.Admissible policy globals operands oracle₂)
    (hexecute₁ : operation.execute ctx oracle₁ globals operands = .ok outcome₁)
    (hexecute₂ : operation.execute ctx oracle₂ globals operands = .ok outcome₂)
    (hmload : operation ≠ .mload32) :
    outcome₁ = outcome₂ ∨
      Trace.QueryDivergence outcome₁.trace outcome₂.trace := by
  classical
  cases operation with
  | gas =>
      simp only [execute] at hexecute₁ hexecute₂
      obtain rfl := Except.ok.inj hexecute₁
      obtain rfl := Except.ok.inj hexecute₂
      by_cases horacle : oracle₁ = oracle₂
      · exact .inl (by cases horacle; rfl)
      · exact .inr ⟨[], .gas oracle₁, [], .gas oracle₂, [], rfl, rfl,
          fun heq => horacle (Sir.Event.gas.inj heq), rfl⟩
  | call =>
      by_cases horacle : oracle₁ = oracle₂
      · subst oracle₂
        rw [hexecute₁] at hexecute₂
        exact .inl (Except.ok.inj hexecute₂)
      · obtain ⟨callee₁, gasValue₁, hcallee₁, hgas₁, rfl⟩ :=
          executeCallInv hexecute₁
        obtain ⟨callee₂, gasValue₂, hcallee₂, hgas₂, rfl⟩ :=
          executeCallInv hexecute₂
        obtain rfl := Option.some.inj (hcallee₁.symm.trans hcallee₂)
        obtain rfl := Option.some.inj (hgas₁.symm.trans hgas₂)
        exact .inr ⟨[], _, [], _, [], rfl, rfl,
          fun heq => horacle (congrArg CallRecord.result (Sir.Event.call.inj heq)), rfl⟩
  | malloc =>
      obtain ⟨size₁, hsize₁, hallows₁, _, _, _⟩ := hadmissible₁
      obtain ⟨size₂, hsize₂, hallows₂, _, _, _⟩ := hadmissible₂
      obtain rfl := Option.some.inj (hsize₁.symm.trans hsize₂)
      obtain rfl := hmalloc (.inl rfl) _ _ _ _ hallows₁ hallows₂
      rw [hexecute₁] at hexecute₂
      exact .inl (Except.ok.inj hexecute₂)
  | mallocUninit =>
      obtain ⟨size₁, hsize₁, hallows₁, _, _⟩ := hadmissible₁
      obtain ⟨size₂, hsize₂, hallows₂, _, _⟩ := hadmissible₂
      obtain rfl := Option.some.inj (hsize₁.symm.trans hsize₂)
      obtain rfl := hmalloc (.inr rfl) _ _ _ _ hallows₁ hallows₂
      rw [hexecute₁] at hexecute₂
      exact .inl (Except.ok.inj hexecute₂)
  | mload32 => exact (hmload rfl).elim
  | _ =>
      obtain rfl : oracle₁ = oracle₂ := rfl
      rw [hexecute₁] at hexecute₂
      exact .inl (Except.ok.inj hexecute₂)

end Operation

namespace OperandFrame

theorem firesHalt_false (frame : OperandFrame) {policy : MemoryPolicy} {ctx : CallContext}
    {operation : Operation} {src : frame.Source} {env : frame.Environment}
    {globals globals' : Globals} {trace : Trace}
    (h : frame.FiresHalt policy ctx operation src env globals trace globals') : False := by
  cases h with
  | halted _ _ hexecute => exact Operation.execute_ne_halted hexecute

theorem fires_dialogue (frame : OperandFrame) {policy : MemoryPolicy}
    {operation : Operation}
    (hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic)
    {ctx : CallContext}
    {src : frame.Source} {dst : frame.Destination} {env env₁ env₂ : frame.Environment}
    {globals globals₁ globals₂ : Globals} {trace₁ trace₂ : Trace}
    (hmload : operation ≠ .mload32)
    (h₁ : frame.Fires policy ctx operation src dst env globals trace₁ env₁ globals₁)
    (h₂ : frame.Fires policy ctx operation src dst env globals trace₂ env₂ globals₂) :
    (trace₁ = trace₂ ∧ env₁ = env₂ ∧ globals₁ = globals₂) ∨
      Trace.QueryDivergence trace₁ trace₂ := by
  cases h₁ with
  | next hadmissible₁ hfetch₁ hexecute₁ hstore₁ =>
    cases h₂ with
    | next hadmissible₂ hfetch₂ hexecute₂ hstore₂ =>
      rw [hfetch₁] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases Operation.execute_dialogue ctx operation hmalloc globals _
          hadmissible₁ hadmissible₂ hexecute₁ hexecute₂ hmload with heq | hdiv
      · injection heq with hresults hglobals htrace
        subst hresults hglobals htrace
        rw [hstore₁] at hstore₂
        exact .inl ⟨rfl, Except.ok.inj hstore₂, rfl⟩
      · exact .inr hdiv

theorem firesHalt_dialogue (frame : OperandFrame) {policy : MemoryPolicy}
    {operation : Operation}
    (hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic)
    {ctx : CallContext}
    {src : frame.Source} {env : frame.Environment} {globals globals₁ globals₂ : Globals}
    {trace₁ trace₂ : Trace} (hmload : operation ≠ .mload32)
    (h₁ : frame.FiresHalt policy ctx operation src env globals trace₁ globals₁)
    (h₂ : frame.FiresHalt policy ctx operation src env globals trace₂ globals₂) :
    (trace₁ = trace₂ ∧ globals₁ = globals₂) ∨
      Trace.QueryDivergence trace₁ trace₂ := by
  cases h₁ with
  | halted hadmissible₁ hfetch₁ hexecute₁ =>
    cases h₂ with
    | halted hadmissible₂ hfetch₂ hexecute₂ =>
      rw [hfetch₁] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases Operation.execute_dialogue ctx operation hmalloc globals _
          hadmissible₁ hadmissible₂ hexecute₁ hexecute₂ hmload with heq | hdiv
      · injection heq with hglobals htrace
        subst hglobals htrace
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv

theorem fires_firesHalt_dialogue (frame : OperandFrame) {policy : MemoryPolicy}
    {operation : Operation}
    (hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic)
    {ctx : CallContext}
    {src : frame.Source} {dst : frame.Destination} {env env' : frame.Environment}
    {globals globals₁ globals₂ : Globals} {trace₁ trace₂ : Trace}
    (hmload : operation ≠ .mload32)
    (h₁ : frame.Fires policy ctx operation src dst env globals trace₁ env' globals₁)
    (h₂ : frame.FiresHalt policy ctx operation src env globals trace₂ globals₂) :
    Trace.QueryDivergence trace₁ trace₂ := by
  cases h₁ with
  | next hadmissible₁ hfetch₁ hexecute₁ _ =>
    cases h₂ with
    | halted hadmissible₂ hfetch₂ hexecute₂ =>
      rw [hfetch₁] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases Operation.execute_dialogue ctx operation hmalloc globals _
          hadmissible₁ hadmissible₂ hexecute₁ hexecute₂ hmload with heq | hdiv
      · cases heq
      · exact hdiv

end OperandFrame

@[elab_as_elim]
theorem Steps.inductionOn {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {motive : (state : State frame) → (trace : Trace) → (final : State frame) →
      Steps frame decoder policy ctx state trace final → Prop}
    (refl : ∀ state, motive state [] state .refl)
    (tail : ∀ {state middle final : State frame} {trace₁ trace₂ : Trace}
      (start : Steps frame decoder policy ctx state trace₁ middle)
      (next : Step frame decoder policy ctx middle trace₂ final),
      motive state trace₁ middle start →
        motive state (trace₁ ++ trace₂) final (start.tail next))
    {state final : State frame} {trace : Trace}
    (h : Steps frame decoder policy ctx state trace final) : motive state trace final h := by
  refine Steps.rec (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun state trace final h => motive state trace final h)
      (motive_3 := fun _ _ _ _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?refl ?tail ?_ h
  case refl => intro state; exact refl state
  case tail => intro state middle final trace₁ trace₂ start next ih _
               exact tail start next ih
  all_goals intros; trivial

theorem Steps.trans {frame : OperandFrame}
    {decoder : Decoder frame} {policy : MemoryPolicy} {ctx : CallContext}
    {start middle final : State frame} {firstTrace secondTrace : Trace}
    (first : Steps frame decoder policy ctx start firstTrace middle)
    (second : Steps frame decoder policy ctx middle secondTrace final) :
    Steps frame decoder policy ctx start (firstTrace ++ secondTrace) final := by
  exact Steps.inductionOn
    (motive := fun middle secondTrace final _ =>
      ∀ {start firstTrace}, Steps frame decoder policy ctx start firstTrace middle →
        Steps frame decoder policy ctx start (firstTrace ++ secondTrace) final)
    (fun _ => by
      intro start firstTrace first
      simpa using first)
    (fun {state middle final trace₁ trace₂} rest step ih => by
      intro start firstTrace first
      simpa [List.append_assoc] using (ih first).tail step)
    second first

def Stuck {frame : OperandFrame} (decoder : Decoder frame) (policy : MemoryPolicy)
    (ctx : CallContext) (state : State frame) : Prop :=
  ∀ trace final, ¬ Step frame decoder policy ctx state trace final

theorem Steps.single {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext} {state final : State frame}
    {trace : Trace} (h : Step frame decoder policy ctx state trace final) :
    Steps frame decoder policy ctx state trace final :=
  .tail .refl h

theorem Steps.headDecomp {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext} {state final : State frame}
    {trace : Trace} (h : Steps frame decoder policy ctx state trace final) :
    (state = final ∧ trace = []) ∨
      ∃ middle trace₁ trace₂,
        Step frame decoder policy ctx state trace₁ middle ∧
        Steps frame decoder policy ctx middle trace₂ final ∧
        trace = trace₁ ++ trace₂ := by
  refine Steps.inductionOn (motive := fun state trace final _ =>
      (state = final ∧ trace = []) ∨
        ∃ middle trace₁ trace₂,
          Step frame decoder policy ctx state trace₁ middle ∧
          Steps frame decoder policy ctx middle trace₂ final ∧
          trace = trace₁ ++ trace₂)
    (fun _ => .inl ⟨rfl, rfl⟩)
    (fun start next ih => by
      rcases ih with ⟨rfl, rfl⟩ | ⟨middle, pre, suffix, step, rest, rfl⟩
      · exact .inr ⟨_, _, [], next, .refl, by simp⟩
      · exact .inr ⟨middle, pre, suffix ++ _, step, rest.tail next, by simp⟩)
    h

theorem Steps.eq_of_stuck {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext} {state final : State frame}
    {trace : Trace} (h : Steps frame decoder policy ctx state trace final)
    (hstuck : Stuck decoder policy ctx state) : final = state ∧ trace = [] := by
  rcases h.headDecomp with ⟨rfl, rfl⟩ | ⟨middle, trace₁, _, step, _, _⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd step (hstuck trace₁ middle)

theorem stuck_of_exit {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {state : State frame} {outcome : FunctionOutcome}
    (hcontrol : state.control = outcome.toControl) : Stuck decoder policy ctx state := by
  intro trace final hstep
  cases outcome with
  | returned results =>
      rcases decoder.terminal.1 state.environment state.globals results with ⟨hdecode, hcontrolStep⟩
      cases hstep <;> simp_all [FunctionOutcome.toControl]
  | halted =>
      rcases decoder.terminal.2 state.environment state.globals with ⟨hdecode, hcontrolStep⟩
      cases hstep <;> simp_all [FunctionOutcome.toControl]

private theorem dialogue_op {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {state : State frame} {operation : Operation} {src : frame.Source} {dst : frame.Destination}
    {next : Machine.MachineControl} {trace : Trace} {env' : frame.Environment} {globals' : Globals}
    (hdecode : decoder.decode state.control =
      some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
    (hfires : frame.Fires policy ctx operation src dst state.environment state.globals
      trace env' globals') :
    StepDialogue decoder policy ctx state trace
      { globals := globals', environment := env', control := next } := by
  have hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic := by
    intro hop
    rcases halloc with hdet | hno
    · exact hdet
    · rcases hop with rfl | rfl
      · exact (hno.1 _ _ _ _ hdecode).elim
      · exact (hno.2 _ _ _ _ hdecode).elim
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | operation hdecode₂ hfires₂ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      obtain ⟨hinstr, hnext⟩ := Prod.mk.inj heq
      cases hnext
      cases hinstr
      have hmload : operation ≠ .mload32 := fun hop => by
        subst hop
        exact hnomload _ _ _ _ hdecode
      rcases frame.fires_dialogue hmalloc hmload hfires hfires₂ with hsame | hdiv
      · obtain ⟨rfl, rfl, rfl⟩ := hsame
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv
  | operationHalted hdecode₂ hfires₂ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      obtain ⟨hinstr, _⟩ := Prod.mk.inj heq
      cases hinstr
      have hmload : operation ≠ .mload32 := fun hop => by
        subst hop
        exact hnomload _ _ _ _ hdecode
      exact .inr (frame.fires_firesHalt_dialogue hmalloc hmload hfires hfires₂)
  | internalCall hdecode₂ _ _ _ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      exact Instruction.Kind.noConfusion (congrArg Instruction.kind (congrArg Prod.fst heq))
  | control hcontrol₂ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode
      rw [hcontrol₂] at hnone
      contradiction

private theorem dialogue_opHalted {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {state : State frame} {operation : Operation} {src : frame.Source} {dst : frame.Destination}
    {next : Machine.MachineControl} {trace : Trace} {globals' : Globals}
    (hdecode : decoder.decode state.control =
      some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
    (hfires : frame.FiresHalt policy ctx operation src state.environment state.globals
      trace globals') :
    StepDialogue decoder policy ctx state trace
      { globals := globals', environment := state.environment, control := .halted } := by
  have hmalloc : operation = .malloc ∨ operation = .mallocUninit → policy.Deterministic := by
    intro hop
    rcases halloc with hdet | hno
    · exact hdet
    · rcases hop with rfl | rfl
      · exact (hno.1 _ _ _ _ hdecode).elim
      · exact (hno.2 _ _ _ _ hdecode).elim
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | operation hdecode₂ hfires₂ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      obtain ⟨hinstr, _⟩ := Prod.mk.inj heq
      cases hinstr
      have hmload : operation ≠ .mload32 := fun hop => by
        subst hop
        exact hnomload _ _ _ _ hdecode
      exact .inr (Trace.QueryDivergence.symmetric
        (frame.fires_firesHalt_dialogue hmalloc hmload hfires₂ hfires))
  | operationHalted hdecode₂ hfires₂ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      obtain ⟨hinstr, _⟩ := Prod.mk.inj heq
      cases hinstr
      have hmload : operation ≠ .mload32 := fun hop => by
        subst hop
        exact hnomload _ _ _ _ hdecode
      rcases frame.firesHalt_dialogue hmalloc hmload hfires hfires₂ with hsame | hdiv
      · obtain ⟨rfl, rfl⟩ := hsame
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv
  | internalCall hdecode₂ _ _ _ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      exact Instruction.Kind.noConfusion (congrArg Instruction.kind (congrArg Prod.fst heq))
  | control hcontrol₂ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode
      rw [hcontrol₂] at hnone
      contradiction

private theorem dialogue_icall {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {state : State frame} {callee : FunctionId} {src : frame.Source} {dst : frame.Destination}
    {next : Machine.MachineControl} {values : Array Word} {trace : Trace}
    {globals' : Globals} {outcome : FunctionOutcome} {env' : frame.Environment}
    {control' : Machine.MachineControl}
    (hdecode : decoder.decode state.control =
      some (⟨Instruction.Kind.icall callee, src, dst⟩, next))
    (hfetch : frame.fetch state.environment src = .ok values)
    (hresume : decoder.resume outcome state.environment dst next = some (env', control'))
    (ih : EvalDialogue decoder policy ctx callee state.globals values trace globals' outcome) :
    StepDialogue decoder policy ctx state trace
      { globals := globals', environment := env', control := control' } := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | operation hdecode₂ _ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      exact Instruction.Kind.noConfusion (congrArg Instruction.kind (congrArg Prod.fst heq))
  | operationHalted hdecode₂ _ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      exact Instruction.Kind.noConfusion (congrArg Instruction.kind (congrArg Prod.fst heq))
  | internalCall hdecode₂ hfetch₂ hcallee₂ hresume₂ =>
      have heq := Option.some.inj (hdecode.symm.trans hdecode₂)
      obtain ⟨hinstr, hnext⟩ := Prod.mk.inj heq
      cases hnext
      cases hinstr
      rw [hfetch] at hfetch₂
      obtain rfl := Except.ok.inj hfetch₂
      rcases ih _ _ _ hcallee₂ with ⟨rfl, rfl, rfl⟩ | hdiv
      · rw [hresume] at hresume₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hresume₂)
        exact .inl ⟨rfl, rfl⟩
      · exact .inr hdiv
  | control hcontrol₂ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode
      rw [hcontrol₂] at hnone
      contradiction

private theorem dialogue_control {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {state : State frame} {trace : Trace} {env' : frame.Environment}
    {globals' : Globals} {control' : Machine.MachineControl}
    (hcontrol : decoder.control state.environment state.globals state.control =
      some (trace, env', globals', control')) :
    StepDialogue decoder policy ctx state trace
      { globals := globals', environment := env', control := control' } := by
  intro trace₂ final₂ hstep₂
  cases hstep₂ with
  | operation hdecode₂ _ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode₂
      rw [hcontrol] at hnone
      contradiction
  | operationHalted hdecode₂ _ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode₂
      rw [hcontrol] at hnone
      contradiction
  | internalCall hdecode₂ _ _ _ =>
      have hnone := decoder.exclusive state.environment state.globals state.control _ _ hdecode₂
      rw [hcontrol] at hnone
      contradiction
  | control hcontrol₂ =>
      rw [hcontrol] at hcontrol₂
      have heq := Option.some.inj hcontrol₂
      have htrace := congrArg (fun result => result.1) heq
      have henv := congrArg (fun result => result.2.1) heq
      have hglobals := congrArg (fun result => result.2.2.1) heq
      have hnext := congrArg (fun result => result.2.2.2) heq
      exact .inl ⟨htrace, by cases henv; cases hglobals; cases hnext; rfl⟩

private theorem runDialogue_refl {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext} {state : State frame} :
    RunDialogue decoder policy ctx state [] state :=
  fun trace _ h => .inl ⟨trace, h, rfl⟩

private theorem runDialogue_tail {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {state middle final : State frame} {trace₁ trace₂ : Trace}
    (next : Step frame decoder policy ctx middle trace₂ final)
    (ihRun : RunDialogue decoder policy ctx state trace₁ middle)
    (ihStep : StepDialogue decoder policy ctx middle trace₂ final) :
    RunDialogue decoder policy ctx state (trace₁ ++ trace₂) final := by
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

private theorem evalDialogue_exit {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    {function : FunctionId} {globals : Globals} {args : Array Word}
    {trace : Trace} {initial exit : State frame} {outcome : FunctionOutcome}
    (hentry : decoder.entry function globals args = some initial)
    (hexit : exit.control = outcome.toControl)
    (ihRun : RunDialogue decoder policy ctx initial trace exit) :
    EvalDialogue decoder policy ctx function globals args trace exit.globals outcome := by
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

theorem stepDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {state final : State frame} {trace : Trace}
    (h : Step frame decoder policy ctx state trace final) :
    StepDialogue decoder policy ctx state trace final := by
  refine Step.rec
    (motive_1 := fun state trace final _ =>
      StepDialogue decoder policy ctx state trace final)
    (motive_2 := fun state trace final _ =>
      RunDialogue decoder policy ctx state trace final)
    (motive_3 := fun function globals args trace globals' outcome _ =>
      EvalDialogue decoder policy ctx function globals args trace globals' outcome)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  case refine_1 => intros; apply dialogue_op halloc hnomload <;> assumption
  case refine_2 => intros; apply dialogue_opHalted halloc hnomload <;> assumption
  case refine_3 => intros; apply dialogue_icall <;> assumption
  case refine_4 => intros; apply dialogue_control; assumption
  case refine_5 => intros; exact runDialogue_refl
  case refine_6 => intros; apply runDialogue_tail <;> assumption
  case refine_7 => intros; apply evalDialogue_exit <;> assumption

theorem runDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {state final : State frame} {trace : Trace}
    (h : Steps frame decoder policy ctx state trace final) :
    RunDialogue decoder policy ctx state trace final := by
  refine Steps.inductionOn (motive := fun state trace final _ =>
      RunDialogue decoder policy ctx state trace final)
    (fun _ => runDialogue_refl)
    (fun _ next ihRun => runDialogue_tail next ihRun
      (stepDialogue_all halloc hnomload next)) h

theorem evalDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : FunctionEvaluation frame decoder policy ctx function globals args trace globals' outcome) :
    EvalDialogue decoder policy ctx function globals args trace globals' outcome := by
  cases h with
  | exit hentry hrun hexit =>
      exact evalDialogue_exit hentry hexit
        (runDialogue_all halloc hnomload hrun)

theorem Steps.confluence_or_queryDivergence
    {frame : OperandFrame} {decoder : Decoder frame} {policy : MemoryPolicy}
    {ctx : CallContext} (halloc : policy.Deterministic ∨ decoder.NoMalloc)
    (hnomload : decoder.NoMload)
    {state final₁ final₂ : State frame} {trace₁ trace₂ : Trace}
    (h₁ : Steps frame decoder policy ctx state trace₁ final₁)
    (h₂ : Steps frame decoder policy ctx state trace₂ final₂) :
    (∃ suffix, Steps frame decoder policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Steps frame decoder policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  runDialogue_all halloc hnomload h₁ trace₂ final₂ h₂

end Proofs

end Sir.Machine
