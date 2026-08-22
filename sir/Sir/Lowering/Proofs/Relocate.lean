import Sir.Lowering.Proofs.Headline

namespace Sir.Lowering

open Machine

def relabelTo (function : FunctionId) : MachineControl → MachineControl
  | .running cursor => .running { cursor with fn := function }
  | control => control

def relabelState {frame : OperandFrame} (function : FunctionId) (state : State frame) :
    State frame :=
  { state with control := relabelTo function state.control }

def AtFunction (function : FunctionId) : MachineControl → Prop
  | .running cursor => cursor.fn = function
  | _ => True

theorem relabelTo_toControl (function : FunctionId) (outcome : FunctionOutcome) :
    relabelTo function outcome.toControl = outcome.toControl := by
  cases outcome <;> rfl

structure Relocation {frame : OperandFrame} (source target : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) (a b : FunctionId) : Prop where
  decode : ∀ cursor instruction next, cursor.fn = a →
    source.decode (.running cursor) = some (instruction, next) →
    target.decode (.running { cursor with fn := b }) = some (instruction, relabelTo b next)
  control : ∀ env globals cursor trace env' globals' next, cursor.fn = a →
    source.control env globals (.running cursor) = some (trace, env', globals', next) →
    target.control env globals (.running { cursor with fn := b }) =
      some (trace, env', globals', relabelTo b next)
  noCall : ∀ cursor callee src dst next, cursor.fn = a →
    source.decode (.running cursor) ≠ some (⟨.icall callee, src, dst⟩, next)
  preserves : ∀ state trace final, Step frame source policy ctx state trace final →
    AtFunction a state.control → AtFunction a final.control
  entry : ∀ globals args state, source.entry a globals args = some state →
    target.entry b globals args = some (relabelState b state) ∧ AtFunction a state.control

section

variable {frame : OperandFrame} {source target : Decoder frame} {policy : MemoryPolicy}
  {ctx : CallContext} {a b : FunctionId}

theorem Relocation.step (relocation : Relocation source target policy ctx a b)
    {state final : State frame} {trace : Trace}
    (step : Step frame source policy ctx state trace final)
    (located : AtFunction a state.control) :
    Step frame target policy ctx (relabelState b state) trace (relabelState b final) := by
  cases hcontrol : state.control with
  | halted => exact absurd step (Machine.stuck_of_exit (outcome := .halted) hcontrol _ _)
  | returned results =>
      exact absurd step (Machine.stuck_of_exit (outcome := .returned results) hcontrol _ _)
  | running cursor =>
      rw [hcontrol] at located
      have relabelled : (relabelState b state).control = .running { cursor with fn := b } := by
        simp [relabelState, hcontrol, relabelTo]
      cases step with
      | operation hdecode hfires =>
          rw [hcontrol] at hdecode
          refine Step.operation (state := relabelState b state) ?_ hfires
          rw [relabelled]
          exact relocation.decode cursor _ _ located hdecode
      | operationHalted hdecode hfires =>
          rw [hcontrol] at hdecode
          exact Step.operationHalted (state := relabelState b state)
            (relabelled ▸ relocation.decode cursor _ _ located hdecode) hfires
      | internalCall hdecode hfetch hcallee hresume =>
          rw [hcontrol] at hdecode
          exact absurd hdecode (relocation.noCall cursor _ _ _ _ located)
      | control hstep =>
          rw [hcontrol] at hstep
          refine Step.control (state := relabelState b state) ?_
          rw [relabelled]
          exact relocation.control _ _ cursor _ _ _ _ located hstep

theorem Relocation.steps (relocation : Relocation source target policy ctx a b)
    {state final : State frame} {trace : Trace}
    (steps : Steps frame source policy ctx state trace final)
    (located : AtFunction a state.control) :
    Steps frame target policy ctx (relabelState b state) trace (relabelState b final) ∧
      AtFunction a final.control := by
  refine Steps.inductionOn
    (motive := fun state trace final _ => AtFunction a state.control →
      Steps frame target policy ctx (relabelState b state) trace (relabelState b final) ∧
        AtFunction a final.control)
    (fun _ located => ⟨.refl, located⟩)
    (fun start next ih located => by
      obtain ⟨steps, middleLocated⟩ := ih located
      exact ⟨steps.tail (relocation.step next middleLocated),
        relocation.preserves _ _ _ next middleLocated⟩)
    steps located

theorem Relocation.evaluation (relocation : Relocation source target policy ctx a b)
    {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : FunctionEvaluation frame source policy ctx a globals args trace
      finalGlobals outcome) :
    FunctionEvaluation frame target policy ctx b globals args trace finalGlobals outcome := by
  cases evaluation with
  | exit hentry hrun hexit =>
      rename_i initial exit
      obtain ⟨targetEntry, located⟩ := relocation.entry _ _ _ hentry
      obtain ⟨targetRun, _⟩ := relocation.steps hrun located
      have relabelledExit : (relabelState b exit).control = outcome.toControl := by
        simp [relabelState, hexit, relabelTo_toControl]
      exact FunctionEvaluation.exit (exit := relabelState b exit) targetEntry targetRun
        relabelledExit

end

end Sir.Lowering
