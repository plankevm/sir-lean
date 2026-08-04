import Sir.Theorems

namespace Sir.Examples

def haltedCallCallerBlock : BlockId := ⟨0⟩
def haltedCallCalleeBlock : BlockId := ⟨0⟩
def haltedCallCaller : FunctionId := ⟨0⟩
def haltedCallCallee : FunctionId := ⟨1⟩

def haltedCallProgram : Program :=
  { functions := #[
      { blocks := #[{
          inputs := #[]
          statements := #[.icall haltedCallCallee #[] #[]]
          terminator := .halt
          outputs := #[] }]
        entry := haltedCallCallerBlock },
      { blocks := #[{
          inputs := #[]
          statements := #[]
          terminator := .halt
          outputs := #[] }]
        entry := haltedCallCalleeBlock }
    ]
    initEntry := haltedCallCaller
    mainEntry := none }

private theorem haltedCall_callEdge_iff (caller callee : FunctionId) :
    haltedCallProgram.callEdge caller callee ↔
      caller = haltedCallCaller ∧ callee = haltedCallCallee := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt,
      haltedCallProgram, haltedCallCallee, haltedCallCaller]

private theorem haltedCall_acyclicCalls (function : FunctionId) :
    ¬ Relation.TransGen haltedCallProgram.callEdge function function := by
  intro cycle
  have endpoints {caller callee : FunctionId}
      (h : Relation.TransGen haltedCallProgram.callEdge caller callee) :
      caller = haltedCallCaller ∧ callee = haltedCallCallee := by
    induction h with
    | single edge => exact haltedCall_callEdge_iff _ _ |>.mp edge
    | tail _ edge ih =>
      rcases ih with ⟨_, calleeEq⟩
      rcases haltedCall_callEdge_iff _ _ |>.mp edge with ⟨callerEq, _⟩
      have := congrArg FunctionId.id (calleeEq.symm.trans callerEq)
      simp [haltedCallCallee, haltedCallCaller] at this
  rcases endpoints cycle with ⟨first, second⟩
  have := congrArg FunctionId.id (first.symm.trans second)
  simp [haltedCallCallee, haltedCallCaller] at this

theorem haltedCallProgram_wellFormed : haltedCallProgram.WellFormed := by
  constructor
  · rintro callee args dests hstatement
    rcases callee with ⟨callee⟩
    simp [Program.HasStmt, Function.HasStmt, haltedCallProgram,
      haltedCallCallee] at hstatement
    rcases hstatement with ⟨rfl, rfl, rfl⟩
    exact ⟨_, Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩, rfl⟩
  · intro fn hfn block hblock hterm
    simp [haltedCallProgram] at hfn
    rcases hfn with rfl | rfl <;> simp at hblock <;> subst hblock <;> simp at hterm
  · exact haltedCall_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro entry hentry
      simp [haltedCallProgram] at hentry
  · intro fn hfn block hblock target htarget
    simp [haltedCallProgram] at hfn
    rcases hfn with rfl | rfl <;>
      · simp at hblock
        subst block
        simp [Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [haltedCallProgram] at hfn
    rcases hfn with rfl | rfl
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Stmt.variablesRead, BasicBlock.variablesDefinedBefore]
      · simp [Terminator.variablesRead]
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        simp at hstatement
      · simp [Terminator.variablesRead]

private theorem haltedCall_evalCallee (ctx : CallContext) (world : World) :
    Generic.GenEvalFn localsFrame (sirDecoder haltedCallProgram) sirPolicy ctx
      haltedCallCallee { world := world } #[] [] ({ world := world } : Globals) .halted := by
  let initial : MachineState :=
    { globals := { world := world }
      control := .running
        { fn := haltedCallCallee, block := haltedCallCalleeBlock, position := .terminator } }
  let final : MachineState := { globals := { world := world }, control := .halted }
  have hentry : haltedCallProgram.callState? haltedCallCallee { world := world } #[] =
      some initial := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hstep : Generic.GenStep localsFrame (sirDecoder haltedCallProgram) sirPolicy ctx
      initial.gen [] final.gen := step_terminator rfl rfl
  exact EvalFn.halted hentry (Generic.GenSteps.single hstep) rfl

private theorem haltedCallProgram_eval (ctx : CallContext) (world : World) :
    Generic.GenEvalFn localsFrame (sirDecoder haltedCallProgram) sirPolicy ctx
      haltedCallCaller { world := world } #[] [] ({ world := world } : Globals) .halted := by
  let initial : MachineState :=
    { globals := { world := world }
      control := .running
        { fn := haltedCallCaller, block := haltedCallCallerBlock, position := .statement 0 } }
  let final : MachineState := { globals := { world := world }, control := .halted }
  have hentry : haltedCallProgram.callState? haltedCallCaller { world := world } #[] =
      some initial := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hargs : (#[] : Array VarId).mapM (initial.locals.lookup ·) = .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstep : Generic.GenStep localsFrame (sirDecoder haltedCallProgram) sirPolicy ctx
      initial.gen [] final.gen :=
    step_icallHalted rfl hargs (haltedCall_evalCallee ctx world)
  exact EvalFn.halted hentry (Generic.GenSteps.single hstep) rfl

theorem haltedCallProgram_runs (ctx : CallContext) (world : World) :
    EvalFn haltedCallProgram ctx haltedCallProgram.initEntry { world := world } #[] []
      ({ world := world } : Globals) .halted := by
  simpa [haltedCallProgram] using haltedCallProgram_eval ctx world

end Sir.Examples
