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
        entry := haltedCallCallerBlock
        outputs := none },
      { blocks := #[{
          inputs := #[]
          statements := #[]
          terminator := .halt
          outputs := #[] }]
        entry := haltedCallCalleeBlock
        outputs := some 0 }
    ]
    initEntry := haltedCallCaller
    mainEntry := none }

private theorem haltedCall_callEdge_iff (callee caller : FunctionId) :
    haltedCallProgram.callEdge callee caller ↔
      callee = haltedCallCallee ∧ caller = haltedCallCaller := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt,
      haltedCallProgram, haltedCallCallee, haltedCallCaller]

private theorem haltedCall_acyclicCalls (function : FunctionId) :
    ¬ Relation.TransGen haltedCallProgram.callEdge function function := by
  intro cycle
  have endpoints {callee caller : FunctionId}
      (h : Relation.TransGen haltedCallProgram.callEdge callee caller) :
      callee = haltedCallCallee ∧ caller = haltedCallCaller := by
    induction h with
    | single edge => exact haltedCall_callEdge_iff _ _ |>.mp edge
    | tail _ edge ih =>
      rcases ih with ⟨_, callerEq⟩
      rcases haltedCall_callEdge_iff _ _ |>.mp edge with ⟨calleeEq, _⟩
      have := congrArg FunctionId.id (callerEq.symm.trans calleeEq)
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
    exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
  · rintro ⟨_ | _ | function⟩ fn hfn
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, haltedCallProgram] at hfn
  · exact haltedCall_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro entry hentry
      simp [haltedCallProgram] at hentry
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock target htarget
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      simp at hblock
      subst block
      simp [Terminator.jumpTargets] at htarget
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      simp at hblock
      subst block
      simp [Terminator.jumpTargets] at htarget
    · simp [Program.function?, haltedCallProgram] at hfn
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Stmt.variablesRead, BasicBlock.variablesDefinedBefore]
      · simp [Terminator.variablesRead]
    · simp [Program.function?, haltedCallProgram] at hfn
      subst fn
      simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        simp at hstatement
      · simp [Terminator.variablesRead]
    · simp [Program.function?, haltedCallProgram] at hfn

private theorem haltedCall_evalCallee (ctx : CallContext) (world : World) :
    EvalFn haltedCallProgram ctx haltedCallCallee { world := world } #[] []
      ({ world := world } : Globals) .halted := by
  refine EvalFn.halted (s₀ :=
      { globals := { world := world }
        control := .running
          { fn := haltedCallCallee, block := haltedCallCalleeBlock, position := .terminator } })
      (exit := { globals := { world := world }, control := .halted }) ?_ ?_ rfl
  · apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  exact Steps.single (.terminator (program := haltedCallProgram) (ctx := ctx) rfl rfl)

theorem haltedCallProgram_runs (ctx : CallContext) (world : World) :
    haltedCallProgram.RunsInit ctx world [] ({ world := world } : Globals) := by
  let initial : MachineState :=
    { globals := { world := world }
      control := .running
        { fn := haltedCallCaller, block := haltedCallCallerBlock, position := .statement 0 } }
  let final : MachineState := { globals := { world := world }, control := .halted }
  refine EvalFn.halted (s₀ := initial) (exit := final) ?_ (Steps.single ?_) rfl
  · apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hargs : (#[] : Array VarId).mapM
      (initial.locals.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  exact SmallStep.icallHalted (program := haltedCallProgram) (ctx := ctx)
    (state := initial) (hstmt := rfl) (hargs := hargs)
    (hcallee := haltedCall_evalCallee ctx world)

end Sir.Examples
