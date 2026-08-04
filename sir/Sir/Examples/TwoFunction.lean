import Sir.Theorems

namespace Sir

def witnessMainBlock : BlockId := ⟨0⟩
def witnessAddBlock : BlockId := ⟨0⟩
def witnessMain : FunctionId := ⟨0⟩
def witnessAdd2 : FunctionId := ⟨1⟩

def witnessA : VarId := ⟨0⟩
def witnessB : VarId := ⟨1⟩
def witnessR : VarId := ⟨2⟩
def witnessX : VarId := ⟨3⟩
def witnessY : VarId := ⟨4⟩
def witnessZ : VarId := ⟨5⟩

def witnessAddProgram : Program :=
  { functions := #[
      { blocks := #[{
          inputs := #[]
          statements := #[
            .assign witnessA (.constant 2),
            .assign witnessB (.constant 3),
            .icall witnessAdd2 #[witnessA, witnessB] #[witnessR]
          ]
          terminator := .halt
          outputs := #[] }]
        entry := witnessMainBlock },
      { blocks := #[{
          inputs := #[witnessX, witnessY]
          statements := #[.assign witnessZ (.add witnessX witnessY)]
          terminator := .iret
          outputs := #[witnessZ] }]
        entry := witnessAddBlock }
    ]
    initEntry := witnessMain
    mainEntry := none }

private theorem witness_callEdge_iff (caller callee : FunctionId) :
    witnessAddProgram.callEdge caller callee ↔ caller = witnessMain ∧ callee = witnessAdd2 := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt, witnessAddProgram,
      witnessAdd2, witnessMain]

private theorem witness_acyclicCalls (f : FunctionId) :
    ¬ Relation.TransGen witnessAddProgram.callEdge f f := by
  intro hcycle
  have endpoints {caller callee : FunctionId}
      (h : Relation.TransGen witnessAddProgram.callEdge caller callee) :
      caller = witnessMain ∧ callee = witnessAdd2 := by
    induction h with
    | single hEdge => exact witness_callEdge_iff _ _ |>.mp hEdge
    | tail _ hEdge ih =>
      rcases ih with ⟨_, hcallee⟩
      rcases witness_callEdge_iff _ _ |>.mp hEdge with ⟨hcaller, _⟩
      have := congrArg FunctionId.id (hcallee.symm.trans hcaller)
      simp [witnessAdd2, witnessMain] at this
  rcases endpoints hcycle with ⟨hf, hf'⟩
  have := congrArg FunctionId.id (hf.symm.trans hf')
  simp [witnessAdd2, witnessMain] at this

theorem witnessAddProgram_wellFormed : witnessAddProgram.WellFormed := by
  constructor
  · rintro callee args dests h
    rcases callee with ⟨callee⟩
    simp [Program.HasStmt, Function.HasStmt, witnessAddProgram, witnessAdd2] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨_, Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩, rfl⟩
  · intro fn hfn block hblock hterm
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl <;> simp at hblock <;> subst hblock <;>
      simp [Function.outputs?] at hterm ⊢
  · exact witness_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro e he
      simp [witnessAddProgram] at he
  · intro fn hfn block hblock target htarget
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl <;>
      · simp at hblock
        subst block
        simp [Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | _ | _ | index) <;> simp at hstatement
        all_goals subst statement
        all_goals simp [BasicBlock.variablesDefinedBefore, Expr.variablesRead,
          Stmt.variablesRead, Stmt.variablesDefined, witnessA, witnessB]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead]
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [BasicBlock.variablesDefinedBefore, Expr.variablesRead,
          Stmt.variablesRead, witnessX]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead,
          Stmt.variablesDefined, witnessX, witnessY, witnessZ]

theorem witnessAddProgram_add2_deterministic :
    witnessAddProgram.FunctionDeterministic witnessAdd2 := by
  apply Program.functionDeterministic_of_memOracleFree
  rintro s hstmt
  simp [Program.HasStmt, Function.HasStmt, witnessAddProgram] at hstmt
  rcases hstmt with (rfl | rfl | rfl) | rfl <;> simp [Stmt.isMemOracle]

private theorem witness_evalFn_add2 (ctx : CallContext) (w : World) :
    Generic.GenEvalFn localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      witnessAdd2 { world := w } #[2, 3] [] ({ world := w } : Globals)
        (.returned #[5]) := by
  let initial : MachineState :=
    { globals := { world := w }
      locals := (Locals.empty.assign witnessX 2).assign witnessY 3
      control := .running
        { fn := witnessAdd2, block := witnessAddBlock, position := .statement 0 } }
  let afterAdd : MachineState :=
    { globals := { world := w }
      locals := ((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5
      control := .running
        { fn := witnessAdd2, block := witnessAddBlock, position := .terminator } }
  let final : MachineState := { afterAdd with control := .returned #[5] }
  have hentry : witnessAddProgram.callState? witnessAdd2 { world := w } #[2, 3] =
      some initial := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, (Locals.empty.assign witnessX 2).assign witnessY 3,
      rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hfetch : #[witnessX, witnessY].mapM
      (((Locals.empty.assign witnessX 2).assign witnessY 3).lookup ·) = .ok #[2, 3] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstore : Locals.bindValues
      ((Locals.empty.assign witnessX 2).assign witnessY 3) #[witnessZ] #[5] =
      .ok (((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5) := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have hadd : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      initial.gen [] afterAdd.gen := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [decodeExpr, Generic.Instr.Fires]
    exact fires_of hfetch (by trivial)
      (Generic.Operation.execute_add_ok ctx 2 3 ({ world := w } : Globals)) hstore
  have houtputs : #[witnessZ].mapM
      ((((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5).lookup ·) =
      .ok #[5] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hreturn : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      afterAdd.gen [] final.gen :=
    step_terminator rfl (eval_terminator_iret_ok rfl rfl houtputs)
  exact EvalFn.returned hentry
    (Generic.GenSteps.tail (Generic.GenSteps.single hadd) hreturn) rfl

private theorem witnessAddProgram_eval (ctx : CallContext) (w : World) :
    Generic.GenEvalFn localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      witnessMain { world := w } #[] [] ({ world := w } : Globals) .halted := by
  let initial : MachineState :=
    { globals := { world := w }
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 0 } }
  let state₁ : MachineState :=
    { globals := { world := w }
      locals := Locals.empty.assign witnessA 2
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 1 } }
  let state₂ : MachineState :=
    { globals := { world := w }
      locals := (Locals.empty.assign witnessA 2).assign witnessB 3
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 2 } }
  let state₃ : MachineState :=
    { globals := { world := w }
      locals := ((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .terminator } }
  let final : MachineState := { state₃ with control := .halted }
  have hentry : witnessAddProgram.callState? witnessMain { world := w } #[] = some initial := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hfetchEmpty (locals : Locals) :
      (#[] : Array VarId).mapM (locals.lookup ·) = .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreA : Locals.bindValues Locals.empty #[witnessA] #[2] =
      .ok (Locals.empty.assign witnessA 2) := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have hstep₁ : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      initial.gen [] state₁.gen := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [decodeExpr, Generic.Instr.Fires]
    exact fires_of (hfetchEmpty Locals.empty) (by trivial)
      (Generic.Operation.execute_constant_ok ctx 2 ({ world := w } : Globals) #[]) hstoreA
  have hstoreB : Locals.bindValues (Locals.empty.assign witnessA 2) #[witnessB] #[3] =
      .ok ((Locals.empty.assign witnessA 2).assign witnessB 3) := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have hstep₂ : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      state₁.gen [] state₂.gen := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [decodeExpr, Generic.Instr.Fires]
    exact fires_of (hfetchEmpty (Locals.empty.assign witnessA 2)) (by trivial)
      (Generic.Operation.execute_constant_ok ctx 3 ({ world := w } : Globals) #[]) hstoreB
  have hargs : #[witnessA, witnessB].mapM
      (((Locals.empty.assign witnessA 2).assign witnessB 3).lookup ·) = .ok #[2, 3] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hbind : Locals.bindReturns ((Locals.empty.assign witnessA 2).assign witnessB 3)
      #[witnessR] #[5] =
      .ok (((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5) := by
    simp only [Locals.bindReturns, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hstep₃ : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      state₂.gen [] state₃.gen :=
    step_icall rfl hargs (witness_evalFn_add2 ctx w) hbind
  have hstep₄ : Generic.GenStep localsFrame (sirDecoder witnessAddProgram) sirPolicy ctx
      state₃.gen [] final.gen := step_terminator rfl rfl
  exact EvalFn.halted hentry
    (.tail (.tail (.tail (Generic.GenSteps.single hstep₁) hstep₂) hstep₃) hstep₄) rfl

theorem witnessAddProgram_runs (ctx : CallContext) (w : World) :
    witnessAddProgram.RunsInit ctx w [] ({ world := w } : Globals) :=
  witnessAddProgram_eval ctx w

end Sir
