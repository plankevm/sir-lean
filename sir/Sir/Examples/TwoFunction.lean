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

def witnessAddProgram : Vars.Program :=
  { functions := #[
      { entry := {
          inputs := #[]
          statements := #[
            .assign witnessA (.constant 2),
            .assign witnessB (.constant 3),
            .icall witnessAdd2 #[witnessA, witnessB] #[witnessR]
          ]
          terminator := .halt
          outputs := #[] }
        rest := #[] },
      { entry := {
          inputs := #[witnessX, witnessY]
          statements := #[.assign witnessZ (.add witnessX witnessY)]
          terminator := .iret
          outputs := #[witnessZ] }
        rest := #[] }
    ]
    initEntry := witnessMain
    mainEntry := none }

private theorem witness_callEdge_iff (caller callee : FunctionId) :
    witnessAddProgram.callEdge caller callee ↔ caller = witnessMain ∧ callee = witnessAdd2 := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Vars.Program.callEdge, Vars.Program.function?, Vars.Function.HasStmt, witnessAddProgram,
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
    simp [Vars.Program.HasStmt, Vars.Function.HasStmt, witnessAddProgram, witnessAdd2] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨_, Vars.Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩, rfl⟩
  · intro fn hfn block hblock hterm
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl <;> simp at hblock <;> subst hblock <;>
      simp [Vars.Function.outputs?, Vars.Function.blocks] at hterm ⊢
  · exact witness_acyclicCalls
  · constructor
    · exact Vars.Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro e he
      simp [witnessAddProgram] at he
  · intro fn hfn block hblock target htarget
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl <;>
      · simp at hblock
        subst block
        simp [Vars.Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [witnessAddProgram] at hfn
    rcases hfn with rfl | rfl
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | _ | _ | index) <;> simp at hstatement
        all_goals subst statement
        all_goals simp [Vars.Block.variablesDefinedBefore, Vars.Expr.variablesRead,
          Vars.Stmt.variablesRead, Vars.Stmt.variablesDefined, witnessA, witnessB]
      · simp [Vars.Block.variablesDefinedBefore, Vars.Terminator.variablesRead]
    · simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Vars.Block.variablesDefinedBefore, Vars.Expr.variablesRead,
          Vars.Stmt.variablesRead, witnessX]
      · simp [Vars.Block.variablesDefinedBefore, Vars.Terminator.variablesRead,
          Vars.Stmt.variablesDefined, witnessX, witnessY, witnessZ]

theorem witnessAddProgram_add2_deterministic :
    witnessAddProgram.FunctionDeterministic witnessAdd2 := by
  apply Vars.Program.functionDeterministic_of_memOracleFree
  rintro s hstmt
  simp [Vars.Program.HasStmt, Vars.Function.HasStmt, witnessAddProgram] at hstmt
  rcases hstmt with (rfl | rfl | rfl) | rfl <;> simp [Vars.Stmt.isMemOracle]

private theorem witness_evalFn_add2 (ctx : CallContext) (w : World) :
    Vars.EvalFn witnessAddProgram ctx
      witnessAdd2 { world := w } #[2, 3] [] ({ world := w } : Globals)
        (.returned #[5]) := by
  let initial : Vars.State :=
    { globals := { world := w }
      environment := (Locals.empty.assign witnessX 2).assign witnessY 3
      control := .running
        { fn := witnessAdd2, block := witnessAddBlock, position := .statement 0 } }
  let afterAdd : Vars.State :=
    { globals := { world := w }
      environment := ((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5
      control := .running
        { fn := witnessAdd2, block := witnessAddBlock, position := .terminator } }
  let final : Vars.State := { afterAdd with control := .returned #[5] }
  have hentry : witnessAddProgram.callState? witnessAdd2 { world := w } #[2, 3] =
      some initial := by
    apply Vars.Program.callState?_eq_some_iff.mpr
    refine ⟨_, (Locals.empty.assign witnessX 2).assign witnessY 3, rfl, ?_, rfl⟩
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
  have hadd : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      initial [] afterAdd := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [Vars.decodeExpression, Machine.Instruction.Fires]
    exact fires_of hfetch (by trivial)
      (Machine.Operation.execute_add_ok ctx 2 3 ({ world := w } : Globals)) hstore
  have houtputs : #[witnessZ].mapM
      ((((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5).lookup ·) =
      .ok #[5] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hreturn : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      afterAdd [] final :=
    step_terminator rfl (Vars.evaluateTerminator_iret_ok rfl rfl houtputs)
  exact Vars.EvalFn.returned hentry
    (Machine.Steps.tail (Machine.Steps.single hadd) hreturn) rfl

private theorem witnessAddProgram_eval (ctx : CallContext) (w : World) :
    Vars.EvalFn witnessAddProgram ctx
      witnessMain { world := w } #[] [] ({ world := w } : Globals) .halted := by
  let initial : Vars.State :=
    { globals := { world := w }
      environment := .empty
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 0 } }
  let state₁ : Vars.State :=
    { globals := { world := w }
      environment := Locals.empty.assign witnessA 2
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 1 } }
  let state₂ : Vars.State :=
    { globals := { world := w }
      environment := (Locals.empty.assign witnessA 2).assign witnessB 3
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 2 } }
  let state₃ : Vars.State :=
    { globals := { world := w }
      environment := ((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .terminator } }
  let final : Vars.State := { state₃ with control := .halted }
  have hentry : witnessAddProgram.callState? witnessMain { world := w } #[] = some initial := by
    apply Vars.Program.callState?_eq_some_iff.mpr
    refine ⟨_, Locals.empty, rfl, ?_, rfl⟩
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
  have hstep₁ : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      initial [] state₁ := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [Vars.decodeExpression, Machine.Instruction.Fires]
    exact fires_of (hfetchEmpty Locals.empty) (by trivial)
      (Machine.Operation.execute_constant_ok ctx 2 ({ world := w } : Globals) #[]) hstoreA
  have hstoreB : Locals.bindValues (Locals.empty.assign witnessA 2) #[witnessB] #[3] =
      .ok ((Locals.empty.assign witnessA 2).assign witnessB 3) := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have hstep₂ : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      state₁ [] state₂ := by
    apply step_assign (program := witnessAddProgram) (ctx := ctx) rfl
    simp only [Vars.decodeExpression, Machine.Instruction.Fires]
    exact fires_of (hfetchEmpty (Locals.empty.assign witnessA 2)) (by trivial)
      (Machine.Operation.execute_constant_ok ctx 3 ({ world := w } : Globals) #[]) hstoreB
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
  have hstep₃ : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      state₂ [] state₃ :=
    step_icall rfl hargs (witness_evalFn_add2 ctx w) hbind
  have hstep₄ : Machine.Step Vars.frame (Vars.decoder witnessAddProgram) Machine.memoryPolicy ctx
      state₃ [] final := step_terminator rfl rfl
  exact Vars.EvalFn.halted hentry
    (.tail (.tail (.tail (Machine.Steps.single hstep₁) hstep₂) hstep₃) hstep₄) rfl

theorem witnessAddProgram_runs (ctx : CallContext) (w : World) :
    Vars.EvalFn witnessAddProgram ctx witnessAddProgram.initEntry { world := w } #[] []
      ({ world := w } : Globals) .halted := by
  simpa [witnessAddProgram] using witnessAddProgram_eval ctx w

end Sir
