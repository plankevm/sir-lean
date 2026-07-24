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
        entry := witnessMainBlock
        outputs := none },
      { blocks := #[{
          inputs := #[witnessX, witnessY]
          statements := #[.assign witnessZ (.add witnessX witnessY)]
          terminator := .iret
          outputs := #[witnessZ] }]
        entry := witnessAddBlock
        outputs := some 1 }
    ]
    initEntry := witnessMain
    mainEntry := none }

private theorem witness_callEdge_iff (callee caller : FunctionId) :
    witnessAddProgram.callEdge callee caller ↔ callee = witnessAdd2 ∧ caller = witnessMain := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt, witnessAddProgram,
      witnessAdd2, witnessMain]

private theorem witness_acyclicCalls (f : FunctionId) :
    ¬ Relation.TransGen witnessAddProgram.callEdge f f := by
  intro hcycle
  have endpoints {callee caller : FunctionId}
      (h : Relation.TransGen witnessAddProgram.callEdge callee caller) :
      callee = witnessAdd2 ∧ caller = witnessMain := by
    induction h with
    | single hEdge => exact witness_callEdge_iff _ _ |>.mp hEdge
    | tail _ hEdge ih =>
      rcases ih with ⟨_, hcaller⟩
      rcases witness_callEdge_iff _ _ |>.mp hEdge with ⟨hcallee, _⟩
      have := congrArg FunctionId.id (hcaller.symm.trans hcallee)
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
    exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
  · rintro ⟨_ | _ | f⟩ fn hfn
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, witnessAddProgram] at hfn
  · exact witness_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro e he
      simp [witnessAddProgram] at he
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock target htarget
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      simp at hblock
      subst block
      simp [Terminator.jumpTargets] at htarget
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      simp at hblock
      subst block
      simp [Terminator.jumpTargets] at htarget
    · simp [Program.function?, witnessAddProgram] at hfn
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | _ | _ | index) <;> simp at hstatement
        all_goals subst statement
        all_goals simp [BasicBlock.variablesDefinedBefore, Expr.variablesRead,
          Stmt.variablesRead, Stmt.variablesDefined, witnessA, witnessB]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead]
    · simp [Program.function?, witnessAddProgram] at hfn
      subst fn
      simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [BasicBlock.variablesDefinedBefore, Expr.variablesRead,
          Stmt.variablesRead, witnessX]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead,
          Stmt.variablesDefined, witnessX, witnessY, witnessZ]
    · simp [Program.function?, witnessAddProgram] at hfn

theorem witnessAddProgram_add2_deterministic :
    witnessAddProgram.FunctionDeterministic witnessAdd2 := by
  apply Program.functionDeterministic_of_memOracleFree
  rintro s hstmt
  simp [Program.HasStmt, Function.HasStmt, witnessAddProgram] at hstmt
  rcases hstmt with (rfl | rfl | rfl) | rfl <;> simp [Stmt.isMemOracle]

private theorem witness_evalFn_add2 (ctx : CallContext) (w : World) :
    EvalFn witnessAddProgram ctx witnessAdd2 { world := w } #[2, 3] []
      ({ world := w } : Globals) (.returned #[5]) := by
  refine EvalFn.returned
    (s₀ := { globals := { world := w },
               locals := (Locals.empty.assign witnessX 2).assign witnessY 3,
               control := .running
                 { fn := witnessAdd2, block := witnessAddBlock, position := .statement 0 } })
    (exit := { globals := { world := w },
               locals := ((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5,
               control := .returned #[5] })
    ?hentry ?hrun ?hret
  case hentry =>
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, (Locals.empty.assign witnessX 2).assign witnessY 3,
      rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  case hrun =>
    have step := SmallStep.assign (program := witnessAddProgram) (ctx := ctx)
      (state := { globals := { world := w },
                  locals := (Locals.empty.assign witnessX 2).assign witnessY 3,
                  control := .running
                    { fn := witnessAdd2, block := witnessAddBlock, position := .statement 0 } })
      (hstmt := rfl) (heval := rfl)
    have houtputs : #[witnessZ].mapM
        ((((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5).lookup ·) =
        .ok #[5] := by
      rw [Array.mapM_eq_mapM_toList]
      rfl
    have ret := SmallStep.terminator (program := witnessAddProgram) (ctx := ctx)
      (state := { globals := { world := w },
                  locals := ((Locals.empty.assign witnessX 2).assign witnessY 3).assign witnessZ 5,
                  control := .running
                    { fn := witnessAdd2, block := witnessAddBlock, position := .terminator } })
      (hterm := rfl) (heval := eval_terminator_iret_ok rfl rfl houtputs)
    exact (Steps.single step).tail ret
  case hret =>
    rfl

theorem witnessAddProgram_runs (ctx : CallContext) (w : World) :
    witnessAddProgram.RunsInit ctx w [] ({ world := w } : Globals) := by
  let initial : MachineState :=
    { globals := { world := w }
      control := .running
        { fn := witnessMain, block := witnessMainBlock, position := .statement 0 } }
  let final : MachineState :=
    { globals := { world := w }
      locals := ((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5
      control := .halted }
  refine EvalFn.halted (s₀ := initial) (exit := final) ?_ ?_ rfl
  · apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have step₁ := SmallStep.assign (program := witnessAddProgram) (ctx := ctx)
    (state := { globals := { world := w },
                locals := .empty,
                control := .running
                  { fn := witnessMain, block := witnessMainBlock, position := .statement 0 } })
    (hstmt := rfl) (heval := rfl)
  have step₂ := SmallStep.assign (program := witnessAddProgram) (ctx := ctx)
    (state := { globals := { world := w },
                locals := Locals.empty.assign witnessA 2,
                control := .running
                  { fn := witnessMain, block := witnessMainBlock, position := .statement 1 } })
    (hstmt := rfl) (heval := rfl)
  have hargs : #[witnessA, witnessB].mapM
      (((Locals.empty.assign witnessA 2).assign witnessB 3).lookup ·) = .ok #[2, 3] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hbind : Locals.bindReturns ((Locals.empty.assign witnessA 2).assign witnessB 3)
      #[witnessR] #[5] =
      .ok (((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5) := by
    simp only [Locals.bindReturns, Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have step₃ := SmallStep.icall (program := witnessAddProgram) (ctx := ctx)
    (state := { globals := { world := w },
                locals := (Locals.empty.assign witnessA 2).assign witnessB 3,
                control := .running
                  { fn := witnessMain, block := witnessMainBlock, position := .statement 2 } })
    (hstmt := rfl) (hargs := hargs) (hcallee := witness_evalFn_add2 ctx w) (hbind := hbind)
  have step₄ := SmallStep.terminator (program := witnessAddProgram) (ctx := ctx)
    (state := { globals := { world := w },
                locals := ((Locals.empty.assign witnessA 2).assign witnessB 3).assign witnessR 5,
                control := .running
                  { fn := witnessMain, block := witnessMainBlock, position := .terminator } })
    (hterm := rfl) (heval := rfl)
  exact Steps.tail (Steps.tail (Steps.tail (Steps.single step₁) step₂) step₃) step₄

end Sir
