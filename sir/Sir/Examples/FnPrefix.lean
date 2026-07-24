import Sir.Theorems

namespace Sir

def prefixEntry : FunctionId := ⟨0⟩
def prefixCallee : FunctionId := ⟨1⟩
def prefixEntryBlock : BlockId := ⟨0⟩
def prefixCalleeBlock : BlockId := ⟨0⟩
def prefixLoopBlock : BlockId := ⟨1⟩
def prefixGasVariable : VarId := ⟨0⟩

def prefixProgram : Program :=
  { functions := #[
      { blocks := #[{
          inputs := #[]
          statements := #[.icall prefixCallee #[] #[]]
          terminator := .halt
          outputs := #[] }]
        entry := prefixEntryBlock
        outputs := none },
      { blocks := #[
          { inputs := #[]
            statements := #[.gas prefixGasVariable]
            terminator := .jump prefixLoopBlock
            outputs := #[prefixGasVariable] },
          { inputs := #[prefixGasVariable]
            statements := #[]
            terminator := .jump prefixLoopBlock
            outputs := #[prefixGasVariable] }]
        entry := prefixCalleeBlock
        outputs := some 0 }]
    initEntry := prefixEntry
    mainEntry := none }

private theorem prefix_callEdge_iff (callee caller : FunctionId) :
    prefixProgram.callEdge callee caller ↔
      callee = prefixCallee ∧ caller = prefixEntry := by
  rcases caller with ⟨_ | _ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt, prefixProgram,
      prefixCallee, prefixEntry]

private theorem prefix_acyclicCalls (function : FunctionId) :
    ¬ Relation.TransGen prefixProgram.callEdge function function := by
  intro hcycle
  have endpoints {callee caller : FunctionId}
      (h : Relation.TransGen prefixProgram.callEdge callee caller) :
      callee = prefixCallee ∧ caller = prefixEntry := by
    induction h with
    | single hEdge => exact prefix_callEdge_iff _ _ |>.mp hEdge
    | tail _ hEdge ih =>
      rcases ih with ⟨_, hcaller⟩
      rcases prefix_callEdge_iff _ _ |>.mp hEdge with ⟨hcallee, _⟩
      have := congrArg FunctionId.id (hcaller.symm.trans hcallee)
      simp [prefixCallee, prefixEntry] at this
  rcases endpoints hcycle with ⟨hfunction, hfunction'⟩
  have := congrArg FunctionId.id (hfunction.symm.trans hfunction')
  simp [prefixCallee, prefixEntry] at this

theorem prefixProgram_wellFormed : prefixProgram.WellFormed := by
  constructor
  · rintro callee args destinations hstmt
    rcases callee with ⟨callee⟩
    simp [Program.HasStmt, Function.HasStmt, prefixProgram, prefixCallee] at hstmt
    rcases hstmt with ⟨rfl, rfl, rfl⟩
    exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
  · rintro ⟨_ | _ | function⟩ fn hfn
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      constructor <;> simp
    · simp [Program.function?, prefixProgram] at hfn
  · exact prefix_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro entry hentry
      simp [prefixProgram] at hentry
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock target htarget
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      simp at hblock
      subst block
      simp [Terminator.jumpTargets] at htarget
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      simp at hblock
      rcases hblock with rfl | rfl
      · simp [Terminator.jumpTargets] at htarget
        subst target
        exact ⟨_, rfl, rfl⟩
      · simp [Terminator.jumpTargets] at htarget
        subst target
        exact ⟨_, rfl, rfl⟩
    · simp [Program.function?, prefixProgram] at hfn
  · rintro ⟨_ | _ | function⟩ fn hfn block hblock
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      simp at hblock
      subst block
      constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [BasicBlock.variablesDefinedBefore, Stmt.variablesRead]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead]
    · simp [Program.function?, prefixProgram] at hfn
      subst fn
      simp at hblock
      rcases hblock with rfl | rfl
      · constructor
        · intro index statement hstatement
          rcases index with (_ | index) <;> simp at hstatement
          subst statement
          simp [BasicBlock.variablesDefinedBefore, Stmt.variablesRead]
        · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead,
            Stmt.variablesDefined]
      · constructor
        · intro index statement hstatement
          simp at hstatement
        · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead]
    · simp [Program.function?, prefixProgram] at hfn

theorem prefixProgram_observes_gas_before_loop
    (ctx : CallContext) (world : World) (gas : Word) :
    prefixProgram.NextObservableEffect ctx prefixEntry world [] .gas := by
  let caller : MachineState :=
    { globals := { world }
      control := .running
        { fn := prefixEntry, block := prefixEntryBlock, position := .statement 0 } }
  let callee : MachineState :=
    { globals := { world }
      control := .running
        { fn := prefixCallee, block := prefixCalleeBlock, position := .statement 0 } }
  let afterGas : MachineState :=
    { globals := { world }
      locals := Locals.empty.assign prefixGasVariable gas
      control := .running
        { fn := prefixCallee, block := prefixCalleeBlock, position := .terminator } }
  have callerEntry :
      prefixProgram.callState? prefixEntry { world } #[] = some caller := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have calleeEntry :
      prefixProgram.callState? prefixCallee { world } #[] = some callee := by
    apply Program.callState?_eq_some_iff.mpr
    refine ⟨_, _, Locals.empty, rfl, rfl, ?_, rfl⟩
    simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have gasStep : SmallStep prefixProgram ctx callee [.gas gas] afterGas :=
    .gas rfl rfl
  have inner : FnPrefix prefixProgram ctx prefixCallee { world } #[] [.gas gas] :=
    .steps calleeEntry (Steps.single gasStep)
  have callArgs : #[].mapM (caller.locals.lookup ·) = .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have outer : FnPrefix prefixProgram ctx prefixEntry { world } #[] [.gas gas] :=
    .descend callerEntry .refl rfl callArgs inner
  exact ⟨gas, [.gas gas], [], outer, by simp⟩

end Sir
