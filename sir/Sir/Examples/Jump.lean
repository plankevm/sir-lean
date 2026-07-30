import Sir.Theorems

namespace Sir.Examples

def jumpSourceBlock : BlockId := ⟨0⟩
def jumpTargetBlock : BlockId := ⟨1⟩
def jumpEntry : FunctionId := ⟨0⟩
def jumpDefined : VarId := ⟨0⟩
def jumpParameter : VarId := ⟨1⟩
def jumpDoubled : VarId := ⟨2⟩

def jumpProgram : Program :=
  { functions := #[
      { blocks := #[
          { inputs := #[]
            statements := #[.assign jumpDefined (.constant 7)]
            terminator := .jump jumpTargetBlock
            outputs := #[jumpDefined] },
          { inputs := #[jumpParameter]
            statements := #[.assign jumpDoubled (.add jumpParameter jumpParameter)]
            terminator := .halt
            outputs := #[] }]
        entry := jumpSourceBlock
        outputs := none }]
    initEntry := jumpEntry
    mainEntry := none }

private theorem jump_no_callEdge (caller callee : FunctionId) :
    ¬ jumpProgram.callEdge caller callee := by
  rcases caller with ⟨_ | caller⟩ <;>
    simp [Program.callEdge, Program.function?, Function.HasStmt, jumpProgram]

private theorem jump_acyclicCalls (function : FunctionId) :
    ¬ Relation.TransGen jumpProgram.callEdge function function := by
  have absurd {caller callee : FunctionId}
      (h : Relation.TransGen jumpProgram.callEdge caller callee) : False := by
    induction h with
    | single edge => exact jump_no_callEdge _ _ edge
    | tail _ edge _ => exact jump_no_callEdge _ _ edge
  exact absurd

theorem jumpProgram_wellFormed : jumpProgram.WellFormed := by
  constructor
  · rintro callee args dests hstatement
    simp [Program.HasStmt, Function.HasStmt, jumpProgram] at hstatement
  · intro fn hfn
    simp [jumpProgram] at hfn
    subst hfn
    constructor <;> simp
  · exact jump_acyclicCalls
  · constructor
    · exact Program.functionInputOutputArity_iff.mpr ⟨_, rfl, rfl, rfl⟩
    · intro entry hentry
      simp [jumpProgram] at hentry
  · intro fn hfn block hblock target htarget
    simp [jumpProgram] at hfn
    subst hfn
    simp at hblock
    rcases hblock with rfl | rfl
    · simp [Terminator.jumpTargets] at htarget
      subst htarget
      exact ⟨_, rfl, rfl⟩
    · simp [Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [jumpProgram] at hfn
    subst hfn
    simp at hblock
    rcases hblock with rfl | rfl
    · constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Stmt.variablesRead, Expr.variablesRead]
      · simp [BasicBlock.variablesDefinedBefore, Terminator.variablesRead,
          Stmt.variablesDefined]
    · constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Stmt.variablesRead, Expr.variablesRead,
          BasicBlock.variablesDefinedBefore]
      · simp [Terminator.variablesRead]

end Sir.Examples
