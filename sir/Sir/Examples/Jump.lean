import Sir.Theorems

namespace Sir.Examples

def jumpTargetBlock : BlockId := ⟨1⟩
def jumpDefined : VarId := ⟨0⟩
def jumpParameter : VarId := ⟨1⟩
def jumpDoubled : VarId := ⟨2⟩

def jumpProgram : Vars.Program :=
  { init :=
      { entry :=
          { inputs := #[]
            statements := #[.assign jumpDefined (.constant 7)]
            terminator := .jump jumpTargetBlock
            outputs := #[jumpDefined] }
        rest := #[
          { inputs := #[jumpParameter]
            statements := #[.assign jumpDoubled (.add jumpParameter jumpParameter)]
            terminator := .halt
            outputs := #[] }] }
    main := none
    rest := #[] }

private theorem jump_no_callEdge (caller callee : FunctionId) :
    ¬ jumpProgram.callEdge caller callee := by
  rcases caller with ⟨_ | caller⟩ <;>
    simp [Vars.Program.callEdge, Vars.Program.function?, Vars.Program.functions,
      Vars.Function.HasStmt, jumpProgram]

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
    simp [Vars.Program.HasStmt, Vars.Function.HasStmt, jumpProgram] at hstatement
  · intro fn hfn block hblock hterm
    simp [jumpProgram] at hfn
    subst hfn
    simp at hblock
    rcases hblock with rfl | rfl <;> simp at hterm
  · exact jump_acyclicCalls
  · refine ⟨⟨rfl, rfl⟩, ?_⟩
    intro m hmain
    simp [jumpProgram] at hmain
  · intro fn hfn block hblock target htarget
    simp [jumpProgram] at hfn
    subst hfn
    simp at hblock
    rcases hblock with rfl | rfl
    · simp [Vars.Terminator.jumpTargets] at htarget
      subst htarget
      exact ⟨_, rfl, rfl⟩
    · simp [Vars.Terminator.jumpTargets] at htarget
  · intro fn hfn block hblock
    simp [jumpProgram] at hfn
    subst hfn
    simp at hblock
    rcases hblock with rfl | rfl
    · constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead]
      · simp [Vars.Block.variablesDefinedBefore, Vars.Terminator.variablesRead,
          Vars.Stmt.variablesDefined]
    · constructor
      · intro index statement hstatement
        rcases index with (_ | index) <;> simp at hstatement
        subst statement
        simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead,
          Vars.Block.variablesDefinedBefore]
      · simp [Vars.Terminator.variablesRead]

end Sir.Examples
