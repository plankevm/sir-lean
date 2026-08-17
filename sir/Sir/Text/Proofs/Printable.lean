import Sir.Text.Spec.Printable
import Sir.Vars.Proofs.Normalize

namespace Sir.Vars.Text

private theorem Stmt.functionReferencesInRange_renameVariables
    (rename : VarId → VarId) (functionCount : Nat) (statement : Stmt) :
    (statement.renameVariables rename).FunctionReferencesInRange functionCount ↔
      statement.FunctionReferencesInRange functionCount := by
  cases statement <;> simp [Stmt.renameVariables, Stmt.FunctionReferencesInRange]

private theorem Terminator.blockReferencesInRange_renameVariables
    (rename : VarId → VarId) (blockCount : Nat) (terminator : Terminator) :
    (terminator.renameVariables rename).BlockReferencesInRange blockCount ↔
      terminator.BlockReferencesInRange blockCount := by
  cases terminator <;>
    simp [Terminator.renameVariables, Terminator.BlockReferencesInRange]

private theorem Block.referencesInRange_renameVariables
    (rename : VarId → VarId) (functionCount blockCount : Nat) (block : Block) :
    (block.renameVariables rename).ReferencesInRange functionCount blockCount ↔
      block.ReferencesInRange functionCount blockCount := by
  simp [Block.renameVariables, Block.ReferencesInRange,
    Stmt.functionReferencesInRange_renameVariables,
    Terminator.blockReferencesInRange_renameVariables]

private theorem Function.printable_renameVariables
    (rename : VarId → VarId) (functionCount : Nat) (function : Function) :
    (function.renameVariables rename).Printable functionCount ↔
      function.Printable functionCount := by
  simp [Function.Printable, Block.referencesInRange_renameVariables]

namespace Proofs

theorem Program.Printable.renameVariables {program : Program}
    (printable : program.Printable) (rename : VarId → VarId) :
    (program.renameVariables rename).Printable := by
  simpa [Vars.Program.Printable, Function.printable_renameVariables] using printable

theorem Program.Printable.normalize {program : Program}
    (printable : program.Printable) : program.normalize.Printable :=
  Program.Printable.renameVariables printable program.normalVariable

end Proofs
end Sir.Vars.Text
