import Sir.Vars.Spec

namespace Sir.Vars

def Stmt.FunctionReferencesInRange (functionCount : Nat) : Stmt → Prop
  | .icall callee _ _ => callee.id < functionCount
  | _ => True

def Terminator.BlockReferencesInRange (blockCount : Nat) : Terminator → Prop
  | .jump target => target.id < blockCount
  | .branch _ thenTarget elseTarget =>
      thenTarget.id < blockCount ∧ elseTarget.id < blockCount
  | _ => True

def Block.ReferencesInRange (functionCount blockCount : Nat)
    (block : Block) : Prop :=
  (∀ statement ∈ block.statements,
    statement.FunctionReferencesInRange functionCount) ∧
  block.terminator.BlockReferencesInRange blockCount

def Function.Printable (functionCount : Nat) (function : Function) : Prop :=
  ∀ block ∈ function.blocks,
    block.ReferencesInRange functionCount function.blocks.size

def Program.Printable (program : Program) : Prop :=
  ∀ function ∈ program.functions,
    function.Printable program.functions.size

end Sir.Vars
