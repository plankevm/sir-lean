import Sir.Spec.State

namespace Sir

/-- `callEdge callee caller`: some block of `caller` icalls `callee` (note the argument order). -/
def Program.callEdge (p : Program) (callee caller : FunctionId) : Prop :=
  ∃ args dests fn, p.function? caller = some fn ∧ fn.HasStmt (.icall callee args dests)

def Expr.variablesRead : Expr → List VarId
  | .constant _ => []
  | .var identifier => [identifier]
  | .add lhs rhs | .lt lhs rhs => [lhs, rhs]
  | .sload key => [key]

def Stmt.variablesRead : Stmt → List VarId
  | .assign _ value => value.variablesRead
  | .sstore key value => [key, value]
  | .gas _ => []
  | .call callData => [callData.callee, callData.gas]
  | .mallocUninit _ size => [size]
  | .mstore32 offset value => [offset, value]
  | .mload32 _ offset => [offset]
  | .icall _ args _ => args.toList

def Stmt.variablesDefined : Stmt → List VarId
  | .assign result _ | .gas result | .mallocUninit result _
  | .mload32 result _ => [result]
  | .call callData => [callData.result]
  | .icall _ _ dests => dests.toList
  | .sstore _ _ | .mstore32 _ _ => []

def Terminator.variablesRead : Terminator → List VarId
  | .branch condition _ _ => [condition]
  | .halt | .jump _ | .iret => []

def Terminator.jumpTargets : Terminator → List BlockId
  | .jump target => [target]
  | .branch _ thenTarget elseTarget => [thenTarget, elseTarget]
  | .halt | .iret => []

def BasicBlock.variablesDefinedBefore (block : BasicBlock) : Nat → List VarId
  | 0 => block.inputs.toList
  | index + 1 =>
      match block.statements[index]? with
      | some statement =>
          block.variablesDefinedBefore index ++ statement.variablesDefined
      | none => block.variablesDefinedBefore index

/-- Ensures every local lookup is preceded by a parameter or statement result that supplies it. -/
def BasicBlock.VariablesDefinedBeforeUse (block : BasicBlock) : Prop :=
  (∀ index statement, block.statements[index]? = some statement →
    ∀ identifier ∈ statement.variablesRead,
      identifier ∈ block.variablesDefinedBefore index) ∧
  ∀ identifier ∈ block.terminator.variablesRead ++ block.outputs.toList,
    identifier ∈ block.variablesDefinedBefore block.statements.size

structure Program.WellFormed (p : Program) : Prop where
  icallArity :
    ∀ callee args dests, p.HasStmt (.icall callee args dests) →
      p.FunctionInputOutputArity args.size (some dests.size) callee
  iretArity :
    ∀ fn ∈ p.functions,
      (∀ n, fn.outputs = some n →
        ∀ block ∈ fn.blocks, block.terminator = .iret → block.outputs.size = n) ∧
      (fn.outputs = none → ∀ block ∈ fn.blocks, block.terminator ≠ .iret)
  acyclicCalls : ∀ f, ¬ Relation.TransGen p.callEdge f f
  entryArity : p.AtEntries (p.FunctionInputOutputArity 0 none)
  validJumpTargets :
    ∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, fn.block? target = some targetBlock ∧
          targetBlock.inputs.size = block.outputs.size
  variablesDefinedBeforeUse :
    ∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, block.VariablesDefinedBeforeUse
end Sir
