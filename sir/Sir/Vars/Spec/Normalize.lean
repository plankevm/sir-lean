import Sir.Vars.Spec

namespace Sir.Vars

def Expr.renameVariables (rename : VarId → VarId) : Expr → Expr
  | .constant value => .constant value
  | .var source => .var (rename source)
  | .add lhs rhs => .add (rename lhs) (rename rhs)
  | .lt lhs rhs => .lt (rename lhs) (rename rhs)
  | .sload key => .sload (rename key)

def Stmt.renameVariables (rename : VarId → VarId) : Stmt → Stmt
  | .assign result value => .assign (rename result) (value.renameVariables rename)
  | .sstore key value => .sstore (rename key) (rename value)
  | .gas result => .gas (rename result)
  | .call callData => .call {
      callee := rename callData.callee
      gas := rename callData.gas
      result := rename callData.result }
  | .malloc result size => .malloc (rename result) (rename size)
  | .mallocUninit result size => .mallocUninit (rename result) (rename size)
  | .mstore32 offset value => .mstore32 (rename offset) (rename value)
  | .mload32 result offset => .mload32 (rename result) (rename offset)
  | .icall callee args dests => .icall callee (args.map rename) (dests.map rename)

def Terminator.renameVariables (rename : VarId → VarId) : Terminator → Terminator
  | .halt => .halt
  | .jump target => .jump target
  | .branch condition thenTarget elseTarget =>
      .branch (rename condition) thenTarget elseTarget
  | .iret => .iret

def Block.renameVariables (rename : VarId → VarId) (block : Block) : Block :=
  { inputs := block.inputs.map rename
    statements := block.statements.map (Stmt.renameVariables rename)
    terminator := block.terminator.renameVariables rename
    outputs := block.outputs.map rename }

def Function.renameVariables (rename : VarId → VarId) (function : Function) : Function :=
  { entry := function.entry.renameVariables rename
    rest := function.rest.map (Block.renameVariables rename) }

def Program.renameVariables (rename : VarId → VarId) (program : Program) : Program :=
  { init := program.init.renameVariables rename
    main := program.main.map (Function.renameVariables rename)
    rest := program.rest.map (Function.renameVariables rename) }

def Expr.variableOccurrences : Expr → List VarId
  | .constant _ => []
  | .var source => [source]
  | .add lhs rhs => [lhs, rhs]
  | .lt lhs rhs => [lhs, rhs]
  | .sload key => [key]

def Stmt.variableOccurrences : Stmt → List VarId
  | .assign result value => result :: value.variableOccurrences
  | .sstore key value => [key, value]
  | .gas result => [result]
  | .call callData => [callData.result, callData.gas, callData.callee]
  | .malloc result size => [result, size]
  | .mallocUninit result size => [result, size]
  | .mstore32 offset value => [offset, value]
  | .mload32 result offset => [result, offset]
  | .icall _ args dests => dests.toList ++ args.toList

def Terminator.variableOccurrences : Terminator → List VarId
  | .halt => []
  | .jump _ => []
  | .branch condition _ _ => [condition]
  | .iret => []

def Block.variableOccurrences (block : Block) : List VarId :=
  block.inputs.toList ++ block.outputs.toList ++
    block.statements.toList.flatMap Stmt.variableOccurrences ++
    block.terminator.variableOccurrences

def Function.variableOccurrences (function : Function) : List VarId :=
  function.blocks.toList.flatMap Block.variableOccurrences

def Program.variableOccurrences (program : Program) : List VarId :=
  program.functions.toList.flatMap Function.variableOccurrences

def Program.normalVariable (program : Program) (identifier : VarId) : VarId :=
  ⟨program.variableOccurrences.eraseDups.idxOf identifier⟩

def Program.normalize (program : Program) : Program :=
  program.renameVariables program.normalVariable

def Program.Normal (program : Program) : Prop :=
  program.normalize = program

def Program.AlphaEquiv (left right : Program) : Prop :=
  ∃ forward backward : VarId → VarId,
    left.renameVariables forward = right ∧ right.renameVariables backward = left

end Sir.Vars
