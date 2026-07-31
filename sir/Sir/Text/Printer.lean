import Sir.Text.Token

namespace Sir.Vars.Text

def functionName (program : Program) (function : FunctionId) : String :=
  if function = program.initEntry then "init"
  else if program.mainEntry = some function then "main"
  else "fn" ++ decimalString function.id

def blockName (block : BlockId) : String :=
  "block" ++ decimalString block.id

def variableName (identifier : VarId) : String :=
  "v" ++ decimalString identifier.id

def variableToken (identifier : VarId) : Token :=
  .identifier (variableName identifier)

def variableTokens (identifiers : Array VarId) : List Token :=
  identifiers.toList.map variableToken

def definitionTokens (results : Array VarId) : List Token :=
  if results.isEmpty then [] else variableTokens results ++ [.equals]

def exprTokens : Expr → List Token
  | .constant value => [.identifier "const", .number value.toNat]
  | .var source => [.identifier "copy", variableToken source]
  | .add lhs rhs => [.identifier "add", variableToken lhs, variableToken rhs]
  | .lt lhs rhs => [.identifier "lt", variableToken lhs, variableToken rhs]
  | .sload key => [.identifier "sload", variableToken key]

def stmtTokens (program : Program) : Stmt → List Token
  | .assign result value => definitionTokens #[result] ++ exprTokens value
  | .sstore key value => [.identifier "sstore", variableToken key, variableToken value]
  | .gas result => definitionTokens #[result] ++ [.identifier "gas"]
  | .call callData =>
      definitionTokens #[callData.result] ++
        [.identifier "call", variableToken callData.gas, variableToken callData.callee]
  | .malloc result size =>
      definitionTokens #[result] ++ [.identifier "malloc", variableToken size]
  | .mallocUninit result size =>
      definitionTokens #[result] ++ [.identifier "mallocany", variableToken size]
  | .mstore32 offset value =>
      [.identifier "mstore256", variableToken offset, variableToken value]
  | .mload32 result offset =>
      definitionTokens #[result] ++ [.identifier "mload256", variableToken offset]
  | .icall callee args dests =>
      definitionTokens dests ++
        [.identifier "icall", .label (functionName program callee)] ++ variableTokens args

def terminatorTokens : Terminator → List Token
  | .halt => [.identifier "stop"]
  | .iret => [.identifier "iret"]
  | .jump target => [.fatArrow, .label (blockName target)]
  | .branch condition thenTarget elseTarget =>
      [.fatArrow, variableToken condition, .question, .label (blockName thenTarget),
        .colon, .label (blockName elseTarget)]

def blockTokens (program : Program) (identifier : BlockId) (block : Block) :
    List Token :=
  [.identifier (blockName identifier)] ++ variableTokens block.inputs ++
      (if block.outputs.isEmpty then [] else .arrow :: variableTokens block.outputs) ++
      [.leftBrace, .newline] ++
    (block.statements.toList.flatMap fun statement => stmtTokens program statement ++ [.newline]) ++
    terminatorTokens block.terminator ++ [.newline, .rightBrace, .newline]

def functionTokens (program : Program) (identifier : FunctionId) (function : Function) :
    List Token :=
  [.identifier "fn", .identifier (functionName program identifier), .colon, .newline] ++
    (function.blocks.toList.zipIdx.flatMap fun (block, index) =>
      blockTokens program ⟨index⟩ block)

def programTokens (program : Program) : List Token :=
  program.functions.toList.zipIdx.flatMap fun (function, index) =>
    functionTokens program ⟨index⟩ function

def print (program : Program) : String :=
  render (programTokens program)

end Sir.Vars.Text
