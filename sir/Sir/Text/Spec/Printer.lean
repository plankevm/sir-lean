import Sir.Text.Spec.Mnemonic

namespace Sir.Vars.Text

def functionName (program : Program) (function : FunctionId) : String :=
  if function = program.initId then "init"
  else if program.mainId? = some function then "main"
  else "fn" ++ decimalString function.id

def blockName (block : BlockId) : String :=
  "block" ++ decimalString block.id

def variableName (identifier : VarId) : String :=
  "v" ++ decimalString identifier.id

def variableToken (identifier : VarId) : Token :=
  .identifier (variableName identifier)

def variableTokens (identifiers : Array VarId) : List Token :=
  identifiers.toList.map variableToken

def definitionTokens (results : List VarId) : List Token :=
  if results.isEmpty then [] else results.map variableToken ++ [.equals]

def immediateTokens (program : Program) : Stmt → List Token
  | .assign _ (.constant value) => [.number value.toNat]
  | .icall callee _ _ => [.label (functionName program callee)]
  | _ => []

def stmtTokens (program : Program) (statement : Stmt) : List Token :=
  definitionTokens (spelling statement).results ++
    .identifier (spelling statement).name ::
      (immediateTokens program statement ++ (spelling statement).operands.map variableToken)

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
