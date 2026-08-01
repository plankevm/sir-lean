import Sir.Text.Parser

namespace Sir.Vars.Text

def idLit (id : Nat) : String := "⟨" ++ decimalString id ++ "⟩"

def varLit (identifier : VarId) : String := idLit identifier.id

def arrayLit (elements : List String) : String :=
  if elements.isEmpty then "#[]" else "#[" ++ String.intercalate ", " elements ++ "]"

def varArrayLit (identifiers : Array VarId) : String :=
  arrayLit (identifiers.toList.map varLit)

def exprLit : Expr → String
  | .constant value => "(.constant (.ofNat " ++ decimalString value.toNat ++ "))"
  | .var source => "(.var " ++ varLit source ++ ")"
  | .add lhs rhs => "(.add " ++ varLit lhs ++ " " ++ varLit rhs ++ ")"
  | .lt lhs rhs => "(.lt " ++ varLit lhs ++ " " ++ varLit rhs ++ ")"
  | .sload key => "(.sload " ++ varLit key ++ ")"

def stmtLit : Stmt → String
  | .assign result value => ".assign " ++ varLit result ++ " " ++ exprLit value
  | .sstore key value => ".sstore " ++ varLit key ++ " " ++ varLit value
  | .gas result => ".gas " ++ varLit result
  | .call callData =>
      ".call { callee := " ++ varLit callData.callee ++ ", gas := " ++ varLit callData.gas ++
        ", result := " ++ varLit callData.result ++ " }"
  | .malloc result size => ".malloc " ++ varLit result ++ " " ++ varLit size
  | .mallocUninit result size => ".mallocUninit " ++ varLit result ++ " " ++ varLit size
  | .mstore32 offset value => ".mstore32 " ++ varLit offset ++ " " ++ varLit value
  | .mload32 result offset => ".mload32 " ++ varLit result ++ " " ++ varLit offset
  | .icall callee args dests =>
      ".icall " ++ idLit callee.id ++ " " ++ varArrayLit args ++ " " ++ varArrayLit dests

def terminatorLit : Terminator → String
  | .halt => ".halt"
  | .iret => ".iret"
  | .jump target => ".jump " ++ idLit target.id
  | .branch condition thenTarget elseTarget =>
      ".branch " ++ varLit condition ++ " " ++ idLit thenTarget.id ++ " " ++ idLit elseTarget.id

def indent (depth : Nat) : String :=
  String.ofList (List.replicate (2 * depth) ' ')

def blockLit (depth : Nat) (block : Block) : String :=
  let statements :=
    if block.statements.isEmpty then "#[]"
    else "#[\n" ++
      String.intercalate ",\n"
        (block.statements.toList.map fun statement =>
          indent (depth + 2) ++ stmtLit statement) ++ "]"
  "{ inputs := " ++ varArrayLit block.inputs ++ ",\n" ++
    indent (depth + 1) ++ "statements := " ++ statements ++ ",\n" ++
    indent (depth + 1) ++ "terminator := " ++ terminatorLit block.terminator ++ ",\n" ++
    indent (depth + 1) ++ "outputs := " ++ varArrayLit block.outputs ++ " }"

def functionLit (depth : Nat) (function : Function) : String :=
  "{ blocks := #[\n" ++
    String.intercalate ",\n"
      (function.blocks.toList.map fun block =>
        indent (depth + 2) ++ blockLit (depth + 2) block) ++ "],\n" ++
    indent (depth + 1) ++ "entry := " ++ idLit function.entry.id ++ " }"

def toLeanModule (declaration : String) (program : Program) : String :=
  "import Sir.Vars.Spec\n\nnamespace Sir.Vars\n\ndef " ++ declaration ++ " : Program :=\n" ++
  "  { functions := #[\n" ++
    String.intercalate ",\n"
      (program.functions.toList.map fun function =>
        indent 3 ++ functionLit 3 function) ++ "],\n" ++
  "    initEntry := " ++ idLit program.initEntry.id ++ ",\n" ++
  "    mainEntry := " ++
    (match program.mainEntry with
     | none => "none"
     | some entry => "some " ++ idLit entry.id) ++ " }\n\nend Sir.Vars\n"

def isDeclarationStart (character : Char) : Bool :=
  character.isAlpha || character == '_'

def isDeclarationRest (character : Char) : Bool :=
  character.isAlphanum || character == '_' || character == '\''

def isDeclarationName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => isDeclarationStart first && rest.all isDeclarationRest

def extract (source declaration : String) : Except String String := do
  if !isDeclarationName declaration then
    throw s!"invalid declaration name {String.quote declaration}"
  let program ← parse source
  return toLeanModule declaration program

end Sir.Vars.Text
