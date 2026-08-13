import Sir.Text.Token

namespace Sir.Vars.Text

abbrev Line := List Token

def splitLinesAux (current : List Token) : List Token → List Line
  | [] => if current.isEmpty then [] else [current.reverse]
  | .newline :: rest =>
      if current.isEmpty then splitLinesAux [] rest
      else current.reverse :: splitLinesAux [] rest
  | token :: rest => splitLinesAux (token :: current) rest

def splitLines (tokens : List Token) : List Line :=
  splitLinesAux [] tokens

def describe (line : Line) : String :=
  render line

abbrev ParserM := StateT (List String) (Except String)

def internVariable (name : String) : ParserM VarId := do
  let names ← get
  match names.findIdx? (· == name) with
  | some index => return ⟨index⟩
  | none =>
      set (names ++ [name])
      return ⟨names.length⟩

def temporaryName (identifier : VarId) : String :=
  "%" ++ decimalString identifier.id

def freshVariable : ParserM VarId := do
  let names ← get
  set (names ++ [temporaryName ⟨names.length⟩])
  return ⟨names.length⟩

def liftNumbers : List Token → ParserM (List Stmt × List Token)
  | [] => return ([], [])
  | .number value :: rest => do
      let target ← freshVariable
      let (preludes, tokens) ← liftNumbers rest
      return (.assign target (.constant (.ofNat value)) :: preludes,
        .identifier (temporaryName target) :: tokens)
  | token :: rest => do
      let (preludes, tokens) ← liftNumbers rest
      return (preludes, token :: tokens)

def variableList : List Token → ParserM (Array VarId)
  | [] => return #[]
  | .identifier name :: rest => do
      let head ← internVariable name
      return #[head] ++ (← variableList rest)
  | token :: _ => throw s!"expected a local name, got '{describe [token]}'"

def operand : Token → ParserM (List Stmt × VarId)
  | .identifier name => do return ([], ← internVariable name)
  | .number value => do
      let target ← freshVariable
      return ([.assign target (.constant (.ofNat value))], target)
  | token => throw s!"expected a local name or a number, got '{describe [token]}'"

def operands : List Token → ParserM (List Stmt × Array VarId)
  | [] => return ([], #[])
  | token :: rest => do
      let (prelude, identifier) ← operand token
      let (preludes, identifiers) ← operands rest
      return (prelude ++ preludes, #[identifier] ++ identifiers)

def parseMnemonic (functions : List String) (line : Line) (mnemonic : String)
    (results : List VarId) (parameters : List Token) : ParserM (List Stmt) :=
  match mnemonic, results, parameters with
  | "copy", [result], [source] => do
      let (_, sourceId) ← operand source
      pure [.assign result (.var sourceId)]
  | "add", [result], [lhs, rhs] => do
      let (_, lhsId) ← operand lhs
      let (_, rhsId) ← operand rhs
      pure [.assign result (.add lhsId rhsId)]
  | "lt", [result], [lhs, rhs] => do
      let (_, lhsId) ← operand lhs
      let (_, rhsId) ← operand rhs
      pure [.assign result (.lt lhsId rhsId)]
  | "sload", [result], [key] => do
      let (_, keyId) ← operand key
      pure [.assign result (.sload keyId)]
  | "sstore", [], [key, value] => do
      let (_, keyId) ← operand key
      let (_, valueId) ← operand value
      pure [.sstore keyId valueId]
  | "gas", [result], [] => pure [.gas result]
  | "call", [result], [gas, callee] => do
      let (_, gasId) ← operand gas
      let (_, calleeId) ← operand callee
      pure [.call { callee := calleeId, gas := gasId, result := result }]
  | "malloc", [result], [size] => do
      let (_, sizeId) ← operand size
      pure [.malloc result sizeId]
  | "mallocany", [result], [size] => do
      let (_, sizeId) ← operand size
      pure [.mallocUninit result sizeId]
  | "mstore256", [], [offset, value] => do
      let (_, offsetId) ← operand offset
      let (_, valueId) ← operand value
      pure [.mstore32 offsetId valueId]
  | "mload256", [result], [offset] => do
      let (_, offsetId) ← operand offset
      pure [.mload32 result offsetId]
  | "icall", dests, .label calleeName :: args => do
      let some calleeIndex := functions.findIdx? (· == calleeName)
        | throw s!"unknown function '@{calleeName}'"
      let (_, arguments) ← operands args
      pure [.icall ⟨calleeIndex⟩ arguments dests.toArray]
  | _, _, _ => throw s!"unsupported operation '{describe line}'"

def statementParts (line : Line) : List Token × List Token :=
  match line.span (· != .equals) with
  | (before, .equals :: after) => (before, after)
  | _ => ([], line)

def parseStatement (functions : List String) (line : Line) : ParserM (List Stmt) := do
  let (resultTokens, operandTokens) := statementParts line
  match operandTokens with
  | .identifier "const" :: parameters => do
      let results ← variableList resultTokens
      match results.toList, parameters with
      | [result], [.number value] =>
          return [.assign result (.constant (.ofNat value))]
      | _, _ => throw s!"unsupported operation '{describe line}'"
  | .identifier mnemonic :: rawParameters => do
      let (lifted, parameters) ← liftNumbers rawParameters
      let results ← variableList resultTokens
      let body ← parseMnemonic functions line mnemonic results.toList parameters
      pure (lifted ++ body)
  | _ => throw s!"expected an operation mnemonic in '{describe line}'"

def resolveBlock (blocks : List String) (name : String) : ParserM BlockId := do
  let some index := blocks.findIdx? (· == name) | throw s!"unknown block '@{name}'"
  return ⟨index⟩

def parseTerminator (blocks : List String) : Line → ParserM Terminator
  | [.identifier "stop"] => return .halt
  | [.identifier "iret"] => return .iret
  | [.fatArrow, .label target] => return .jump (← resolveBlock blocks target)
  | [.fatArrow, .identifier condition, .question, .label thenTarget, .colon,
      .label elseTarget] => do
      return .branch (← internVariable condition) (← resolveBlock blocks thenTarget)
        (← resolveBlock blocks elseTarget)
  | line => throw s!"expected a terminator, got '{describe line}'"

def parseBlockBody (functions blocks : List String) :
    List Line → ParserM (Array Stmt × Terminator)
  | [] => throw "a block must end with a terminator"
  | [line] => do return (#[], ← parseTerminator blocks line)
  | line :: rest => do
      let statements ← parseStatement functions line
      let (following, terminator) ← parseBlockBody functions blocks rest
      return (statements.toArray ++ following, terminator)

def parseBlockHeader : Line → ParserM (Array VarId × Array VarId)
  | .identifier _ :: rest =>
      match rest.reverse with
      | .leftBrace :: reversedSignature => do
          let signature := reversedSignature.reverse
          let (inputTokens, outputTokens) :=
            match signature.span (· != .arrow) with
            | (before, .arrow :: after) => (before, after)
            | _ => (signature, [])
          return (← variableList inputTokens, ← variableList outputTokens)
      | _ => throw "expected '{' at the end of a block header"
  | line => throw s!"expected a block header, got '{describe line}'"

def parseBlock (functions blocks : List String) (header : Line) (body : List Line) :
    ParserM Block := do
  let (inputs, outputs) ← parseBlockHeader header
  let (statements, terminator) ← parseBlockBody functions blocks body
  return { inputs := inputs, statements := statements, terminator := terminator,
           outputs := outputs }

def blockHeaderName : Line → Except String String
  | .identifier name :: _ => .ok name
  | line => .error s!"expected a block header, got '{describe line}'"

def isBlockHeader (line : Line) : Bool :=
  line.getLast? == some Token.leftBrace

def splitBlocksAux (groups : List (Line × List Line)) (isOpen : Bool) :
    List Line → Except String (List (Line × List Line))
  | [] =>
      if isOpen then .error "a block is missing its '}'"
      else .ok (groups.reverse.map fun group => (group.fst, group.snd.reverse))
  | line :: rest =>
      if isOpen then
        if line == [Token.rightBrace] then splitBlocksAux groups false rest
        else
          match groups with
          | [] => .error s!"unexpected line '{describe line}'"
          | (header, body) :: others =>
              splitBlocksAux ((header, line :: body) :: others) true rest
      else if isBlockHeader line then splitBlocksAux ((line, []) :: groups) true rest
      else .error s!"expected a block header, got '{describe line}'"

def splitBlocks (lines : List Line) : Except String (List (Line × List Line)) :=
  splitBlocksAux [] false lines

def splitFunctionsAux (groups : List (String × List Line)) :
    List Line → Except String (List (String × List Line))
  | [] => .ok (groups.reverse.map fun group => (group.fst, group.snd.reverse))
  | line :: rest =>
      match line with
      | [.identifier "fn", .identifier name, .colon] =>
          splitFunctionsAux ((name, []) :: groups) rest
      | _ =>
          match groups with
          | [] => .error s!"expected a function header, got '{describe line}'"
          | (name, body) :: others => splitFunctionsAux ((name, line :: body) :: others) rest

def splitFunctions (lines : List Line) : Except String (List (String × List Line)) :=
  splitFunctionsAux [] lines

def hasDuplicates : List String → Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicates rest

def parseFunctionGroups (functions : List String) (groups : List (Line × List Line)) :
    ParserM Function := do
  let blocks ← liftM (groups.mapM fun group => blockHeaderName group.fst)
  if hasDuplicates blocks then throw "duplicate block name"
  let parsed ← groups.mapM fun group => parseBlock functions blocks group.fst group.snd
  return { blocks := parsed.toArray, entry := ⟨0⟩ }

def parseFunction (functions : List String) (body : List Line) : ParserM Function :=
  match splitBlocks body with
  | .error message => throw message
  | .ok groups => parseFunctionGroups functions groups

def parseFunctionGroupsList (names : List String) (groups : List (String × List Line)) :
    ParserM (List Function) :=
  groups.mapM fun group => parseFunction names group.snd

def parseProgramGroups (groups : List (String × List Line)) : Except String Program := do
  let names := groups.map Prod.fst
  if hasDuplicates names then .error "duplicate function name"
  let (functions, _) ← (parseFunctionGroupsList names groups).run []
  let some initEntry := names.findIdx? (· == "init")
    | .error "the program has no function named 'init'"
  return { functions := functions.toArray, initEntry := ⟨initEntry⟩,
           mainEntry := (names.findIdx? (· == "main")).map FunctionId.mk }

def parseTokens (tokens : List Token) : Except String Program :=
  match splitFunctions (splitLines tokens) with
  | .error message => .error message
  | .ok groups => parseProgramGroups groups

def parse (source : String) : Except String Program :=
  parseTokens (tokenize source)

/-- Smart unfolding copies the unreduced lexer term held in the interning state once per
unfolding attempt; plain delta reduction does not. -/
macro "parse_rfl" : tactic =>
  `(tactic| set_option smartUnfolding false in set_option maxRecDepth 100000 in rfl)

end Sir.Vars.Text
