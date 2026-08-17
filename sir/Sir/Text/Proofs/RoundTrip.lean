import Sir.Text.Proofs.Printer
import Sir.Text.Proofs.ParsePrintable

namespace Sir.Vars.Text

private def lineTokens (lines : List Line) : List Token :=
  lines.flatMap fun line => line ++ [.newline]

private def blockLines (program : Program) (identifier : BlockId)
    (block : Block) : List Line :=
  ([.identifier (blockName identifier)] ++ variableTokens block.inputs ++
      (if block.outputs.isEmpty then [] else .arrow :: variableTokens block.outputs) ++
      [.leftBrace]) ::
    block.statements.toList.map (stmtTokens program) ++
    [terminatorTokens block.terminator, [.rightBrace]]

private def functionLines (program : Program) (identifier : FunctionId)
    (function : Function) : List Line :=
  [.identifier "fn", .identifier (functionName program identifier), .colon] ::
    (function.blocks.toList.zipIdx.flatMap fun (block, index) =>
      blockLines program ⟨index⟩ block)

private def programLines (program : Program) : List Line :=
  program.functions.toList.zipIdx.flatMap fun (function, index) =>
    functionLines program ⟨index⟩ function

private def functionBodyLines (program : Program) (function : Function) : List Line :=
  function.blocks.toList.zipIdx.flatMap fun (block, index) =>
    blockLines program ⟨index⟩ block

private def printedFunctionGroups (program : Program) : List (String × List Line) :=
  program.functions.toList.zipIdx.map fun (function, index) =>
    (functionName program ⟨index⟩, functionBodyLines program function)

private def printedFunctionNames (program : Program) : List String :=
  (printedFunctionGroups program).map Prod.fst

private theorem blockTokens_eq_lineTokens (program : Program) (identifier : BlockId)
    (block : Block) :
    blockTokens program identifier block = lineTokens (blockLines program identifier block) := by
  simp [blockTokens, blockLines, lineTokens, List.flatMap_append, List.flatMap_map]

private theorem lineTokens_append (first second : List Line) :
    lineTokens (first ++ second) = lineTokens first ++ lineTokens second := by
  simp [lineTokens, List.flatMap_append]

private theorem lineTokens_flatMap {α : Type} (values : List α) (lines : α → List Line) :
    lineTokens (values.flatMap lines) =
      values.flatMap fun value => lineTokens (lines value) := by
  induction values with
  | nil => rfl
  | cons value following induction =>
      simp only [List.flatMap_cons, lineTokens_append, induction]

private theorem functionTokens_eq_lineTokens (program : Program) (identifier : FunctionId)
    (function : Function) :
    functionTokens program identifier function =
      lineTokens (functionLines program identifier function) := by
  rw [functionTokens, functionLines]
  simp only [lineTokens, List.flatMap_cons]
  rw [show List.flatMap (fun line => line ++ [Token.newline])
        (List.flatMap
          (fun x => blockLines program { id := x.2 } x.1)
          function.blocks.toList.zipIdx) =
      lineTokens (List.flatMap
        (fun x => blockLines program { id := x.2 } x.1)
        function.blocks.toList.zipIdx) by rfl]
  rw [lineTokens_flatMap]
  congr 1
  apply List.flatMap_congr
  intro pair member
  rcases pair with ⟨block, index⟩
  exact blockTokens_eq_lineTokens program ⟨index⟩ block

private theorem programTokens_eq_lineTokens (program : Program) :
    programTokens program = lineTokens (programLines program) := by
  rw [programTokens, programLines, lineTokens_flatMap]
  apply List.flatMap_congr
  intro pair member
  rcases pair with ⟨function, index⟩
  exact functionTokens_eq_lineTokens program ⟨index⟩ function

private theorem splitLinesAux_append_line (current line rest : List Token)
    (currentNe : current ≠ []) (noNewline : .newline ∉ line) :
    splitLinesAux current (line ++ .newline :: rest) =
      (current.reverse ++ line) :: splitLinesAux [] rest := by
  induction line generalizing current with
  | nil => simp [splitLinesAux, currentNe]
  | cons token following induction =>
      have tokenNe : token ≠ .newline := by
        intro equality
        subst token
        exact noNewline (by simp)
      rw [List.cons_append]
      simp [splitLinesAux]
      rw [induction (token :: current) (by simp)]
      · simp
      · intro member
        exact noNewline (List.mem_cons_of_mem token member)

private theorem splitLines_lineTokens (lines : List Line)
    (nonempty : ∀ line ∈ lines, line ≠ [])
    (noNewline : ∀ line ∈ lines, Token.newline ∉ line) :
    splitLines (lineTokens lines) = lines := by
  induction lines with
  | nil => rfl
  | cons line following induction =>
      rw [splitLines]
      rw [lineTokens, List.flatMap_cons]
      rw [show line ++ [.newline] ++
          List.flatMap (fun line => line ++ [.newline]) following =
          line ++ .newline :: List.flatMap (fun line => line ++ [.newline]) following by
        simp]
      cases line with
      | nil => exact False.elim (nonempty [] (by simp) rfl)
      | cons token rest =>
          have tokenNe : token ≠ .newline := by
            intro equality
            subst token
            exact noNewline (.newline :: rest) (by simp) (by simp)
          simp only [List.cons_append]
          simp [splitLinesAux]
          rw [splitLinesAux_append_line [token] rest
            (List.flatMap (fun line => line ++ [Token.newline]) following)
            (by simp) (by
              intro member
              exact noNewline (token :: rest) (by simp) (by simp [member]))]
          simp only [List.reverse_singleton, List.singleton_append]
          rw [← splitLines]
          exact congrArg (List.cons (token :: rest))
            (induction (fun line member => nonempty line (by simp [member]))
              (fun line member => noNewline line (by simp [member])))

private theorem programLines_nonempty (program : Program) :
    ∀ line ∈ programLines program, line ≠ [] := by
  intro line member
  simp only [programLines, List.mem_flatMap] at member
  rcases member with ⟨pair, _, member⟩
  rcases pair with ⟨function, index⟩
  simp only [functionLines, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨pair, _, member⟩
  · simp
  rcases pair with ⟨block, blockIndex⟩
  simp only [blockLines, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with (rfl | ⟨statement, _, rfl⟩) | following
  · simp
  · cases statement <;> simp [stmtTokens, definitionTokens]
  rcases following with rfl | following
  · cases block.terminator <;> simp [terminatorTokens]
  rcases following with rfl | impossible
  · simp
  · simp at impossible

private theorem programLines_noNewline (program : Program) :
    ∀ line ∈ programLines program, Token.newline ∉ line := by
  intro line member
  simp only [programLines, List.mem_flatMap] at member
  rcases member with ⟨pair, _, member⟩
  rcases pair with ⟨function, index⟩
  simp only [functionLines, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨pair, _, member⟩
  · simp
  rcases pair with ⟨block, blockIndex⟩
  simp only [blockLines, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with (rfl | ⟨statement, _, rfl⟩) | following
  · simp [variableTokens, variableToken]
  · cases statement with
    | assign _ value =>
        cases value <;>
          simp [stmtTokens, definitionTokens, exprTokens, variableTokens, variableToken]
    | sstore | gas | call | malloc | mallocUninit | mstore32 | mload32 | icall =>
        simp [stmtTokens, definitionTokens, variableTokens, variableToken]
  rcases following with rfl | following
  · cases block.terminator <;>
      simp [terminatorTokens, variableToken]
  rcases following with rfl | impossible
  · simp
  · simp at impossible

private theorem splitLines_programTokens (program : Program) :
    splitLines (programTokens program) = programLines program := by
  rw [programTokens_eq_lineTokens]
  exact splitLines_lineTokens _ (programLines_nonempty program)
    (programLines_noNewline program)

@[simp] private theorem blockName_ne_fn (identifier : BlockId) :
    blockName identifier ≠ "fn" := by
  intro equality
  have characters := congrArg String.toList equality
  simp [blockName, String.toList_append] at characters

@[simp] private theorem variableName_ne_fn (identifier : VarId) :
    variableName identifier ≠ "fn" := by
  intro equality
  have characters := congrArg String.toList equality
  simp [variableName, String.toList_append] at characters

private theorem functionBodyLines_not_header (program : Program) (function : Function) :
    ∀ line ∈ functionBodyLines program function,
      ∀ name, line ≠ [.identifier "fn", .identifier name, .colon] := by
  intro line member name
  simp only [functionBodyLines, List.mem_flatMap] at member
  rcases member with ⟨pair, _, member⟩
  rcases pair with ⟨block, blockIndex⟩
  simp only [blockLines, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with (lineEq | ⟨statement, _, lineEq⟩) | following
  · subst line
    simp
  · subst line
    cases statement with
    | assign _ value =>
        cases value <;>
          simp [stmtTokens, definitionTokens, variableTokens, variableToken]
    | icall callee args dests =>
        rcases dests with ⟨dests⟩
        cases dests <;>
          simp [stmtTokens, definitionTokens, variableTokens, variableToken]
    | sstore | gas | call | malloc | mallocUninit | mstore32 | mload32 =>
        simp [stmtTokens, definitionTokens, variableTokens, variableToken]
  rcases following with lineEq | following
  · subst line
    cases block.terminator <;> simp [terminatorTokens]
  rcases following with lineEq | impossible
  · subst line
    simp
  · simp at impossible

private theorem splitFunctionsAux_body (groups : List (String × List Line))
    (name : String) (accumulated body rest : List Line)
    (notHeader : ∀ line ∈ body,
      ∀ functionName, line ≠ [.identifier "fn", .identifier functionName, .colon]) :
    splitFunctionsAux ((name, accumulated) :: groups) (body ++ rest) =
      splitFunctionsAux ((name, body.reverse ++ accumulated) :: groups) rest := by
  induction body generalizing accumulated with
  | nil => rfl
  | cons line following induction =>
      rw [List.cons_append]
      rw [splitFunctionsAux]
      · rw [induction (line :: accumulated)]
        · simp
        · intro next member functionName equality
          exact notHeader next (by simp [member]) functionName equality
      · exact notHeader line (by simp)

private theorem splitFunctionsAux_programLines (program : Program)
    (groupsPrefix : List (String × List Line)) :
    splitFunctionsAux groupsPrefix (programLines program) =
      .ok (groupsPrefix.reverse.map (fun group => (group.fst, group.snd.reverse)) ++
        printedFunctionGroups program) := by
  rw [programLines, printedFunctionGroups]
  generalize valuesEq : program.functions.toList.zipIdx = values
  clear valuesEq
  induction values generalizing groupsPrefix with
  | nil => simp [splitFunctionsAux]
  | cons pair following induction =>
      rcases pair with ⟨function, index⟩
      simp only [List.flatMap_cons, List.map_cons, functionLines]
      rw [splitFunctionsAux.eq_def]
      change splitFunctionsAux ((functionName program ⟨index⟩, []) :: groupsPrefix)
        (functionBodyLines program function ++
          List.flatMap (fun x => functionLines program { id := x.2 } x.1) following) = _
      rw [splitFunctionsAux_body groupsPrefix (functionName program ⟨index⟩) []
        (functionBodyLines program function)
        (List.flatMap (fun x => functionLines program { id := x.2 } x.1) following)
        (functionBodyLines_not_header program function)]
      rw [induction]
      simp

private theorem splitFunctions_programLines (program : Program) :
    splitFunctions (programLines program) = .ok (printedFunctionGroups program) := by
  rw [splitFunctions, splitFunctionsAux_programLines]
  rfl

@[simp] private theorem decimalString_inj {left right : Nat} :
    decimalString left = decimalString right ↔ left = right := by
  constructor
  · intro equality
    have characters := congrArg String.toList equality
    rw [toList_decimalString, toList_decimalString] at characters
    have values := congrArg (digitsValue 10) characters
    simpa [digitsValue_decimalDigits] using values
  · exact congrArg decimalString

@[simp] private theorem fn_decimal_ne_init (identifier : Nat) :
    "fn" ++ decimalString identifier ≠ "init" := by
  intro equality
  have characters := congrArg String.toList equality
  simp [String.toList_append] at characters

@[simp] private theorem fn_decimal_ne_main (identifier : Nat) :
    "fn" ++ decimalString identifier ≠ "main" := by
  intro equality
  have characters := congrArg String.toList equality
  simp [String.toList_append] at characters

@[simp] private theorem init_ne_fn_decimal (identifier : Nat) :
    "init" ≠ "fn" ++ decimalString identifier :=
  Ne.symm (fn_decimal_ne_init identifier)

@[simp] private theorem main_ne_fn_decimal (identifier : Nat) :
    "main" ≠ "fn" ++ decimalString identifier :=
  Ne.symm (fn_decimal_ne_main identifier)

private theorem functionName_injective {program : Program} (printable : program.Printable)
    {left right : FunctionId}
    (_leftBound : left.id < program.functions.size)
    (rightBound : right.id < program.functions.size)
    (equality : functionName program left = functionName program right) :
    left = right := by
  rcases printable with ⟨initBound, mainValid, functionsValid⟩
  cases mainEq : program.mainEntry with
  | none =>
      by_cases leftInit : left = program.initEntry <;>
        by_cases rightInit : right = program.initEntry <;>
        simp_all [functionName, eq_comm]
      cases left
      cases right
      simp_all
  | some mainEntry =>
      simp [mainEq] at mainValid
      by_cases leftInit : left = program.initEntry <;>
        by_cases rightInit : right = program.initEntry <;>
        by_cases leftMain : left = mainEntry <;>
        by_cases rightMain : right = mainEntry <;>
        simp_all [functionName, eq_comm]
      cases left
      cases right
      simp_all

private theorem printedFunctionNames_eq (program : Program) :
    printedFunctionNames program =
      program.functions.toList.zipIdx.map fun pair =>
        functionName program ⟨pair.2⟩ := by
  simp [printedFunctionNames, printedFunctionGroups, Function.comp_def]

private theorem printedFunctionNames_length (program : Program) :
    (printedFunctionNames program).length = program.functions.size := by
  simp [printedFunctionNames_eq]

private theorem printedFunctionNames_getElem (program : Program) (index : Nat)
    (bound : index < (printedFunctionNames program).length) :
    (printedFunctionNames program)[index] = functionName program ⟨index⟩ := by
  simp [printedFunctionNames, printedFunctionGroups]

private theorem printedFunctionNames_findIdx (program : Program)
    (printable : program.Printable) (identifier : FunctionId)
    (bound : identifier.id < program.functions.size) :
    (printedFunctionNames program).findIdx? (· == functionName program identifier) =
      some identifier.id := by
  rw [List.findIdx?_eq_some_iff_findIdx_eq]
  have listBound : identifier.id < (printedFunctionNames program).length := by
    simpa [printedFunctionNames_length] using bound
  refine ⟨listBound, (List.findIdx_eq listBound).2 ⟨?_, ?_⟩⟩
  · simp [printedFunctionNames_getElem]
  · intro index indexBound
    simp only [beq_eq_false_iff_ne]
    intro equality
    have nameEquality : functionName program ⟨index⟩ =
        functionName program identifier := by
      rw [← printedFunctionNames_getElem program index (by omega)]
      exact equality
    have identifiersEqual : (⟨index⟩ : FunctionId) = identifier :=
      functionName_injective printable (Nat.lt_trans indexBound bound) bound nameEquality
    exact Nat.ne_of_lt indexBound (congrArg FunctionId.id identifiersEqual)

private theorem printedFunctionNames_init_findIdx (program : Program)
    (printable : program.Printable) :
    (printedFunctionNames program).findIdx? (· == "init") =
      some program.initEntry.id := by
  have nameEq : functionName program program.initEntry = "init" := by
    simp [functionName]
  rw [← nameEq]
  exact printedFunctionNames_findIdx program printable program.initEntry printable.1

private def printedVariableNames (identifiers : List VarId) : List String :=
  identifiers.eraseDups.map variableName

@[simp] private theorem variableName_inj {left right : VarId} :
    variableName left = variableName right ↔ left = right := by
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  simp [variableName]

private theorem printedVariableNames_findIdx (identifiers : List VarId)
    (identifier : VarId) :
    (printedVariableNames identifiers).findIdx? (· == variableName identifier) =
      identifiers.eraseDups.idxOf? identifier := by
  rw [printedVariableNames, List.findIdx?_map]
  apply congrArg (fun predicate => identifiers.eraseDups.findIdx? predicate)
  funext other
  simp

private theorem singleton_removeAll_eq_nil {identifier : VarId} {identifiers : List VarId}
    (member : identifier ∈ identifiers) :
    [identifier].removeAll identifiers = [] := by
  induction identifiers with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equal : identifier = head
      · subst head
        simp [List.removeAll_cons]
      · have tailMember : identifier ∈ tail := by simpa [equal] using member
        simpa [List.removeAll_cons, equal] using induction tailMember

private theorem singleton_removeAll_eq_self {identifier : VarId} {identifiers : List VarId}
    (notMember : identifier ∉ identifiers) :
    [identifier].removeAll identifiers = [identifier] := by
  induction identifiers with
  | nil => rfl
  | cons head tail induction =>
      have unequal : identifier ≠ head := by
        intro equality
        exact notMember (by simp [equality])
      have tailNotMember : identifier ∉ tail := by
        intro member
        exact notMember (by simp [member])
      simpa [List.removeAll_cons, unequal] using induction tailNotMember

private theorem internVariable_printed (prior : List VarId) (identifier : VarId) :
    (internVariable (variableName identifier)).run (printedVariableNames prior) =
      .ok (⟨prior.eraseDups.idxOf identifier⟩,
        printedVariableNames (prior ++ [identifier])) := by
  simp only [internVariable, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, pure, Except.pure, Except.bind]
  rw [printedVariableNames_findIdx]
  by_cases member : identifier ∈ prior
  · have eraseMember : identifier ∈ prior.eraseDups :=
      List.mem_eraseDups.mpr member
    have indexBound := List.idxOf_lt_length_of_mem eraseMember
    have found : prior.eraseDups.idxOf? identifier =
        some (prior.eraseDups.idxOf identifier) := by
      rw [List.idxOf?, List.findIdx?_eq_some_iff_findIdx_eq]
      exact ⟨indexBound, rfl⟩
    rw [found]
    rw [show printedVariableNames (prior ++ [identifier]) =
        printedVariableNames prior by
      simp [printedVariableNames, List.eraseDups_append,
        singleton_removeAll_eq_nil member]]
    simp [pure, StateT.pure, Except.pure]
  · have eraseNotMember : identifier ∉ prior.eraseDups := by
      simpa using member
    rw [List.idxOf?_eq_none_iff.mpr eraseNotMember]
    rw [show printedVariableNames (prior ++ [identifier]) =
        printedVariableNames prior ++ [variableName identifier] by
      rw [printedVariableNames, List.eraseDups_append,
        singleton_removeAll_eq_self member]
      simp only [List.eraseDups_cons, List.filter_nil, List.eraseDups_nil,
        List.map_append, List.map_singleton]
      rfl]
    simp [bind, StateT.bind, StateT.set, pure, StateT.pure, Except.pure, Except.bind,
      printedVariableNames, List.idxOf_eq_length eraseNotMember]

private theorem eraseDups_idxOf_of_prefix {listPrefix full : List VarId}
    {identifier : VarId} (isPrefix : listPrefix <+: full)
    (member : identifier ∈ listPrefix) :
    full.eraseDups.idxOf identifier = listPrefix.eraseDups.idxOf identifier := by
  rcases isPrefix with ⟨suffix, rfl⟩
  rw [List.eraseDups_append, List.idxOf_append]
  simp [List.mem_eraseDups.mpr member]

private theorem eraseDups_idxOf_append_self (prior : List VarId) (identifier : VarId) :
    (prior ++ [identifier]).eraseDups.idxOf identifier =
      prior.eraseDups.idxOf identifier := by
  by_cases member : identifier ∈ prior
  · rw [List.eraseDups_append, singleton_removeAll_eq_nil member]
    simp
  · have eraseNotMember : identifier ∉ prior.eraseDups := by simpa using member
    rw [List.eraseDups_append, singleton_removeAll_eq_self member,
      List.eraseDups_cons]
    simp [List.idxOf_append, eraseNotMember]

private theorem internVariable_canonical (full prior : List VarId) (identifier : VarId)
    (isPrefix : prior ++ [identifier] <+: full) :
    (internVariable (variableName identifier)).run (printedVariableNames prior) =
      .ok (⟨full.eraseDups.idxOf identifier⟩,
        printedVariableNames (prior ++ [identifier])) := by
  rw [internVariable_printed]
  rw [eraseDups_idxOf_of_prefix (identifier := identifier) isPrefix (by simp),
    eraseDups_idxOf_append_self]

private theorem variableList_printed (full prior identifiers : List VarId)
    (isPrefix : prior ++ identifiers <+: full) :
    (variableList (identifiers.map variableToken)).run (printedVariableNames prior) =
      .ok ((identifiers.map fun identifier =>
          (⟨full.eraseDups.idxOf identifier⟩ : VarId)).toArray,
        printedVariableNames (prior ++ identifiers)) := by
  induction identifiers generalizing prior with
  | nil =>
      simp [variableList, StateT.run, pure, StateT.pure, Except.pure]
  | cons identifier following induction =>
      simp only [List.map_cons, variableToken, variableList]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      have headPrefix : prior ++ [identifier] <+: full :=
        (show prior ++ [identifier] <+: prior ++ identifier :: following from
          ⟨following, by simp⟩).trans isPrefix
      rw [show internVariable (variableName identifier)
        (printedVariableNames prior) =
          .ok (⟨full.eraseDups.idxOf identifier⟩,
            printedVariableNames (prior ++ [identifier])) from
        internVariable_canonical full prior identifier headPrefix]
      simp only [pure, StateT.pure, Except.pure]
      have tailPrefix : (prior ++ [identifier]) ++ following <+: full := by
        simpa [List.append_assoc] using isPrefix
      rw [show variableList (following.map variableToken)
          (printedVariableNames (prior ++ [identifier])) =
        .ok ((following.map fun identifier =>
            (⟨full.eraseDups.idxOf identifier⟩ : VarId)).toArray,
          printedVariableNames ((prior ++ [identifier]) ++ following)) from
        induction (prior ++ [identifier]) tailPrefix]
      simp [List.append_assoc]

private def canonicalRename (full : List VarId) (identifier : VarId) : VarId :=
  ⟨full.eraseDups.idxOf identifier⟩

@[simp] private theorem identifier_ne_equals (name : String) :
    (Token.identifier name != Token.equals) = true := by
  rfl

@[simp] private theorem label_ne_equals (name : String) :
    (Token.label name != Token.equals) = true := by
  rfl

private theorem span_variableTokens_end_aux (identifiers : List VarId)
    (accumulated : List Token) :
    List.span.loop (· != Token.equals) (identifiers.map variableToken) accumulated =
      (accumulated.reverse ++ identifiers.map variableToken, []) := by
  induction identifiers generalizing accumulated with
  | nil => simp [List.span.loop]
  | cons identifier following induction =>
      simp only [List.map_cons, variableToken, List.span.loop, identifier_ne_equals]
      rw [induction (Token.identifier (variableName identifier) :: accumulated)]
      simp

private theorem span_variableTokens_end (identifiers : List VarId) :
    (identifiers.map variableToken).span (· != Token.equals) =
      (identifiers.map variableToken, []) := by
  simpa [List.span] using span_variableTokens_end_aux identifiers []

private theorem span_variableTokens_equals_aux (identifiers : List VarId)
    (rest accumulated : List Token) :
    List.span.loop (· != Token.equals)
        (identifiers.map variableToken ++ Token.equals :: rest) accumulated =
      (accumulated.reverse ++ identifiers.map variableToken, Token.equals :: rest) := by
  induction identifiers generalizing accumulated with
  | nil => simp [List.span.loop]
  | cons identifier following induction =>
      simp only [List.map_cons, List.cons_append, variableToken, List.span.loop,
        identifier_ne_equals]
      rw [induction (Token.identifier (variableName identifier) :: accumulated)]
      simp

private theorem span_variableTokens_equals (identifiers : List VarId) (rest : List Token) :
    (identifiers.map variableToken ++ Token.equals :: rest).span (· != Token.equals) =
      (identifiers.map variableToken, Token.equals :: rest) := by
  simpa [List.span] using span_variableTokens_equals_aux identifiers rest []

private theorem statementParts_icall_no_results (name : String) (args : List VarId) :
    statementParts
        (Token.identifier "icall" :: Token.label name :: args.map variableToken) =
      ([], Token.identifier "icall" :: Token.label name :: args.map variableToken) := by
  rw [statementParts]
  simp only [List.span, List.span.loop, identifier_ne_equals, label_ne_equals]
  rw [span_variableTokens_end_aux args [Token.label name, Token.identifier "icall"]]

private theorem statementParts_results (results : List VarId) (rest : List Token) :
    statementParts (results.map variableToken ++ Token.equals :: rest) =
      (results.map variableToken, rest) := by
  rw [statementParts, span_variableTokens_equals]

@[simp] private theorem word_ofNat_toNat (value : Word) :
    (.ofNat value.toNat : Word) = value := by
  calc
    (.ofNat value.toNat : Word) =
        Evm.UInt256.ofBitVec (BitVec.ofNat 256 value.toNat) := by
      have bound : value.toNat < 2 ^ 256 := value.toBitVec.isLt
      simp only [Evm.UInt256.ofNat, Evm.UInt256.ofBitVec, Evm.UInt256.mk.injEq]
      repeat' apply And.intro
      all_goals apply UInt32.toBitVec_inj.mp
      all_goals
        simp only [UInt32.toBitVec_ofNat', BitVec.extractLsb', BitVec.toNat_ofNat]
        norm_num at bound ⊢
        rw [Nat.mod_eq_of_lt bound]
    _ = Evm.UInt256.ofBitVec value.toBitVec := by
      change Evm.UInt256.ofBitVec (BitVec.ofNat 256 value.toBitVec.toNat) = _
      rw [BitVec.ofNat_toNat]
      simp
    _ = value := Evm.UInt256.ofBitVec_toBitVec value

private theorem parseStatement_assign_constant (functions : List String)
    (full prior : List VarId) (result : VarId) (value : Word)
    (isPrefix : prior ++ [result] <+: full) :
    (parseStatement functions
      (stmtTokens {
        functions := #[], initEntry := ⟨0⟩, mainEntry := none }
        (.assign result (.constant value)))).run (printedVariableNames prior) =
      .ok ([.assign (canonicalRename full result) (.constant value)],
        printedVariableNames (prior ++ [result])) := by
  simp [stmtTokens, definitionTokens, exprTokens, parseStatement, statementParts,
    variableTokens, variableToken, List.span, List.span.loop]
  simp only [StateT.run, bind, Except.bind]
  rw [show variableList [Token.identifier (variableName result)]
      (printedVariableNames prior) =
      .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
    simpa [canonicalRename] using variableList_printed full prior [result] isPrefix]
  simp [pure, StateT.pure, Except.pure]

@[simp] private theorem liftNumbers_variableTokens (identifiers : List VarId)
    (names : List String) :
    (liftNumbers (identifiers.map variableToken)).run names =
      .ok (([], identifiers.map variableToken), names) := by
  induction identifiers with
  | nil => simp [liftNumbers, StateT.run, pure, StateT.pure, Except.pure]
  | cons identifier following induction =>
      simp only [List.map_cons, liftNumbers, variableToken, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show liftNumbers (following.map variableToken) names =
          .ok (([], following.map variableToken), names) from induction]
      simp [pure, StateT.pure, Except.pure]

private theorem liftNumbers_icall (name : String) (identifiers : List VarId)
    (names : List String) :
    liftNumbers (Token.label name :: identifiers.map variableToken) names =
      .ok (([], Token.label name :: identifiers.map variableToken), names) := by
  simp only [liftNumbers, bind, StateT.bind, Except.bind]
  rw [show liftNumbers (identifiers.map variableToken) names =
      .ok (([], identifiers.map variableToken), names) from
    liftNumbers_variableTokens identifiers names]
  simp [pure, StateT.pure, Except.pure]

private theorem operand_printed (full prior : List VarId) (identifier : VarId)
    (isPrefix : prior ++ [identifier] <+: full) :
    (operand (variableToken identifier)).run (printedVariableNames prior) =
      .ok (([], canonicalRename full identifier),
        printedVariableNames (prior ++ [identifier])) := by
  simp only [operand, variableToken, StateT.run, bind, StateT.bind, Except.bind]
  rw [show internVariable (variableName identifier) (printedVariableNames prior) =
      .ok (canonicalRename full identifier,
        printedVariableNames (prior ++ [identifier])) from by
    simpa [canonicalRename] using internVariable_canonical full prior identifier isPrefix]
  simp [pure, StateT.pure, Except.pure]

private theorem operands_printed (full prior identifiers : List VarId)
    (isPrefix : prior ++ identifiers <+: full) :
    (operands (identifiers.map variableToken)).run (printedVariableNames prior) =
      .ok (([], identifiers.map (canonicalRename full) |>.toArray),
        printedVariableNames (prior ++ identifiers)) := by
  induction identifiers generalizing prior with
  | nil => simp [operands, StateT.run, pure, StateT.pure, Except.pure]
  | cons identifier following induction =>
      simp only [List.map_cons, operands, StateT.run, bind, StateT.bind, Except.bind]
      rw [show operand (variableToken identifier) (printedVariableNames prior) =
          .ok (([], canonicalRename full identifier),
            printedVariableNames (prior ++ [identifier])) from
        operand_printed full prior identifier
        ((show prior ++ [identifier] <+: prior ++ identifier :: following from
          ⟨following, by simp⟩).trans isPrefix)]
      simp only
      rw [show operands (following.map variableToken)
            (printedVariableNames (prior ++ [identifier])) =
          .ok (([], following.map (canonicalRename full) |>.toArray),
            printedVariableNames ((prior ++ [identifier]) ++ following)) from
        induction (prior ++ [identifier]) (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, List.append_assoc]

private theorem statementParts_definition (results : List VarId)
    (operandTokens : List Token)
    (headless : statementParts operandTokens = ([], operandTokens)) :
    statementParts (definitionTokens results.toArray ++ operandTokens) =
      (results.map variableToken, operandTokens) := by
  cases results with
  | nil => simpa [definitionTokens] using headless
  | cons head tail =>
      simpa [definitionTokens, variableTokens] using
        statementParts_results (head :: tail) operandTokens

private theorem parseStatement_printed_head (functions : List String)
    (full prior results : List VarId) (mnemonic : String) (parameters : List Token)
    (notConst : mnemonic ≠ "const")
    (headless : statementParts (Token.identifier mnemonic :: parameters) =
      ([], Token.identifier mnemonic :: parameters))
    (numberFree : liftNumbers parameters (printedVariableNames prior) =
      .ok (([], parameters), printedVariableNames prior))
    (isPrefix : prior ++ results <+: full) :
    (parseStatement functions
        (definitionTokens results.toArray ++ Token.identifier mnemonic :: parameters)).run
        (printedVariableNames prior) =
      (parseMnemonic functions
          (definitionTokens results.toArray ++ Token.identifier mnemonic :: parameters)
          mnemonic (results.map (canonicalRename full)) parameters).run
        (printedVariableNames (prior ++ results)) := by
  rw [parseStatement]
  simp only [statementParts_definition results (Token.identifier mnemonic :: parameters)
    headless]
  simp only [StateT.run, bind, StateT.bind, Except.bind]
  rw [numberFree]
  simp only []
  rw [show variableList (results.map variableToken) (printedVariableNames prior) =
      .ok ((results.map (canonicalRename full)).toArray,
        printedVariableNames (prior ++ results)) from by
    simpa [canonicalRename] using variableList_printed full prior results isPrefix]
  simp only []
  cases outcome : parseMnemonic functions
      (definitionTokens results.toArray ++ Token.identifier mnemonic :: parameters) mnemonic
      (results.map (canonicalRename full)) parameters
      (printedVariableNames (prior ++ results)) with
  | error message => rfl
  | ok pair => rfl

private theorem parseStatement_printed (program : Program) (printable : program.Printable)
    (full prior : List VarId) (statement : Stmt)
    (references : statement.FunctionReferencesInRange program.functions.size)
    (isPrefix : prior ++ statement.variableOccurrences <+: full) :
    (parseStatement (printedFunctionNames program) (stmtTokens program statement)).run
        (printedVariableNames prior) =
      .ok ([statement.renameVariables (canonicalRename full)],
        printedVariableNames (prior ++ statement.variableOccurrences)) := by
  cases statement with
  | assign result value =>
      cases value with
      | constant value =>
          simpa [Stmt.variableOccurrences, Stmt.renameVariables] using
            parseStatement_assign_constant (printedFunctionNames program) full prior result value
              isPrefix
      | var source =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences] at isPrefix ⊢
          rw [show stmtTokens program (.assign result (.var source)) =
              definitionTokens ([result] : List VarId).toArray ++
                Token.identifier "copy" :: [variableToken source] from rfl,
            parseStatement_printed_head (printedFunctionNames program) full prior [result]
              "copy" [variableToken source] (by decide)
              (by simp [statementParts, variableToken, List.span, List.span.loop])
              (by simpa using liftNumbers_variableTokens [source] (printedVariableNames prior))
              ((show prior ++ [result] <+: prior ++ [result, source] from
                ⟨[source], by simp⟩).trans isPrefix)]
          simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
            StateT.bind, Except.bind]
          rw [show operand (variableToken source) (printedVariableNames (prior ++ [result])) =
              .ok (([], canonicalRename full source),
                printedVariableNames (prior ++ [result] ++ [source])) from
            operand_printed full (prior ++ [result]) source
              (by simpa [List.append_assoc] using isPrefix)]
          simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, Expr.renameVariables,
            List.append_assoc]
      | add lhs rhs =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences] at isPrefix ⊢
          rw [show stmtTokens program (.assign result (.add lhs rhs)) =
              definitionTokens ([result] : List VarId).toArray ++
                Token.identifier "add" :: [variableToken lhs, variableToken rhs] from rfl,
            parseStatement_printed_head (printedFunctionNames program) full prior [result]
              "add" [variableToken lhs, variableToken rhs] (by decide)
              (by simp [statementParts, variableToken, List.span, List.span.loop])
              (by simpa using liftNumbers_variableTokens [lhs, rhs] (printedVariableNames prior))
              ((show prior ++ [result] <+: prior ++ [result, lhs, rhs] from
                ⟨[lhs, rhs], by simp⟩).trans isPrefix)]
          simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
            StateT.bind, Except.bind]
          rw [show operand (variableToken lhs) (printedVariableNames (prior ++ [result])) =
              .ok (([], canonicalRename full lhs),
                printedVariableNames (prior ++ [result] ++ [lhs])) from
            operand_printed full (prior ++ [result]) lhs
              (by simpa [List.append_assoc] using
                ((show prior ++ [result, lhs] <+: prior ++ [result, lhs, rhs] from
                  ⟨[rhs], by simp⟩).trans isPrefix))]
          simp only []
          rw [show operand (variableToken rhs)
              (printedVariableNames (prior ++ [result] ++ [lhs])) =
              .ok (([], canonicalRename full rhs),
                printedVariableNames (prior ++ [result] ++ [lhs] ++ [rhs])) from
            operand_printed full (prior ++ [result] ++ [lhs]) rhs
              (by simpa [List.append_assoc] using isPrefix)]
          simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, Expr.renameVariables,
            List.append_assoc]
      | lt lhs rhs =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences] at isPrefix ⊢
          rw [show stmtTokens program (.assign result (.lt lhs rhs)) =
              definitionTokens ([result] : List VarId).toArray ++
                Token.identifier "lt" :: [variableToken lhs, variableToken rhs] from rfl,
            parseStatement_printed_head (printedFunctionNames program) full prior [result]
              "lt" [variableToken lhs, variableToken rhs] (by decide)
              (by simp [statementParts, variableToken, List.span, List.span.loop])
              (by simpa using liftNumbers_variableTokens [lhs, rhs] (printedVariableNames prior))
              ((show prior ++ [result] <+: prior ++ [result, lhs, rhs] from
                ⟨[lhs, rhs], by simp⟩).trans isPrefix)]
          simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
            StateT.bind, Except.bind]
          rw [show operand (variableToken lhs) (printedVariableNames (prior ++ [result])) =
              .ok (([], canonicalRename full lhs),
                printedVariableNames (prior ++ [result] ++ [lhs])) from
            operand_printed full (prior ++ [result]) lhs
              (by simpa [List.append_assoc] using
                ((show prior ++ [result, lhs] <+: prior ++ [result, lhs, rhs] from
                  ⟨[rhs], by simp⟩).trans isPrefix))]
          simp only []
          rw [show operand (variableToken rhs)
              (printedVariableNames (prior ++ [result] ++ [lhs])) =
              .ok (([], canonicalRename full rhs),
                printedVariableNames (prior ++ [result] ++ [lhs] ++ [rhs])) from
            operand_printed full (prior ++ [result] ++ [lhs]) rhs
              (by simpa [List.append_assoc] using isPrefix)]
          simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, Expr.renameVariables,
            List.append_assoc]
      | sload key =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences] at isPrefix ⊢
          rw [show stmtTokens program (.assign result (.sload key)) =
              definitionTokens ([result] : List VarId).toArray ++
                Token.identifier "sload" :: [variableToken key] from rfl,
            parseStatement_printed_head (printedFunctionNames program) full prior [result]
              "sload" [variableToken key] (by decide)
              (by simp [statementParts, variableToken, List.span, List.span.loop])
              (by simpa using liftNumbers_variableTokens [key] (printedVariableNames prior))
              ((show prior ++ [result] <+: prior ++ [result, key] from
                ⟨[key], by simp⟩).trans isPrefix)]
          simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
            StateT.bind, Except.bind]
          rw [show operand (variableToken key) (printedVariableNames (prior ++ [result])) =
              .ok (([], canonicalRename full key),
                printedVariableNames (prior ++ [result] ++ [key])) from
            operand_printed full (prior ++ [result]) key
              (by simpa [List.append_assoc] using isPrefix)]
          simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, Expr.renameVariables,
            List.append_assoc]
  | sstore key value =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.sstore key value) =
          definitionTokens ([] : List VarId).toArray ++
            Token.identifier "sstore" :: [variableToken key, variableToken value] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [] "sstore"
          [variableToken key, variableToken value] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [key, value] (printedVariableNames prior))
          (by simpa using
            (show prior <+: prior ++ [key, value] from ⟨[key, value], rfl⟩).trans isPrefix)]
      simp only [List.map_nil, List.append_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken key) (printedVariableNames prior) =
          .ok (([], canonicalRename full key), printedVariableNames (prior ++ [key])) from
        operand_printed full prior key
          ((show prior ++ [key] <+: prior ++ [key, value] from
            ⟨[value], by simp⟩).trans isPrefix)]
      simp only []
      rw [show operand (variableToken value) (printedVariableNames (prior ++ [key])) =
          .ok (([], canonicalRename full value),
            printedVariableNames (prior ++ [key] ++ [value])) from
        operand_printed full (prior ++ [key]) value
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | gas result =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.gas result) =
          definitionTokens ([result] : List VarId).toArray ++
            Token.identifier "gas" :: [] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [result] "gas"
          [] (by decide) (by simp [statementParts, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [] (printedVariableNames prior))
          isPrefix]
      simp [List.map_cons, List.map_nil, parseMnemonic, StateT.run, pure, StateT.pure,
        Except.pure, Stmt.renameVariables]
  | call callData =>
      rcases callData with ⟨callee, gas, result⟩
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.call ⟨callee, gas, result⟩) =
          definitionTokens ([result] : List VarId).toArray ++
            Token.identifier "call" :: [variableToken gas, variableToken callee] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [result] "call"
          [variableToken gas, variableToken callee] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [gas, callee] (printedVariableNames prior))
          ((show prior ++ [result] <+: prior ++ [result, gas, callee] from
            ⟨[gas, callee], by simp⟩).trans isPrefix)]
      simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken gas) (printedVariableNames (prior ++ [result])) =
          .ok (([], canonicalRename full gas),
            printedVariableNames (prior ++ [result] ++ [gas])) from
        operand_printed full (prior ++ [result]) gas
          (by simpa [List.append_assoc] using
            ((show prior ++ [result, gas] <+: prior ++ [result, gas, callee] from
              ⟨[callee], by simp⟩).trans isPrefix))]
      simp only []
      rw [show operand (variableToken callee)
          (printedVariableNames (prior ++ [result] ++ [gas])) =
          .ok (([], canonicalRename full callee),
            printedVariableNames (prior ++ [result] ++ [gas] ++ [callee])) from
        operand_printed full (prior ++ [result] ++ [gas]) callee
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | malloc result size =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.malloc result size) =
          definitionTokens ([result] : List VarId).toArray ++
            Token.identifier "malloc" :: [variableToken size] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [result]
          "malloc" [variableToken size] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [size] (printedVariableNames prior))
          ((show prior ++ [result] <+: prior ++ [result, size] from
            ⟨[size], by simp⟩).trans isPrefix)]
      simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken size) (printedVariableNames (prior ++ [result])) =
          .ok (([], canonicalRename full size),
            printedVariableNames (prior ++ [result] ++ [size])) from
        operand_printed full (prior ++ [result]) size
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | mallocUninit result size =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.mallocUninit result size) =
          definitionTokens ([result] : List VarId).toArray ++
            Token.identifier "mallocany" :: [variableToken size] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [result]
          "mallocany" [variableToken size] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [size] (printedVariableNames prior))
          ((show prior ++ [result] <+: prior ++ [result, size] from
            ⟨[size], by simp⟩).trans isPrefix)]
      simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken size) (printedVariableNames (prior ++ [result])) =
          .ok (([], canonicalRename full size),
            printedVariableNames (prior ++ [result] ++ [size])) from
        operand_printed full (prior ++ [result]) size
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | mstore32 offset value =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.mstore32 offset value) =
          definitionTokens ([] : List VarId).toArray ++
            Token.identifier "mstore256" ::
              [variableToken offset, variableToken value] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [] "mstore256"
          [variableToken offset, variableToken value] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using
            liftNumbers_variableTokens [offset, value] (printedVariableNames prior))
          (by simpa using
            (show prior <+: prior ++ [offset, value] from
              ⟨[offset, value], rfl⟩).trans isPrefix)]
      simp only [List.map_nil, List.append_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken offset) (printedVariableNames prior) =
          .ok (([], canonicalRename full offset), printedVariableNames (prior ++ [offset])) from
        operand_printed full prior offset
          ((show prior ++ [offset] <+: prior ++ [offset, value] from
            ⟨[value], by simp⟩).trans isPrefix)]
      simp only []
      rw [show operand (variableToken value) (printedVariableNames (prior ++ [offset])) =
          .ok (([], canonicalRename full value),
            printedVariableNames (prior ++ [offset] ++ [value])) from
        operand_printed full (prior ++ [offset]) value
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | mload32 result offset =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      rw [show stmtTokens program (.mload32 result offset) =
          definitionTokens ([result] : List VarId).toArray ++
            Token.identifier "mload256" :: [variableToken offset] from rfl,
        parseStatement_printed_head (printedFunctionNames program) full prior [result]
          "mload256" [variableToken offset] (by decide)
          (by simp [statementParts, variableToken, List.span, List.span.loop])
          (by simpa using liftNumbers_variableTokens [offset] (printedVariableNames prior))
          ((show prior ++ [result] <+: prior ++ [result, offset] from
            ⟨[offset], by simp⟩).trans isPrefix)]
      simp only [List.map_cons, List.map_nil, parseMnemonic, StateT.run, bind,
        StateT.bind, Except.bind]
      rw [show operand (variableToken offset) (printedVariableNames (prior ++ [result])) =
          .ok (([], canonicalRename full offset),
            printedVariableNames (prior ++ [result] ++ [offset])) from
        operand_printed full (prior ++ [result]) offset
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, Stmt.renameVariables, List.append_assoc]
  | icall callee args dests =>
      rcases args with ⟨args⟩
      rcases dests with ⟨dests⟩
      simp only [Stmt.variableOccurrences,
        Stmt.FunctionReferencesInRange] at references isPrefix ⊢
      cases dests with
      | nil =>
          simp only [List.nil_append] at isPrefix ⊢
          rw [show stmtTokens program (.icall callee ⟨args⟩ ⟨[]⟩) =
              definitionTokens ([] : List VarId).toArray ++
                Token.identifier "icall" :: Token.label (functionName program callee) ::
                  args.map variableToken from rfl,
            parseStatement_printed_head (printedFunctionNames program) full prior [] "icall"
              (Token.label (functionName program callee) :: args.map variableToken)
              (by decide) (statementParts_icall_no_results _ args)
              (liftNumbers_icall (functionName program callee) args _)
              (by simpa using
                (show prior <+: prior ++ args from ⟨args, rfl⟩).trans isPrefix)]
          simp only [List.map_nil, List.append_nil, parseMnemonic, StateT.run, bind]
          rw [printedFunctionNames_findIdx program printable callee references]
          simp only [StateT.bind]
          rw [show operands (args.map variableToken) (printedVariableNames prior) =
              .ok (([], args.map (canonicalRename full) |>.toArray),
                printedVariableNames (prior ++ args)) from
            operands_printed full prior args isPrefix]
          simp [bind, Except.bind, pure, StateT.pure, Except.pure, Stmt.renameVariables]
      | cons destination following =>
          simp only [List.cons_append] at isPrefix ⊢
          rw [show stmtTokens program (.icall callee ⟨args⟩ ⟨destination :: following⟩) =
              definitionTokens (destination :: following : List VarId).toArray ++
                Token.identifier "icall" :: Token.label (functionName program callee) ::
                  args.map variableToken from by
              simp [stmtTokens, definitionTokens, variableTokens, List.append_assoc],
            parseStatement_printed_head (printedFunctionNames program) full prior
              (destination :: following) "icall"
              (Token.label (functionName program callee) :: args.map variableToken)
              (by decide) (statementParts_icall_no_results _ args)
              (liftNumbers_icall (functionName program callee) args _)
              ((show prior ++ (destination :: following) <+:
                  prior ++ (destination :: following) ++ args from ⟨args, by simp⟩).trans
                (by simpa [List.append_assoc] using isPrefix))]
          simp only [parseMnemonic, StateT.run, bind]
          rw [printedFunctionNames_findIdx program printable callee references]
          simp only [StateT.bind]
          rw [show operands (args.map variableToken)
                (printedVariableNames (prior ++ destination :: following)) =
              .ok (([], args.map (canonicalRename full) |>.toArray),
                printedVariableNames (prior ++ destination :: following ++ args)) from
            operands_printed full (prior ++ destination :: following) args
              (by simpa [List.append_assoc] using isPrefix)]
          simp [bind, Except.bind, pure, StateT.pure, Except.pure, List.append_assoc,
            Stmt.renameVariables]

private def printedBlockNames (function : Function) : List String :=
  function.blocks.toList.zipIdx.map fun pair => blockName ⟨pair.2⟩

private theorem printedBlockNames_length (function : Function) :
    (printedBlockNames function).length = function.blocks.size := by
  simp [printedBlockNames]

private theorem printedBlockNames_getElem (function : Function) (index : Nat)
    (bound : index < (printedBlockNames function).length) :
    (printedBlockNames function)[index] = blockName ⟨index⟩ := by
  simp [printedBlockNames]

private theorem printedBlockNames_findIdx (function : Function) (identifier : BlockId)
    (bound : identifier.id < function.blocks.size) :
    (printedBlockNames function).findIdx? (· == blockName identifier) =
      some identifier.id := by
  rw [List.findIdx?_eq_some_iff_findIdx_eq]
  have listBound : identifier.id < (printedBlockNames function).length := by
    simpa [printedBlockNames_length] using bound
  refine ⟨listBound, (List.findIdx_eq listBound).2 ⟨?_, ?_⟩⟩
  · simp [printedBlockNames_getElem]
  · intro index indexBound
    simp only [beq_eq_false_iff_ne]
    intro equality
    have nameEquality : blockName ⟨index⟩ = blockName identifier := by
      rw [← printedBlockNames_getElem function index (by omega)]
      exact equality
    have identifiersEqual : (⟨index⟩ : BlockId) = identifier := by
      cases identifier
      simp [blockName] at nameEquality ⊢
      exact nameEquality
    exact Nat.ne_of_lt indexBound (congrArg BlockId.id identifiersEqual)

private theorem parseTerminator_printed (function : Function) (full prior : List VarId)
    (terminator : Terminator)
    (references : terminator.BlockReferencesInRange function.blocks.size)
    (isPrefix : prior ++ terminator.variableOccurrences <+: full) :
    (parseTerminator (printedBlockNames function) (terminatorTokens terminator)).run
        (printedVariableNames prior) =
      .ok (terminator.renameVariables (canonicalRename full),
        printedVariableNames (prior ++ terminator.variableOccurrences)) := by
  cases terminator with
  | halt => simp [parseTerminator, terminatorTokens, Terminator.renameVariables,
      Terminator.variableOccurrences, StateT.run, pure, StateT.pure, Except.pure]
  | iret => simp [parseTerminator, terminatorTokens, Terminator.renameVariables,
      Terminator.variableOccurrences, StateT.run, pure, StateT.pure, Except.pure]
  | jump target =>
      simp only [Terminator.BlockReferencesInRange] at references
      simp [parseTerminator, terminatorTokens, resolveBlock, Terminator.renameVariables,
        Terminator.variableOccurrences, StateT.run, bind, StateT.bind, Except.bind]
      rw [printedBlockNames_findIdx function target references]
      simp [pure, StateT.pure, Except.pure]
  | branch condition thenTarget elseTarget =>
      rcases references with ⟨thenBound, elseBound⟩
      simp only [Terminator.variableOccurrences] at isPrefix ⊢
      simp [parseTerminator, terminatorTokens, resolveBlock, Terminator.renameVariables,
        variableToken, StateT.run, bind, StateT.bind, Except.bind]
      rw [show internVariable (variableName condition) (printedVariableNames prior) =
          .ok (canonicalRename full condition, printedVariableNames (prior ++ [condition])) from by
        simpa [canonicalRename] using
          internVariable_canonical full prior condition isPrefix]
      simp only
      rw [printedBlockNames_findIdx function thenTarget thenBound]
      simp only
      rw [printedBlockNames_findIdx function elseTarget elseBound]
      simp [pure, StateT.pure, Except.pure]

private theorem parseBlockBody_printed (program : Program) (printable : program.Printable)
    (function : Function) (full prior : List VarId) (statements : List Stmt)
    (terminator : Terminator)
    (statementReferences : ∀ statement ∈ statements,
      statement.FunctionReferencesInRange program.functions.size)
    (terminatorReferences : terminator.BlockReferencesInRange function.blocks.size)
    (isPrefix : prior ++ statements.flatMap Stmt.variableOccurrences ++
        terminator.variableOccurrences <+: full) :
    (parseBlockBody (printedFunctionNames program) (printedBlockNames function)
        (statements.map (stmtTokens program) ++ [terminatorTokens terminator])).run
        (printedVariableNames prior) =
      .ok (((statements.map (·.renameVariables (canonicalRename full))).toArray,
        terminator.renameVariables (canonicalRename full)),
        printedVariableNames (prior ++ statements.flatMap Stmt.variableOccurrences ++
          terminator.variableOccurrences)) := by
  induction statements generalizing prior with
  | nil =>
      simp only [List.map_nil, List.nil_append, List.flatMap_nil, List.nil_append] at isPrefix ⊢
      rw [parseBlockBody.eq_2]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show parseTerminator (printedBlockNames function) (terminatorTokens terminator)
            (printedVariableNames prior) =
          .ok (terminator.renameVariables (canonicalRename full),
            printedVariableNames (prior ++ terminator.variableOccurrences)) from
        parseTerminator_printed function full prior terminator terminatorReferences
          (by simpa using isPrefix)]
      simp [pure, StateT.pure, Except.pure]
  | cons statement following induction =>
      simp only [List.map_cons, List.cons_append, List.flatMap_cons] at isPrefix ⊢
      have isPrefix' : prior ++ statement.variableOccurrences ++
          following.flatMap Stmt.variableOccurrences ++ terminator.variableOccurrences <+:
          full := by
        simpa [List.append_assoc] using isPrefix
      rw [parseBlockBody.eq_3 _ _ _ _ (by simp)]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show parseStatement (printedFunctionNames program) (stmtTokens program statement)
            (printedVariableNames prior) =
          .ok ([statement.renameVariables (canonicalRename full)],
            printedVariableNames (prior ++ statement.variableOccurrences)) from
        parseStatement_printed program printable full prior statement
          (statementReferences statement (by simp))
          ((show prior ++ statement.variableOccurrences <+:
              prior ++ statement.variableOccurrences ++
                following.flatMap Stmt.variableOccurrences ++
                  terminator.variableOccurrences from
            ⟨following.flatMap Stmt.variableOccurrences ++ terminator.variableOccurrences,
              by simp [List.append_assoc]⟩).trans isPrefix')]
      simp only
      rw [show parseBlockBody (printedFunctionNames program) (printedBlockNames function)
            (following.map (stmtTokens program) ++ [terminatorTokens terminator])
            (printedVariableNames (prior ++ statement.variableOccurrences)) =
          .ok (((following.map (·.renameVariables (canonicalRename full))).toArray,
            terminator.renameVariables (canonicalRename full)),
            printedVariableNames ((prior ++ statement.variableOccurrences) ++
              following.flatMap Stmt.variableOccurrences ++ terminator.variableOccurrences)) from
        induction (prior ++ statement.variableOccurrences)
          (fun followingStatement member =>
            statementReferences followingStatement (by simp [member]))
          (by simpa [List.append_assoc] using isPrefix')]
      simp [pure, StateT.pure, Except.pure, List.append_assoc]

@[simp] private theorem variableToken_ne_arrow (identifier : VarId) :
    (variableToken identifier != Token.arrow) = true := by
  rfl

private theorem spanVariableTokensToEndAux (identifiers : List VarId)
    (accumulated : List Token) :
    List.span.loop (· != Token.arrow) (identifiers.map variableToken) accumulated =
      (accumulated.reverse ++ identifiers.map variableToken, []) := by
  induction identifiers generalizing accumulated with
  | nil => simp [List.span.loop]
  | cons identifier following induction =>
      simp only [List.map_cons, List.span.loop, variableToken_ne_arrow]
      rw [induction (variableToken identifier :: accumulated)]
      simp

private theorem spanVariableTokensToEnd (identifiers : List VarId) :
    (identifiers.map variableToken).span (· != Token.arrow) =
      (identifiers.map variableToken, []) := by
  simpa [List.span] using spanVariableTokensToEndAux identifiers []

private theorem spanVariableTokensToArrowAux (identifiers : List VarId)
    (rest accumulated : List Token) :
    List.span.loop (· != Token.arrow)
        (identifiers.map variableToken ++ Token.arrow :: rest) accumulated =
      (accumulated.reverse ++ identifiers.map variableToken, Token.arrow :: rest) := by
  induction identifiers generalizing accumulated with
  | nil => simp [List.span.loop]
  | cons identifier following induction =>
      simp only [List.map_cons, List.cons_append, List.span.loop, variableToken_ne_arrow]
      rw [induction (variableToken identifier :: accumulated)]
      simp

private theorem spanVariableTokensToArrow (identifiers : List VarId) (rest : List Token) :
    (identifiers.map variableToken ++ Token.arrow :: rest).span (· != Token.arrow) =
      (identifiers.map variableToken, Token.arrow :: rest) := by
  simpa [List.span] using spanVariableTokensToArrowAux identifiers rest []

private theorem parseBlockHeader_printed (full prior : List VarId) (identifier : BlockId)
    (block : Block)
    (isPrefix : prior ++ block.inputs.toList ++ block.outputs.toList <+: full) :
    (parseBlockHeader
      ([Token.identifier (blockName identifier)] ++ variableTokens block.inputs ++
        (if block.outputs.isEmpty then [] else
          Token.arrow :: variableTokens block.outputs) ++ [Token.leftBrace])).run
        (printedVariableNames prior) =
      .ok ((block.inputs.map (canonicalRename full),
        block.outputs.map (canonicalRename full)),
        printedVariableNames (prior ++ block.inputs.toList ++ block.outputs.toList)) := by
  rcases block with ⟨inputs, statements, terminator, outputs⟩
  rcases inputs with ⟨inputs⟩
  rcases outputs with ⟨outputs⟩
  cases outputs with
  | nil =>
    simp only [List.append_nil] at isPrefix ⊢
    simp [parseBlockHeader, variableTokens]
    rw [← List.span_eq_takeWhile_dropWhile, spanVariableTokensToEnd]
    simp only
    rw [show StateT.run (variableList (inputs.map variableToken))
          (printedVariableNames prior) =
        .ok (inputs.map (canonicalRename full) |>.toArray,
          printedVariableNames (prior ++ inputs)) from
      variableList_printed full prior inputs (by
        simpa using isPrefix)]
    simp [variableList, StateT.run, bind, pure, StateT.pure, Except.bind, Except.pure,
      Functor.map, Except.map]
  | cons output following =>
    simp only at isPrefix ⊢
    simp [parseBlockHeader, variableTokens]
    rw [← List.span_eq_takeWhile_dropWhile, spanVariableTokensToArrow]
    simp only
    rw [show StateT.run (variableList (inputs.map variableToken))
          (printedVariableNames prior) =
        .ok (inputs.map (canonicalRename full) |>.toArray,
          printedVariableNames (prior ++ inputs)) from
      variableList_printed full prior inputs
        ((show prior ++ inputs <+: prior ++ inputs ++ output :: following from
          ⟨output :: following, rfl⟩).trans isPrefix)]
    simp only [bind, Except.bind]
    rw [show StateT.run
          (variableList (variableToken output :: following.map variableToken))
          (printedVariableNames (prior ++ inputs)) =
        .ok ((output :: following).map (canonicalRename full) |>.toArray,
          printedVariableNames ((prior ++ inputs) ++ output :: following)) from by
      simpa [List.map_cons] using
        variableList_printed full (prior ++ inputs) (output :: following)
          (by simpa [List.append_assoc] using isPrefix)]
    simp [List.append_assoc]

private theorem parseBlock_printed (program : Program) (printable : program.Printable)
    (function : Function) (full prior : List VarId) (identifier : BlockId)
    (block : Block)
    (references : block.ReferencesInRange program.functions.size function.blocks.size)
    (isPrefix : prior ++ block.variableOccurrences <+: full) :
    (parseBlock (printedFunctionNames program) (printedBlockNames function)
      ([Token.identifier (blockName identifier)] ++ variableTokens block.inputs ++
        (if block.outputs.isEmpty then [] else
          Token.arrow :: variableTokens block.outputs) ++ [Token.leftBrace])
      (block.statements.toList.map (stmtTokens program) ++
        [terminatorTokens block.terminator])).run (printedVariableNames prior) =
      .ok (block.renameVariables (canonicalRename full),
        printedVariableNames (prior ++ block.variableOccurrences)) := by
  rcases references with ⟨statementReferences, terminatorReferences⟩
  simp only [parseBlock, StateT.run, bind, StateT.bind, Except.bind]
  rw [show parseBlockHeader
        ([Token.identifier (blockName identifier)] ++ variableTokens block.inputs ++
          (if block.outputs.isEmpty then [] else
            Token.arrow :: variableTokens block.outputs) ++ [Token.leftBrace])
        (printedVariableNames prior) =
      .ok ((block.inputs.map (canonicalRename full),
        block.outputs.map (canonicalRename full)),
        printedVariableNames
          (prior ++ block.inputs.toList ++ block.outputs.toList)) from
    parseBlockHeader_printed full prior identifier block
      ((show prior ++ block.inputs.toList ++ block.outputs.toList <+:
          prior ++ block.variableOccurrences from
        ⟨block.statements.toList.flatMap Stmt.variableOccurrences ++
            block.terminator.variableOccurrences,
          by simp [Block.variableOccurrences, List.append_assoc]⟩).trans isPrefix)]
  simp only
  rw [show parseBlockBody (printedFunctionNames program) (printedBlockNames function)
        (block.statements.toList.map (stmtTokens program) ++
          [terminatorTokens block.terminator])
        (printedVariableNames
          (prior ++ block.inputs.toList ++ block.outputs.toList)) =
      .ok (((block.statements.toList.map
          (·.renameVariables (canonicalRename full))).toArray,
        block.terminator.renameVariables (canonicalRename full)),
        printedVariableNames
          ((prior ++ block.inputs.toList ++ block.outputs.toList) ++
            block.statements.toList.flatMap Stmt.variableOccurrences ++
              block.terminator.variableOccurrences)) from
    parseBlockBody_printed program printable function full
      (prior ++ block.inputs.toList ++ block.outputs.toList) block.statements.toList
      block.terminator
      (fun statement member => statementReferences statement (by simpa using member))
      terminatorReferences (by
        simpa [Block.variableOccurrences, List.append_assoc] using isPrefix)]
  have statementMap :
      (block.statements.toList.map
          (·.renameVariables (canonicalRename full))).toArray =
        block.statements.map (·.renameVariables (canonicalRename full)) := by
    cases block.statements
    simp
  rw [statementMap]
  simp [Block.renameVariables, Block.variableOccurrences, pure, StateT.pure, Except.pure,
    List.append_assoc]

private def printedBlockHeader (identifier : BlockId) (block : Block) : Line :=
  [Token.identifier (blockName identifier)] ++ variableTokens block.inputs ++
    (if block.outputs.isEmpty then [] else
      Token.arrow :: variableTokens block.outputs) ++ [Token.leftBrace]

private def printedBlockBody (program : Program) (block : Block) : List Line :=
  block.statements.toList.map (stmtTokens program) ++
    [terminatorTokens block.terminator]

private def printedBlockGroups (program : Program) (function : Function) :
    List (Line × List Line) :=
  function.blocks.toList.zipIdx.map fun pair =>
    (printedBlockHeader ⟨pair.2⟩ pair.1, printedBlockBody program pair.1)

private theorem blockLines_eq (program : Program) (identifier : BlockId)
    (block : Block) :
    blockLines program identifier block =
      printedBlockHeader identifier block ::
        printedBlockBody program block ++ [[Token.rightBrace]] := by
  simp [blockLines, printedBlockHeader, printedBlockBody]

private theorem printedBlockHeader_isHeader (identifier : BlockId) (block : Block) :
    isBlockHeader (printedBlockHeader identifier block) = true := by
  rw [show printedBlockHeader identifier block =
      ([Token.identifier (blockName identifier)] ++ variableTokens block.inputs ++
        (if block.outputs.isEmpty then [] else
          Token.arrow :: variableTokens block.outputs)) ++ [Token.leftBrace] by
    simp [printedBlockHeader, List.append_assoc]]
  unfold isBlockHeader
  rw [List.getLast?_append]
  rfl

private theorem printedBlockBody_ne_rightBrace (program : Program) (block : Block) :
    ∀ line ∈ printedBlockBody program block, line ≠ [Token.rightBrace] := by
  intro line member
  simp only [printedBlockBody, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨statement, _, rfl⟩ | rfl
  · cases statement with
    | assign _ value =>
        cases value <;> simp [stmtTokens, definitionTokens, variableTokens, variableToken]
    | icall callee args dests =>
        rcases dests with ⟨dests⟩
        cases dests <;> simp [stmtTokens, definitionTokens, variableTokens, variableToken]
    | sstore | gas | call | malloc | mallocUninit | mstore32 | mload32 =>
        simp [stmtTokens, definitionTokens, variableTokens, variableToken]
  · cases block.terminator <;> simp [terminatorTokens]

private theorem splitBlocksAux_body (groups : List (Line × List Line))
    (header : Line) (accumulated body rest : List Line)
    (notRightBrace : ∀ line ∈ body, line ≠ [Token.rightBrace]) :
    splitBlocksAux ((header, accumulated) :: groups) true
        (body ++ [Token.rightBrace] :: rest) =
      splitBlocksAux ((header, body.reverse ++ accumulated) :: groups) false rest := by
  induction body generalizing accumulated with
  | nil => simp [splitBlocksAux]
  | cons line following induction =>
      rw [List.cons_append, splitBlocksAux.eq_def]
      simp only
      rw [show (line == [Token.rightBrace]) = false by
        simp [notRightBrace line (by simp)]]
      simp only [Bool.false_eq_true, if_false]
      rw [induction (line :: accumulated)]
      · simp
      · intro next member
        exact notRightBrace next (by simp [member])

private theorem splitBlocksAux_functionBodyLines (program : Program) (function : Function)
    (groupsPrefix : List (Line × List Line)) :
    splitBlocksAux groupsPrefix false (functionBodyLines program function) =
      .ok (groupsPrefix.reverse.map (fun group => (group.fst, group.snd.reverse)) ++
        printedBlockGroups program function) := by
  rw [functionBodyLines, printedBlockGroups]
  generalize valuesEq : function.blocks.toList.zipIdx = values
  clear valuesEq
  induction values generalizing groupsPrefix with
  | nil => simp [splitBlocksAux]
  | cons pair following induction =>
      rcases pair with ⟨block, index⟩
      simp only [List.flatMap_cons, List.map_cons]
      rw [blockLines_eq]
      rw [show printedBlockHeader ⟨index⟩ block ::
            printedBlockBody program block ++ [[Token.rightBrace]] ++
              following.flatMap (fun pair => blockLines program ⟨pair.2⟩ pair.1) =
          printedBlockHeader ⟨index⟩ block ::
            (printedBlockBody program block ++ [Token.rightBrace] ::
              following.flatMap (fun pair => blockLines program ⟨pair.2⟩ pair.1)) by
        simp [List.append_assoc]]
      rw [splitBlocksAux.eq_def]
      simp only [Bool.false_eq_true, if_false]
      rw [if_pos (printedBlockHeader_isHeader ⟨index⟩ block)]
      rw [splitBlocksAux_body groupsPrefix (printedBlockHeader ⟨index⟩ block) []
        (printedBlockBody program block)
        (following.flatMap fun pair => blockLines program ⟨pair.2⟩ pair.1)
        (printedBlockBody_ne_rightBrace program block)]
      rw [induction]
      simp

private theorem splitBlocks_functionBodyLines (program : Program) (function : Function) :
    splitBlocks (functionBodyLines program function) =
      .ok (printedBlockGroups program function) := by
  rw [splitBlocks, splitBlocksAux_functionBodyLines]
  rfl

private theorem hasDuplicates_blockNames (identifiers : List Nat)
    (nodup : identifiers.Nodup) :
    hasDuplicates (identifiers.map fun identifier => blockName ⟨identifier⟩) = false := by
  induction identifiers with
  | nil => rfl
  | cons identifier following induction =>
      simp only [List.nodup_cons] at nodup
      have notMember : blockName ⟨identifier⟩ ∉
          following.map fun followingIdentifier => blockName ⟨followingIdentifier⟩ := by
        simpa [blockName] using nodup.1
      have notContained :
          (following.map fun followingIdentifier =>
            blockName ⟨followingIdentifier⟩).contains (blockName ⟨identifier⟩) = false := by
        cases contained : (following.map fun followingIdentifier =>
            blockName ⟨followingIdentifier⟩).contains (blockName ⟨identifier⟩) with
        | false => rfl
        | true => exact False.elim (notMember (List.contains_iff_mem.mp contained))
      rw [List.map_cons, hasDuplicates.eq_def]
      simp only
      rw [notContained, induction nodup.2]
      rfl

private theorem printedBlockNames_noDuplicates (function : Function) :
    hasDuplicates (printedBlockNames function) = false := by
  rw [printedBlockNames]
  rw [show (function.blocks.toList.zipIdx.map fun pair => blockName ⟨pair.2⟩) =
      (function.blocks.toList.zipIdx.map Prod.snd).map fun identifier =>
        blockName ⟨identifier⟩ by
    rw [List.map_map]
    rfl]
  rw [show function.blocks.toList.zipIdx.map Prod.snd =
      List.range' 0 function.blocks.toList.length by simp]
  apply hasDuplicates_blockNames
  exact List.nodup_range'

private theorem mapM_blockHeaderName_printedBlockGroups (program : Program)
    (function : Function) :
    (printedBlockGroups program function).mapM (fun group => blockHeaderName group.fst) =
      .ok (printedBlockNames function) := by
  rw [printedBlockGroups, printedBlockNames]
  generalize valuesEq : function.blocks.toList.zipIdx = values
  clear valuesEq
  induction values with
  | nil => rfl
  | cons pair following induction =>
      rcases pair with ⟨block, index⟩
      simp only [List.map_cons, List.mapM_cons]
      rw [show blockHeaderName (printedBlockHeader ⟨index⟩ block) =
          .ok (blockName ⟨index⟩) by
        simp [blockHeaderName, printedBlockHeader]]
      simp [induction, bind, Except.bind, pure, Except.pure]

private theorem mapM_parseBlock_printed (program : Program) (printable : program.Printable)
    (function : Function) (full prior : List VarId)
    (values : List (Block × Nat))
    (references : ∀ pair ∈ values,
      pair.1.ReferencesInRange program.functions.size function.blocks.size)
    (isPrefix : prior ++ values.flatMap (fun pair => pair.1.variableOccurrences) <+:
      full) :
    ((values.map fun pair =>
        (printedBlockHeader ⟨pair.2⟩ pair.1, printedBlockBody program pair.1)).mapM
      (fun group => parseBlock (printedFunctionNames program) (printedBlockNames function)
        group.fst group.snd)).run (printedVariableNames prior) =
      .ok (values.map (fun pair =>
          pair.1.renameVariables (canonicalRename full)),
        printedVariableNames
          (prior ++ values.flatMap (fun pair => pair.1.variableOccurrences))) := by
  induction values generalizing prior with
  | nil => simp [StateT.run, pure, StateT.pure, Except.pure]
  | cons pair following induction =>
      rcases pair with ⟨block, index⟩
      simp only [List.map_cons, List.mapM_cons, List.flatMap_cons]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show parseBlock (printedFunctionNames program) (printedBlockNames function)
            (printedBlockHeader ⟨index⟩ block) (printedBlockBody program block)
            (printedVariableNames prior) =
          .ok (block.renameVariables (canonicalRename full),
            printedVariableNames (prior ++ block.variableOccurrences)) from by
        simpa [printedBlockHeader, printedBlockBody] using
          parseBlock_printed program printable function full prior ⟨index⟩ block
            (references (block, index) (by simp))
            ((show prior ++ block.variableOccurrences <+:
                prior ++ block.variableOccurrences ++
                  following.flatMap (fun pair => pair.1.variableOccurrences) from
              ⟨following.flatMap (fun pair => pair.1.variableOccurrences), rfl⟩).trans
                (by simpa [List.append_assoc] using isPrefix))]
      simp only
      rw [show ((following.map fun pair =>
            (printedBlockHeader ⟨pair.2⟩ pair.1,
              printedBlockBody program pair.1)).mapM
            (fun group => parseBlock (printedFunctionNames program)
              (printedBlockNames function) group.fst group.snd))
            (printedVariableNames (prior ++ block.variableOccurrences)) =
          .ok (following.map (fun pair =>
              pair.1.renameVariables (canonicalRename full)),
            printedVariableNames ((prior ++ block.variableOccurrences) ++
              following.flatMap (fun pair => pair.1.variableOccurrences))) from
        induction (prior ++ block.variableOccurrences)
          (fun followingPair member => references followingPair (by simp [member]))
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, List.append_assoc]

private theorem parseFunctionGroups_printed (program : Program)
    (printable : program.Printable) (function : Function)
    (functionPrintable : function.Printable program.functions.size)
    (full prior : List VarId)
    (isPrefix : prior ++ function.variableOccurrences <+: full) :
    (parseFunctionGroups (printedFunctionNames program)
      (printedBlockGroups program function)).run (printedVariableNames prior) =
      .ok (function.renameVariables (canonicalRename full),
        printedVariableNames (prior ++ function.variableOccurrences)) := by
  rcases functionPrintable with ⟨entryZero, references⟩
  simp only [parseFunctionGroups, StateT.run, bind, StateT.bind, Except.bind]
  rw [mapM_blockHeaderName_printedBlockGroups program function]
  simp only [bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, Except.bind]
  simp only [pure, Except.pure]
  rw [printedBlockNames_noDuplicates function]
  simp only [Bool.false_eq_true, if_false]
  simp only [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind]
  rw [show ((printedBlockGroups program function).mapM fun group =>
        parseBlock (printedFunctionNames program) (printedBlockNames function)
          group.fst group.snd) (printedVariableNames prior) =
      .ok (function.blocks.toList.zipIdx.map (fun pair =>
          pair.1.renameVariables (canonicalRename full)),
        printedVariableNames (prior ++ function.blocks.toList.zipIdx.flatMap
          (fun pair => pair.1.variableOccurrences))) from by
    simpa [printedBlockGroups] using
      mapM_parseBlock_printed program printable function full prior
        function.blocks.toList.zipIdx
        (fun pair member => references pair.1 (by
          have : pair.1 ∈ function.blocks.toList := by
            exact List.fst_mem_of_mem_zipIdx member
          simpa using this))
        (by
          have occurrencesEq :
              function.blocks.toList.zipIdx.flatMap
                  (fun pair => pair.1.variableOccurrences) =
                function.blocks.toList.flatMap Block.variableOccurrences := by
            rw [← List.flatMap_map, List.zipIdx_map_fst]
          simpa [Function.variableOccurrences, occurrencesEq] using isPrefix)]
  have parsedBlocksEq :
      function.blocks.toList.zipIdx.map (fun pair =>
          pair.1.renameVariables (canonicalRename full)) =
        function.blocks.toList.map
          (·.renameVariables (canonicalRename full)) := by
    rw [show function.blocks.toList.zipIdx.map (fun pair =>
          pair.1.renameVariables (canonicalRename full)) =
        (function.blocks.toList.zipIdx.map Prod.fst).map
          (·.renameVariables (canonicalRename full)) by
      rw [List.map_map]
      rfl]
    rw [List.zipIdx_map_fst]
  have occurrencesEq :
      function.blocks.toList.zipIdx.flatMap (fun pair => pair.1.variableOccurrences) =
        function.blocks.toList.flatMap Block.variableOccurrences := by
    rw [← List.flatMap_map, List.zipIdx_map_fst]
  rw [parsedBlocksEq, occurrencesEq]
  have blockMap :
      (function.blocks.toList.map
          (·.renameVariables (canonicalRename full))).toArray =
        function.blocks.map (·.renameVariables (canonicalRename full)) := by
    cases function.blocks
    simp
  simp [Function.renameVariables, Function.variableOccurrences, entryZero, blockMap]

private theorem parseFunction_printed (program : Program) (printable : program.Printable)
    (function : Function) (functionPrintable : function.Printable program.functions.size)
    (full prior : List VarId)
    (isPrefix : prior ++ function.variableOccurrences <+: full) :
    (parseFunction (printedFunctionNames program)
      (functionBodyLines program function)).run (printedVariableNames prior) =
      .ok (function.renameVariables (canonicalRename full),
        printedVariableNames (prior ++ function.variableOccurrences)) := by
  rw [parseFunction, splitBlocks_functionBodyLines]
  exact parseFunctionGroups_printed program printable function functionPrintable full prior isPrefix

private theorem hasDuplicates_eq_false_of_nodup (names : List String)
    (nodup : names.Nodup) : hasDuplicates names = false := by
  induction names with
  | nil => rfl
  | cons name following induction =>
      simp only [List.nodup_cons] at nodup
      have notContained : following.contains name = false := by
        cases contained : following.contains name with
        | false => rfl
        | true => exact False.elim (nodup.1 (List.contains_iff_mem.mp contained))
      rw [hasDuplicates.eq_def]
      simp only
      rw [notContained, induction nodup.2]
      rfl

private theorem printedFunctionNames_noDuplicates (program : Program)
    (printable : program.Printable) :
    hasDuplicates (printedFunctionNames program) = false := by
  apply hasDuplicates_eq_false_of_nodup
  rw [printedFunctionNames_eq]
  rw [show (program.functions.toList.zipIdx.map fun pair =>
        functionName program ⟨pair.2⟩) =
      (program.functions.toList.zipIdx.map Prod.snd).map fun identifier =>
        functionName program ⟨identifier⟩ by
    rw [List.map_map]
    rfl]
  rw [show program.functions.toList.zipIdx.map Prod.snd =
      List.range' 0 program.functions.toList.length by simp]
  apply List.Nodup.map_on
  · intro left leftMember right rightMember equality
    apply congrArg FunctionId.id
    apply functionName_injective printable
    · rcases List.mem_range'.mp leftMember with ⟨index, bound, equality⟩
      simpa [equality] using bound
    · rcases List.mem_range'.mp rightMember with ⟨index, bound, equality⟩
      simpa [equality] using bound
    · exact equality
  · exact List.nodup_range'

private theorem mapM_parseFunction_printed (program : Program)
    (printable : program.Printable) (full prior : List VarId)
    (values : List (Function × Nat))
    (functionPrintables : ∀ pair ∈ values,
      pair.1.Printable program.functions.size)
    (isPrefix : prior ++ values.flatMap (fun pair => pair.1.variableOccurrences) <+:
      full) :
    ((values.map fun pair =>
        (functionName program ⟨pair.2⟩, functionBodyLines program pair.1)).mapM
      (fun group => parseFunction (printedFunctionNames program) group.snd)).run
        (printedVariableNames prior) =
      .ok (values.map (fun pair =>
          pair.1.renameVariables (canonicalRename full)),
        printedVariableNames
          (prior ++ values.flatMap (fun pair => pair.1.variableOccurrences))) := by
  induction values generalizing prior with
  | nil => simp [StateT.run, pure, StateT.pure, Except.pure]
  | cons pair following induction =>
      rcases pair with ⟨function, index⟩
      simp only [List.map_cons, List.mapM_cons, List.flatMap_cons]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show parseFunction (printedFunctionNames program)
            (functionBodyLines program function) (printedVariableNames prior) =
          .ok (function.renameVariables (canonicalRename full),
            printedVariableNames (prior ++ function.variableOccurrences)) from
        parseFunction_printed program printable function
          (functionPrintables (function, index) (by simp)) full prior
          ((show prior ++ function.variableOccurrences <+:
              prior ++ function.variableOccurrences ++
                following.flatMap (fun pair => pair.1.variableOccurrences) from
            ⟨following.flatMap (fun pair => pair.1.variableOccurrences), rfl⟩).trans
              (by simpa [List.append_assoc] using isPrefix))]
      simp only
      rw [show ((following.map fun pair =>
            (functionName program ⟨pair.2⟩, functionBodyLines program pair.1)).mapM
          (fun group => parseFunction (printedFunctionNames program) group.snd))
          (printedVariableNames (prior ++ function.variableOccurrences)) =
        .ok (following.map (fun pair =>
            pair.1.renameVariables (canonicalRename full)),
          printedVariableNames ((prior ++ function.variableOccurrences) ++
            following.flatMap (fun pair => pair.1.variableOccurrences))) from
        induction (prior ++ function.variableOccurrences)
          (fun followingPair member => functionPrintables followingPair (by simp [member]))
          (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, List.append_assoc]

private theorem parseFunctionGroupsList_printed (program : Program)
    (printable : program.Printable) :
    (parseFunctionGroupsList (printedFunctionNames program)
      (printedFunctionGroups program)).run [] =
      .ok (program.functions.toList.map
          (·.renameVariables (canonicalRename program.variableOccurrences)),
        printedVariableNames program.variableOccurrences) := by
  rw [parseFunctionGroupsList]
  have occurrencesEq :
      program.functions.toList.zipIdx.flatMap (fun pair => pair.1.variableOccurrences) =
        program.variableOccurrences := by
    rw [← List.flatMap_map, List.zipIdx_map_fst]
    rfl
  have parsed := mapM_parseFunction_printed program printable
    program.variableOccurrences [] program.functions.toList.zipIdx
    (fun pair member => printable.2.2 pair.1 (by
      have : pair.1 ∈ program.functions.toList := List.fst_mem_of_mem_zipIdx member
      simpa using this))
    (by simp [occurrencesEq])
  have parsedFunctionsEq :
      program.functions.toList.zipIdx.map (fun pair =>
          pair.1.renameVariables (canonicalRename program.variableOccurrences)) =
        program.functions.toList.map
          (·.renameVariables (canonicalRename program.variableOccurrences)) := by
    rw [show program.functions.toList.zipIdx.map (fun pair =>
          pair.1.renameVariables (canonicalRename program.variableOccurrences)) =
        (program.functions.toList.zipIdx.map Prod.fst).map
          (·.renameVariables (canonicalRename program.variableOccurrences)) by
      rw [List.map_map]
      rfl]
    rw [List.zipIdx_map_fst]
  simpa [printedFunctionGroups, printedFunctionNames, parsedFunctionsEq,
    occurrencesEq] using parsed

private theorem printedFunctionNames_main_findIdx (program : Program)
    (printable : program.Printable) :
    (printedFunctionNames program).findIdx? (· == "main") =
      program.mainEntry.map FunctionId.id := by
  cases mainEq : program.mainEntry with
  | none =>
      simp only [Option.map_none]
      rw [List.findIdx?_eq_none_iff]
      intro name member
      simp only [printedFunctionNames_eq, List.mem_map] at member
      rcases member with ⟨pair, _, rfl⟩
      by_cases isInit : (⟨pair.2⟩ : FunctionId) = program.initEntry
      · simp [functionName, isInit]
      · simp [functionName, mainEq, isInit]
  | some mainEntry =>
      have mainValid := printable.2.1
      simp [mainEq] at mainValid
      have bound : mainEntry.id < program.functions.size := by
        exact mainValid.1
      have nameEq : functionName program mainEntry = "main" := by
        simp [functionName, mainEq, mainValid.2]
      simp only [Option.map_some]
      rw [← nameEq]
      exact printedFunctionNames_findIdx program printable mainEntry bound

private theorem parseProgramGroups_printed (program : Program)
    (printable : program.Printable) :
    parseProgramGroups (printedFunctionGroups program) =
      .ok (program.canonicalize) := by
  rw [parseProgramGroups]
  rw [show (printedFunctionGroups program).map Prod.fst =
      printedFunctionNames program by rfl]
  rw [printedFunctionNames_noDuplicates program printable]
  simp only [Bool.false_eq_true, if_false]
  rw [show (parseFunctionGroupsList (printedFunctionNames program)
      (printedFunctionGroups program)).run [] =
      .ok (program.functions.toList.map
          (·.renameVariables (canonicalRename program.variableOccurrences)),
        printedVariableNames program.variableOccurrences) from
    parseFunctionGroupsList_printed program printable]
  simp only [bind, Except.bind]
  rw [printedFunctionNames_init_findIdx program printable]
  simp only [printedFunctionNames_main_findIdx program printable]
  have functionMap :
      (program.functions.toList.map
          (·.renameVariables (canonicalRename program.variableOccurrences))).toArray =
        program.functions.map
          (·.renameVariables (canonicalRename program.variableOccurrences)) := by
    cases program.functions
    simp
  have renameEq : canonicalRename program.variableOccurrences =
      program.canonicalVariable := by
    funext identifier
    rfl
  rw [renameEq] at functionMap ⊢
  rw [functionMap]
  cases mainEq : program.mainEntry with
  | none => simp [Program.canonicalize, Program.renameVariables, mainEq, pure, Except.pure]
  | some mainEntry =>
      cases mainEntry
      simp [Program.canonicalize, Program.renameVariables, mainEq, pure, Except.pure]

private theorem parseTokens_programTokens (program : Program)
    (printable : program.Printable) :
    parseTokens (programTokens program) = .ok program.canonicalize := by
  rw [parseTokens, splitLines_programTokens, splitFunctions_programLines]
  exact parseProgramGroups_printed program printable

namespace Proofs

theorem parse_print_canonicalize {program : Program}
    (printable : program.Printable) :
    parse (print program) = .ok program.canonicalize := by
  rw [parse, tokenize_print]
  exact parseTokens_programTokens program printable

theorem parse_print {source : String} {program : Program}
    (parsed : parse source = .ok program) :
    parse (print program) = .ok program := by
  rw [parse_print_canonicalize (parse_printable parsed), parse_canonical parsed]

theorem parse_print_alphaEquiv {program parsedProgram : Program}
    (printable : program.Printable)
    (parsed : parse (print program) = .ok parsedProgram) :
    parsedProgram.AlphaEquiv program := by
  have canonicalized : parsedProgram = program.canonicalize :=
    Except.ok.inj (parsed.symm.trans (parse_print_canonicalize printable))
  rw [canonicalized]
  exact Vars.Proofs.Program.canonicalize_alphaEquiv program

end Proofs
end Sir.Vars.Text
