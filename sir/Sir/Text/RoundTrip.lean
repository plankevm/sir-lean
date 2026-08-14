import Sir.Text.Witness
import Sir.Text.PrintLex
import Sir.Text.ParsePrintable
import Sir.Examples.Jump
import Sir.Examples.Memory
import Sir.Examples.HaltedCall

namespace Sir.Vars.Text

open Sir.Examples

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
        simp [stmtTokens, definitionTokens, exprTokens, variableTokens, variableToken]
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
    (leftBound : left.id < program.functions.size)
    (rightBound : right.id < program.functions.size)
    (equality : functionName program left = functionName program right) :
    left = right := by
  rcases printable with ⟨initBound, mainValid, functionsValid⟩
  cases mainEq : program.mainEntry with
  | none =>
      by_cases leftInit : left = program.initEntry <;>
        by_cases rightInit : right = program.initEntry <;>
        simp_all [functionName, eq_comm] <;>
        cases left <;> cases right <;> simp_all
  | some mainEntry =>
      simp [mainEq] at mainValid
      by_cases leftInit : left = program.initEntry <;>
        by_cases rightInit : right = program.initEntry <;>
        by_cases leftMain : left = mainEntry <;>
        by_cases rightMain : right = mainEntry <;>
        simp_all [functionName, eq_comm] <;>
        cases left <;> cases right <;> simp_all

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
  simp [Function.comp_def]

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
  simp only [internVariable, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure,
    Except.pure, Except.bind]
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
    simp [StateT.run, bind, StateT.bind, set, StateT.set, pure, StateT.pure,
      Except.pure, Except.bind]
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
    simp [StateT.run, bind, StateT.bind, set, StateT.set, pure, StateT.pure,
      Except.pure, Except.bind, printedVariableNames,
      List.idxOf_eq_length eraseNotMember]

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
    simp [List.idxOf_append, List.mem_eraseDups.mpr member]
  · have eraseNotMember : identifier ∉ prior.eraseDups := by simpa using member
    rw [List.eraseDups_append, singleton_removeAll_eq_self member,
      List.eraseDups_cons]
    simp [List.idxOf_append, eraseNotMember, List.idxOf_eq_length eraseNotMember]

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
      simp [StateT.run, pure, StateT.pure, Except.pure, List.append_assoc]

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
      simp only [List.map_cons, variableToken, List.span.loop, identifier_ne_equals,
        if_true]
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
        identifier_ne_equals, if_true]
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
  simp only [List.span, List.span.loop, identifier_ne_equals, label_ne_equals, if_true]
  rw [span_variableTokens_end_aux args [Token.label name, Token.identifier "icall"]]

private theorem statementParts_icall_results (results args : List VarId) (name : String)
    (_nonempty : results ≠ []) :
    statementParts
        (results.map variableToken ++ Token.equals ::
          Token.identifier "icall" :: Token.label name :: args.map variableToken) =
      (results.map variableToken,
        Token.identifier "icall" :: Token.label name :: args.map variableToken) := by
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
  simp only [StateT.run, bind, StateT.bind, Except.bind]
  rw [show variableList [Token.identifier (variableName result)]
      (printedVariableNames prior) =
      .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
    simpa [canonicalRename] using variableList_printed full prior [result] isPrefix]
  simp [StateT.run, pure, StateT.pure, Except.pure]

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
  simp only [liftNumbers, StateT.run, bind, StateT.bind, Except.bind]
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
      simp only [Except.bind]
      rw [show operands (following.map variableToken)
            (printedVariableNames (prior ++ [identifier])) =
          .ok (([], following.map (canonicalRename full) |>.toArray),
            printedVariableNames ((prior ++ [identifier]) ++ following)) from
        induction (prior ++ [identifier]) (by simpa [List.append_assoc] using isPrefix)]
      simp [pure, StateT.pure, Except.pure, List.append_assoc]

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
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences, List.cons_append,
            List.nil_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, exprTokens, parseStatement, statementParts,
            variableTokens, variableToken, List.span, List.span.loop, Stmt.renameVariables,
            Expr.renameVariables]
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers [Token.identifier (variableName source)]
                (printedVariableNames prior) =
              .ok (([], [Token.identifier (variableName source)]),
                printedVariableNames prior) from by
            simpa [variableToken] using liftNumbers_variableTokens [source]
              (printedVariableNames prior)]
          simp only [Except.bind]
          rw [show variableList [Token.identifier (variableName result)]
              (printedVariableNames prior) =
                .ok (#[canonicalRename full result],
                  printedVariableNames (prior ++ [result])) from by
            simpa [canonicalRename] using variableList_printed full prior [result]
              ((show prior ++ [result] <+: prior ++ [result, source] from
                ⟨[source], by simp⟩).trans isPrefix)]
          simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
          rw [show internVariable (variableName source)
              (printedVariableNames (prior ++ [result])) =
                .ok (canonicalRename full source,
                  printedVariableNames (prior ++ [result, source])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result]) source (by
                simpa [List.append_assoc] using isPrefix)]
          simp [StateT.run, pure, StateT.pure, Except.pure, List.append_assoc]
      | add lhs rhs =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences, List.cons_append,
            List.nil_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, exprTokens, parseStatement, statementParts,
            variableTokens, variableToken, List.span, List.span.loop, Stmt.renameVariables,
            Expr.renameVariables]
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers
                [Token.identifier (variableName lhs), Token.identifier (variableName rhs)]
                (printedVariableNames prior) =
              .ok (([], [Token.identifier (variableName lhs),
                  Token.identifier (variableName rhs)]), printedVariableNames prior) from by
            simpa [variableToken] using liftNumbers_variableTokens [lhs, rhs]
              (printedVariableNames prior)]
          simp only [Except.bind]
          rw [show variableList [Token.identifier (variableName result)]
              (printedVariableNames prior) =
                .ok (#[canonicalRename full result],
                  printedVariableNames (prior ++ [result])) from by
            simpa [canonicalRename] using variableList_printed full prior [result]
              ((show prior ++ [result] <+: prior ++ [result, lhs, rhs] from
                ⟨[lhs, rhs], by simp⟩).trans isPrefix)]
          simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
          rw [show internVariable (variableName lhs)
              (printedVariableNames (prior ++ [result])) =
                .ok (canonicalRename full lhs,
                  printedVariableNames (prior ++ [result, lhs])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result]) lhs (by
                simpa [List.append_assoc] using
                  ((show prior ++ [result, lhs] <+: prior ++ [result, lhs, rhs] from
                    ⟨[rhs], by simp⟩).trans isPrefix))]
          simp only [pure, StateT.pure, Except.pure, Except.bind]
          rw [show internVariable (variableName rhs)
              (printedVariableNames (prior ++ [result, lhs])) =
                .ok (canonicalRename full rhs,
                  printedVariableNames (prior ++ [result, lhs, rhs])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result, lhs]) rhs (by
                simpa [List.append_assoc] using isPrefix)]
          simp [StateT.run, pure, StateT.pure, Except.pure, List.append_assoc]
      | lt lhs rhs =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences, List.cons_append,
            List.nil_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, exprTokens, parseStatement, statementParts,
            variableTokens, variableToken, List.span, List.span.loop, Stmt.renameVariables,
            Expr.renameVariables]
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers
                [Token.identifier (variableName lhs), Token.identifier (variableName rhs)]
                (printedVariableNames prior) =
              .ok (([], [Token.identifier (variableName lhs),
                  Token.identifier (variableName rhs)]), printedVariableNames prior) from by
            simpa [variableToken] using liftNumbers_variableTokens [lhs, rhs]
              (printedVariableNames prior)]
          simp only [Except.bind]
          rw [show variableList [Token.identifier (variableName result)]
              (printedVariableNames prior) =
                .ok (#[canonicalRename full result],
                  printedVariableNames (prior ++ [result])) from by
            simpa [canonicalRename] using variableList_printed full prior [result]
              ((show prior ++ [result] <+: prior ++ [result, lhs, rhs] from
                ⟨[lhs, rhs], by simp⟩).trans isPrefix)]
          simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
          rw [show internVariable (variableName lhs)
              (printedVariableNames (prior ++ [result])) =
                .ok (canonicalRename full lhs,
                  printedVariableNames (prior ++ [result, lhs])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result]) lhs (by
                simpa [List.append_assoc] using
                  ((show prior ++ [result, lhs] <+: prior ++ [result, lhs, rhs] from
                    ⟨[rhs], by simp⟩).trans isPrefix))]
          simp only [pure, StateT.pure, Except.pure, Except.bind]
          rw [show internVariable (variableName rhs)
              (printedVariableNames (prior ++ [result, lhs])) =
                .ok (canonicalRename full rhs,
                  printedVariableNames (prior ++ [result, lhs, rhs])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result, lhs]) rhs (by
                simpa [List.append_assoc] using isPrefix)]
          simp [StateT.run, pure, StateT.pure, Except.pure, List.append_assoc]
      | sload key =>
          simp only [Stmt.variableOccurrences, Expr.variableOccurrences, List.cons_append,
            List.nil_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, exprTokens, parseStatement, statementParts,
            variableTokens, variableToken, List.span, List.span.loop, Stmt.renameVariables,
            Expr.renameVariables]
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers [Token.identifier (variableName key)]
                (printedVariableNames prior) =
              .ok (([], [Token.identifier (variableName key)]),
                printedVariableNames prior) from by
            simpa [variableToken] using liftNumbers_variableTokens [key]
              (printedVariableNames prior)]
          simp only [Except.bind]
          rw [show variableList [Token.identifier (variableName result)]
              (printedVariableNames prior) =
                .ok (#[canonicalRename full result],
                  printedVariableNames (prior ++ [result])) from by
            simpa [canonicalRename] using variableList_printed full prior [result]
              ((show prior ++ [result] <+: prior ++ [result, key] from
                ⟨[key], by simp⟩).trans isPrefix)]
          simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
          rw [show internVariable (variableName key)
              (printedVariableNames (prior ++ [result])) =
                .ok (canonicalRename full key,
                  printedVariableNames (prior ++ [result, key])) from by
            simpa [canonicalRename, List.append_assoc] using
              internVariable_canonical full (prior ++ [result]) key (by
                simpa [List.append_assoc] using isPrefix)]
          simp [StateT.run, pure, StateT.pure, Except.pure, List.append_assoc]
  | sstore key value =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, parseStatement, statementParts, parseMnemonic, liftNumbers,
        variableToken, List.span, List.span.loop, Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      simp only [variableList, pure, StateT.pure, Except.pure, parseMnemonic, operand,
        StateT.run, bind, StateT.bind, Except.bind]
      rw [show internVariable (variableName key) (printedVariableNames prior) =
          .ok (canonicalRename full key, printedVariableNames (prior ++ [key])) from by
        simpa [canonicalRename] using internVariable_canonical full prior key
          ((show prior ++ [key] <+: prior ++ [key, value] from ⟨[value], by simp⟩).trans
            isPrefix)]
      simp only [pure, StateT.pure, Except.pure, Except.bind, Functor.map, Except.map,
        StateT.map]
      simp only [StateT.bind, StateT.pure, Except.bind, Except.pure]
      rw [show internVariable (variableName value) (printedVariableNames (prior ++ [key])) =
          .ok (canonicalRename full value, printedVariableNames (prior ++ [key, value])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [key]) value (by
            simpa [List.append_assoc] using isPrefix)]
      simp [StateT.run, bind, pure, StateT.pure, Except.pure, Except.bind,
        List.append_assoc]
  | gas result =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, definitionTokens, parseStatement, statementParts, parseMnemonic,
        variableTokens, variableToken, List.span, List.span.loop, Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show liftNumbers [] (printedVariableNames prior) =
          .ok (([], []), printedVariableNames prior) from by
        simpa using liftNumbers_variableTokens [] (printedVariableNames prior)]
      simp only [Except.bind]
      rw [show variableList [Token.identifier (variableName result)]
          (printedVariableNames prior) =
            .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
        simpa [canonicalRename] using variableList_printed full prior [result] isPrefix]
      simp [parseMnemonic, StateT.run, pure, StateT.pure, Except.pure]
  | call callData =>
      rcases callData with ⟨callee, gas, result⟩
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, definitionTokens, parseStatement, statementParts, parseMnemonic,
        liftNumbers, variableTokens, variableToken, List.span, List.span.loop,
        Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show variableList [Token.identifier (variableName result)]
          (printedVariableNames prior) =
            .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
        simpa [canonicalRename] using variableList_printed full prior [result]
          ((show prior ++ [result] <+: prior ++ [result, gas, callee] from
            ⟨[gas, callee], by simp⟩).trans isPrefix)]
      simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
      rw [show internVariable (variableName gas) (printedVariableNames (prior ++ [result])) =
          .ok (canonicalRename full gas, printedVariableNames (prior ++ [result, gas])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [result]) gas (by
            simpa [List.append_assoc] using
              ((show prior ++ [result, gas] <+: prior ++ [result, gas, callee] from
                ⟨[callee], by simp⟩).trans isPrefix))]
      simp only [pure, StateT.pure, Except.pure, Except.bind, Functor.map, Except.map,
        StateT.map]
      simp only [StateT.bind, StateT.pure, Except.bind, Except.pure]
      rw [show internVariable (variableName callee)
          (printedVariableNames (prior ++ [result, gas])) =
            .ok (canonicalRename full callee,
              printedVariableNames (prior ++ [result, gas, callee])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [result, gas]) callee (by
            simpa [List.append_assoc] using isPrefix)]
      simp [StateT.run, bind, pure, StateT.pure, Except.pure, Except.bind,
        List.append_assoc]
  | malloc result size | mallocUninit result size =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, definitionTokens, parseStatement, statementParts, parseMnemonic,
        liftNumbers, variableTokens, variableToken, List.span, List.span.loop,
        Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show variableList [Token.identifier (variableName result)]
          (printedVariableNames prior) =
            .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
        simpa [canonicalRename] using variableList_printed full prior [result]
          ((show prior ++ [result] <+: prior ++ [result, size] from
            ⟨[size], by simp⟩).trans isPrefix)]
      simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
      simp only [StateT.bind, pure, StateT.pure, Except.pure, Except.bind,
        Functor.map, Except.map, StateT.map]
      rw [show internVariable (variableName size) (printedVariableNames (prior ++ [result])) =
          .ok (canonicalRename full size, printedVariableNames (prior ++ [result, size])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [result]) size (by
            simpa [List.append_assoc] using isPrefix)]
      simp [StateT.run, bind, pure, StateT.pure, Except.pure, Except.bind,
        List.append_assoc]
  | mstore32 offset value =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, parseStatement, statementParts, parseMnemonic, liftNumbers,
        variableToken, List.span, List.span.loop, Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      simp only [variableList, pure, StateT.pure, Except.pure, parseMnemonic, operand,
        StateT.run, bind, StateT.bind, Except.bind]
      rw [show internVariable (variableName offset) (printedVariableNames prior) =
          .ok (canonicalRename full offset, printedVariableNames (prior ++ [offset])) from by
        simpa [canonicalRename] using internVariable_canonical full prior offset
          ((show prior ++ [offset] <+: prior ++ [offset, value] from ⟨[value], by simp⟩).trans
            isPrefix)]
      simp only [pure, StateT.pure, Except.pure, Except.bind, Functor.map, Except.map,
        StateT.map]
      simp only [StateT.bind, StateT.pure, Except.bind, Except.pure]
      rw [show internVariable (variableName value) (printedVariableNames (prior ++ [offset])) =
          .ok (canonicalRename full value, printedVariableNames (prior ++ [offset, value])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [offset]) value (by
            simpa [List.append_assoc] using isPrefix)]
      simp [StateT.run, bind, pure, StateT.pure, Except.pure, Except.bind,
        List.append_assoc]
  | mload32 result offset =>
      simp only [Stmt.variableOccurrences] at isPrefix ⊢
      simp [stmtTokens, definitionTokens, parseStatement, statementParts, parseMnemonic,
        liftNumbers, variableTokens, variableToken, List.span, List.span.loop,
        Stmt.renameVariables]
      simp only [StateT.run, bind, StateT.bind, Except.bind]
      rw [show variableList [Token.identifier (variableName result)]
          (printedVariableNames prior) =
            .ok (#[canonicalRename full result], printedVariableNames (prior ++ [result])) from by
        simpa [canonicalRename] using variableList_printed full prior [result]
          ((show prior ++ [result] <+: prior ++ [result, offset] from
            ⟨[offset], by simp⟩).trans isPrefix)]
      simp only [parseMnemonic, operand, StateT.run, bind, StateT.bind, Except.bind]
      simp only [StateT.bind, pure, StateT.pure, Except.pure, Except.bind,
        Functor.map, Except.map, StateT.map]
      rw [show internVariable (variableName offset) (printedVariableNames (prior ++ [result])) =
          .ok (canonicalRename full offset, printedVariableNames (prior ++ [result, offset])) from by
        simpa [canonicalRename, List.append_assoc] using
          internVariable_canonical full (prior ++ [result]) offset (by
            simpa [List.append_assoc] using isPrefix)]
      simp [StateT.run, bind, pure, StateT.pure, Except.pure, Except.bind,
        List.append_assoc]
  | icall callee args dests =>
      rcases args with ⟨args⟩
      rcases dests with ⟨dests⟩
      simp only [Stmt.variableOccurrences,
        Stmt.FunctionReferencesInRange] at references isPrefix ⊢
      cases dests with
      | nil =>
          simp only [List.nil_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, variableTokens]
          rw [parseStatement]
          rw [statementParts_icall_no_results]
          simp
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers
                (Token.label (functionName program callee) :: args.map variableToken)
                (printedVariableNames prior) =
              .ok (([], Token.label (functionName program callee) :: args.map variableToken),
                printedVariableNames prior) from
            liftNumbers_icall (functionName program callee) args _]
          simp only [Except.bind]
          rw [show variableList [] (printedVariableNames prior) =
              .ok (#[], printedVariableNames prior) from by
            simpa using variableList_printed full prior []
              (by simpa using
                ((show prior <+: prior ++ args from ⟨args, rfl⟩).trans isPrefix))]
          simp only [Except.bind]
          simp only [parseMnemonic, StateT.run, bind, StateT.bind, Except.bind]
          rw [printedFunctionNames_findIdx program printable callee references]
          simp only [StateT.bind, Except.bind]
          rw [show operands (args.map variableToken) (printedVariableNames prior) =
              .ok (([], args.map (canonicalRename full) |>.toArray),
                printedVariableNames (prior ++ args)) from
            operands_printed full prior args isPrefix]
          simp [parseMnemonic, StateT.run, bind, pure, StateT.pure, Except.bind,
            Except.pure, Stmt.renameVariables]
      | cons destination following =>
          simp only [List.cons_append] at isPrefix ⊢
          simp [stmtTokens, definitionTokens, variableTokens]
          rw [parseStatement]
          rw [show statementParts
                (variableToken destination ::
                  (following.map variableToken ++ Token.equals ::
                    Token.identifier "icall" :: Token.label (functionName program callee) ::
                      args.map variableToken)) =
              ((destination :: following).map variableToken,
                Token.identifier "icall" :: Token.label (functionName program callee) ::
                  args.map variableToken) from by
            simpa [List.map_cons, List.cons_append] using
              statementParts_icall_results (destination :: following) args
                (functionName program callee) (by simp)]
          simp
          simp only [StateT.run, bind, StateT.bind, Except.bind]
          rw [show liftNumbers
                (Token.label (functionName program callee) :: args.map variableToken)
                (printedVariableNames prior) =
              .ok (([], Token.label (functionName program callee) :: args.map variableToken),
                printedVariableNames prior) from
            liftNumbers_icall (functionName program callee) args _]
          simp only [Except.bind]
          rw [show variableList
                (variableToken destination :: following.map variableToken)
                (printedVariableNames prior) =
              .ok ((destination :: following).map (canonicalRename full) |>.toArray,
                printedVariableNames (prior ++ destination :: following)) from
            by
              simpa [List.map_cons] using
                variableList_printed full prior (destination :: following)
                  ((show prior ++ destination :: following <+:
                      prior ++ (destination :: following) ++ args from
                    ⟨args, by simp⟩).trans
                    (by simpa [List.append_assoc] using isPrefix))]
          simp only [Except.bind]
          simp only [parseMnemonic, StateT.run, bind, StateT.bind, Except.bind]
          rw [printedFunctionNames_findIdx program printable callee references]
          simp only [StateT.bind, Except.bind]
          rw [show operands (args.map variableToken)
                (printedVariableNames (prior ++ destination :: following)) =
              .ok (([], args.map (canonicalRename full) |>.toArray),
                printedVariableNames ((prior ++ destination :: following) ++ args)) from
            operands_printed full (prior ++ destination :: following) args (by
              simpa [List.append_assoc] using isPrefix)]
          simp [parseMnemonic, StateT.run, bind, pure, StateT.pure, Except.bind,
            Except.pure, List.append_assoc, Stmt.renameVariables]

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
      simp only [Except.bind]
      rw [printedBlockNames_findIdx function thenTarget thenBound]
      simp only [Except.bind]
      rw [printedBlockNames_findIdx function elseTarget elseBound]
      simp [pure, StateT.pure, Except.pure]

namespace Examples

def witnessAddPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 2 \nv1 = const 3 \nv2 = icall @fn1 v0 v1 \nstop \n} \n" ++
  "fn fn1 : \nblock0 v3 v4 -> v5 { \nv5 = add v3 v4 \niret \n} \n"

theorem parse_print_witnessAdd : parse (print witnessAddProgram) = .ok witnessAddProgram := by
  rw [show print witnessAddProgram = witnessAddPrinted by parse_rfl]
  parse_rfl

def jumpPrinted : String :=
  "fn init : \nblock0 -> v0 { \nv0 = const 7 \n=> @block1 \n} \n" ++
  "block1 v1 { \nv2 = add v1 v1 \nstop \n} \n"

theorem parse_print_jump : parse (print jumpProgram) = .ok jumpProgram := by
  rw [show print jumpProgram = jumpPrinted by parse_rfl]
  parse_rfl

def initializedLoadPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 32 \nv1 = mallocany v0 \nv2 = const 42 \n" ++
  "mstore256 v1 v2 \nv3 = mload256 v1 \nsstore v3 v3 \nstop \n} \n"

theorem parse_print_initializedLoad : parse (print initializedLoad) = .ok initializedLoad := by
  rw [show print initializedLoad = initializedLoadPrinted by parse_rfl]
  parse_rfl

def zeroSizeStorePrinted : String :=
  "fn init : \nblock0 { \nv0 = const 0 \nv1 = mallocany v0 \nsstore v1 v1 \nstop \n} \n"

theorem parse_print_zeroSizeStore : parse (print zeroSizeStore) = .ok zeroSizeStore := by
  rw [show print zeroSizeStore = zeroSizeStorePrinted by parse_rfl]
  parse_rfl

def haltedCallPrinted : String :=
  "fn init : \nblock0 { \nicall @fn1 \nstop \n} \nfn fn1 : \nblock0 { \nstop \n} \n"

theorem parse_print_haltedCall : parse (print haltedCallProgram) = .ok haltedCallProgram := by
  rw [show print haltedCallProgram = haltedCallPrinted by parse_rfl]
  parse_rfl

def nonzeroEntryProgram : Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[], statements := #[], terminator := .halt, outputs := #[] }]
      entry := ⟨1⟩ }]
    initEntry := ⟨0⟩
    mainEntry := none }

def zeroEntryProgram : Program :=
  { functions := #[{
      blocks := #[{
        inputs := #[], statements := #[], terminator := .halt, outputs := #[] }]
      entry := ⟨0⟩ }]
    initEntry := ⟨0⟩
    mainEntry := none }

theorem parse_print_nonzeroEntry :
    parse (print nonzeroEntryProgram) = .ok zeroEntryProgram := by
  parse_rfl

theorem parse_print_nonzeroEntry_ne_canonicalize :
    parse (print nonzeroEntryProgram) ≠ .ok nonzeroEntryProgram.canonicalize := by
  intro equality
  rw [parse_print_nonzeroEntry] at equality
  have programsEqual : zeroEntryProgram = nonzeroEntryProgram.canonicalize :=
    Except.ok.inj equality
  have entriesEqual := congrArg
    (fun program => (program.functions[0]?).map Function.entry) programsEqual
  simp [zeroEntryProgram, nonzeroEntryProgram, Program.canonicalize,
    Program.renameVariables, Function.renameVariables] at entriesEqual

end Examples
end Sir.Vars.Text
