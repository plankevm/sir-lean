import Sir.Text.Lexer
import Sir.Text.Printer

namespace Sir.Vars.Text

theorem toList_decimalString (value : Nat) :
    (decimalString value).toList = decimalDigits value := by
  simp [decimalString, String.toList_ofList]

theorem toList_append_decimalString {lead : String} {first : Char} {rest : List Char}
    (hname : lead.toList = first :: rest) (value : Nat) :
    (lead ++ decimalString value).toList = first :: (rest ++ decimalDigits value) := by
  rw [String.toList_append, toList_decimalString, hname, List.cons_append]

theorem all_isIdentifierBody_append_decimalDigits {first : Char} {rest : List Char}
    (hbody : (first :: rest).all isIdentifierBody = true) (value : Nat) :
    (first :: (rest ++ decimalDigits value)).all isIdentifierBody = true := by
  simp only [List.all_cons, Bool.and_eq_true, List.all_append] at hbody ⊢
  exact ⟨hbody.left, hbody.right,
    all_isIdentifierBody_of_all_isDigit (decimalDigits_all_isDigit value)⟩

theorem renderable_identifier_decimal {lead : String} {first : Char} {rest : List Char}
    (hname : lead.toList = first :: rest) (hdigit : first.isDigit = false)
    (hbody : (first :: rest).all isIdentifierBody = true) (value : Nat) :
    (Token.identifier (lead ++ decimalString value)).Renderable :=
  ⟨first, rest ++ decimalDigits value, toList_append_decimalString hname value, hdigit,
    all_isIdentifierBody_append_decimalDigits hbody value⟩

theorem renderable_label_decimal {lead : String} {first : Char} {rest : List Char}
    (hname : lead.toList = first :: rest)
    (hbody : (first :: rest).all isIdentifierBody = true) (value : Nat) :
    (Token.label (lead ++ decimalString value)).Renderable :=
  ⟨first, rest ++ decimalDigits value, toList_append_decimalString hname value,
    all_isIdentifierBody_append_decimalDigits hbody value⟩

@[simp] theorem renderable_number (value : Nat) : (Token.number value).Renderable := trivial
@[simp] theorem renderable_equals : Token.equals.Renderable := trivial
@[simp] theorem renderable_arrow : Token.arrow.Renderable := trivial
@[simp] theorem renderable_fatArrow : Token.fatArrow.Renderable := trivial
@[simp] theorem renderable_colon : Token.colon.Renderable := trivial
@[simp] theorem renderable_question : Token.question.Renderable := trivial
@[simp] theorem renderable_leftBrace : Token.leftBrace.Renderable := trivial
@[simp] theorem renderable_rightBrace : Token.rightBrace.Renderable := trivial
@[simp] theorem renderable_newline : Token.newline.Renderable := trivial

@[simp] theorem renderable_variableToken (identifier : VarId) :
    (variableToken identifier).Renderable :=
  renderable_identifier_decimal (lead := "v") rfl (by decide) (by decide) identifier.id

@[simp] theorem renderable_blockNameToken (block : BlockId) :
    (Token.identifier (blockName block)).Renderable :=
  renderable_identifier_decimal (lead := "block") rfl (by decide) (by decide) block.id

@[simp] theorem renderable_blockNameLabel (block : BlockId) :
    (Token.label (blockName block)).Renderable :=
  renderable_label_decimal (lead := "block") rfl (by decide) block.id

@[simp] theorem renderable_functionNameToken (program : Program) (function : FunctionId) :
    (Token.identifier (functionName program function)).Renderable := by
  rw [functionName]
  split
  · exact ⟨'i', _, rfl, by decide, by decide⟩
  split
  · exact ⟨'m', _, rfl, by decide, by decide⟩
  · exact renderable_identifier_decimal (lead := "fn") rfl (by decide) (by decide) function.id

@[simp] theorem renderable_functionNameLabel (program : Program) (function : FunctionId) :
    (Token.label (functionName program function)).Renderable := by
  rw [functionName]
  split
  · exact ⟨'i', _, rfl, by decide⟩
  split
  · exact ⟨'m', _, rfl, by decide⟩
  · exact renderable_label_decimal (lead := "fn") rfl (by decide) function.id

@[simp] theorem renderable_variableTokens (identifiers : Array VarId) :
    ∀ token ∈ variableTokens identifiers, token.Renderable := by
  simp [variableTokens]

@[simp] theorem renderable_definitionTokens (results : Array VarId) :
    ∀ token ∈ definitionTokens results, token.Renderable := by
  rw [definitionTokens]
  split
  · simp
  · simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨renderable_variableTokens results, trivial, by simp⟩

@[simp] theorem renderable_exprTokens (value : Expr) :
    ∀ token ∈ exprTokens value, token.Renderable := by
  cases value <;>
    simp only [exprTokens, List.forall_mem_cons]
  all_goals repeat' apply And.intro
  all_goals first
    | exact ⟨_, _, rfl, by decide, by decide⟩
    | simp

@[simp] theorem renderable_stmtTokens (program : Program) (statement : Stmt) :
    ∀ token ∈ stmtTokens program statement, token.Renderable := by
  cases statement <;>
    simp only [stmtTokens, List.forall_mem_append, List.forall_mem_cons]
  all_goals repeat' apply And.intro
  all_goals first
    | exact ⟨_, _, rfl, by decide, by decide⟩
    | exact renderable_definitionTokens _
    | exact renderable_exprTokens _
    | exact renderable_variableTokens _
    | simp

@[simp] theorem renderable_terminatorTokens (terminator : Terminator) :
    ∀ token ∈ terminatorTokens terminator, token.Renderable := by
  cases terminator <;>
    simp only [terminatorTokens, List.forall_mem_cons]
  all_goals repeat' apply And.intro
  all_goals first
    | exact ⟨_, _, rfl, by decide, by decide⟩
    | simp

@[simp] theorem renderable_blockTokens (program : Program) (identifier : BlockId)
    (block : Block) :
    ∀ token ∈ blockTokens program identifier block, token.Renderable := by
  rw [blockTokens]
  split <;>
    simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap]
  all_goals repeat' apply And.intro
  all_goals first
    | exact renderable_variableTokens _
    | exact renderable_terminatorTokens _
    | simp
  all_goals
    intro _ _
    exact renderable_stmtTokens _ _

@[simp] theorem renderable_functionTokens (program : Program) (identifier : FunctionId)
    (function : Function) :
    ∀ token ∈ functionTokens program identifier function, token.Renderable := by
  simp only [functionTokens, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_flatMap]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, _, rfl, by decide, by decide⟩
    | (intro _ _; exact renderable_blockTokens _ _ _)
    | simp

theorem renderable_programTokens (program : Program) :
    ∀ token ∈ programTokens program, token.Renderable := by
  simp only [programTokens, List.forall_mem_flatMap]
  intro _ _
  exact renderable_functionTokens _ _ _

theorem tokenize_print (program : Program) :
    tokenize (print program) = programTokens program :=
  tokenize_render (renderable_programTokens program)

end Sir.Vars.Text
