import Sir.Text.Spec.Parser
import Sir.Vars.Proofs.Canonical

namespace Sir.Vars.Text

inductive InterningInvariant : List String → List VarId → Prop where
  | empty : InterningInvariant [] []
  | existing {names occurrences identifier}
      (invariant : InterningInvariant names occurrences)
      (bound : identifier.id < names.length) :
      InterningInvariant names (occurrences ++ [identifier])
  | fresh {names occurrences name}
      (invariant : InterningInvariant names occurrences) :
      InterningInvariant (names ++ [name])
        (occurrences ++ [⟨names.length⟩])

namespace InterningInvariant

theorem append_existing {names occurrences : List _} {identifier : VarId}
    (invariant : InterningInvariant names occurrences)
    (bound : identifier.id < names.length) :
    InterningInvariant names (occurrences ++ [identifier]) :=
  .existing invariant bound

theorem append_fresh {names occurrences : List _} {name : String}
    (invariant : InterningInvariant names occurrences) :
    InterningInvariant (names ++ [name])
      (occurrences ++ [⟨names.length⟩]) :=
  .fresh invariant

theorem identifiers_bounded {names occurrences}
    (invariant : InterningInvariant names occurrences) :
    ∀ identifier ∈ occurrences, identifier.id < names.length := by
  induction invariant with
  | empty => simp
  | existing invariant bound induction =>
      intro identifier member
      simp only [List.mem_append, List.mem_singleton] at member
      exact member.elim (induction identifier) (fun equality => equality ▸ bound)
  | fresh invariant induction =>
      intro identifier member
      simp only [List.mem_append, List.mem_singleton] at member
      rw [List.length_append, List.length_singleton]
      exact member.elim
        (fun previous => Nat.lt_succ_of_lt (induction identifier previous))
        (fun equality => by subst identifier; simp)

theorem contains_all {names occurrences}
    (invariant : InterningInvariant names occurrences) :
    ∀ index, index < names.length → (⟨index⟩ : VarId) ∈ occurrences := by
  induction invariant with
  | empty => simp
  | existing invariant _ induction =>
      intro index bound
      exact List.mem_append_left _ (induction index bound)
  | fresh invariant induction =>
      intro index bound
      rw [List.length_append, List.length_singleton] at bound
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bound) with previous | current
      · exact List.mem_append_left _ (induction index previous)
      · exact List.mem_append_right _ (by simp [current])

theorem eraseDups_eq_range {names occurrences}
    (invariant : InterningInvariant names occurrences) :
    occurrences.eraseDups = (List.range names.length).map VarId.mk := by
  induction invariant with
  | empty => rfl
  | @existing names occurrences identifier invariant bound induction =>
      rw [List.eraseDups_append, induction]
      have member : identifier ∈ occurrences :=
        contains_all invariant identifier.id bound
      rw [singleton_removeAll_eq_nil member]
      simp [List.eraseDups]
  | @fresh names occurrences name invariant induction =>
      rw [List.eraseDups_append, induction]
      have notMember : (⟨names.length⟩ : VarId) ∉ occurrences := by
        intro member
        exact Nat.lt_irrefl _ (identifiers_bounded invariant _ member)
      rw [singleton_removeAll_eq_self notMember]
      rw [List.eraseDups_cons]
      simp [List.range_succ]

where
  singleton_removeAll_eq_nil {identifier : VarId} {identifiers : List VarId}
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
  singleton_removeAll_eq_self {identifier : VarId} {identifiers : List VarId}
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

private theorem idxOf_range (index count : Nat) (bound : index < count) :
    ((List.range count).map VarId.mk).idxOf ⟨index⟩ = index := by
  induction count with
  | zero => omega
  | succ count induction =>
      rw [List.range_succ, List.map_append, List.idxOf_append]
      by_cases previous : index < count
      · have member : (⟨index⟩ : VarId) ∈ (List.range count).map VarId.mk := by
          simp [previous]
        simp [member, induction previous]
      · have current : index = count := by omega
        subst index
        have notMember : (⟨count⟩ : VarId) ∉ (List.range count).map VarId.mk := by
          simp
        simp [notMember]

theorem canonicalVariable_eq {program : Program} {names occurrences}
    (invariant : InterningInvariant names occurrences)
    (occurrences_eq : occurrences = program.variableOccurrences)
    {identifier : VarId} (member : identifier ∈ program.variableOccurrences) :
    program.canonicalVariable identifier = identifier := by
  have bound : identifier.id < names.length :=
    identifiers_bounded invariant identifier (occurrences_eq ▸ member)
  simp only [Program.canonicalVariable]
  rw [← occurrences_eq, eraseDups_eq_range invariant, idxOf_range _ _ bound]

theorem canonical {program : Program} {names : List String}
    (invariant : InterningInvariant names program.variableOccurrences) :
    program.Canonical := by
  rw [Program.Canonical, Program.canonicalize]
  calc
    program.renameVariables program.canonicalVariable =
        program.renameVariables id := by
      apply Vars.Proofs.Program.renameVariables_congr
      intro identifier member
      exact canonicalVariable_eq invariant rfl member
    _ = program := Vars.Proofs.Program.renameVariables_id program

end InterningInvariant

def PreservesInterning {α : Type} (action : ParserM α) (occurrences : α → List VarId) : Prop :=
  ∀ names prior value finalNames,
    InterningInvariant names prior →
    action.run names = .ok (value, finalNames) →
    InterningInvariant finalNames (prior ++ occurrences value)

theorem internVariable_preserves (name : String) :
    PreservesInterning (internVariable name) (fun identifier => [identifier]) := by
  intro names prior identifier finalNames invariant run
  simp [internVariable, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    set, pure, Except.pure, Except.bind] at run
  generalize foundEq : names.findIdx? (· == name) = found at run
  cases found with
  | none =>
      simp [bind, StateT.bind, StateT.set, pure, StateT.pure, Except.pure, Except.bind] at run
      rcases run with ⟨rfl, rfl⟩
      exact InterningInvariant.fresh invariant
  | some index =>
      simp [pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      apply InterningInvariant.existing invariant
      exact (List.findIdx?_eq_some_iff_findIdx_eq.mp foundEq).1

theorem freshVariable_preserves :
    PreservesInterning freshVariable (fun identifier => [identifier]) := by
  intro names prior identifier finalNames invariant run
  change (Except.ok (⟨names.length⟩, names ++ [temporaryName ⟨names.length⟩]) =
    Except.ok (identifier, finalNames)) at run
  simp only [Except.ok.injEq, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  exact InterningInvariant.fresh invariant

private theorem run_bind_ok {α β : Type} {action : ParserM α}
    {next : α → ParserM β} {initial final : List String} {result : β}
    (run : (action >>= next).run initial = .ok (result, final)) :
    ∃ value middle,
      action.run initial = .ok (value, middle) ∧
      (next value).run middle = .ok (result, final) := by
  rw [StateT.run_bind] at run
  cases firstRun : action.run initial with
  | error message => simp [firstRun, bind, Except.bind] at run
  | ok pair =>
      refine ⟨pair.1, pair.2, by simp only [Prod.eta], ?_⟩
      simpa [firstRun] using run

theorem variableList_preserves (tokens : List Token) :
    PreservesInterning (variableList tokens) (fun identifiers => identifiers.toList) := by
  induction tokens with
  | nil =>
      intro names prior identifiers finalNames invariant run
      simp [variableList, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simpa using invariant
  | cons token rest induction =>
      cases token with
      | identifier name =>
          intro names prior identifiers finalNames invariant run
          rw [variableList] at run
          obtain ⟨head, middleNames, headRun, followingRun⟩ := run_bind_ok run
          obtain ⟨following, followingNames, restRun, returnRun⟩ :=
            run_bind_ok followingRun
          have afterHead := internVariable_preserves name names prior head middleNames
            invariant headRun
          have afterRest := induction middleNames (prior ++ [head]) following
            followingNames afterHead restRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          simpa [List.append_assoc] using afterRest
      | _ =>
          intro names prior identifiers finalNames invariant run
          simp [variableList, StateT.run, throw, throwThe, MonadExceptOf.throw,
            StateT.lift] at run

def statementOccurrences (statements : List Stmt) : List VarId :=
  statements.flatMap Stmt.variableOccurrences

theorem liftNumbers_preserves (tokens : List Token) :
    PreservesInterning (liftNumbers tokens)
      (fun result => statementOccurrences result.1) := by
  induction tokens with
  | nil =>
      intro names prior result finalNames invariant run
      simp [liftNumbers, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simpa [statementOccurrences] using invariant
  | cons token rest induction =>
      cases token with
      | number value =>
          intro names prior result finalNames invariant run
          rw [liftNumbers] at run
          obtain ⟨target, targetNames, targetRun, followingRun⟩ := run_bind_ok run
          obtain ⟨following, followingNames, restRun, returnRun⟩ :=
            run_bind_ok followingRun
          have afterTarget := freshVariable_preserves names prior target targetNames
            invariant targetRun
          have afterRest := induction targetNames (prior ++ [target]) following
            followingNames afterTarget restRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          simpa [statementOccurrences, Stmt.variableOccurrences,
            List.append_assoc] using afterRest
      | _ =>
          intro names prior result finalNames invariant run
          simp only [liftNumbers] at run
          obtain ⟨following, followingNames, restRun, returnRun⟩ :=
            run_bind_ok run
          have afterRest := induction names prior following followingNames invariant restRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          simpa using afterRest

theorem operand_preserves (token : Token) :
    PreservesInterning (operand token)
      (fun result => statementOccurrences result.1 ++ [result.2]) := by
  cases token with
  | identifier name =>
      intro names prior result finalNames invariant run
      rw [operand] at run
      obtain ⟨identifier, middleNames, internRun, returnRun⟩ := run_bind_ok run
      have afterIntern := internVariable_preserves name names prior identifier middleNames
        invariant internRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [statementOccurrences] using afterIntern
  | number value =>
      intro names prior result finalNames invariant run
      rw [operand] at run
      obtain ⟨identifier, middleNames, freshRun, returnRun⟩ := run_bind_ok run
      have afterFresh := freshVariable_preserves names prior identifier middleNames
        invariant freshRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
        InterningInvariant.existing afterFresh
          (InterningInvariant.identifiers_bounded afterFresh identifier (by simp))
  | _ =>
      intro names prior result finalNames invariant run
      simp [operand, StateT.run, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run

def ContainsNoNumbers (tokens : List Token) : Prop :=
  ∀ value, Token.number value ∉ tokens

theorem liftNumbers_containsNoNumbers {tokens result names finalNames}
    (run : (liftNumbers tokens).run names = .ok (result, finalNames)) :
    ContainsNoNumbers result.2 := by
  induction tokens generalizing names result finalNames with
  | nil =>
      simp [liftNumbers, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simp [ContainsNoNumbers]
  | cons token rest induction =>
      cases token with
      | number value =>
          rw [liftNumbers] at run
          obtain ⟨target, targetNames, targetRun, followingRun⟩ := run_bind_ok run
          obtain ⟨following, followingNames, restRun, returnRun⟩ :=
            run_bind_ok followingRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          have followingNoNumbers := induction restRun
          intro other member
          simp only [List.mem_cons] at member
          exact member.elim Token.noConfusion (followingNoNumbers other)
      | _ =>
          simp only [liftNumbers] at run
          obtain ⟨following, followingNames, restRun, returnRun⟩ := run_bind_ok run
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          have followingNoNumbers := induction restRun
          intro value member
          simp only [List.mem_cons] at member
          exact member.elim (by simp_all) (followingNoNumbers value)

theorem operand_preserves_of_not_number {token : Token}
    (notNumber : ∀ value, token ≠ .number value) :
    PreservesInterning (operand token) (fun result => [result.2]) := by
  cases token with
  | identifier name =>
      intro names prior result finalNames invariant run
      rw [operand] at run
      obtain ⟨identifier, middleNames, internRun, returnRun⟩ := run_bind_ok run
      have afterIntern := internVariable_preserves name names prior identifier middleNames
        invariant internRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa using afterIntern
  | number value => exact (notNumber value rfl).elim
  | _ =>
      intro names prior result finalNames invariant run
      simp [operand, StateT.run, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run

theorem operands_preserves_of_containsNoNumbers {tokens : List Token}
    (noNumbers : ContainsNoNumbers tokens) :
    PreservesInterning (operands tokens) (fun result => result.2.toList) := by
  induction tokens with
  | nil =>
      intro names prior result finalNames invariant run
      simp [operands, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simpa using invariant
  | cons token rest induction =>
      intro names prior result finalNames invariant run
      rw [operands] at run
      obtain ⟨head, headNames, headRun, followingRun⟩ := run_bind_ok run
      obtain ⟨following, followingNames, restRun, returnRun⟩ :=
        run_bind_ok followingRun
      have tokenNotNumber : ∀ value, token ≠ .number value := by
        intro value equality
        exact noNumbers value (by simp [equality])
      have restNoNumbers : ContainsNoNumbers rest := by
        intro value member
        exact noNumbers value (by simp [member])
      have afterHead := operand_preserves_of_not_number tokenNotNumber names prior
        head headNames invariant headRun
      have afterRest := induction restNoNumbers headNames (prior ++ [head.2]) following
        followingNames afterHead restRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [List.append_assoc] using afterRest

theorem parseMnemonic_preserves (functions : List String) (line : Line)
    (mnemonic : String) (results : List VarId) (parameters : List Token)
    (noNumbers : ContainsNoNumbers parameters) :
    ∀ names prior statements finalNames,
      InterningInvariant names (prior ++ results) →
      (parseMnemonic functions line mnemonic results parameters).run names =
        .ok (statements, finalNames) →
      InterningInvariant finalNames (prior ++ statementOccurrences statements) := by
  intro names prior statements finalNames invariant run
  unfold parseMnemonic at run
  split at run
  case h_1 result source =>
    obtain ⟨operandResult, operandNames, operandRun, returnRun⟩ := run_bind_ok run
    have tokenNotNumber : ∀ value, source ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterOperand := operand_preserves_of_not_number tokenNotNumber names
      (prior ++ [result]) operandResult operandNames invariant operandRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterOperand
  case h_2 result lhs rhs =>
    obtain ⟨leftResult, leftNames, leftRun, afterLeftRun⟩ := run_bind_ok run
    obtain ⟨rightResult, rightNames, rightRun, returnRun⟩ := run_bind_ok afterLeftRun
    have leftNotNumber : ∀ value, lhs ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have rightNotNumber : ∀ value, rhs ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterLeft := operand_preserves_of_not_number leftNotNumber names
      (prior ++ [result]) leftResult leftNames invariant leftRun
    have afterRight := operand_preserves_of_not_number rightNotNumber leftNames
      (prior ++ [result] ++ [leftResult.2]) rightResult rightNames afterLeft rightRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterRight
  case h_3 result lhs rhs =>
    obtain ⟨leftResult, leftNames, leftRun, afterLeftRun⟩ := run_bind_ok run
    obtain ⟨rightResult, rightNames, rightRun, returnRun⟩ := run_bind_ok afterLeftRun
    have leftNotNumber : ∀ value, lhs ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have rightNotNumber : ∀ value, rhs ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterLeft := operand_preserves_of_not_number leftNotNumber names
      (prior ++ [result]) leftResult leftNames invariant leftRun
    have afterRight := operand_preserves_of_not_number rightNotNumber leftNames
      (prior ++ [result] ++ [leftResult.2]) rightResult rightNames afterLeft rightRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterRight
  case h_4 result key =>
    obtain ⟨operandResult, operandNames, operandRun, returnRun⟩ := run_bind_ok run
    have tokenNotNumber : ∀ value, key ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterOperand := operand_preserves_of_not_number tokenNotNumber names
      (prior ++ [result]) operandResult operandNames invariant operandRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterOperand
  case h_5 key storedValue =>
    obtain ⟨leftResult, leftNames, leftRun, afterLeftRun⟩ := run_bind_ok run
    obtain ⟨rightResult, rightNames, rightRun, returnRun⟩ := run_bind_ok afterLeftRun
    have leftNotNumber : ∀ number, key ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have rightNotNumber : ∀ number, storedValue ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have afterLeft := operand_preserves_of_not_number leftNotNumber names prior
      leftResult leftNames (by simpa using invariant) leftRun
    have afterRight := operand_preserves_of_not_number rightNotNumber leftNames
      (prior ++ [leftResult.2]) rightResult rightNames afterLeft rightRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterRight
  case h_6 =>
    simp [StateT.run, pure, StateT.pure, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences] using invariant
  case h_7 result gas callee =>
    obtain ⟨leftResult, leftNames, leftRun, afterLeftRun⟩ := run_bind_ok run
    obtain ⟨rightResult, rightNames, rightRun, returnRun⟩ := run_bind_ok afterLeftRun
    have leftNotNumber : ∀ number, gas ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have rightNotNumber : ∀ number, callee ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have afterLeft := operand_preserves_of_not_number leftNotNumber names
      (prior ++ [result]) leftResult leftNames invariant leftRun
    have afterRight := operand_preserves_of_not_number rightNotNumber leftNames
      (prior ++ [result] ++ [leftResult.2]) rightResult rightNames afterLeft rightRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterRight
  case h_8 result size =>
    obtain ⟨operandResult, operandNames, operandRun, returnRun⟩ := run_bind_ok run
    have tokenNotNumber : ∀ value, size ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterOperand := operand_preserves_of_not_number tokenNotNumber names
      (prior ++ [result]) operandResult operandNames invariant operandRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterOperand
  case h_9 result size =>
    obtain ⟨operandResult, operandNames, operandRun, returnRun⟩ := run_bind_ok run
    have tokenNotNumber : ∀ value, size ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterOperand := operand_preserves_of_not_number tokenNotNumber names
      (prior ++ [result]) operandResult operandNames invariant operandRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterOperand
  case h_10 offset storedValue =>
    obtain ⟨leftResult, leftNames, leftRun, afterLeftRun⟩ := run_bind_ok run
    obtain ⟨rightResult, rightNames, rightRun, returnRun⟩ := run_bind_ok afterLeftRun
    have leftNotNumber : ∀ number, offset ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have rightNotNumber : ∀ number, storedValue ≠ .number number := by
      intro number equality
      exact noNumbers number (by simp [equality])
    have afterLeft := operand_preserves_of_not_number leftNotNumber names prior
      leftResult leftNames (by simpa using invariant) leftRun
    have afterRight := operand_preserves_of_not_number rightNotNumber leftNames
      (prior ++ [leftResult.2]) rightResult rightNames afterLeft rightRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterRight
  case h_11 result offset =>
    obtain ⟨operandResult, operandNames, operandRun, returnRun⟩ := run_bind_ok run
    have tokenNotNumber : ∀ value, offset ≠ .number value := by
      intro value equality
      exact noNumbers value (by simp [equality])
    have afterOperand := operand_preserves_of_not_number tokenNotNumber names
      (prior ++ [result]) operandResult operandNames invariant operandRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
      afterOperand
  case h_12 calleeName args =>
    generalize foundEq : functions.findIdx? (· == calleeName) = found at run
    cases found with
    | none =>
        simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run
    | some calleeIndex =>
        obtain ⟨argumentResult, argumentNames, argumentRun, returnRun⟩ := run_bind_ok run
        have argsNoNumbers : ContainsNoNumbers args := by
          intro value member
          exact noNumbers value (by simp [member])
        have afterArguments := operands_preserves_of_containsNoNumbers argsNoNumbers
          names (prior ++ results) argumentResult argumentNames invariant argumentRun
        simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
        rcases returnRun with ⟨rfl, rfl⟩
        simpa [statementOccurrences, Stmt.variableOccurrences, List.append_assoc] using
          afterArguments
  case h_13 =>
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

theorem parseStatement_preserves (functions : List String) (line : Line) :
    PreservesInterning (parseStatement functions line) statementOccurrences := by
  intro names prior statements finalNames invariant run
  unfold parseStatement at run
  generalize partsEq : statementParts line = parts at run
  rcases parts with ⟨resultTokens, operandTokens⟩
  cases operandTokens with
  | nil =>
      simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run
  | cons operation parameters =>
      cases operation with
      | identifier mnemonic =>
          by_cases constant : mnemonic = "const"
          · subst mnemonic
            simp only at run
            obtain ⟨results, resultNames, resultsRun, followingRun⟩ := run_bind_ok run
            have afterResults := variableList_preserves resultTokens names prior results
              resultNames invariant resultsRun
            cases resultListEq : results.toList with
            | nil =>
                simp [resultListEq, StateT.run, throw, throwThe,
                  MonadExceptOf.throw, StateT.lift] at followingRun
            | cons result otherResults =>
                cases otherResults with
                | cons second rest =>
                    simp [resultListEq, StateT.run, throw, throwThe,
                      MonadExceptOf.throw, StateT.lift] at followingRun
                | nil =>
                    cases parameters with
                    | nil =>
                        simp [resultListEq, StateT.run, throw, throwThe,
                          MonadExceptOf.throw, StateT.lift] at followingRun
                    | cons parameter otherParameters =>
                        cases parameter with
                        | number value =>
                            cases otherParameters with
                            | cons next rest =>
                                simp [resultListEq, StateT.run, throw, throwThe,
                                  MonadExceptOf.throw, StateT.lift] at followingRun
                            | nil =>
                                simp [resultListEq, StateT.run, pure, StateT.pure,
                                  Except.pure] at followingRun
                                rcases followingRun with ⟨rfl, rfl⟩
                                simpa [statementOccurrences, Stmt.variableOccurrences,
                                  resultListEq] using afterResults
                        | _ =>
                            simp [resultListEq, StateT.run, throw, throwThe,
                              MonadExceptOf.throw, StateT.lift] at followingRun
          · simp only at run
            obtain ⟨liftedResult, liftedNames, liftedRun, afterLiftRun⟩ :=
              run_bind_ok run
            rcases liftedResult with ⟨lifted, liftedTokens⟩
            obtain ⟨results, resultNames, resultsRun, bodyRun⟩ :=
              run_bind_ok afterLiftRun
            obtain ⟨body, bodyNames, mnemonicRun, returnRun⟩ := run_bind_ok bodyRun
            have afterLift := liftNumbers_preserves parameters names prior
              (lifted, liftedTokens) liftedNames invariant liftedRun
            have afterResults := variableList_preserves resultTokens liftedNames
              (prior ++ statementOccurrences lifted) results resultNames afterLift resultsRun
            have noNumbers := liftNumbers_containsNoNumbers liftedRun
            have afterBody := parseMnemonic_preserves functions line mnemonic results.toList
              liftedTokens noNumbers resultNames (prior ++ statementOccurrences lifted) body
              bodyNames afterResults mnemonicRun
            simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
            rcases returnRun with ⟨rfl, rfl⟩
            simpa [statementOccurrences, List.flatMap_append,
              List.append_assoc] using afterBody
      | _ =>
          simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

private theorem resolveBlock_preserves_state {blocks : List String} {name : String}
    {initial final : List String} {identifier : BlockId}
    (run : (resolveBlock blocks name).run initial = .ok (identifier, final)) :
    final = initial := by
  unfold resolveBlock at run
  generalize foundEq : blocks.findIdx? (· == name) = found at run
  cases found with
  | none =>
      simp [StateT.run, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run
  | some index =>
      simp [StateT.run, pure, StateT.pure, Except.pure] at run
      exact run.2.symm

theorem parseTerminator_preserves (blocks : List String) (line : Line) :
    PreservesInterning (parseTerminator blocks line) Terminator.variableOccurrences := by
  intro names prior terminator finalNames invariant run
  unfold parseTerminator at run
  split at run
  case h_1 =>
    simp [StateT.run, pure, StateT.pure, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [Terminator.variableOccurrences] using invariant
  case h_2 =>
    simp [StateT.run, pure, StateT.pure, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [Terminator.variableOccurrences] using invariant
  case h_3 =>
    obtain ⟨target, targetNames, targetRun, returnRun⟩ := run_bind_ok run
    have targetNamesEq := resolveBlock_preserves_state targetRun
    subst targetNames
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [Terminator.variableOccurrences] using invariant
  case h_4 _ condition _ _ =>
    obtain ⟨conditionId, conditionNames, conditionRun, afterConditionRun⟩ :=
      run_bind_ok run
    have afterCondition := internVariable_preserves condition names prior conditionId
      conditionNames invariant conditionRun
    obtain ⟨thenTarget, thenNames, thenRun, afterThenRun⟩ :=
      run_bind_ok afterConditionRun
    obtain ⟨elseTarget, elseNames, elseRun, returnRun⟩ := run_bind_ok afterThenRun
    have thenNamesEq := resolveBlock_preserves_state thenRun
    have elseNamesEq := resolveBlock_preserves_state elseRun
    subst thenNames
    subst elseNames
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    simpa [Terminator.variableOccurrences] using afterCondition
  case h_5 =>
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

def blockBodyOccurrences (body : Array Stmt × Terminator) : List VarId :=
  statementOccurrences body.1.toList ++ body.2.variableOccurrences

theorem parseBlockBody_preserves (functions blocks : List String) (lines : List Line) :
    PreservesInterning (parseBlockBody functions blocks lines) blockBodyOccurrences := by
  induction lines with
  | nil =>
      intro names prior body finalNames invariant run
      simp [parseBlockBody, StateT.run, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run
  | cons line rest induction =>
      cases rest with
      | nil =>
          intro names prior body finalNames invariant run
          simp only [parseBlockBody] at run
          obtain ⟨terminator, terminatorNames, terminatorRun, returnRun⟩ := run_bind_ok run
          have afterTerminator := parseTerminator_preserves blocks line names prior
            terminator terminatorNames invariant terminatorRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          simpa [blockBodyOccurrences, statementOccurrences] using afterTerminator
      | cons next following =>
          intro names prior body finalNames invariant run
          simp only [parseBlockBody] at run
          obtain ⟨statements, statementNames, statementRun, followingRun⟩ :=
            run_bind_ok run
          obtain ⟨bodyResult, bodyNames, bodyRun, returnRun⟩ :=
            run_bind_ok followingRun
          have afterStatements := parseStatement_preserves functions line names prior
            statements statementNames invariant statementRun
          have afterBody := induction statementNames
            (prior ++ statementOccurrences statements) bodyResult bodyNames
            afterStatements bodyRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases bodyResult with ⟨followingStatements, terminator⟩
          rcases returnRun with ⟨rfl, rfl⟩
          simpa [blockBodyOccurrences, statementOccurrences, List.flatMap_append,
            List.append_assoc] using afterBody

def blockHeaderOccurrences (header : Array VarId × Array VarId) : List VarId :=
  header.1.toList ++ header.2.toList

theorem parseBlockHeader_preserves (line : Line) :
    PreservesInterning (parseBlockHeader line) blockHeaderOccurrences := by
  intro names prior header finalNames invariant run
  unfold parseBlockHeader at run
  split at run
  · rename_i name rest
    split at run
    · rename_i reversedSignature equality
      obtain ⟨inputs, inputNames, inputRun, outputRun⟩ := run_bind_ok run
      obtain ⟨outputs, outputNames, outputsRun, returnRun⟩ := run_bind_ok outputRun
      have afterInputs := variableList_preserves _ names prior inputs inputNames
        invariant inputRun
      have afterOutputs := variableList_preserves _ inputNames
        (prior ++ inputs.toList) outputs outputNames afterInputs outputsRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [blockHeaderOccurrences, List.append_assoc] using afterOutputs
    · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run
  · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

theorem parseBlock_preserves (functions blocks : List String) (header : Line)
    (body : List Line) :
    PreservesInterning (parseBlock functions blocks header body)
      Block.variableOccurrences := by
  intro names prior block finalNames invariant run
  unfold parseBlock at run
  obtain ⟨headerResult, headerNames, headerRun, bodyFollowingRun⟩ := run_bind_ok run
  obtain ⟨bodyResult, bodyNames, bodyRun, returnRun⟩ := run_bind_ok bodyFollowingRun
  rcases headerResult with ⟨inputs, outputs⟩
  rcases bodyResult with ⟨statements, terminator⟩
  have afterHeader := parseBlockHeader_preserves header names prior (inputs, outputs)
    headerNames invariant headerRun
  have afterBody := parseBlockBody_preserves functions blocks body headerNames
    (prior ++ blockHeaderOccurrences (inputs, outputs)) (statements, terminator)
    bodyNames afterHeader bodyRun
  simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
  rcases returnRun with ⟨rfl, rfl⟩
  simpa [blockHeaderOccurrences, blockBodyOccurrences, statementOccurrences,
    Block.variableOccurrences, List.append_assoc] using afterBody

def blocksOccurrences (blocks : List Block) : List VarId :=
  blocks.flatMap Block.variableOccurrences

theorem mapM_parseBlock_preserves (functions blocks : List String)
    (groups : List (Line × List Line)) :
    PreservesInterning
      (groups.mapM fun group => parseBlock functions blocks group.fst group.snd)
      blocksOccurrences := by
  induction groups with
  | nil =>
      intro names prior parsed finalNames invariant run
      simp [StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      change InterningInvariant names (prior ++ [])
      simpa using invariant
  | cons group rest induction =>
      intro names prior parsed finalNames invariant run
      simp only [List.mapM_cons] at run
      obtain ⟨block, blockNames, blockRun, restFollowingRun⟩ := run_bind_ok run
      obtain ⟨following, followingNames, restRun, returnRun⟩ :=
        run_bind_ok restFollowingRun
      have afterBlock := parseBlock_preserves functions blocks group.fst group.snd names
        prior block blockNames invariant blockRun
      have afterRest := induction blockNames
        (prior ++ block.variableOccurrences) following followingNames afterBlock restRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [blocksOccurrences, List.append_assoc] using afterRest

theorem parseFunction_preserves (functions : List String) (body : List Line) :
    PreservesInterning (parseFunction functions body) Function.variableOccurrences := by
  intro names prior function finalNames invariant run
  unfold parseFunction at run
  generalize groupsEq : splitBlocks body = groupsResult at run
  cases groupsResult with
  | error message =>
      simp [StateT.run, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run
  | ok groups =>
      unfold parseFunctionGroups at run
      simp [StateT.run, bind, StateT.bind, liftM, monadLift, MonadLift.monadLift,
        StateT.lift, Except.bind] at run
      generalize blocksEq : groups.mapM (fun group => blockHeaderName group.fst) =
        blocksResult at run
      cases blocksResult with
      | error message => simp at run
      | ok blockNames =>
          by_cases duplicates : hasDuplicates blockNames
          · simp [duplicates, bind, StateT.bind, pure, Except.pure, Except.bind, throw, throwThe,
              MonadExceptOf.throw, StateT.lift] at run
          · simp [duplicates, bind, StateT.bind, pure, StateT.pure, Except.pure,
              Except.bind] at run
            generalize parsedEq :
              (groups.mapM fun group => parseBlock functions blockNames group.fst group.snd)
                names = parsedResult
            rw [parsedEq] at run
            cases parsedResult with
            | error message => contradiction
            | ok result =>
                rcases result with ⟨parsed, parsedNames⟩
                change Except.ok
                  ({ blocks := parsed.toArray, entry := ⟨0⟩ }, parsedNames) =
                    Except.ok (function, finalNames) at run
                simp only [Except.ok.injEq, Prod.mk.injEq] at run
                rcases run with ⟨rfl, rfl⟩
                have afterParsed := mapM_parseBlock_preserves functions blockNames groups
                  names prior parsed parsedNames invariant parsedEq
                simpa [Function.variableOccurrences, blocksOccurrences] using afterParsed

def functionsOccurrences (functions : List Function) : List VarId :=
  functions.flatMap Function.variableOccurrences

theorem mapM_parseFunction_preserves (names : List String)
    (groups : List (String × List Line)) :
    PreservesInterning
      (groups.mapM fun group => parseFunction names group.snd)
      functionsOccurrences := by
  induction groups with
  | nil =>
      intro stateNames prior parsed finalNames invariant run
      simp [StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simpa [functionsOccurrences] using invariant
  | cons group rest induction =>
      intro stateNames prior parsed finalNames invariant run
      simp only [List.mapM_cons] at run
      obtain ⟨function, functionNames, functionRun, restFollowingRun⟩ := run_bind_ok run
      obtain ⟨following, followingNames, restRun, returnRun⟩ :=
        run_bind_ok restFollowingRun
      have afterFunction := parseFunction_preserves names group.snd stateNames prior
        function functionNames invariant functionRun
      have afterRest := induction functionNames
        (prior ++ function.variableOccurrences) following followingNames afterFunction restRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      simpa [functionsOccurrences, List.append_assoc] using afterRest

theorem parseTokens_canonical {tokens : List Token} {program : Program}
    (parsed : parseTokens tokens = .ok program) : program.Canonical := by
  unfold parseTokens at parsed
  generalize splitEq : splitFunctions (splitLines tokens) = groupsResult at parsed
  cases groupsResult with
  | error message => contradiction
  | ok groups =>
      unfold parseProgramGroups at parsed
      let names := groups.map Prod.fst
      by_cases duplicates : hasDuplicates names
      · simp [names, duplicates, bind, Except.bind] at parsed
      · simp [names, duplicates, bind, Except.bind] at parsed
        generalize functionsRunEq :
          (parseFunctionGroupsList names groups).run [] = functionsResult
          at parsed
        cases functionsResult with
        | error message => simp [pure, Except.pure] at parsed
        | ok result =>
            rcases result with ⟨functions, finalNames⟩
            have invariant := mapM_parseFunction_preserves names groups [] [] functions
              finalNames .empty functionsRunEq
            have namesEq : names = groups.map Prod.fst := rfl
            generalize initEq : names.findIdx? (· == "init") = initResult
            cases initResult with
            | none =>
                have groupInitEq :
                    groups.findIdx? ((fun name => name == "init") ∘ Prod.fst) = none := by
                  simpa [names, List.findIdx?_map, Function.comp_def] using initEq
                simp only [pure, Except.pure] at parsed
                rw [groupInitEq] at parsed
                contradiction
            | some initEntry =>
                have groupInitEq :
                    groups.findIdx? ((fun name => name == "init") ∘ Prod.fst) = some initEntry := by
                  simpa [names, List.findIdx?_map, Function.comp_def] using initEq
                simp only [pure, Except.pure] at parsed
                rw [groupInitEq] at parsed
                simp only [Except.ok.injEq] at parsed
                subst program
                apply InterningInvariant.canonical
                simpa [Program.variableOccurrences, functionsOccurrences] using invariant

namespace Proofs

theorem parse_canonical {source : String} {program : Program}
    (parsed : parse source = .ok program) : program.Canonical :=
  parseTokens_canonical parsed

end Proofs
end Sir.Vars.Text
