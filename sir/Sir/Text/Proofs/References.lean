import Sir.Text.Proofs.ParseNormal

namespace Sir.Vars

def Stmt.FunctionReferencesInRange (functionCount : Nat) : Stmt → Prop
  | .icall callee _ _ => callee.id < functionCount
  | _ => True

def Terminator.BlockReferencesInRange (blockCount : Nat) : Terminator → Prop
  | .jump target => target.id < blockCount
  | .branch _ thenTarget elseTarget =>
      thenTarget.id < blockCount ∧ elseTarget.id < blockCount
  | _ => True

def Block.ReferencesInRange (functionCount blockCount : Nat)
    (block : Block) : Prop :=
  (∀ statement ∈ block.statements,
    statement.FunctionReferencesInRange functionCount) ∧
  block.terminator.BlockReferencesInRange blockCount

def Function.ReferencesInRange (functionCount : Nat) (function : Function) : Prop :=
  ∀ block ∈ function.blocks,
    block.ReferencesInRange functionCount function.blocks.size

def Program.ReferencesInRange (program : Program) : Prop :=
  ∀ function ∈ program.functions,
    function.ReferencesInRange program.functions.size

end Sir.Vars

namespace Sir.Vars.Text

private theorem findIdx?_bound {α : Type} {values : List α}
    {predicate : α → Bool} {index : Nat}
    (found : values.findIdx? predicate = some index) :
    index < values.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1

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

private theorem parseMnemonic_functionReferencesInRange
    (functions : List String) (line : Line) (mnemonic : String)
    (results : List VarId) (parameters : List Token)
    {names finalNames : List String} {statements : List Stmt}
    (run : (parseMnemonic functions line mnemonic results parameters).run names =
      .ok (statements, finalNames)) :
    ∀ statement ∈ statements,
      statement.FunctionReferencesInRange functions.length := by
  unfold parseMnemonic at run
  split at run
  all_goals repeat' split at run
  all_goals
    simp_all [StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift,
      Stmt.FunctionReferencesInRange]
  all_goals grind [findIdx?_bound]

private theorem liftNumbers_functionReferencesInRange (functionCount : Nat)
    (tokens : List Token)
    {names finalNames : List String} {result : List Stmt × List Token}
    (run : (liftNumbers tokens).run names = .ok (result, finalNames)) :
    ∀ statement ∈ result.1,
      statement.FunctionReferencesInRange functionCount := by
  induction tokens generalizing names finalNames result with
  | nil =>
      simp [liftNumbers, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simp
  | cons token rest induction =>
      cases token with
      | number value =>
          simp only [liftNumbers] at run
          obtain ⟨target, targetNames, targetRun, followingRun⟩ := run_bind_ok run
          obtain ⟨following, followingNames, restRun, returnRun⟩ :=
            run_bind_ok followingRun
          have valid := induction restRun
          rcases following with ⟨preludes, liftedTokens⟩
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          simpa [Stmt.FunctionReferencesInRange] using valid
      | identifier | label | equals | arrow | fatArrow | colon | question |
          leftBrace | rightBrace | newline | invalid =>
          simp only [liftNumbers] at run
          obtain ⟨following, followingNames, restRun, returnRun⟩ := run_bind_ok run
          have valid := induction restRun
          rcases following with ⟨preludes, liftedTokens⟩
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          exact valid

private theorem parseStatement_functionReferencesInRange
    (functions : List String) (line : Line)
    {names finalNames : List String} {statements : List Stmt}
    (run : (parseStatement functions line).run names = .ok (statements, finalNames)) :
    ∀ statement ∈ statements,
      statement.FunctionReferencesInRange functions.length := by
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
                                simp [Stmt.FunctionReferencesInRange]
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
            have liftedValid :=
              liftNumbers_functionReferencesInRange (functionCount := functions.length)
                parameters liftedRun
            have bodyValid := parseMnemonic_functionReferencesInRange functions line mnemonic
              results.toList liftedTokens mnemonicRun
            simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
            rcases returnRun with ⟨rfl, rfl⟩
            simpa using List.forall_mem_append.mpr ⟨liftedValid, bodyValid⟩
      | _ =>
          simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

private theorem resolveBlock_bound {blocks : List String} {name : String}
    {initial final : List String} {identifier : BlockId}
    (run : (resolveBlock blocks name).run initial = .ok (identifier, final)) :
    identifier.id < blocks.length := by
  unfold resolveBlock at run
  generalize foundEq : blocks.findIdx? (· == name) = found at run
  cases found with
  | none =>
      simp [StateT.run, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run
  | some index =>
      simp [StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      exact findIdx?_bound foundEq

private theorem parseTerminator_blockReferencesInRange
    (blocks : List String) (line : Line)
    {names finalNames : List String} {terminator : Terminator}
    (run : (parseTerminator blocks line).run names = .ok (terminator, finalNames)) :
    terminator.BlockReferencesInRange blocks.length := by
  unfold parseTerminator at run
  split at run
  case h_1 =>
    simp [StateT.run, pure, StateT.pure, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    trivial
  case h_2 =>
    simp [StateT.run, pure, StateT.pure, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    trivial
  case h_3 =>
    obtain ⟨target, targetNames, targetRun, returnRun⟩ := run_bind_ok run
    have targetBound := resolveBlock_bound targetRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    exact targetBound
  case h_4 =>
    obtain ⟨condition, conditionNames, conditionRun, afterConditionRun⟩ :=
      run_bind_ok run
    obtain ⟨thenTarget, thenNames, thenRun, afterThenRun⟩ :=
      run_bind_ok afterConditionRun
    obtain ⟨elseTarget, elseNames, elseRun, returnRun⟩ := run_bind_ok afterThenRun
    have thenBound := resolveBlock_bound thenRun
    have elseBound := resolveBlock_bound elseRun
    simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
    rcases returnRun with ⟨rfl, rfl⟩
    exact ⟨thenBound, elseBound⟩
  case h_5 =>
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift] at run

private theorem parseBlockBody_referencesInRange
    (functions blocks : List String) (lines : List Line)
    {names finalNames : List String} {body : Array Stmt × Terminator}
    (run : (parseBlockBody functions blocks lines).run names = .ok (body, finalNames)) :
    (∀ statement ∈ body.1,
      statement.FunctionReferencesInRange functions.length) ∧
    body.2.BlockReferencesInRange blocks.length := by
  induction lines generalizing names finalNames body with
  | nil =>
      simp [parseBlockBody, StateT.run, throw, throwThe, MonadExceptOf.throw,
        StateT.lift] at run
  | cons line rest induction =>
      cases rest with
      | nil =>
          simp only [parseBlockBody] at run
          obtain ⟨terminator, terminatorNames, terminatorRun, returnRun⟩ := run_bind_ok run
          have terminatorValid :=
            parseTerminator_blockReferencesInRange blocks line terminatorRun
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          exact ⟨by simp, terminatorValid⟩
      | cons next following =>
          simp only [parseBlockBody] at run
          obtain ⟨statements, statementNames, statementRun, followingRun⟩ :=
            run_bind_ok run
          obtain ⟨bodyResult, bodyNames, bodyRun, returnRun⟩ :=
            run_bind_ok followingRun
          have statementsValid :=
            parseStatement_functionReferencesInRange functions line statementRun
          have bodyValid := induction bodyRun
          rcases bodyResult with ⟨followingStatements, terminator⟩
          simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
          rcases returnRun with ⟨rfl, rfl⟩
          refine ⟨?_, bodyValid.2⟩
          intro statement member
          simp only [Array.mem_append, List.mem_toArray] at member
          exact member.elim (statementsValid statement) (bodyValid.1 statement)

private theorem parseBlock_referencesInRange
    (functions blocks : List String) (header : Line) (lines : List Line)
    {names finalNames : List String} {block : Block}
    (run : (parseBlock functions blocks header lines).run names =
      .ok (block, finalNames)) :
    block.ReferencesInRange functions.length blocks.length := by
  unfold parseBlock at run
  obtain ⟨headerResult, headerNames, headerRun, bodyFollowingRun⟩ := run_bind_ok run
  obtain ⟨bodyResult, bodyNames, bodyRun, returnRun⟩ := run_bind_ok bodyFollowingRun
  rcases headerResult with ⟨inputs, outputs⟩
  rcases bodyResult with ⟨statements, terminator⟩
  have bodyValid := parseBlockBody_referencesInRange functions blocks lines bodyRun
  simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
  rcases returnRun with ⟨rfl, rfl⟩
  exact bodyValid

private theorem except_mapM_length {α β ε : Type} (action : α → Except ε β) :
    ∀ {values : List α} {results : List β},
      values.mapM action = .ok results → results.length = values.length := by
  intro values
  induction values with
  | nil =>
      intro results run
      simp [pure, Except.pure] at run
      rcases run with rfl
      rfl
  | cons value following induction =>
      intro results run
      simp only [List.mapM_cons, bind, Except.bind] at run
      cases actionRun : action value with
      | error message => simp [actionRun] at run
      | ok result =>
          simp only [actionRun] at run
          cases followingRun : following.mapM action with
          | error message => simp [followingRun] at run
          | ok followingResults =>
              simp [followingRun, pure, Except.pure] at run
              rcases run with rfl
              simp [induction followingRun]

private theorem mapM_parseBlock_referencesInRange
    (functions blocks : List String) (groups : List (Line × List Line))
    {names finalNames : List String} {parsed : List Block}
    (run : (groups.mapM fun group =>
      parseBlock functions blocks group.fst group.snd).run names =
        .ok (parsed, finalNames)) :
    parsed.length = groups.length ∧
    ∀ block ∈ parsed,
      block.ReferencesInRange functions.length blocks.length := by
  induction groups generalizing names finalNames parsed with
  | nil =>
      simp [StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simp
  | cons group rest induction =>
      simp only [List.mapM_cons] at run
      obtain ⟨block, blockNames, blockRun, restFollowingRun⟩ := run_bind_ok run
      obtain ⟨following, followingNames, restRun, returnRun⟩ :=
        run_bind_ok restFollowingRun
      have blockValid := parseBlock_referencesInRange functions blocks
        group.fst group.snd blockRun
      have followingValid := induction restRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      refine ⟨by simp [followingValid.1], ?_⟩
      intro candidate member
      rcases List.mem_cons.mp member with rfl | followingMember
      · exact blockValid
      · exact followingValid.2 candidate followingMember

private theorem parseFunction_referencesInRange (functions : List String) (body : List Line)
    {names finalNames : List String} {function : Function}
    (run : (parseFunction functions body).run names = .ok (function, finalNames)) :
    function.ReferencesInRange functions.length := by
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
                have blockNamesLength := except_mapM_length
                  (fun group : Line × List Line => blockHeaderName group.fst) blocksEq
                have parsedValid := mapM_parseBlock_referencesInRange
                  functions blockNames groups parsedEq
                cases parsed with
                | nil =>
                    simp [throw, throwThe, MonadExceptOf.throw, StateT.lift] at run
                | cons entry rest =>
                    change Except.ok
                      ({ entry := entry, rest := rest.toArray }, parsedNames) =
                        Except.ok (function, finalNames) at run
                    simp only [Except.ok.injEq, Prod.mk.injEq] at run
                    rcases run with ⟨rfl, rfl⟩
                    intro block member
                    have blockValid := parsedValid.2 block
                      (by simpa [Function.blocks] using member)
                    simpa [Function.blocks, parsedValid.1, blockNamesLength] using blockValid

private theorem mapM_parseFunction_referencesInRange
    (names : List String) (groups : List (String × List Line))
    {stateNames finalNames : List String} {functions : List Function}
    (run : (parseFunctionGroupsList names groups).run stateNames =
      .ok (functions, finalNames)) :
    functions.length = groups.length ∧
    ∀ function ∈ functions, function.ReferencesInRange names.length := by
  induction groups generalizing stateNames finalNames functions with
  | nil =>
      simp [parseFunctionGroupsList, StateT.run, pure, StateT.pure, Except.pure] at run
      rcases run with ⟨rfl, rfl⟩
      simp
  | cons group rest induction =>
      simp only [parseFunctionGroupsList, List.mapM_cons] at run
      obtain ⟨function, functionNames, functionRun, restFollowingRun⟩ := run_bind_ok run
      obtain ⟨following, followingNames, restRun, returnRun⟩ :=
        run_bind_ok restFollowingRun
      have functionValid := parseFunction_referencesInRange names group.snd functionRun
      have followingValid := induction restRun
      simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
      rcases returnRun with ⟨rfl, rfl⟩
      refine ⟨by simp [followingValid.1], ?_⟩
      intro candidate member
      rcases List.mem_cons.mp member with rfl | followingMember
      · exact functionValid
      · exact followingValid.2 candidate followingMember

private theorem parseFunctionSlots_referencesInRange (names : List String)
    (initGroup : String × List Line) (following : List (String × List Line))
    {stateNames finalNames : List String} {slots : Function × List Function}
    (run : (parseFunctionSlots names initGroup following).run stateNames =
      .ok (slots, finalNames)) :
    slots.2.length = following.length ∧
    ∀ function ∈ slots.1 :: slots.2, function.ReferencesInRange names.length := by
  unfold parseFunctionSlots at run
  obtain ⟨init, initNames, initRun, followingRun⟩ := run_bind_ok run
  obtain ⟨parsed, parsedNames, parsedRun, returnRun⟩ := run_bind_ok followingRun
  have initValid := parseFunction_referencesInRange names initGroup.snd initRun
  have followingValid := mapM_parseFunction_referencesInRange names following parsedRun
  simp [StateT.run, pure, StateT.pure, Except.pure] at returnRun
  rcases returnRun with ⟨rfl, rfl⟩
  refine ⟨followingValid.1, ?_⟩
  intro function member
  rcases List.mem_cons.mp member with rfl | followingMember
  · exact initValid
  · exact followingValid.2 function followingMember

private theorem parseProgramSlots_referencesInRange {initGroup : String × List Line}
    {mainGroup : Option (String × List Line)} {others : List (String × List Line)}
    {program : Program}
    (parsed : parseProgramSlots initGroup mainGroup others = .ok program) :
    program.ReferencesInRange := by
  unfold parseProgramSlots at parsed
  simp only [] at parsed
  split at parsed
  · simp at parsed
  · rename_i result slotsEq
    rcases result with ⟨slots, slotNames⟩
    simp only [Except.ok.injEq] at parsed
    subst program
    have valid := parseFunctionSlots_referencesInRange _ initGroup _ slotsEq
    have sizeEq : (programOfSlots mainGroup.isSome slots.1 slots.2).functions.size =
        (initGroup.fst :: (mainGroup.toList ++ others).map Prod.fst).length := by
      simp [programOfSlots_functions, valid.1]
    intro function member
    rw [sizeEq]
    exact valid.2 function (by simpa [programOfSlots_functions] using member)

private theorem parseProgramGroups_referencesInRange {groups : List (String × List Line)}
    {program : Program} (parsed : parseProgramGroups groups = .ok program) :
    program.ReferencesInRange := by
  unfold parseProgramGroups at parsed
  by_cases duplicates : hasDuplicates (groups.map Prod.fst)
  · simp [duplicates, bind, Except.bind] at parsed
  · simp only [duplicates, Bool.false_eq_true, if_false, bind, Except.bind, pure,
      Except.pure] at parsed
    cases initEq : groups.find? (fun group => group.fst == "init") with
    | none =>
        rw [initEq] at parsed
        simp at parsed
    | some initGroup =>
        rw [initEq] at parsed
        exact parseProgramSlots_referencesInRange parsed

private theorem parseTokens_referencesInRange {tokens : List Token} {program : Program}
    (parsed : parseTokens tokens = .ok program) : program.ReferencesInRange := by
  unfold parseTokens at parsed
  generalize splitEq : splitFunctions (splitLines tokens) = groupsResult at parsed
  cases groupsResult with
  | error message => contradiction
  | ok groups => exact parseProgramGroups_referencesInRange parsed

namespace Proofs

theorem parse_referencesInRange {source : String} {program : Program}
    (parsed : parse source = .ok program) : program.ReferencesInRange :=
  parseTokens_referencesInRange parsed

end Proofs
end Sir.Vars.Text
