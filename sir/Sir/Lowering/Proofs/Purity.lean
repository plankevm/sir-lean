import Sir.Lowering.Proofs.Replay

namespace Sir.Lowering

theorem Symbolic.operationOf_not_memory_oracle (statement : Vars.Stmt)
    (symbolicOperation : Machine.Operation × List Symbolic.Value × Symbolic.Value)
    (supported : Symbolic.operationOf statement = some symbolicOperation) :
    ¬ statement.isMemOracle := by
  cases statement with
  | assign result expression =>
      cases expression <;> simp [Symbolic.operationOf, Vars.Stmt.isMemOracle] at supported ⊢
  | sstore => simp [Symbolic.operationOf] at supported
  | gas => simp [Symbolic.operationOf] at supported
  | call => simp [Symbolic.operationOf] at supported
  | malloc => simp [Symbolic.operationOf] at supported
  | mallocUninit => simp [Symbolic.operationOf] at supported
  | mstore32 => simp [Symbolic.operationOf] at supported
  | mload32 => simp [Symbolic.operationOf] at supported
  | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.operationOf_decodes_pure {statement : Vars.Stmt}
    {symbolicOperation : Machine.Operation × List Symbolic.Value × Symbolic.Value}
    (supported : Symbolic.operationOf statement = some symbolicOperation) :
    (Vars.decodeStatement statement).kind = .primitive symbolicOperation.1 ∧
      symbolicOperation.1 ≠ .gas ∧ symbolicOperation.1 ≠ .call := by
  obtain ⟨operation, operands, resultValue⟩ := symbolicOperation
  cases statement with
  | assign result expression =>
      cases expression <;>
        simp only [Symbolic.operationOf, Option.some.injEq, Prod.mk.injEq,
          reduceCtorEq] at supported
      all_goals obtain ⟨rfl, -, -⟩ := supported
      all_goals simp [Vars.decodeStatement, Vars.decodeExpression]
  | _ => simp [Symbolic.operationOf] at supported

theorem Symbolic.State.fireNextStatement_eq_some
    (state nextState : Symbolic.State) (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation)
    (fire : state.fireNextStatement sourceStatements operation = some nextState) :
    ∃ statement statementIndex operands result,
      state.firstFireable sourceStatements operation =
          some (statement, statementIndex) ∧
        Symbolic.operationOf statement = some (operation, operands, result) ∧
        state.fireable sourceStatements operation
          (statement, statementIndex) = true ∧
        nextState = { state with
          stack := result :: state.stack.drop operands.length
          firedStatementIndices := statementIndex :: state.firedStatementIndices } := by
  unfold Symbolic.State.fireNextStatement at fire
  cases foundEq : state.firstFireable sourceStatements operation with
  | none => simp [foundEq] at fire
  | some candidate =>
      obtain ⟨statement, statementIndex⟩ := candidate
      obtain ⟨_, canFire⟩ :=
        state.firstFireable_eq_some sourceStatements operation statement
          statementIndex foundEq
      cases operationEq : Symbolic.operationOf statement with
      | none => simp [foundEq, operationEq] at fire
      | some symbolicOperation =>
          obtain ⟨expectedOperation, operands, result⟩ := symbolicOperation
          simp only [Symbolic.State.fireable, operationEq,
            decide_eq_true_eq] at canFire
          rcases canFire with ⟨notFired, rfl, stackBound, stackPrefix, resultAbsent,
            readsAvailable⟩
          simp [foundEq, operationEq] at fire
          subst nextState
          refine ⟨statement, statementIndex, operands, result, ?_, ?_, ?_, rfl⟩
          · simp
          · simpa using operationEq
          · simp only [Symbolic.State.fireable, operationEq,
              decide_eq_true_eq]
            exact ⟨notFired, trivial, stackBound, stackPrefix, resultAbsent, readsAvailable⟩

theorem Symbolic.execute_preserves_fired_statement_indices
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState)
    (valid : state.firedStatementIndices.Nodup ∧
      ∀ index ∈ state.firedStatementIndices, index < sourceStatements.size) :
    nextState.firedStatementIndices.Nodup ∧
      ∀ index ∈ nextState.firedStatementIndices, index < sourceStatements.size := by
  cases instruction with
  | swap depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact valid
  | exchange firstDepth secondDepth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact valid
  | dup depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, value, _, rfl⟩ := replay
      exact valid
  | pop =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          simp [Symbolic.execute, stackEq] at replay
          subst nextState
          exact valid
  | op operation =>
      simp only [Symbolic.execute] at replay
      obtain ⟨statement, statementIndex, operands, result, foundEq, operationEq, canFire,
          rfl⟩ := state.fireNextStatement_eq_some nextState sourceStatements operation replay
      obtain ⟨statementAt, _⟩ :=
        state.firstFireable_eq_some sourceStatements operation statement
          statementIndex foundEq
      simp only [Symbolic.State.fireable, operationEq,
        decide_eq_true_eq] at canFire
      refine ⟨List.nodup_cons.mpr ⟨canFire.1, valid.1⟩, ?_⟩
      intro index member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (Array.getElem?_eq_some_iff.mp statementAt).1
      · exact valid.2 index member
  | flippedOp operation =>
      simp only [Symbolic.execute] at replay
      split at replay <;> rename_i binary
      · split at replay <;> rename_i exchangeEq
        · simp at replay
        · rename_i stack
          obtain ⟨statement, statementIndex, operands, result, foundEq, operationEq, canFire,
              rfl⟩ := ({ state with stack } : Symbolic.State).fireNextStatement_eq_some
                nextState sourceStatements operation replay
          obtain ⟨statementAt, _⟩ :=
            ({ state with stack } : Symbolic.State).firstFireable_eq_some
              sourceStatements operation statement statementIndex foundEq
          simp only [Symbolic.State.fireable, operationEq,
            decide_eq_true_eq] at canFire
          refine ⟨List.nodup_cons.mpr ⟨canFire.1, valid.1⟩, ?_⟩
          intro index member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact (Array.getElem?_eq_some_iff.mp statementAt).1
          · exact valid.2 index member
      · simp at replay
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at replay
  | store slot =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          cases bindingEq : state.slotValue? slot with
          | some binding => simp [Symbolic.execute, stackEq, bindingEq] at replay
          | none =>
              simp [Symbolic.execute, stackEq, bindingEq] at replay
              subst nextState
              exact valid
  | load slot =>
      simp [Symbolic.execute] at replay
      obtain ⟨value, _, rfl⟩ := replay
      exact valid

theorem Symbolic.executeList_preserves_fired_statement_indices
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState)
    (valid : state.firedStatementIndices.Nodup ∧
      ∀ index ∈ state.firedStatementIndices, index < sourceStatements.size) :
    finalState.firedStatementIndices.Nodup ∧
      ∀ index ∈ finalState.firedStatementIndices, index < sourceStatements.size := by
  induction targetInstructions generalizing state with
  | nil =>
      simp at replay
      subst finalState
      exact valid
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          exact inductionHypothesis nextState replay
            (Symbolic.execute_preserves_fired_statement_indices sourceStatements state
              nextState instruction replayInstruction valid)

theorem Symbolic.executeAll_preserves_fired_statement_indices
    (sourceStatements : Array Vars.Stmt) (targetInstructions : Array Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : Symbolic.executeAll sourceStatements targetInstructions state = some finalState)
    (valid : state.firedStatementIndices.Nodup ∧
      ∀ index ∈ state.firedStatementIndices, index < sourceStatements.size) :
    finalState.firedStatementIndices.Nodup ∧
      ∀ index ∈ finalState.firedStatementIndices, index < sourceStatements.size := by
  apply Symbolic.executeList_preserves_fired_statement_indices sourceStatements
    targetInstructions.toList state finalState
  · simpa [Symbolic.executeAll] using replay
  · exact valid

theorem fired_statement_indices_complete (state : Symbolic.State)
    (sourceStatements : Array Vars.Stmt) (nodup : state.firedStatementIndices.Nodup)
    (bounded : ∀ index ∈ state.firedStatementIndices, index < sourceStatements.size)
    (firedAll : state.firedCount = sourceStatements.size) :
    ∀ index < sourceStatements.size, index ∈ state.firedStatementIndices := by
  intro index indexBound
  by_contra absent
  have extendedNodup : (index :: state.firedStatementIndices).Nodup :=
    List.nodup_cons.mpr ⟨absent, nodup⟩
  have subset : (index :: state.firedStatementIndices).toFinset ⊆
      Finset.range sourceStatements.size := by
    intro candidate member
    simp only [List.mem_toFinset, List.mem_cons] at member
    simp only [Finset.mem_range]
    rcases member with rfl | member
    · exact indexBound
    · exact bounded candidate member
  have cardBound := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup extendedNodup, Finset.card_range] at cardBound
  have lengthEq : state.firedStatementIndices.length = sourceStatements.size := by
    simpa [Symbolic.State.firedCount] using firedAll
  simp only [List.length_cons] at cardBound
  omega

def Symbolic.State.ValuesAvailable (state : Symbolic.State)
    (sourceStatements : Array Vars.Stmt) : Prop :=
  (∀ value ∈ state.stack,
    state.available sourceStatements value.identifier = true) ∧
  ∀ binding ∈ state.slotBindings,
    state.available sourceStatements binding.2.identifier = true

theorem Symbolic.State.initial_values_available (sourceStatements : Array Vars.Stmt)
    (entryLayout : Array Symbolic.Value) :
    (Symbolic.State.initial entryLayout).ValuesAvailable sourceStatements := by
  constructor
  · intro value member
    simp [Symbolic.State.initial, Symbolic.State.available]
    exact ⟨value, by simpa [Symbolic.State.initial] using member, rfl⟩
  · intro binding member
    simp [Symbolic.State.initial] at member

theorem Symbolic.exchange_subset (stack nextStack : List Symbolic.Value)
    (firstDepth secondDepth : Nat)
    (exchanged : Symbolic.exchange stack firstDepth secondDepth = some nextStack) :
    nextStack ⊆ stack := by
  unfold Symbolic.exchange at exchanged
  cases firstEq : stack[firstDepth]? with
  | none => simp [firstEq] at exchanged
  | some first =>
      cases secondEq : stack[secondDepth]? with
      | none => simp [firstEq, secondEq] at exchanged
      | some second =>
          simp [firstEq, secondEq] at exchanged
          subst nextStack
          intro value member
          rcases List.mem_or_eq_of_mem_set member with member | rfl
          · rcases List.mem_or_eq_of_mem_set member with member | rfl
            · exact member
            · exact List.mem_of_getElem? secondEq
          · exact List.mem_of_getElem? firstEq

theorem Symbolic.State.available_after_fire
    (state : Symbolic.State) (sourceStatements : Array Vars.Stmt)
    (statementIndex : Nat) (identifier : VarId)
    (available : state.available sourceStatements identifier = true) :
    ({ state with firedStatementIndices := statementIndex :: state.firedStatementIndices } :
      Symbolic.State).available sourceStatements identifier = true := by
  unfold Symbolic.State.available at available ⊢
  simp only [List.any_cons, Bool.or_eq_true] at available ⊢
  exact available.elim Or.inl (fun remaining => Or.inr (Or.inr remaining))

theorem Symbolic.execute_preserves_values_available
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState)
    (available : state.ValuesAvailable sourceStatements) :
    nextState.ValuesAvailable sourceStatements := by
  cases instruction with
  | swap depth =>
      change (if 1 ≤ depth ∧ depth ≤ 16 then
          (Symbolic.exchange state.stack 0 depth).map fun stack => { state with stack }
        else none) = some nextState at replay
      by_cases depthWithinReach : 1 ≤ depth ∧ depth ≤ 16
      · rw [if_pos depthWithinReach] at replay
        cases exchanged : Symbolic.exchange state.stack 0 depth with
        | none => simp [exchanged] at replay
        | some nextStack =>
            simp [exchanged] at replay
            subst nextState
            exact ⟨fun value member => available.1 value
              (Symbolic.exchange_subset state.stack nextStack 0 depth exchanged member),
              available.2⟩
      · simp [depthWithinReach] at replay
  | exchange firstDepth secondDepth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, nextStack, exchanged, rfl⟩ := replay
      exact ⟨fun value member => available.1 value
        (Symbolic.exchange_subset state.stack nextStack firstDepth secondDepth exchanged member),
        available.2⟩
  | dup depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨depthBound, value, valueAt, nextStateEq⟩ := replay
      subst nextState
      refine ⟨?_, available.2⟩
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact available.1 candidate (List.mem_of_getElem? valueAt)
      · exact available.1 candidate member
  | pop =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          simp [Symbolic.execute, stackEq] at replay
          subst nextState
          exact ⟨fun candidate member => available.1 candidate (by simp [stackEq, member]),
            available.2⟩
  | op operation =>
      simp only [Symbolic.execute] at replay
      unfold Symbolic.State.fireNextStatement at replay
      cases foundEq : state.firstFireable sourceStatements operation with
      | none => simp [foundEq] at replay
      | some candidate =>
          obtain ⟨statement, statementIndex⟩ := candidate
          obtain ⟨statementAt, canFire⟩ :=
            state.firstFireable_eq_some sourceStatements operation statement
              statementIndex foundEq
          cases symbolicOperationEq : Symbolic.operationOf statement with
          | none => simp [foundEq, symbolicOperationEq] at replay
          | some symbolicOperation =>
              obtain ⟨expectedOperation, symbolicOperands, symbolicResult⟩ := symbolicOperation
              obtain ⟨result, rfl⟩ := Symbolic.operationOf_result_variable statement
                expectedOperation symbolicOperands symbolicResult symbolicOperationEq
              simp [foundEq, symbolicOperationEq] at replay
              subst nextState
              have resultDefined := Symbolic.operationOf_result_mem statement
                expectedOperation symbolicOperands result symbolicOperationEq
              have resultAvailable :
                  ({ state with
                    firedStatementIndices := statementIndex :: state.firedStatementIndices } :
                    Symbolic.State).available sourceStatements result = true := by
                simp [Symbolic.State.available, Symbolic.definesVariable,
                  statementAt, resultDefined]
              constructor
              · intro value member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact resultAvailable
                · exact state.available_after_fire sourceStatements statementIndex
                    value.identifier (available.1 value (List.mem_of_mem_drop member))
              · intro binding member
                exact state.available_after_fire sourceStatements statementIndex
                  binding.2.identifier (available.2 binding member)
  | flippedOp operation =>
      simp only [Symbolic.execute] at replay
      split at replay
      · split at replay <;> rename_i exchangeEq
        · simp at replay
        · rename_i stack
          let flippedState : Symbolic.State := { state with stack }
          have flippedAvailable : flippedState.ValuesAvailable sourceStatements :=
            ⟨fun value member => available.1 value
                (Symbolic.exchange_subset state.stack stack 0 1 exchangeEq member),
              available.2⟩
          change flippedState.fireNextStatement sourceStatements operation = some nextState
            at replay
          unfold Symbolic.State.fireNextStatement at replay
          cases foundEq : flippedState.firstFireable sourceStatements operation with
          | none => simp [foundEq] at replay
          | some candidate =>
              obtain ⟨statement, statementIndex⟩ := candidate
              obtain ⟨statementAt, canFire⟩ :=
                flippedState.firstFireable_eq_some sourceStatements operation
                  statement statementIndex foundEq
              cases symbolicOperationEq : Symbolic.operationOf statement with
              | none => simp [foundEq, symbolicOperationEq] at replay
              | some symbolicOperation =>
                  obtain ⟨expectedOperation, symbolicOperands, symbolicResult⟩ := symbolicOperation
                  obtain ⟨result, rfl⟩ :=
                    Symbolic.operationOf_result_variable statement expectedOperation
                      symbolicOperands symbolicResult symbolicOperationEq
                  simp [foundEq, symbolicOperationEq] at replay
                  subst nextState
                  have resultDefined := Symbolic.operationOf_result_mem statement
                    expectedOperation symbolicOperands result symbolicOperationEq
                  have resultAvailable :
                      ({ flippedState with firedStatementIndices :=
                          statementIndex :: flippedState.firedStatementIndices } :
                        Symbolic.State).available sourceStatements result = true := by
                    simp [Symbolic.State.available,
                      Symbolic.definesVariable, statementAt, resultDefined]
                  constructor
                  · intro value member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact resultAvailable
                    · exact flippedState.available_after_fire sourceStatements
                        statementIndex value.identifier
                        (flippedAvailable.1 value (List.mem_of_mem_drop member))
                  · intro binding member
                    exact flippedState.available_after_fire sourceStatements
                      statementIndex binding.2.identifier (flippedAvailable.2 binding member)
      · simp at replay
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at replay
  | store slot =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          cases bindingEq : state.slotValue? slot with
          | some binding => simp [Symbolic.execute, stackEq, bindingEq] at replay
          | none =>
              simp [Symbolic.execute, stackEq, bindingEq] at replay
              subst nextState
              refine ⟨fun candidate member => available.1 candidate (by simp [stackEq, member]), ?_⟩
              intro binding member
              rw [Array.mem_push] at member
              rcases member with member | rfl
              · exact available.2 binding member
              · exact available.1 value (by simp [stackEq])
  | load slot =>
      simp [Symbolic.execute] at replay
      obtain ⟨loadedValue, valueAt, nextStateEq⟩ := replay
      subst nextState
      refine ⟨?_, available.2⟩
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · obtain ⟨binding, bindingMember, bindingValue⟩ :=
          state.slotValue?_member slot candidate valueAt
        rw [← bindingValue]
        exact available.2 binding bindingMember
      · exact available.1 candidate member

theorem Symbolic.executeList_preserves_values_available
    (sourceStatements : Array Vars.Stmt) (instructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : instructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState) (available : state.ValuesAvailable sourceStatements) :
    finalState.ValuesAvailable sourceStatements := by
  induction instructions generalizing state with
  | nil =>
      simp at replay
      subst finalState
      exact available
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          exact inductionHypothesis nextState replay
            (Symbolic.execute_preserves_values_available sourceStatements state nextState
              instruction replayInstruction available)

theorem Symbolic.executeAll_preserves_values_available
    (sourceStatements : Array Vars.Stmt) (instructions : Array Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : Symbolic.executeAll sourceStatements instructions state = some finalState)
    (available : state.ValuesAvailable sourceStatements) :
    finalState.ValuesAvailable sourceStatements := by
  apply Symbolic.executeList_preserves_values_available sourceStatements
    instructions.toList state finalState
  · simpa [Symbolic.executeAll] using replay
  · exact available

theorem Symbolic.execute_preserves_not_memory_oracle
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle) :
    ∀ index ∈ nextState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle := by
  cases instruction with
  | swap depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact supported
  | exchange firstDepth secondDepth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact supported
  | dup depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, value, _, rfl⟩ := replay
      exact supported
  | pop =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          simp [Symbolic.execute, stackEq] at replay
          subst nextState
          exact supported
  | op operation =>
      simp only [Symbolic.execute] at replay
      unfold Symbolic.State.fireNextStatement at replay
      cases foundEq : state.firstFireable sourceStatements operation with
      | none => simp [foundEq] at replay
      | some candidate =>
          obtain ⟨firedStatement, statementIndex⟩ := candidate
          obtain ⟨statementEq, canFire⟩ :=
            state.firstFireable_eq_some sourceStatements operation
              firedStatement statementIndex foundEq
          cases operationEq : Symbolic.operationOf firedStatement with
          | none => simp [foundEq, operationEq] at replay
          | some symbolicOperation =>
              obtain ⟨expectedOperation, operands, result⟩ := symbolicOperation
              simp [foundEq, operationEq] at replay
              subst nextState
              intro index member statement statementAt
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · obtain rfl := Option.some.inj (statementEq.symm.trans statementAt)
                exact Symbolic.operationOf_not_memory_oracle firedStatement
                  (expectedOperation, operands, result) operationEq
              · exact supported index member statement statementAt
  | flippedOp operation =>
      simp only [Symbolic.execute] at replay
      split at replay
      · split at replay
        · simp at replay
        · rename_i stack exchangeEq
          obtain ⟨firedStatement, statementIndex, operands, result, foundEq, operationEq,
              canFire, rfl⟩ :=
            ({ state with stack } : Symbolic.State).fireNextStatement_eq_some nextState
              sourceStatements operation replay
          obtain ⟨statementEq, _⟩ :=
            ({ state with stack } : Symbolic.State).firstFireable_eq_some
              sourceStatements operation firedStatement statementIndex foundEq
          intro index member statement statementAt
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · obtain rfl := Option.some.inj (statementEq.symm.trans statementAt)
            exact Symbolic.operationOf_not_memory_oracle firedStatement
              (operation, operands, result) operationEq
          · exact supported index member statement statementAt
      · simp at replay
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at replay
  | store slot =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          cases bindingEq : state.slotValue? slot with
          | some binding => simp [Symbolic.execute, stackEq, bindingEq] at replay
          | none =>
              simp [Symbolic.execute, stackEq, bindingEq] at replay
              subst nextState
              exact supported
  | load slot =>
      simp [Symbolic.execute] at replay
      obtain ⟨value, _, rfl⟩ := replay
      exact supported

theorem Symbolic.executeList_not_memory_oracle (sourceStatements : Array Vars.Stmt)
    (targetInstructions : List Stack.Instr) (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle) :
    ∀ index ∈ finalState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle := by
  induction targetInstructions generalizing state with
  | nil =>
      simp at replay
      subst finalState
      exact supported
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          exact inductionHypothesis nextState replay
            (Symbolic.execute_preserves_not_memory_oracle sourceStatements state nextState
              instruction replayInstruction supported)

theorem Symbolic.executeAll_not_memory_oracle (sourceStatements : Array Vars.Stmt)
    (targetInstructions : Array Stack.Instr) (state finalState : Symbolic.State)
    (replay : Symbolic.executeAll sourceStatements targetInstructions state = some finalState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle) :
    ∀ index ∈ finalState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement → ¬ statement.isMemOracle := by
  apply Symbolic.executeList_not_memory_oracle sourceStatements
    targetInstructions.toList state finalState
  · simpa [Symbolic.executeAll] using replay
  · exact supported

theorem Symbolic.execute_preserves_supported_source_statements
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation) :
    ∀ index ∈ nextState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation := by
  cases instruction with
  | swap depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact supported
  | exchange firstDepth secondDepth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, stack, _, rfl⟩ := replay
      exact supported
  | dup depth =>
      simp [Symbolic.execute] at replay
      obtain ⟨_, value, _, rfl⟩ := replay
      exact supported
  | pop =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          simp [Symbolic.execute, stackEq] at replay
          subst nextState
          exact supported
  | op operation =>
      simp only [Symbolic.execute] at replay
      unfold Symbolic.State.fireNextStatement at replay
      cases foundEq : state.firstFireable sourceStatements operation with
      | none => simp [foundEq] at replay
      | some candidate =>
          obtain ⟨firedStatement, statementIndex⟩ := candidate
          obtain ⟨statementEq, canFire⟩ :=
            state.firstFireable_eq_some sourceStatements operation
              firedStatement statementIndex foundEq
          cases operationEq : Symbolic.operationOf firedStatement with
          | none => simp [foundEq, operationEq] at replay
          | some symbolicOperation =>
              obtain ⟨expectedOperation, operands, result⟩ := symbolicOperation
              simp [foundEq, operationEq] at replay
              subst nextState
              intro index member statement statementAt
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · obtain rfl := Option.some.inj (statementEq.symm.trans statementAt)
                exact ⟨(expectedOperation, operands, result), operationEq⟩
              · exact supported index member statement statementAt
  | flippedOp operation =>
      simp only [Symbolic.execute] at replay
      split at replay
      · split at replay
        · simp at replay
        · rename_i stack exchangeEq
          obtain ⟨firedStatement, statementIndex, operands, result, foundEq, operationEq,
              canFire, rfl⟩ :=
            ({ state with stack } : Symbolic.State).fireNextStatement_eq_some nextState
              sourceStatements operation replay
          obtain ⟨statementEq, _⟩ :=
            ({ state with stack } : Symbolic.State).firstFireable_eq_some
              sourceStatements operation firedStatement statementIndex foundEq
          intro index member statement statementAt
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · obtain rfl := Option.some.inj (statementEq.symm.trans statementAt)
            exact ⟨(operation, operands, result), operationEq⟩
          · exact supported index member statement statementAt
      · simp at replay
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at replay
  | store slot =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at replay
      | cons value stack =>
          cases bindingEq : state.slotValue? slot with
          | some binding => simp [Symbolic.execute, stackEq, bindingEq] at replay
          | none =>
              simp [Symbolic.execute, stackEq, bindingEq] at replay
              subst nextState
              exact supported
  | load slot =>
      simp [Symbolic.execute] at replay
      obtain ⟨value, _, rfl⟩ := replay
      exact supported

theorem Symbolic.executeList_supported_source_statements
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation) :
    ∀ index ∈ finalState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation := by
  induction targetInstructions generalizing state with
  | nil =>
      simp at replay
      subst finalState
      exact supported
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          exact inductionHypothesis nextState replay
            (Symbolic.execute_preserves_supported_source_statements sourceStatements state
              nextState instruction replayInstruction supported)

theorem Symbolic.executeAll_supported_source_statements
    (sourceStatements : Array Vars.Stmt) (targetInstructions : Array Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : Symbolic.executeAll sourceStatements targetInstructions state = some finalState)
    (supported : ∀ index ∈ state.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation) :
    ∀ index ∈ finalState.firedStatementIndices, ∀ statement,
      sourceStatements[index]? = some statement →
        ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation := by
  apply Symbolic.executeList_supported_source_statements sourceStatements
    targetInstructions.toList state finalState
  · simpa [Symbolic.executeAll] using replay
  · exact supported

theorem StackSchedule.Block.statements_not_memory_oracle
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ statement ∈ certificate.vars.statements, ¬ statement.isMemOracle := by
  obtain ⟨finalState, _, replay, _, fired, _, _, _⟩ := certificate.check_sound accepted
  have supported := Symbolic.executeAll_not_memory_oracle certificate.vars.statements
    certificate.stack.instructions (Symbolic.State.initial certificate.vars.entryLayout)
    finalState replay (by simp [Symbolic.State.initial])
  obtain ⟨nodup, bounded⟩ := Symbolic.executeAll_preserves_fired_statement_indices
    certificate.vars.statements certificate.stack.instructions
    (Symbolic.State.initial certificate.vars.entryLayout) finalState replay
    (by simp [Symbolic.State.initial])
  have complete := fired_statement_indices_complete finalState certificate.vars.statements
    nodup bounded fired
  intro statement statementMember
  rw [Array.mem_iff_getElem] at statementMember
  obtain ⟨index, indexBound, rfl⟩ := statementMember
  exact supported index (complete index indexBound)
    certificate.vars.statements[index] (by simp)

theorem StackSchedule.Block.statements_supported
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ statement ∈ certificate.vars.statements,
      ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation := by
  obtain ⟨finalState, _, replay, _, fired, _, _, _⟩ := certificate.check_sound accepted
  have supported := Symbolic.executeAll_supported_source_statements
    certificate.vars.statements certificate.stack.instructions
    (Symbolic.State.initial certificate.vars.entryLayout) finalState replay
    (by simp [Symbolic.State.initial])
  obtain ⟨nodup, bounded⟩ := Symbolic.executeAll_preserves_fired_statement_indices
    certificate.vars.statements certificate.stack.instructions
    (Symbolic.State.initial certificate.vars.entryLayout) finalState replay
    (by simp [Symbolic.State.initial])
  have complete := fired_statement_indices_complete finalState certificate.vars.statements
    nodup bounded fired
  intro statement statementMember
  rw [Array.mem_iff_getElem] at statementMember
  obtain ⟨index, indexBound, rfl⟩ := statementMember
  exact supported index (complete index indexBound)
    certificate.vars.statements[index] (by simp)

theorem StackSchedule.Block.sourceOrderReferenceLocals_exists
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ())
    (entryLocals : Locals) (entryValues : List Word)
    (interpretations : certificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret entryLocals) = some entryValues) :
    ∃ referenceLocals,
      sourceOrderReferenceLocals certificate.vars.statements entryLocals =
        some referenceLocals := by
  obtain ⟨usesAvailable, _⟩ :=
    StackSchedule.Block.check_source_valid certificate accepted
  apply Sir.Lowering.sourceOrderReferenceLocals_exists certificate.vars.statements
    certificate.vars.entryLayout entryLocals usesAvailable
    (certificate.statements_supported accepted)
  exact Symbolic.Value.interpretations_cover_variables certificate.vars.entryLayout.toList entryValues
    entryLocals interpretations

theorem StackSchedule.vars_program_memOracleFree
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ()) :
    certificate.vars.MemOracleFree := by
  intro statement hasStatement
  rcases hasStatement with ⟨function, functionMember, block, blockMember, statementMember⟩
  simp [StackSchedule.vars] at functionMember
  subst function
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, rfl⟩ := blockMember
  have certificateIndexBound : index < certificate.blocks.size := by
    simpa [StackSchedule.vars] using indexBound
  let blockCertificate := certificate.blocks[index]'certificateIndexBound
  have blockGet : certificate.blocks[index]'certificateIndexBound = blockCertificate := rfl
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt :=
      (certificate.check_sound accepted).2.1 index certificateIndexBound
    simpa [blockGet] using acceptedAt
  apply blockCertificate.statements_not_memory_oracle blockAccepted statement
  simpa [StackSchedule.Block.Source.toBlock, blockGet] using statementMember

theorem StackSchedule.vars_program_statements_supported
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ()) :
    ∀ statement, certificate.vars.HasStmt statement →
      ∃ symbolicOperation, Symbolic.operationOf statement = some symbolicOperation := by
  intro statement hasStatement
  rcases hasStatement with ⟨function, functionMember, block, blockMember, statementMember⟩
  simp [StackSchedule.vars] at functionMember
  subst function
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, rfl⟩ := blockMember
  have certificateIndexBound : index < certificate.blocks.size := by
    simpa [StackSchedule.vars] using indexBound
  let blockCertificate := certificate.blocks[index]'certificateIndexBound
  have blockGet : certificate.blocks[index]'certificateIndexBound = blockCertificate := rfl
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt :=
      (certificate.check_sound accepted).2.1 index certificateIndexBound
    simpa [blockGet] using acceptedAt
  apply blockCertificate.statements_supported blockAccepted statement
  simpa [StackSchedule.Block.Source.toBlock, blockGet] using statementMember

theorem StackSchedule.source_decode_primitive_pure
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    {control next : Machine.MachineControl} {operation : Machine.Operation}
    {src : Vars.frame.Source} {dst : Vars.frame.Destination}
    (decode : Vars.decode certificate.vars control =
      some (⟨Machine.Instruction.Kind.primitive operation, src, dst⟩, next)) :
    operation ≠ .gas ∧ operation ≠ .call := by
  obtain ⟨statement, statementAt, decoded⟩ := Vars.decode_inv.mp decode
  obtain ⟨symbolicOperation, supported⟩ :=
    certificate.vars_program_statements_supported accepted statement
      (Vars.Program.decodeStmt_mem statementAt)
  obtain ⟨kindEq, notGas, notCall⟩ := Symbolic.operationOf_decodes_pure supported
  rw [decoded] at kindEq
  simp at kindEq
  subst kindEq
  exact ⟨notGas, notCall⟩

theorem StackSchedule.source_decode_icall_false
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    {control next : Machine.MachineControl} {callee : FunctionId}
    {src : Vars.frame.Source} {dst : Vars.frame.Destination}
    (decode : Vars.decode certificate.vars control =
      some (⟨Machine.Instruction.Kind.icall callee, src, dst⟩, next)) : False := by
  obtain ⟨statement, statementAt, decoded⟩ := Vars.decode_inv.mp decode
  obtain ⟨symbolicOperation, supported⟩ :=
    certificate.vars_program_statements_supported accepted statement
      (Vars.Program.decodeStmt_mem statementAt)
  obtain ⟨kindEq, -, -⟩ := Symbolic.operationOf_decodes_pure supported
  rw [decoded] at kindEq
  simp at kindEq

theorem StackSchedule.vars_program_terminator_not_iret
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ())
    (cursor : Machine.ProgramCursor) (block : Vars.Block)
    (blockAt : certificate.vars.block? cursor = some block) :
    block.terminator ≠ .iret := by
  rcases cursor with ⟨⟨functionIndex⟩, ⟨blockIndex⟩, position⟩
  rcases functionIndex with _ | functionIndex
  · simp [StackSchedule.vars, Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?] at blockAt
    obtain ⟨blockCertificate, certificateBlockAt, blockSourceEq⟩ := blockAt
    have certificateBlockBound : blockIndex < certificate.blocks.size :=
      of_getElem?_eq_some (c := certificate.blocks) (i := blockIndex) certificateBlockAt
    have blockGet : certificate.blocks[blockIndex] = blockCertificate :=
      (Array.getElem?_eq_some_iff.mp certificateBlockAt).2
    have blockAccepted : blockCertificate.check = .ok () := by
      have acceptedAt :=
        (certificate.check_sound accepted).2.1 blockIndex certificateBlockBound
      simpa [blockGet] using acceptedAt
    obtain ⟨_, expectedStack, _, expected, _⟩ :=
      blockCertificate.check_sound blockAccepted
    rw [← blockSourceEq]
    intro terminator
    change blockCertificate.vars.terminator = .iret at terminator
    simp [terminator, StackSchedule.Block.finalStack] at expected
  · simp [StackSchedule.vars, Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?] at blockAt

theorem StackSchedule.stack_program_terminator_not_iret
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ())
    (cursor : Machine.ProgramCursor) (block : Stack.Block)
    (blockAt : certificate.stack.block? cursor = some block) :
    block.terminator ≠ .iret := by
  rcases cursor with ⟨⟨functionIndex⟩, ⟨blockIndex⟩, position⟩
  rcases functionIndex with _ | functionIndex
  · simp [StackSchedule.stack, Stack.Program.block?,
      Stack.Program.function?, Stack.Function.block?] at blockAt
    obtain ⟨blockCertificate, certificateBlockAt, blockTargetEq⟩ := blockAt
    have certificateBlockBound : blockIndex < certificate.blocks.size :=
      of_getElem?_eq_some (c := certificate.blocks) (i := blockIndex) certificateBlockAt
    have blockGet : certificate.blocks[blockIndex] = blockCertificate :=
      (Array.getElem?_eq_some_iff.mp certificateBlockAt).2
    have blockAccepted : blockCertificate.check = .ok () := by
      have acceptedAt :=
        (certificate.check_sound accepted).2.1 blockIndex certificateBlockBound
      simpa [blockGet] using acceptedAt
    obtain ⟨_, _, _, _, _, terminatorsAgree, _⟩ :=
      blockCertificate.check_sound blockAccepted
    rw [← blockTargetEq]
    intro terminator
    change blockCertificate.stack.terminator = .iret at terminator
    cases blockCertificate.vars.terminator <;>
      simp [terminator, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  · simp [StackSchedule.stack, Stack.Program.block?,
      Stack.Program.function?, Stack.Function.block?] at blockAt

theorem stackDecodeInstruction_next_running
    (program : Stack.Program) (control next : Machine.MachineControl)
    (instruction : Stack.Instr)
    (decode : program.decodeInstruction control = some (next, instruction)) :
    ∃ cursor, next = .running cursor := by
  cases control with
  | returned results => simp [Stack.Program.decodeInstruction] at decode
  | halted => simp [Stack.Program.decodeInstruction] at decode
  | running cursor =>
      rcases cursor with ⟨function, block, position⟩
      cases position with
      | terminator => simp [Stack.Program.decodeInstruction] at decode
      | statement index =>
          cases blockAt : program.block? ⟨function, block, .statement index⟩ with
          | none => simp [Stack.Program.decodeInstruction, blockAt] at decode
          | some stackBlock =>
              cases instructionAt : stackBlock.instructions[index]? with
              | none =>
                  simp [Stack.Program.decodeInstruction, blockAt, instructionAt] at decode
              | some decodedInstruction =>
                  simp [Stack.Program.decodeInstruction, blockAt, instructionAt] at decode
                  exact ⟨_, decode.1.symm⟩

theorem stackJump_next_running
    (program : Stack.Program) (environment nextEnvironment : Stack.Environment)
    (cursor : Machine.ProgramCursor) (target : BlockId) (next : Machine.MachineControl)
    (jump : Stack.jump program environment cursor target = some (nextEnvironment, next)) :
    ∃ nextCursor, next = .running nextCursor := by
  unfold Stack.jump at jump
  cases sourceAt : program.block? cursor with
  | none => simp [sourceAt] at jump
  | some source =>
      cases targetAt : program.block? { cursor with block := target } with
      | none => simp [sourceAt, targetAt] at jump
      | some targetBlock =>
          by_cases mismatch : environment.stack.length ≠ source.outputCount ∨
              source.outputCount ≠ targetBlock.inputCount
          · simp [sourceAt, targetAt, mismatch] at jump
          · simp [sourceAt, targetAt, mismatch] at jump
            exact ⟨_, jump.2.symm⟩

theorem stackTerminatorAt_inv {program : Stack.Program} {control : Machine.MachineControl}
    {terminator : Stack.Terminator}
    (terminatorAt : program.terminatorAt control = some terminator) :
    ∃ cursor block, control = .running cursor ∧ program.block? cursor = some block ∧
      block.terminator = terminator := by
  cases control with
  | returned values => simp [Stack.Program.terminatorAt] at terminatorAt
  | halted => simp [Stack.Program.terminatorAt] at terminatorAt
  | running cursor =>
      cases position : cursor.position with
      | statement index => simp [Stack.Program.terminatorAt, position] at terminatorAt
      | terminator =>
          cases blockAt : program.block? cursor with
          | none => simp [Stack.Program.terminatorAt, position, blockAt] at terminatorAt
          | some block =>
              simp [Stack.Program.terminatorAt, position, blockAt] at terminatorAt
              exact ⟨cursor, block, rfl, blockAt, terminatorAt⟩

theorem stackDecode_decodeInstruction {program : Stack.Program}
    {control next : Machine.MachineControl} {instruction : Machine.Instruction Stack.frame}
    (decode : Stack.decode program control = some (instruction, next)) :
    ∃ decodedInstruction, program.decodeInstruction control = some (next, decodedInstruction) := by
  unfold Stack.decode at decode
  split at decode <;> simp_all

theorem stackDecode_next_running {program : Stack.Program}
    {control next : Machine.MachineControl} {instruction : Machine.Instruction Stack.frame}
    (decode : Stack.decode program control = some (instruction, next)) :
    ∃ cursor, next = .running cursor := by
  obtain ⟨decodedInstruction, instructionDecode⟩ := stackDecode_decodeInstruction decode
  exact stackDecodeInstruction_next_running program control next decodedInstruction
    instructionDecode

theorem stackDecode_primitive_inv {program : Stack.Program}
    {control next : Machine.MachineControl} {operation : Machine.Operation}
    {src : Stack.Source} {dst : Stack.Destination}
    (decode : Stack.decode program control =
      some (⟨Machine.Instruction.Kind.primitive operation, src, dst⟩, next)) :
    program.decodeInstruction control = some (next, .op operation) ∨
      program.decodeInstruction control = some (next, .flippedOp operation) := by
  unfold Stack.decode at decode
  split at decode <;> simp_all

theorem stackDecode_icall_inv {program : Stack.Program}
    {control next : Machine.MachineControl} {callee : FunctionId}
    {src : Stack.Source} {dst : Stack.Destination}
    (decode : Stack.decode program control =
      some (⟨Machine.Instruction.Kind.icall callee, src, dst⟩, next)) :
    ∃ argumentCount resultCount,
      program.decodeInstruction control = some (next, .icall callee argumentCount resultCount) := by
  unfold Stack.decode at decode
  split at decode <;> simp_all

theorem stackControl_trace_nil {program : Stack.Program} {env env' : Stack.Environment}
    {globals globals' : Globals} {control next : Machine.MachineControl} {trace : Trace}
    (controlStep : Stack.control program env globals control =
      some (trace, env', globals', next)) :
    trace = [] := by
  unfold Stack.control at controlStep
  repeat' split at controlStep
  all_goals grind [Option.bind_eq_some_iff]

theorem stackControl_returned_inv {program : Stack.Program} {env env' : Stack.Environment}
    {globals globals' : Globals} {control : Machine.MachineControl} {trace : Trace}
    {results : Array Word}
    (controlStep : Stack.control program env globals control =
      some (trace, env', globals', .returned results)) :
    ∃ cursor block, control = .running cursor ∧ program.block? cursor = some block ∧
      block.terminator = .iret := by
  cases instructionDecode : program.decodeInstruction control with
  | some decoded =>
      obtain ⟨instructionNext, instruction⟩ := decoded
      obtain ⟨cursor, rfl⟩ := stackDecodeInstruction_next_running program control instructionNext
        instruction instructionDecode
      cases instruction <;>
        simp [Stack.control, instructionDecode, Option.bind_eq_some_iff] at controlStep
      all_goals split at controlStep <;> simp_all
  | none =>
      cases terminatorAt : program.terminatorAt control with
      | none =>
          simp [Stack.control, instructionDecode, terminatorAt] at controlStep
          split at controlStep <;> simp_all
      | some terminator =>
          obtain ⟨cursor, block, controlEq, blockAt, terminatorEq⟩ :=
            stackTerminatorAt_inv terminatorAt
          subst controlEq
          cases terminator with
          | halt => simp [Stack.control, instructionDecode, terminatorAt] at controlStep
          | jump target =>
              cases jumpAt : Stack.jump program env cursor target with
              | none => simp [Stack.control, instructionDecode, terminatorAt, jumpAt] at controlStep
              | some jumpResult =>
                  obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                  obtain ⟨nextCursor, rfl⟩ := stackJump_next_running program env jumpEnvironment
                    cursor target jumpControl jumpAt
                  simp [Stack.control, instructionDecode, terminatorAt, jumpAt] at controlStep
          | branch thenTarget elseTarget =>
              cases stackAt : env.stack with
              | nil =>
                  simp [Stack.control, instructionDecode, terminatorAt, stackAt] at controlStep
              | cons condition stack =>
                  cases jumpAt : Stack.jump program { env with stack } cursor
                      (if condition = 0 then elseTarget else thenTarget) with
                  | none =>
                      simp [Stack.control, instructionDecode, terminatorAt, stackAt, jumpAt]
                        at controlStep
                  | some jumpResult =>
                      obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                      obtain ⟨nextCursor, rfl⟩ := stackJump_next_running program
                        { env with stack } jumpEnvironment cursor
                        (if condition = 0 then elseTarget else thenTarget) jumpControl jumpAt
                      simp [Stack.control, instructionDecode, terminatorAt, stackAt, jumpAt]
                        at controlStep
          | iret => exact ⟨cursor, block, rfl, blockAt, terminatorEq⟩

theorem Symbolic.execute_source_operation (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.op operation) = some nextState) :
    ∃ (statement : Vars.Stmt) (statementIndex : Nat) (operands : List Symbolic.Value)
        (result : Symbolic.Value),
      sourceStatements[statementIndex]? = some statement ∧
        Symbolic.operationOf statement = some (operation, operands, result) := by
  simp only [Symbolic.execute] at replay
  unfold Symbolic.State.fireNextStatement at replay
  cases foundEq : state.firstFireable sourceStatements operation with
  | none => simp [foundEq] at replay
  | some candidate =>
      obtain ⟨statement, statementIndex⟩ := candidate
      obtain ⟨statementAt, canFire⟩ :=
        state.firstFireable_eq_some sourceStatements operation statement
          statementIndex foundEq
      cases operationEq : Symbolic.operationOf statement with
      | none => simp [foundEq, operationEq] at replay
      | some symbolicOperation =>
          obtain ⟨expectedOperation, operands, result⟩ := symbolicOperation
          simp only [Symbolic.State.fireable, operationEq,
            decide_eq_true_eq] at canFire
          rw [canFire.2.1] at operationEq
          exact ⟨statement, statementIndex, operands, result, statementAt, operationEq⟩

theorem Symbolic.execute_source_flipped_operation (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.flippedOp operation) =
      some nextState) :
    operation.inputCount = 2 ∧
      ∃ (statement : Vars.Stmt) (statementIndex : Nat) (operands : List Symbolic.Value)
          (result : Symbolic.Value),
        sourceStatements[statementIndex]? = some statement ∧
          Symbolic.operationOf statement = some (operation, operands, result) := by
  simp only [Symbolic.execute] at replay
  split at replay <;> rename_i binary
  · split at replay
    · simp at replay
    · rename_i stack exchangeEq
      obtain ⟨statement, statementIndex, operands, result, foundEq, operationEq, canFire,
          nextStateEq⟩ :=
        ({ state with stack } : Symbolic.State).fireNextStatement_eq_some nextState
          sourceStatements operation replay
      obtain ⟨statementAt, _⟩ :=
        ({ state with stack } : Symbolic.State).firstFireable_eq_some
          sourceStatements operation statement statementIndex foundEq
      exact ⟨binary, statement, statementIndex, operands, result, statementAt, operationEq⟩
  · simp at replay

theorem Symbolic.execute_not_mload (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState) :
    instruction ≠ .op .mload32 := by
  intro instructionEq
  subst instruction
  obtain ⟨statement, statementIndex, operands, result, statementAt, supported⟩ :=
    Symbolic.execute_source_operation sourceStatements state nextState .mload32 replay
  cases statement with
    | assign result expression =>
        cases expression <;> simp [Symbolic.operationOf] at supported
    | sstore => simp [Symbolic.operationOf] at supported
    | gas => simp [Symbolic.operationOf] at supported
    | call => simp [Symbolic.operationOf] at supported
    | malloc => simp [Symbolic.operationOf] at supported
    | mallocUninit => simp [Symbolic.operationOf] at supported
    | mstore32 => simp [Symbolic.operationOf] at supported
    | mload32 => simp [Symbolic.operationOf] at supported
    | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.execute_not_malloc (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState) :
    instruction ≠ .op .malloc := by
  intro instructionEq
  subst instruction
  obtain ⟨statement, statementIndex, operands, result, statementAt, supported⟩ :=
    Symbolic.execute_source_operation sourceStatements state nextState .malloc replay
  cases statement with
    | assign result expression =>
        cases expression <;> simp [Symbolic.operationOf] at supported
    | sstore => simp [Symbolic.operationOf] at supported
    | gas => simp [Symbolic.operationOf] at supported
    | call => simp [Symbolic.operationOf] at supported
    | malloc => simp [Symbolic.operationOf] at supported
    | mallocUninit => simp [Symbolic.operationOf] at supported
    | mstore32 => simp [Symbolic.operationOf] at supported
    | mload32 => simp [Symbolic.operationOf] at supported
    | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.execute_not_mallocUninit (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState) :
    instruction ≠ .op .mallocUninit := by
  intro instructionEq
  subst instruction
  obtain ⟨statement, statementIndex, operands, result, statementAt, supported⟩ :=
    Symbolic.execute_source_operation sourceStatements state nextState .mallocUninit replay
  cases statement with
    | assign result expression =>
        cases expression <;> simp [Symbolic.operationOf] at supported
    | sstore => simp [Symbolic.operationOf] at supported
    | gas => simp [Symbolic.operationOf] at supported
    | call => simp [Symbolic.operationOf] at supported
    | malloc => simp [Symbolic.operationOf] at supported
    | mallocUninit => simp [Symbolic.operationOf] at supported
    | mstore32 => simp [Symbolic.operationOf] at supported
    | mload32 => simp [Symbolic.operationOf] at supported
    | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.execute_excludes_internal_calls (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (instruction : Stack.Instr)
    (replay : Symbolic.execute sourceStatements state instruction = some nextState) :
    ∀ callee argumentCount resultCount,
      instruction ≠ .icall callee argumentCount resultCount := by
  intro callee argumentCount resultCount instructionEq
  subst instruction
  simp [Symbolic.execute] at replay

theorem Symbolic.execute_operation_supported (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.op operation) = some nextState) :
    (∃ value, operation = .constant value) ∨ operation = .copy ∨
      operation = .add ∨ operation = .lt := by
  obtain ⟨statement, statementIndex, operands, result, statementAt, supported⟩ :=
    Symbolic.execute_source_operation sourceStatements state nextState operation replay
  cases statement with
    | assign result expression =>
        cases expression with
        | constant value =>
            simp [Symbolic.operationOf] at supported
            exact .inl ⟨value, supported.1.symm⟩
        | var source =>
            simp [Symbolic.operationOf] at supported
            exact .inr (.inl supported.1.symm)
        | add lhs rhs =>
            simp [Symbolic.operationOf] at supported
            exact .inr (.inr (.inl supported.1.symm))
        | lt lhs rhs =>
            simp [Symbolic.operationOf] at supported
            exact .inr (.inr (.inr supported.1.symm))
        | sload key => simp [Symbolic.operationOf] at supported
    | sstore => simp [Symbolic.operationOf] at supported
    | gas => simp [Symbolic.operationOf] at supported
    | call => simp [Symbolic.operationOf] at supported
    | malloc => simp [Symbolic.operationOf] at supported
    | mallocUninit => simp [Symbolic.operationOf] at supported
    | mstore32 => simp [Symbolic.operationOf] at supported
    | mload32 => simp [Symbolic.operationOf] at supported
    | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.execute_flipped_operation_supported
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.flippedOp operation) =
      some nextState) : operation = .add ∨ operation = .lt := by
  obtain ⟨binary, statement, statementIndex, operands, result, statementAt, supported⟩ :=
    Symbolic.execute_source_flipped_operation sourceStatements state nextState operation
      replay
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp [Symbolic.operationOf] at supported
          rw [← supported.1] at binary
          simp [Machine.Operation.inputCount] at binary
      | var source =>
          simp [Symbolic.operationOf] at supported
          rw [← supported.1] at binary
          simp [Machine.Operation.inputCount] at binary
      | add lhs rhs =>
          simp [Symbolic.operationOf] at supported
          exact .inl supported.1.symm
      | lt lhs rhs =>
          simp [Symbolic.operationOf] at supported
          exact .inr supported.1.symm
      | sload key => simp [Symbolic.operationOf] at supported
  | sstore => simp [Symbolic.operationOf] at supported
  | gas => simp [Symbolic.operationOf] at supported
  | call => simp [Symbolic.operationOf] at supported
  | malloc => simp [Symbolic.operationOf] at supported
  | mallocUninit => simp [Symbolic.operationOf] at supported
  | mstore32 => simp [Symbolic.operationOf] at supported
  | mload32 => simp [Symbolic.operationOf] at supported
  | icall => simp [Symbolic.operationOf] at supported

theorem Symbolic.executeList_operation_supported
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState) :
    ∀ operation, .op operation ∈ targetInstructions →
      (∃ value, operation = .constant value) ∨ operation = .copy ∨
        operation = .add ∨ operation = .lt := by
  induction targetInstructions generalizing state with
  | nil => simp
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          intro operation member
          simp only [List.mem_cons] at member
          rcases member with instructionEq | member
          · subst instruction
            exact Symbolic.execute_operation_supported sourceStatements state nextState
              operation replayInstruction
          · exact inductionHypothesis nextState replay operation member

theorem Symbolic.executeList_flipped_operation_supported
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState) :
    ∀ operation, .flippedOp operation ∈ targetInstructions →
      operation = .add ∨ operation = .lt := by
  induction targetInstructions generalizing state with
  | nil => simp
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          intro operation member
          simp only [List.mem_cons] at member
          rcases member with instructionEq | member
          · subst instruction
            exact Symbolic.execute_flipped_operation_supported sourceStatements state
              nextState operation replayInstruction
          · exact inductionHypothesis nextState replay operation member

theorem Symbolic.executeList_excludes_internal_calls
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState) :
    ∀ instruction ∈ targetInstructions, ∀ callee argumentCount resultCount,
      instruction ≠ .icall callee argumentCount resultCount := by
  induction targetInstructions generalizing state with
  | nil => simp
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with candidateEq | member
          · subst candidate
            exact Symbolic.execute_excludes_internal_calls sourceStatements state
              nextState instruction replayInstruction
          · exact inductionHypothesis nextState replay candidate member

theorem Symbolic.executeList_excludes_memory_oracles
    (sourceStatements : Array Vars.Stmt) (targetInstructions : List Stack.Instr)
    (state finalState : Symbolic.State)
    (replay : targetInstructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState) :
    ∀ instruction ∈ targetInstructions,
      instruction ≠ .op .mload32 ∧ instruction ≠ .op .malloc ∧
        instruction ≠ .op .mallocUninit := by
  induction targetInstructions generalizing state with
  | nil => simp
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at replay
      cases replayInstruction : Symbolic.execute sourceStatements state instruction with
      | none => simp [replayInstruction] at replay
      | some nextState =>
          rw [replayInstruction] at replay
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with candidateEq | member
          · subst candidate
            exact ⟨Symbolic.execute_not_mload sourceStatements state nextState instruction
                replayInstruction,
              Symbolic.execute_not_malloc sourceStatements state nextState instruction
                replayInstruction,
              Symbolic.execute_not_mallocUninit sourceStatements state nextState
                instruction replayInstruction⟩
          · exact inductionHypothesis nextState replay candidate member

theorem StackSchedule.Block.instructions_exclude_memory_oracles
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ instruction ∈ certificate.stack.instructions,
      instruction ≠ .op .mload32 ∧ instruction ≠ .op .malloc ∧
        instruction ≠ .op .mallocUninit := by
  obtain ⟨finalState, _, replay, _, _, _, _, _⟩ := certificate.check_sound accepted
  intro instruction instructionMember
  apply Symbolic.executeList_excludes_memory_oracles certificate.vars.statements
    certificate.stack.instructions.toList (Symbolic.State.initial certificate.vars.entryLayout)
    finalState (by simpa [Symbolic.executeAll] using replay) instruction
  simpa using instructionMember

theorem StackSchedule.Block.instructions_exclude_internal_calls
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ instruction ∈ certificate.stack.instructions, ∀ callee argumentCount resultCount,
      instruction ≠ .icall callee argumentCount resultCount := by
  obtain ⟨finalState, _, replay, _, _, _, _, _⟩ := certificate.check_sound accepted
  intro instruction instructionMember
  apply Symbolic.executeList_excludes_internal_calls certificate.vars.statements
    certificate.stack.instructions.toList (Symbolic.State.initial certificate.vars.entryLayout)
    finalState (by simpa [Symbolic.executeAll] using replay) instruction
  simpa using instructionMember

theorem StackSchedule.Block.instructions_operation_supported
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ operation, .op operation ∈ certificate.stack.instructions →
      (∃ value, operation = .constant value) ∨ operation = .copy ∨
        operation = .add ∨ operation = .lt := by
  obtain ⟨finalState, _, replay, _, _, _, _, _⟩ := certificate.check_sound accepted
  intro operation instructionMember
  apply Symbolic.executeList_operation_supported certificate.vars.statements
    certificate.stack.instructions.toList (Symbolic.State.initial certificate.vars.entryLayout)
    finalState (by simpa [Symbolic.executeAll] using replay) operation
  simpa using instructionMember

theorem StackSchedule.Block.instructions_flipped_operation_supported
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∀ operation, .flippedOp operation ∈ certificate.stack.instructions →
      operation = .add ∨ operation = .lt := by
  obtain ⟨finalState, _, replay, _, _, _, _, _⟩ := certificate.check_sound accepted
  intro operation instructionMember
  apply Symbolic.executeList_flipped_operation_supported certificate.vars.statements
    certificate.stack.instructions.toList (Symbolic.State.initial certificate.vars.entryLayout)
    finalState (by simpa [Symbolic.executeAll] using replay) operation
  simpa using instructionMember

theorem StackSchedule.target_decode_instruction_mem
    (certificate : StackSchedule) (control next : Machine.MachineControl)
    (instruction : Stack.Instr)
    (decode : certificate.stack.decodeInstruction control = some (next, instruction)) :
    ∃ blockCertificate, blockCertificate ∈ certificate.blocks ∧
      instruction ∈ blockCertificate.stack.instructions := by
  cases control with
  | returned results =>
      simp [Stack.Program.decodeInstruction] at decode
  | halted =>
      simp [Stack.Program.decodeInstruction] at decode
  | running cursor =>
      rcases cursor with ⟨⟨functionIndex⟩, ⟨blockIndex⟩, position⟩
      cases position with
      | terminator =>
          simp [Stack.Program.decodeInstruction] at decode
      | statement index =>
          rcases functionIndex with _ | functionIndex
          · simp [StackSchedule.stack,
              Stack.Program.decodeInstruction, Stack.Program.block?,
              Stack.Program.function?, Stack.Function.block?] at decode
            cases blockAt : certificate.blocks[blockIndex]? with
            | none => simp [blockAt] at decode
            | some blockCertificate =>
                cases instructionAt : blockCertificate.stack.instructions[index]? with
                | none =>
                    simp [blockAt, StackSchedule.Block.Target.toBlock,
                      instructionAt] at decode
                | some decodedInstruction =>
                    simp [blockAt, StackSchedule.Block.Target.toBlock,
                      instructionAt] at decode
                    refine ⟨blockCertificate, ?_, ?_⟩
                    · exact Array.mem_iff_getElem.mpr ⟨blockIndex,
                        of_getElem?_eq_some (c := certificate.blocks) (i := blockIndex) blockAt,
                        (Array.getElem?_eq_some_iff.mp blockAt).2⟩
                    · rw [← decode.2]
                      exact Array.mem_iff_getElem.mpr ⟨index,
                        of_getElem?_eq_some (c := blockCertificate.stack.instructions) (i := index)
                          instructionAt,
                        (Array.getElem?_eq_some_iff.mp instructionAt).2⟩
          · simp [StackSchedule.stack,
              Stack.Program.decodeInstruction, Stack.Program.block?,
              Stack.Program.function?, Stack.Function.block?] at decode

theorem StackSchedule.target_decoded_instruction_excludes_memory_oracles
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (control next : Machine.MachineControl) (instruction : Stack.Instr)
    (decode : certificate.stack.decodeInstruction control = some (next, instruction)) :
    instruction ≠ .op .mload32 ∧ instruction ≠ .op .malloc ∧
      instruction ≠ .op .mallocUninit := by
  obtain ⟨blockCertificate, blockMember, instructionMember⟩ :=
    certificate.target_decode_instruction_mem control next instruction decode
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, blockGet⟩ := blockMember
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt := (certificate.check_sound accepted).2.1 index indexBound
    simpa [blockGet] using acceptedAt
  exact blockCertificate.instructions_exclude_memory_oracles blockAccepted instruction
    instructionMember

theorem StackSchedule.target_decoded_instruction_excludes_internal_calls
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (control next : Machine.MachineControl) (instruction : Stack.Instr)
    (decode : certificate.stack.decodeInstruction control = some (next, instruction)) :
    ∀ callee argumentCount resultCount,
      instruction ≠ .icall callee argumentCount resultCount := by
  obtain ⟨blockCertificate, blockMember, instructionMember⟩ :=
    certificate.target_decode_instruction_mem control next instruction decode
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, blockGet⟩ := blockMember
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt := (certificate.check_sound accepted).2.1 index indexBound
    simpa [blockGet] using acceptedAt
  exact blockCertificate.instructions_exclude_internal_calls blockAccepted instruction
    instructionMember

theorem StackSchedule.target_decoded_operation_supported
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (control next : Machine.MachineControl) (operation : Machine.Operation)
    (decode : certificate.stack.decodeInstruction control = some (next, .op operation)) :
    (∃ value, operation = .constant value) ∨ operation = .copy ∨
      operation = .add ∨ operation = .lt := by
  obtain ⟨blockCertificate, blockMember, instructionMember⟩ :=
    certificate.target_decode_instruction_mem control next (.op operation) decode
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, blockGet⟩ := blockMember
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt := (certificate.check_sound accepted).2.1 index indexBound
    simpa [blockGet] using acceptedAt
  exact blockCertificate.instructions_operation_supported blockAccepted operation
    instructionMember

theorem StackSchedule.target_decoded_flipped_operation_supported
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (control next : Machine.MachineControl) (operation : Machine.Operation)
    (decode : certificate.stack.decodeInstruction control =
      some (next, .flippedOp operation)) : operation = .add ∨ operation = .lt := by
  obtain ⟨blockCertificate, blockMember, instructionMember⟩ :=
    certificate.target_decode_instruction_mem control next (.flippedOp operation) decode
  rw [Array.mem_iff_getElem] at blockMember
  obtain ⟨index, indexBound, blockGet⟩ := blockMember
  have blockAccepted : blockCertificate.check = .ok () := by
    have acceptedAt := (certificate.check_sound accepted).2.1 index indexBound
    simpa [blockGet] using acceptedAt
  exact blockCertificate.instructions_flipped_operation_supported blockAccepted operation
    instructionMember

theorem StackSchedule.target_decode_primitive_pure
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    {control next : Machine.MachineControl} {operation : Machine.Operation}
    {src : Stack.Source} {dst : Stack.Destination}
    (decode : Stack.decode certificate.stack control =
      some (⟨Machine.Instruction.Kind.primitive operation, src, dst⟩, next)) :
    operation ≠ .gas ∧ operation ≠ .call := by
  rcases stackDecode_primitive_inv decode with instructionDecode | instructionDecode
  · rcases certificate.target_decoded_operation_supported accepted control next operation
      instructionDecode with ⟨value, rfl⟩ | rfl | rfl | rfl <;> simp
  · rcases certificate.target_decoded_flipped_operation_supported accepted control next operation
      instructionDecode with rfl | rfl <;> simp

theorem StackSchedule.target_decode_icall_false
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    {control next : Machine.MachineControl} {callee : FunctionId}
    {src : Stack.Source} {dst : Stack.Destination}
    (decode : Stack.decode certificate.stack control =
      some (⟨Machine.Instruction.Kind.icall callee, src, dst⟩, next)) : False := by
  obtain ⟨argumentCount, resultCount, instructionDecode⟩ := stackDecode_icall_inv decode
  exact certificate.target_decoded_instruction_excludes_internal_calls accepted control next
    (.icall callee argumentCount resultCount) instructionDecode callee argumentCount resultCount rfl

theorem StackSchedule.stack_program_noMload
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ()) :
    (Stack.decoder certificate.stack).NoMload := by
  intro control src dst next decode
  change Stack.decode certificate.stack control =
    some (⟨Machine.Instruction.Kind.primitive .mload32, src, dst⟩, next) at decode
  cases instructionDecode : certificate.stack.decodeInstruction control with
  | none => simp [Stack.decode, instructionDecode] at decode
  | some decoded =>
      obtain ⟨instructionNext, instruction⟩ := decoded
      cases instruction with
      | op operation =>
          simp [Stack.decode, instructionDecode] at decode
          have operationEq := decode.1.1
          subst operation
          exact (certificate.target_decoded_instruction_excludes_memory_oracles accepted control
            instructionNext (.op .mload32) instructionDecode).1 rfl
      | flippedOp operation =>
          cases operation <;> simp [Stack.decode, instructionDecode] at decode
      | swap depth => simp [Stack.decode, instructionDecode] at decode
      | exchange firstDepth secondDepth =>
          simp [Stack.decode, instructionDecode] at decode
      | dup depth => simp [Stack.decode, instructionDecode] at decode
      | pop => simp [Stack.decode, instructionDecode] at decode
      | icall callee argumentCount resultCount =>
          simp [Stack.decode, instructionDecode] at decode
      | store slot => simp [Stack.decode, instructionDecode] at decode
      | load slot => simp [Stack.decode, instructionDecode] at decode

theorem StackSchedule.stack_program_noMalloc
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ()) :
    (Stack.decoder certificate.stack).NoMalloc := by
  constructor
  · intro control src dst next decode
    change Stack.decode certificate.stack control =
      some (⟨Machine.Instruction.Kind.primitive .malloc, src, dst⟩, next) at decode
    cases instructionDecode : certificate.stack.decodeInstruction control with
    | none => simp [Stack.decode, instructionDecode] at decode
    | some decoded =>
        obtain ⟨instructionNext, instruction⟩ := decoded
        cases instruction with
        | op operation =>
            simp [Stack.decode, instructionDecode] at decode
            have operationEq := decode.1.1
            subst operation
            exact (certificate.target_decoded_instruction_excludes_memory_oracles accepted control
              instructionNext (.op .malloc) instructionDecode).2.1 rfl
        | flippedOp operation =>
            cases operation <;> simp [Stack.decode, instructionDecode] at decode
        | swap depth => simp [Stack.decode, instructionDecode] at decode
        | exchange firstDepth secondDepth =>
            simp [Stack.decode, instructionDecode] at decode
        | dup depth => simp [Stack.decode, instructionDecode] at decode
        | pop => simp [Stack.decode, instructionDecode] at decode
        | icall callee argumentCount resultCount =>
            simp [Stack.decode, instructionDecode] at decode
        | store slot => simp [Stack.decode, instructionDecode] at decode
        | load slot => simp [Stack.decode, instructionDecode] at decode
  · intro control src dst next decode
    change Stack.decode certificate.stack control =
      some (⟨Machine.Instruction.Kind.primitive .mallocUninit, src, dst⟩, next) at decode
    cases instructionDecode : certificate.stack.decodeInstruction control with
    | none => simp [Stack.decode, instructionDecode] at decode
    | some decoded =>
        obtain ⟨instructionNext, instruction⟩ := decoded
        cases instruction with
        | op operation =>
            simp [Stack.decode, instructionDecode] at decode
            have operationEq := decode.1.1
            subst operation
            exact (certificate.target_decoded_instruction_excludes_memory_oracles accepted control
              instructionNext (.op .mallocUninit) instructionDecode).2.2 rfl
        | flippedOp operation =>
            cases operation <;> simp [Stack.decode, instructionDecode] at decode
        | swap depth => simp [Stack.decode, instructionDecode] at decode
        | exchange firstDepth secondDepth =>
            simp [Stack.decode, instructionDecode] at decode
        | dup depth => simp [Stack.decode, instructionDecode] at decode
        | pop => simp [Stack.decode, instructionDecode] at decode
        | icall callee argumentCount resultCount =>
            simp [Stack.decode, instructionDecode] at decode
        | store slot => simp [Stack.decode, instructionDecode] at decode
        | load slot => simp [Stack.decode, instructionDecode] at decode

end Sir.Lowering
