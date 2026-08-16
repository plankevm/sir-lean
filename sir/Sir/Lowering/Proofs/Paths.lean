import Sir.Lowering.Proofs.Purity

namespace Sir.Lowering

theorem evaluateSourceStatementList_source_steps {sourceProgram : Vars.Program}
    (statements : List Vars.Stmt) (startIndex : Nat) (ctx : CallContext) (globals : Globals)
    (locals finalLocals : Locals) (sourceControl : Nat → Machine.MachineControl)
    (evaluated : statements.foldlM evaluateSourceStatement locals = some finalLocals)
    (sourceDecode : ∀ index statement,
      statements[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl (startIndex + index)) =
          some (sourceControl (startIndex + index + 1), statement)) :
    Machine.Steps Vars.frame (Vars.decoder sourceProgram) Machine.memoryPolicy ctx
      (⟨globals, locals, sourceControl startIndex⟩ : Vars.State) []
      (⟨globals, finalLocals, sourceControl (startIndex + statements.length)⟩ :
        Vars.State) := by
  induction statements generalizing startIndex locals with
  | nil =>
      simp at evaluated
      subst finalLocals
      exact Machine.Steps.refl
  | cons statement statements inductionHypothesis =>
      simp only [List.foldlM_cons] at evaluated
      cases evaluatedStatement : evaluateSourceStatement locals statement with
      | none => simp [evaluatedStatement] at evaluated
      | some nextLocals =>
          rw [evaluatedStatement] at evaluated
          obtain ⟨operation, operands, result, resultValue, concreteOperation, rfl⟩ :=
            evaluateSourceStatement_eq_some locals nextLocals statement evaluatedStatement
          have sourceStep := sourceStatementConcreteOperation_source_step ctx globals locals
            (sourceControl startIndex) (sourceControl (startIndex + 1)) statement operation operands
            result resultValue concreteOperation (by simpa using sourceDecode 0 statement (by simp))
          have sourceRest := inductionHypothesis (startIndex + 1) (locals.assign result resultValue)
            evaluated (fun index nextStatement statementAt => by
              have originalAt : (statement :: statements)[index + 1]? = some nextStatement := by
                simpa using statementAt
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                sourceDecode (index + 1) nextStatement originalAt)
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Machine.Steps.trans (Machine.Steps.single sourceStep) sourceRest

theorem sourceOrderReferenceLocals_source_steps {sourceProgram : Vars.Program}
    (sourceStatements : Array Vars.Stmt) (ctx : CallContext) (globals : Globals)
    (locals referenceLocals : Locals) (sourceControl : Nat → Machine.MachineControl)
    (evaluated : sourceOrderReferenceLocals sourceStatements locals = some referenceLocals)
    (sourceDecode : ∀ index statement,
      sourceStatements[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl index) =
          some (sourceControl (index + 1), statement)) :
    Machine.Steps Vars.frame (Vars.decoder sourceProgram) Machine.memoryPolicy ctx
      (⟨globals, locals, sourceControl 0⟩ : Vars.State) []
      (⟨globals, referenceLocals, sourceControl sourceStatements.size⟩ :
        Vars.State) := by
  have decodeList : ∀ index statement,
      sourceStatements.toList[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl (0 + index)) =
          some (sourceControl (0 + index + 1), statement) := by
    intro index statement statementAt
    simpa using sourceDecode index statement (by
      simpa only [Array.getElem?_toList] using statementAt)
  simpa [sourceOrderReferenceLocals] using
    (evaluateSourceStatementList_source_steps (sourceProgram := sourceProgram)
      sourceStatements.toList 0 ctx globals locals referenceLocals sourceControl evaluated decodeList)

theorem Symbolic.execute_preserves_available_variables
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (instruction : Stack.Instr)
    (executed : Symbolic.execute sourceStatements state instruction = some nextState)
    (notOperation : ∀ operation,
      instruction ≠ .op operation ∧ instruction ≠ .flippedOp operation) :
    ∀ identifier,
      nextState.available sourceStatements identifier =
        state.available sourceStatements identifier := by
  cases instruction with
  | swap depth =>
      simp [Symbolic.execute] at executed
      obtain ⟨_, stack, _, rfl⟩ := executed
      intro identifier
      rfl
  | exchange firstDepth secondDepth =>
      simp [Symbolic.execute] at executed
      obtain ⟨_, stack, _, rfl⟩ := executed
      intro identifier
      rfl
  | dup depth =>
      simp [Symbolic.execute] at executed
      obtain ⟨_, value, _, rfl⟩ := executed
      intro identifier
      rfl
  | pop =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at executed
      | cons value stack =>
          simp [Symbolic.execute, stackEq] at executed
          subst nextState
          intro identifier
          rfl
  | op operation => exact (notOperation operation).1 rfl |>.elim
  | flippedOp operation => exact (notOperation operation).2 rfl |>.elim
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at executed
  | store slot =>
      cases stackEq : state.stack with
      | nil => simp [Symbolic.execute, stackEq] at executed
      | cons value stack =>
          cases bindingEq : state.slotValue? slot with
          | some binding => simp [Symbolic.execute, stackEq, bindingEq] at executed
          | none =>
              simp [Symbolic.execute, stackEq, bindingEq] at executed
              subst nextState
              intro identifier
              rfl
  | load slot =>
      simp [Symbolic.execute] at executed
      obtain ⟨value, _, rfl⟩ := executed
      intro identifier
      rfl

theorem Symbolic.State.InterpretsReference.execute_instruction_target_step
    {sourceProgram : Vars.Program} {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (entryLayout : Array Symbolic.Value)
    (state nextState : Symbolic.State) (ctx : CallContext) (globals : Globals)
    (entryLocals locals referenceLocals : Locals) (environment : Stack.Environment)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (interprets : state.InterpretsReference sourceStatements locals referenceLocals environment)
    (sourceControl : Nat → Machine.MachineControl) (targetControl targetNext : Machine.MachineControl)
    (instruction : Stack.Instr)
    (executed : Symbolic.execute sourceStatements state instruction = some nextState)
    (sourceDecode : ∀ index statement,
      sourceStatements[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl index) =
          some (sourceControl (index + 1), statement))
    (targetDecode : targetProgram.decodeInstruction targetControl =
      some (targetNext, instruction)) :
    ∃ nextLocals nextEnvironment,
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, nextEnvironment, targetNext⟩ ∧
      nextState.InterpretsReference sourceStatements nextLocals referenceLocals
        nextEnvironment := by
  cases instruction with
  | swap depth =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_swap_step sourceStatements state nextState ctx globals locals environment
          targetControl targetNext depth executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState (.swap depth) executed (by intro operation; simp)]
      exact available
  | exchange firstDepth secondDepth =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_exchange_step sourceStatements state nextState ctx globals locals
          environment targetControl targetNext firstDepth secondDepth executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState (.exchange firstDepth secondDepth) executed (by intro operation; simp)]
      exact available
  | dup depth =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_dup_step sourceStatements state nextState ctx globals locals environment
          targetControl targetNext depth executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState (.dup depth) executed (by intro operation; simp)]
      exact available
  | pop =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_pop_step sourceStatements state nextState ctx globals locals environment
          targetControl targetNext executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState .pop executed (by intro operation; simp)]
      exact available
  | op operation =>
      obtain ⟨statementIndex, statement, symbolicOperands, operands, result, resultValue,
          statementAt, symbolicOperation, canFire, concreteOperation, stackPrefix, nextStateEq,
          nextInterprets⟩ :=
        interprets.1.execute_operation sourceStatements state nextState locals environment operation
          executed
      obtain ⟨sourceStep, targetStep⟩ := sourceStatementConcreteOperation_steps ctx globals
        locals environment (sourceControl statementIndex) (sourceControl (statementIndex + 1))
        targetControl targetNext statement operation operands result resultValue concreteOperation
        stackPrefix (sourceDecode statementIndex statement statementAt) targetDecode
      obtain ⟨referenceResult, nextAgrees⟩ :=
        Symbolic.State.AvailableVariablesAgree.after_checker_fire state sourceStatements
          entryLayout entryLocals locals referenceLocals usesAvailable variablesUnique evaluated
          interprets.2 statement statementIndex operation operands result resultValue statementAt
          canFire concreteOperation
      subst nextState
      exact ⟨locals.assign result resultValue,
        { environment with
          stack := resultValue :: environment.stack.drop operation.inputCount },
        targetStep, nextInterprets, nextAgrees⟩
  | flippedOp operation =>
      obtain ⟨statementIndex, statement, symbolicOperands, operands, result, resultValue,
          flippedStack, flippedState, binary, statementAt, symbolicOperation, canFire,
          concreteOperation, fetch, flippedStateEq, nextStateEq, nextInterprets⟩ :=
        interprets.1.execute_flipped_operation sourceStatements state nextState locals environment
          operation executed
      have flippedAgrees : flippedState.AvailableVariablesAgree sourceStatements locals
          referenceLocals := by
        intro identifier available
        apply interprets.2 identifier
        simpa [flippedStateEq, Symbolic.State.available] using available
      have targetStep := sourceStatementConcreteOperation_flipped_target_step ctx globals locals
        environment targetControl targetNext statement operation operands result resultValue
        concreteOperation binary fetch targetDecode
      obtain ⟨referenceResult, nextAgrees⟩ :=
        Symbolic.State.AvailableVariablesAgree.after_checker_fire flippedState
          sourceStatements entryLayout entryLocals locals referenceLocals usesAvailable
          variablesUnique evaluated flippedAgrees statement statementIndex operation operands result
          resultValue statementAt canFire concreteOperation
      subst nextState
      exact ⟨locals.assign result resultValue,
        { environment with stack := resultValue :: environment.stack.drop 2 },
        targetStep, nextInterprets, nextAgrees⟩
  | icall callee argumentCount resultCount => simp [Symbolic.execute] at executed
  | store slot =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_store_step sourceStatements state nextState ctx globals locals environment
          targetControl targetNext slot executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState (.store slot) executed (by intro operation; simp)]
      exact available
  | load slot =>
      obtain ⟨nextEnvironment, targetStep, nextInterprets⟩ :=
        interprets.1.execute_load_step sourceStatements state nextState ctx globals locals environment
          targetControl targetNext slot executed targetDecode
      refine ⟨locals, nextEnvironment, targetStep, nextInterprets, ?_⟩
      intro identifier available
      apply interprets.2 identifier
      rw [← Symbolic.execute_preserves_available_variables sourceStatements state
        nextState (.load slot) executed (by intro operation; simp)]
      exact available

theorem Symbolic.State.InterpretsReference.execute_instructions_target_steps
    {sourceProgram : Vars.Program} {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (entryLayout : Array Symbolic.Value)
    (instructions : List Stack.Instr) (state finalState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (entryLocals locals referenceLocals : Locals)
    (environment : Stack.Environment)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (interprets : state.InterpretsReference sourceStatements locals referenceLocals environment)
    (sourceControl targetControl : Nat → Machine.MachineControl) (targetIndex : Nat)
    (executed : instructions.foldlM (Symbolic.execute sourceStatements) state =
      some finalState)
    (sourceDecode : ∀ index statement,
      sourceStatements[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl index) =
          some (sourceControl (index + 1), statement))
    (targetDecode : ∀ index instruction,
      instructions[index]? = some instruction →
        targetProgram.decodeInstruction (targetControl (targetIndex + index)) =
          some (targetControl (targetIndex + index + 1), instruction)) :
    ∃ finalLocals finalEnvironment,
      Machine.Steps Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl targetIndex⟩ []
        ⟨globals, finalEnvironment, targetControl (targetIndex + instructions.length)⟩ ∧
      finalState.InterpretsReference sourceStatements finalLocals referenceLocals
        finalEnvironment := by
  induction instructions generalizing state locals environment targetIndex with
  | nil =>
      simp at executed
      subst finalState
      exact ⟨locals, environment, Machine.Steps.refl, interprets⟩
  | cons instruction instructions inductionHypothesis =>
      simp only [List.foldlM_cons] at executed
      cases instructionExecution : Symbolic.execute sourceStatements state instruction with
      | none => simp [instructionExecution] at executed
      | some nextState =>
          rw [instructionExecution] at executed
          obtain ⟨nextLocals, nextEnvironment, targetStep, nextInterprets⟩ :=
            interprets.execute_instruction_target_step sourceStatements entryLayout state nextState
              ctx globals entryLocals locals referenceLocals environment usesAvailable
              variablesUnique evaluated sourceControl (targetControl targetIndex)
              (targetControl (targetIndex + 1)) instruction instructionExecution sourceDecode
              (by simpa using targetDecode 0 instruction (by simp))
          obtain ⟨finalLocals, finalEnvironment, targetRest, finalInterprets⟩ :=
            inductionHypothesis nextState nextLocals nextEnvironment nextInterprets (targetIndex + 1)
              executed (fun index nextInstruction instructionAt => by
                have originalAt : (instruction :: instructions)[index + 1]? =
                    some nextInstruction := by
                  simpa using instructionAt
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  targetDecode (index + 1) nextInstruction originalAt)
          refine ⟨finalLocals, finalEnvironment, ?_, finalInterprets⟩
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Machine.Steps.trans (Machine.Steps.single targetStep) targetRest

theorem Symbolic.State.InterpretsReference.execute_symbolic_instructions_target_steps
    {sourceProgram : Vars.Program} {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (entryLayout : Array Symbolic.Value)
    (targetInstructions : Array Stack.Instr) (state finalState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (entryLocals locals referenceLocals : Locals)
    (environment : Stack.Environment)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (interprets : state.InterpretsReference sourceStatements locals referenceLocals environment)
    (sourceControl targetControl : Nat → Machine.MachineControl) (targetIndex : Nat)
    (executed : Symbolic.executeAll sourceStatements targetInstructions state = some finalState)
    (sourceDecode : ∀ index statement,
      sourceStatements[index]? = some statement →
        sourceProgram.decodeStmt (sourceControl index) =
          some (sourceControl (index + 1), statement))
    (targetDecode : ∀ index instruction,
      targetInstructions[index]? = some instruction →
        targetProgram.decodeInstruction (targetControl (targetIndex + index)) =
          some (targetControl (targetIndex + index + 1), instruction)) :
    ∃ finalLocals finalEnvironment,
      Machine.Steps Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl targetIndex⟩ []
        ⟨globals, finalEnvironment, targetControl (targetIndex + targetInstructions.size)⟩ ∧
      finalState.InterpretsReference sourceStatements finalLocals referenceLocals
        finalEnvironment := by
  apply interprets.execute_instructions_target_steps sourceStatements entryLayout
    targetInstructions.toList state finalState ctx globals entryLocals locals referenceLocals
    environment usesAvailable variablesUnique evaluated sourceControl targetControl targetIndex
  · simpa [Symbolic.executeAll] using executed
  · exact sourceDecode
  · intro index instruction instructionAt
    apply targetDecode index instruction
    simpa using instructionAt

def SpillAllInvariant (sourceStatements : Array Vars.Stmt) (state : Symbolic.State)
    (defined : List VarId) (fired : Nat) : Prop :=
  state.stack = [] ∧ state.firedCount = fired ∧
    state.firedStatementIndices = (List.range fired).reverse ∧
    (∀ identifier ∈ defined,
      state.available sourceStatements identifier = true) ∧
    (∀ identifier ∈ defined,
      state.slotValue? identifier.id = some (.variable identifier)) ∧
    ∀ binding ∈ state.slotBindings,
      ∃ identifier ∈ defined, binding = (identifier.id, .variable identifier)

theorem SpillAllInvariant.slot_absent
    {sourceStatements : Array Vars.Stmt} {state : Symbolic.State} {defined : List VarId}
    {fired : Nat} {result : VarId}
    (invariant : SpillAllInvariant sourceStatements state defined fired)
    (fresh : result ∉ defined) : state.slotValue? result.id = none := by
  unfold Symbolic.State.slotValue?
  rw [Option.map_eq_none_iff]
  apply Array.find?_eq_none.mpr
  intro binding member equal
  obtain ⟨identifier, identifierMember, bindingEq⟩ := invariant.2.2.2.2.2 binding member
  subst binding
  have : identifier = result := by
    cases identifier
    cases result
    simp_all
  exact fresh (this ▸ identifierMember)

theorem SpillAllInvariant.binding_value_ne
    {sourceStatements : Array Vars.Stmt} {state : Symbolic.State} {defined : List VarId}
    {fired : Nat} {result : VarId}
    (invariant : SpillAllInvariant sourceStatements state defined fired)
    (fresh : result ∉ defined) :
    ∀ binding ∈ state.slotBindings, binding.2 ≠ .variable result := by
  intro binding member equal
  obtain ⟨identifier, identifierMember, bindingEq⟩ := invariant.2.2.2.2.2 binding member
  rw [bindingEq] at equal
  have equalIdentifier : identifier = result := by simpa using equal
  exact fresh (equalIdentifier ▸ identifierMember)

theorem Symbolic.State.slotValue?_push_of_some (state : Symbolic.State)
    (binding : Nat × Symbolic.Value) (slot : Nat) (value : Symbolic.Value)
    (lookup : state.slotValue? slot = some value) :
    ({ state with slotBindings := state.slotBindings.push binding } :
      Symbolic.State).slotValue? slot = some value := by
  unfold Symbolic.State.slotValue? at lookup ⊢
  obtain ⟨found, foundEq, rfl⟩ := Option.map_eq_some_iff.mp lookup
  rw [Array.find?_push, foundEq]
  rfl

theorem Symbolic.State.slotValue?_push_self_of_none (state : Symbolic.State)
    (slot : Nat) (value : Symbolic.Value) (lookup : state.slotValue? slot = none) :
    ({ state with slotBindings := state.slotBindings.push (slot, value) } :
      Symbolic.State).slotValue? slot = some value := by
  unfold Symbolic.State.slotValue? at lookup ⊢
  rw [Option.map_eq_none_iff] at lookup
  rw [Array.find?_push, lookup]
  simp

theorem SpillAllInvariant.store_result
    {sourceStatements : Array Vars.Stmt} {state : Symbolic.State} {defined : List VarId}
    {fired : Nat} {result : VarId} {statement : Vars.Stmt}
    (invariant : SpillAllInvariant sourceStatements state defined fired)
    (fresh : result ∉ defined) (statementAt : sourceStatements[fired]? = some statement)
    (resultDefined : result ∈ statement.variablesDefined) :
    SpillAllInvariant sourceStatements
      { state with
        stack := List.nil
        slotBindings := state.slotBindings.push (result.id, .variable result)
        firedStatementIndices := fired :: state.firedStatementIndices }
      (result :: defined) (fired + 1) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Symbolic.State.firedCount] using
      congrArg Nat.succ invariant.2.1
  · simp [invariant.2.2.1, List.range_succ, List.reverse_append]
  · intro identifier member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [Symbolic.State.available, Symbolic.definesVariable,
        statementAt, resultDefined]
    · have available := invariant.2.2.2.1 identifier member
      unfold Symbolic.State.available at available ⊢
      simp only [List.any_cons, Bool.or_eq_true] at available ⊢
      exact available.elim Or.inl (fun remaining => Or.inr (Or.inr remaining))
  · intro identifier member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact state.slotValue?_push_self_of_none identifier.id (.variable identifier)
        (invariant.slot_absent fresh)
    · exact state.slotValue?_push_of_some (result.id, .variable result) identifier.id
        (.variable identifier) (invariant.2.2.2.2.1 identifier member)
  · intro binding member
    rw [Array.mem_push] at member
    rcases member with member | rfl
    · obtain ⟨identifier, identifierMember, rfl⟩ := invariant.2.2.2.2.2 binding member
      exact ⟨identifier, by simp [identifierMember]⟩
    · exact ⟨result, by simp⟩

theorem execute_lowerStatement
    (sourceStatements : Array Vars.Stmt) (index : Nat) (statement : Vars.Stmt)
    (state : Symbolic.State) (defined : List VarId)
    (invariant : SpillAllInvariant sourceStatements state defined index)
    (statementAt : sourceStatements[index]? = some statement)
    (readsDefined : ∀ identifier ∈ statement.variablesRead, identifier ∈ defined)
    (definitionsFresh : ∀ identifier ∈ statement.variablesDefined, identifier ∉ defined)
    (instructions : Array Stack.Instr)
    (lowered : spillAll.lowerStatement statement = some instructions) :
    ∃ nextState,
      instructions.foldlM (Symbolic.execute sourceStatements) state = some nextState ∧
      SpillAllInvariant sourceStatements nextState
        (statement.variablesDefined ++ defined) (index + 1) := by
  have firedLength : state.firedStatementIndices.length = index := by
    simpa [Symbolic.State.firedCount] using invariant.2.1
  have priorFired : ∀ priorIndex < index, priorIndex ∈ state.firedStatementIndices := by
    intro priorIndex priorBound
    rw [invariant.2.2.1]
    simp [priorBound]
  have readsAvailable : ∀ identifier ∈ statement.variablesRead,
      state.available sourceStatements identifier = true := by
    intro identifier member
    exact invariant.2.2.2.1 identifier (readsDefined identifier member)
  cases statement with
  | assign result expression =>
      cases expression with
      | constant value =>
          simp [spillAll.lowerStatement] at lowered
          subst instructions
          have fresh : result ∉ defined := definitionsFresh result (by simp [Vars.Stmt.variablesDefined])
          have slotAbsent := invariant.slot_absent fresh
          have bindingsAbsent := invariant.binding_value_ne fresh
          let firedState : Symbolic.State :=
            { state with
              stack := [.variable result]
              firedStatementIndices := index :: state.firedStatementIndices }
          let nextState : Symbolic.State :=
            { state with
              stack := List.nil
              slotBindings := state.slotBindings.push (result.id, .variable result)
              firedStatementIndices := index :: state.firedStatementIndices }
          have opExecution : Symbolic.execute sourceStatements state
              (.op (.constant value)) = some firedState := by
            have canFire : state.fireable sourceStatements (.constant value)
                (.assign result (.constant value), index) = true := by
              simp [Symbolic.State.fireable, Symbolic.operationOf,
                invariant.1, invariant.2.2.1, Symbolic.State.slotFree,
                bindingsAbsent, Vars.Stmt.variablesRead, Vars.Expr.variablesRead]
            have found := state.firstFireable_eq_of_prior_fired sourceStatements
              (.constant value) (.assign result (.constant value)) index statementAt canFire
              priorFired
            simp [Symbolic.execute, Symbolic.State.fireNextStatement, found,
              Symbolic.operationOf, invariant.1, firedState]
          have firedSlotAbsent : firedState.slotValue? result.id = none := by
            simpa [firedState] using slotAbsent
          have storeExecution : Symbolic.execute sourceStatements firedState
              (.store result.id) = some nextState := by
            simp only [Symbolic.execute]
            rw [firedSlotAbsent]
          refine ⟨nextState, ?_, ?_⟩
          · simp [opExecution, storeExecution]
          · simpa [nextState, Vars.Stmt.variablesDefined] using invariant.store_result fresh
              statementAt (by simp [Vars.Stmt.variablesDefined])
      | var source =>
          simp [spillAll.lowerStatement] at lowered
          subst instructions
          have sourceDefined : source ∈ defined :=
            readsDefined source (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have sourceLookup := invariant.2.2.2.2.1 source sourceDefined
          have fresh : result ∉ defined := definitionsFresh result (by simp [Vars.Stmt.variablesDefined])
          have slotAbsent := invariant.slot_absent fresh
          have bindingsAbsent := invariant.binding_value_ne fresh
          let loadedState : Symbolic.State :=
            { state with stack := [.variable source] }
          let firedState : Symbolic.State :=
            { state with
              stack := [.variable result]
              firedStatementIndices := index :: state.firedStatementIndices }
          let nextState : Symbolic.State :=
            { state with
              stack := List.nil
              slotBindings := state.slotBindings.push (result.id, .variable result)
              firedStatementIndices := index :: state.firedStatementIndices }
          have loadExecution : Symbolic.execute sourceStatements state
              (.load source.id) = some loadedState := by
            simp only [Symbolic.execute]
            rw [sourceLookup]
            simp [loadedState, invariant.1]
          have opExecution : Symbolic.execute sourceStatements loadedState
              (.op .copy) = some firedState := by
            have sourceAvailable := invariant.2.2.2.1 source sourceDefined
            have loadedReadsAvailable : ∀ identifier ∈
                (Vars.Stmt.assign result (.var source)).variablesRead,
                loadedState.available sourceStatements identifier = true := by
              intro identifier member
              simpa [loadedState] using readsAvailable identifier member
            have loadedSourceAvailable := loadedReadsAvailable source
              (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
            have canFire : loadedState.fireable sourceStatements .copy
                (.assign result (.var source), index) = true := by
              simp only [Symbolic.State.fireable,
                Symbolic.operationOf, decide_eq_true_eq]
              refine ⟨?_, by trivial, by simp [loadedState], by simp [loadedState], ?_, ?_⟩
              · simp [loadedState, invariant.2.2.1]
              · simp [Symbolic.State.slotFree, loadedState, bindingsAbsent]
              · exact List.all_eq_true.mpr loadedReadsAvailable
            have found := loadedState.firstFireable_eq_of_prior_fired
              sourceStatements .copy (.assign result (.var source)) index statementAt canFire
              (by simpa [loadedState] using priorFired)
            simp [Symbolic.execute, Symbolic.State.fireNextStatement, found,
              Symbolic.operationOf, loadedState, firedState]
          have firedSlotAbsent : firedState.slotValue? result.id = none := by
            simpa [firedState] using slotAbsent
          have storeExecution : Symbolic.execute sourceStatements firedState
              (.store result.id) = some nextState := by
            simp only [Symbolic.execute]
            rw [firedSlotAbsent]
          refine ⟨nextState, ?_, ?_⟩
          · simp [loadExecution, opExecution, storeExecution]
          · simpa [nextState, Vars.Stmt.variablesDefined] using invariant.store_result fresh
              statementAt (by simp [Vars.Stmt.variablesDefined])
      | add lhs rhs =>
          simp [spillAll.lowerStatement] at lowered
          subst instructions
          have lhsDefined : lhs ∈ defined :=
            readsDefined lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have rhsDefined : rhs ∈ defined :=
            readsDefined rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have lhsLookup := invariant.2.2.2.2.1 lhs lhsDefined
          have rhsLookup := invariant.2.2.2.2.1 rhs rhsDefined
          have fresh : result ∉ defined := definitionsFresh result (by simp [Vars.Stmt.variablesDefined])
          have slotAbsent := invariant.slot_absent fresh
          have bindingsAbsent := invariant.binding_value_ne fresh
          let rhsLoadedState : Symbolic.State :=
            { state with stack := [.variable rhs] }
          let operandsLoadedState : Symbolic.State :=
            { state with stack := [.variable lhs, .variable rhs] }
          let firedState : Symbolic.State :=
            { state with
              stack := [.variable result]
              firedStatementIndices := index :: state.firedStatementIndices }
          let nextState : Symbolic.State :=
            { state with
              stack := List.nil
              slotBindings := state.slotBindings.push (result.id, .variable result)
              firedStatementIndices := index :: state.firedStatementIndices }
          have rhsLoadExecution : Symbolic.execute sourceStatements state
              (.load rhs.id) = some rhsLoadedState := by
            simp only [Symbolic.execute]
            rw [rhsLookup]
            simp [rhsLoadedState, invariant.1]
          have lhsLoadedLookup : rhsLoadedState.slotValue? lhs.id =
              some (.variable lhs) := by simpa [rhsLoadedState] using lhsLookup
          have lhsLoadExecution : Symbolic.execute sourceStatements rhsLoadedState
              (.load lhs.id) = some operandsLoadedState := by
            simp only [Symbolic.execute]
            rw [lhsLoadedLookup]
            simp [rhsLoadedState, operandsLoadedState]
          have opExecution : Symbolic.execute sourceStatements operandsLoadedState
              (.op .add) = some firedState := by
            have lhsAvailable := invariant.2.2.2.1 lhs lhsDefined
            have rhsAvailable := invariant.2.2.2.1 rhs rhsDefined
            have loadedReadsAvailable : ∀ identifier ∈
                (Vars.Stmt.assign result (.add lhs rhs)).variablesRead,
                operandsLoadedState.available sourceStatements identifier = true := by
              intro identifier member
              simpa [operandsLoadedState] using readsAvailable identifier member
            have loadedLhsAvailable := loadedReadsAvailable lhs
              (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
            have loadedRhsAvailable := loadedReadsAvailable rhs
              (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
            have canFire : operandsLoadedState.fireable sourceStatements .add
                (.assign result (.add lhs rhs), index) = true := by
              simp only [Symbolic.State.fireable,
                Symbolic.operationOf, decide_eq_true_eq]
              refine ⟨?_, by trivial, by simp [operandsLoadedState],
                by simp [operandsLoadedState], ?_, ?_⟩
              · simp [operandsLoadedState, invariant.2.2.1]
              · simp [Symbolic.State.slotFree, operandsLoadedState, bindingsAbsent]
              · exact List.all_eq_true.mpr loadedReadsAvailable
            have found := operandsLoadedState.firstFireable_eq_of_prior_fired
              sourceStatements .add (.assign result (.add lhs rhs)) index statementAt canFire
              (by simpa [operandsLoadedState] using priorFired)
            simp [Symbolic.execute, Symbolic.State.fireNextStatement, found,
              Symbolic.operationOf, operandsLoadedState, firedState]
          have firedSlotAbsent : firedState.slotValue? result.id = none := by
            simpa [firedState] using slotAbsent
          have storeExecution : Symbolic.execute sourceStatements firedState
              (.store result.id) = some nextState := by
            simp only [Symbolic.execute]
            rw [firedSlotAbsent]
          refine ⟨nextState, ?_, ?_⟩
          · simp [rhsLoadExecution, lhsLoadExecution, opExecution, storeExecution]
          · simpa [nextState, Vars.Stmt.variablesDefined] using invariant.store_result fresh
              statementAt (by simp [Vars.Stmt.variablesDefined])
      | lt lhs rhs =>
          simp [spillAll.lowerStatement] at lowered
          subst instructions
          have lhsDefined : lhs ∈ defined :=
            readsDefined lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have rhsDefined : rhs ∈ defined :=
            readsDefined rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have lhsLookup := invariant.2.2.2.2.1 lhs lhsDefined
          have rhsLookup := invariant.2.2.2.2.1 rhs rhsDefined
          have fresh : result ∉ defined := definitionsFresh result (by simp [Vars.Stmt.variablesDefined])
          have slotAbsent := invariant.slot_absent fresh
          have bindingsAbsent := invariant.binding_value_ne fresh
          let rhsLoadedState : Symbolic.State :=
            { state with stack := [.variable rhs] }
          let operandsLoadedState : Symbolic.State :=
            { state with stack := [.variable lhs, .variable rhs] }
          let firedState : Symbolic.State :=
            { state with
              stack := [.variable result]
              firedStatementIndices := index :: state.firedStatementIndices }
          let nextState : Symbolic.State :=
            { state with
              stack := List.nil
              slotBindings := state.slotBindings.push (result.id, .variable result)
              firedStatementIndices := index :: state.firedStatementIndices }
          have rhsLoadExecution : Symbolic.execute sourceStatements state
              (.load rhs.id) = some rhsLoadedState := by
            simp only [Symbolic.execute]
            rw [rhsLookup]
            simp [rhsLoadedState, invariant.1]
          have lhsLoadedLookup : rhsLoadedState.slotValue? lhs.id =
              some (.variable lhs) := by simpa [rhsLoadedState] using lhsLookup
          have lhsLoadExecution : Symbolic.execute sourceStatements rhsLoadedState
              (.load lhs.id) = some operandsLoadedState := by
            simp only [Symbolic.execute]
            rw [lhsLoadedLookup]
            simp [rhsLoadedState, operandsLoadedState]
          have opExecution : Symbolic.execute sourceStatements operandsLoadedState
              (.op .lt) = some firedState := by
            have lhsAvailable := invariant.2.2.2.1 lhs lhsDefined
            have rhsAvailable := invariant.2.2.2.1 rhs rhsDefined
            have loadedReadsAvailable : ∀ identifier ∈
                (Vars.Stmt.assign result (.lt lhs rhs)).variablesRead,
                operandsLoadedState.available sourceStatements identifier = true := by
              intro identifier member
              simpa [operandsLoadedState] using readsAvailable identifier member
            have loadedLhsAvailable := loadedReadsAvailable lhs
              (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
            have loadedRhsAvailable := loadedReadsAvailable rhs
              (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
            have canFire : operandsLoadedState.fireable sourceStatements .lt
                (.assign result (.lt lhs rhs), index) = true := by
              simp only [Symbolic.State.fireable,
                Symbolic.operationOf, decide_eq_true_eq]
              refine ⟨?_, by trivial, by simp [operandsLoadedState],
                by simp [operandsLoadedState], ?_, ?_⟩
              · simp [operandsLoadedState, invariant.2.2.1]
              · simp [Symbolic.State.slotFree, operandsLoadedState, bindingsAbsent]
              · exact List.all_eq_true.mpr loadedReadsAvailable
            have found := operandsLoadedState.firstFireable_eq_of_prior_fired
              sourceStatements .lt (.assign result (.lt lhs rhs)) index statementAt canFire
              (by simpa [operandsLoadedState] using priorFired)
            simp [Symbolic.execute, Symbolic.State.fireNextStatement, found,
              Symbolic.operationOf, operandsLoadedState, firedState]
          have firedSlotAbsent : firedState.slotValue? result.id = none := by
            simpa [firedState] using slotAbsent
          have storeExecution : Symbolic.execute sourceStatements firedState
              (.store result.id) = some nextState := by
            simp only [Symbolic.execute]
            rw [firedSlotAbsent]
          refine ⟨nextState, ?_, ?_⟩
          · simp [rhsLoadExecution, lhsLoadExecution, opExecution, storeExecution]
          · simpa [nextState, Vars.Stmt.variablesDefined] using invariant.store_result fresh
              statementAt (by simp [Vars.Stmt.variablesDefined])
      | sload key => simp [spillAll.lowerStatement] at lowered
  | sstore key value => simp [spillAll.lowerStatement] at lowered
  | gas result => simp [spillAll.lowerStatement] at lowered
  | call callData => simp [spillAll.lowerStatement] at lowered
  | malloc result size => simp [spillAll.lowerStatement] at lowered
  | mallocUninit result size => simp [spillAll.lowerStatement] at lowered
  | mstore32 offset value => simp [spillAll.lowerStatement] at lowered
  | mload32 result offset => simp [spillAll.lowerStatement] at lowered
  | icall callee args dests => simp [spillAll.lowerStatement] at lowered

theorem Symbolic.recordDefinitions_sound
    {defined nextDefined : List VarId} {statement : Vars.Stmt}
    (recorded : Symbolic.recordDefinitions defined statement = some nextDefined) :
    (∀ identifier ∈ statement.variablesRead, identifier ∈ defined) ∧
      nextDefined = statement.variablesDefined ++ defined := by
  unfold Symbolic.recordDefinitions at recorded
  split at recorded
  next accepted =>
    obtain rfl := Option.some.inj recorded
    refine ⟨?_, rfl⟩
    intro identifier member
    simpa using List.all_eq_true.mp accepted identifier member
  next rejected => simp at recorded

theorem execute_lowerStatementList
    (sourceStatements : Array Vars.Stmt) (processed remaining : List Vars.Stmt)
    (instructionArrays : List (Array Stack.Instr))
    (state : Symbolic.State) (defined finalDefined : List VarId)
    (sourceSplit : sourceStatements.toList = processed ++ remaining)
    (invariant : SpillAllInvariant sourceStatements state defined processed.length)
    (definitions : remaining.foldlM Symbolic.recordDefinitions defined =
      some finalDefined)
    (lowered : remaining.mapM spillAll.lowerStatement = some instructionArrays)
    (singleAssignment : (remaining.flatMap Vars.Stmt.variablesDefined ++ defined).Nodup) :
    ∃ finalState,
      (instructionArrays.flatMap Array.toList).foldlM
          (Symbolic.execute sourceStatements) state = some finalState ∧
      SpillAllInvariant sourceStatements finalState finalDefined sourceStatements.size := by
  induction remaining generalizing processed instructionArrays state defined with
  | nil =>
      simp at definitions lowered
      subst finalDefined
      subst instructionArrays
      have processedSize : processed.length = sourceStatements.size := by
        have sizes := congrArg List.length sourceSplit
        simpa using sizes.symm
      refine ⟨state, by simp, ?_⟩
      simpa [processedSize] using invariant
  | cons statement remaining inductionHypothesis =>
      simp only [List.foldlM_cons] at definitions
      cases recorded : Symbolic.recordDefinitions defined statement with
      | none => simp [recorded] at definitions
      | some nextDefined =>
          rw [recorded] at definitions
          simp only [List.mapM_cons] at lowered
          cases loweredStatement : spillAll.lowerStatement statement with
          | none => simp [loweredStatement] at lowered
          | some statementInstructions =>
              rw [loweredStatement] at lowered
              cases loweredRemaining : remaining.mapM spillAll.lowerStatement with
              | none => simp [loweredRemaining] at lowered
              | some remainingInstructions =>
                  simp [loweredRemaining] at lowered
                  subst instructionArrays
                  obtain ⟨readsDefined, nextDefinedEq⟩ :=
                    Symbolic.recordDefinitions_sound recorded
                  subst nextDefined
                  have currentNodup :
                      (statement.variablesDefined ++
                        (remaining.flatMap Vars.Stmt.variablesDefined ++ defined)).Nodup := by
                    simpa [List.flatMap_cons, List.append_assoc] using singleAssignment
                  have definitionsFresh :
                      ∀ identifier ∈ statement.variablesDefined, identifier ∉ defined := by
                    intro identifier member inDefined
                    exact (List.nodup_append.mp currentNodup).2.2 identifier member identifier
                      (by simp [inDefined]) rfl
                  have nextNodup :
                      (remaining.flatMap Vars.Stmt.variablesDefined ++
                        (statement.variablesDefined ++ defined)).Nodup := by
                    apply currentNodup.perm
                    simpa [List.append_assoc] using
                      (List.perm_append_comm (l₁ := statement.variablesDefined)
                        (l₂ := remaining.flatMap Vars.Stmt.variablesDefined)).append_right defined
                  have statementAt : sourceStatements[processed.length]? = some statement := by
                    rw [← Array.getElem?_toList, sourceSplit]
                    simp
                  obtain ⟨nextState, statementExecution, nextInvariant⟩ :=
                    execute_lowerStatement sourceStatements processed.length statement state
                      defined invariant statementAt readsDefined definitionsFresh
                      statementInstructions loweredStatement
                  obtain ⟨finalState, remainingExecution, finalInvariant⟩ :=
                    inductionHypothesis (processed ++ [statement]) remainingInstructions nextState
                      (statement.variablesDefined ++ defined)
                      (by simpa [List.append_assoc] using sourceSplit)
                      (by simpa using nextInvariant) definitions loweredRemaining nextNodup
                  refine ⟨finalState, ?_, finalInvariant⟩
                  simpa [List.foldlM_append, statementExecution] using remainingExecution

theorem lowerStatements_execute
    (sourceStatements : Array Vars.Stmt) (finalDefined : List VarId)
    (targetInstructions : Array Stack.Instr)
    (definitions : spillAll.definitions sourceStatements = some finalDefined)
    (lowered : spillAll.lowerStatements sourceStatements = some targetInstructions)
    (single : spillAll.singleAssignment sourceStatements = true) :
    ∃ finalState,
      Symbolic.executeAll sourceStatements targetInstructions
          (Symbolic.State.initial #[]) = some finalState ∧
      SpillAllInvariant sourceStatements finalState finalDefined sourceStatements.size := by
  unfold spillAll.lowerStatements at lowered
  cases mapped : sourceStatements.mapM spillAll.lowerStatement with
  | none => simp [mapped] at lowered
  | some instructionArrays =>
      simp [mapped] at lowered
      subst targetInstructions
      have mappedList : sourceStatements.toList.mapM spillAll.lowerStatement =
          some instructionArrays.toList := by
        symm
        simpa [mapped] using
          (Array.toList_mapM (f := spillAll.lowerStatement) (xs := sourceStatements))
      have initialInvariant : SpillAllInvariant sourceStatements
          (Symbolic.State.initial #[]) [] 0 := by
        simp [SpillAllInvariant, Symbolic.State.initial,
          Symbolic.State.slotValue?, Symbolic.State.firedCount]
      have definitionsList : sourceStatements.toList.foldlM
          Symbolic.recordDefinitions [] = some finalDefined := by
        simpa [spillAll.definitions] using definitions
      have nodup : (sourceStatements.toList.flatMap Vars.Stmt.variablesDefined ++ []).Nodup := by
        simpa [Sir.Lowering.spillAll.singleAssignment] using single
      obtain ⟨finalState, executed, finalInvariant⟩ :=
        execute_lowerStatementList sourceStatements [] sourceStatements.toList
          instructionArrays.toList (Symbolic.State.initial #[]) [] finalDefined
          (by simp) initialInvariant definitionsList mappedList nodup
      refine ⟨finalState, ?_, finalInvariant⟩
      rw [Symbolic.executeAll, ← Array.foldlM_toList]
      simpa [List.flatMap] using executed

theorem Proofs.spillAll_accepted : spillAll.Accepted := by
  intro statements schedule lowered
  unfold spillAll at lowered
  split at lowered
  next single =>
    cases definitions : spillAll.definitions statements with
    | none => simp [definitions] at lowered
    | some finalDefined =>
        cases instructions : spillAll.lowerStatements statements with
        | none => simp [definitions, instructions] at lowered
        | some targetInstructions =>
            simp [definitions, instructions] at lowered
            subst schedule
            obtain ⟨finalState, executed, invariant⟩ :=
              lowerStatements_execute statements finalDefined targetInstructions
                definitions instructions single
            have usesAvailable : Symbolic.readsAvailable statements #[] = true := by
              simpa [Symbolic.readsAvailable, spillAll.definitions] using
                congrArg Option.isSome definitions
            have variablesUnique : Symbolic.definesOnce statements #[] = true := by
              simpa [Symbolic.definesOnce, spillAll.singleAssignment] using single
            have checkedExecution : StackSchedule.Block.execute statements
                targetInstructions.toList (Symbolic.State.initial #[]) = .ok finalState :=
              (StackSchedule.Block.execute_eq_ok_iff statements targetInstructions.toList
                (Symbolic.State.initial #[]) finalState).mpr (by simpa using executed)
            have noUnavailable : StackSchedule.firstUnavailable statements.toList [] = none := by
              apply (StackSchedule.firstUnavailable_none_iff _ _).mpr
              simpa [Symbolic.readsAvailable] using usesAvailable
            have noDuplicate :
                StackSchedule.firstDuplicate
                  (statements.toList.flatMap Vars.Stmt.variablesDefined) = none := by
              apply (StackSchedule.firstDuplicate_none_iff _).mpr
              simpa [Symbolic.definesOnce] using variablesUnique
            constructor
            · simp [spillAll.schedule, StackSchedule.ofBlock]
            · apply StackSchedule.ofBlock_check
              · simp [StackSchedule.Block.check, StackSchedule.Block.checkFinalStack,
                  StackSchedule.Block.terminatorsAgree, checkedExecution, noUnavailable,
                  noDuplicate, invariant.2.1]
              · rfl
  next => simp at lowered

end Sir.Lowering
