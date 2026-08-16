import Sir.Lowering.Spec
import Sir.Vars.Proofs.Steps
import Sir.Vars.Proofs.Readiness

namespace Sir.Lowering

theorem Symbolic.executeAll_cons (statements : Array Vars.Stmt) (instruction : Stack.Instr)
    (instructions : List Stack.Instr) (initial : Symbolic.State) :
    Symbolic.executeAll statements (instruction :: instructions).toArray initial =
      (Symbolic.execute statements initial instruction).bind
        (Symbolic.executeAll statements instructions.toArray) := by
  simp only [Symbolic.executeAll, ← Array.foldlM_toList, List.foldlM_cons]
  rfl

theorem StackSchedule.Block.replay_eq_ok_iff
    (statements : Array Vars.Stmt) (instructions : List Stack.Instr)
    (initial final : Symbolic.State) :
    StackSchedule.Block.replay statements instructions initial = .ok final ↔
      Symbolic.executeAll statements instructions.toArray initial = some final := by
  induction instructions generalizing initial with
  | nil => simp [StackSchedule.Block.replay, Symbolic.executeAll]
  | cons instruction instructions inductionHypothesis =>
      rw [Symbolic.executeAll_cons]
      simp only [StackSchedule.Block.replay]
      cases Symbolic.execute statements initial instruction with
      | none => simp
      | some next => simpa using inductionHypothesis (initial := next)

theorem StackSchedule.firstUnavailable_none_iff
    (statements : List Vars.Stmt) (available : List VarId) :
    StackSchedule.firstUnavailable statements available = none ↔
      (statements.foldlM Symbolic.recordDefinitions available).isSome := by
  induction statements generalizing available with
  | nil => simp [StackSchedule.firstUnavailable]
  | cons statement statements inductionHypothesis =>
      simp only [StackSchedule.firstUnavailable]
      cases unavailable : statement.variablesRead.find?
          (StackSchedule.identifierUnavailable available) with
      | some identifier =>
          have absent : available.contains identifier = false := by
            have found := List.find?_some unavailable
            simpa [StackSchedule.identifierUnavailable] using found
          have read : identifier ∈ statement.variablesRead :=
            List.mem_of_find?_eq_some unavailable
          have rejected : statement.variablesRead.all available.contains = false := by
            rw [List.all_eq_false]
            exact ⟨identifier, read, by simpa using absent⟩
          simp [Symbolic.recordDefinitions, rejected]
      | none =>
          have acceptedReads : statement.variablesRead.all available.contains = true := by
            rw [List.all_eq_true]
            intro identifier member
            have notFound := (List.find?_eq_none.mp unavailable) identifier member
            simpa [StackSchedule.identifierUnavailable] using notFound
          simp [Symbolic.recordDefinitions, acceptedReads,
            inductionHypothesis]

theorem StackSchedule.firstDuplicate_none_iff (identifiers : List VarId) :
    StackSchedule.firstDuplicate identifiers = none ↔ identifiers.Nodup := by
  induction identifiers with
  | nil => simp [StackSchedule.firstDuplicate]
  | cons identifier identifiers inductionHypothesis =>
      by_cases member : identifier ∈ identifiers <;>
        simp [StackSchedule.firstDuplicate, member, inductionHypothesis]

theorem StackSchedule.Block.check_inv
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∃ finalState,
      certificate.vars.entryLayout.map Symbolic.Value.identifier = certificate.vars.inputs ∧
        certificate.vars.exitLayout.map Symbolic.Value.identifier = certificate.vars.outputs ∧
        StackSchedule.Block.replay certificate.vars.statements
            certificate.stack.instructions.toList
            (Symbolic.State.initial certificate.vars.entryLayout) = .ok finalState ∧
        StackSchedule.firstUnavailable certificate.vars.statements.toList
            (certificate.vars.entryLayout.toList.map Symbolic.Value.identifier) = none ∧
        StackSchedule.firstDuplicate
            ((certificate.vars.entryLayout.toList.map Symbolic.Value.identifier) ++
              certificate.vars.statements.toList.flatMap Vars.Stmt.variablesDefined) = none ∧
        finalState.firedCount = certificate.vars.statements.size ∧
        StackSchedule.Block.terminatorsAgree certificate.vars.terminator
            certificate.stack.terminator = true ∧
        certificate.checkFinalStack finalState = .ok () := by
  simp only [StackSchedule.Block.check] at accepted
  split at accepted <;> try contradiction
  rename_i entryNames
  split at accepted <;> try contradiction
  rename_i exitNames
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i finalState replayed
  split at accepted <;> try contradiction
  rename_i available
  split at accepted <;> try contradiction
  rename_i distinct
  split at accepted <;> try contradiction
  rename_i fired
  split at accepted <;> try contradiction
  rename_i agree
  exact ⟨finalState, by simpa using entryNames, by simpa using exitNames, replayed, available,
    distinct, by simpa using fired, by simpa using agree, accepted⟩

theorem StackSchedule.Block.checkFinalStack_final
    (certificate : StackSchedule.Block) (finalState : Symbolic.State)
    (checked : certificate.checkFinalStack finalState = .ok ()) :
    StackSchedule.Block.finalStack certificate.vars.terminator certificate.vars.exitLayout
      finalState.stack = some finalState.stack := by
  simp only [StackSchedule.Block.checkFinalStack] at checked
  split at checked <;> rename_i sourceTerminator <;>
    simp only [StackSchedule.Block.finalStack, sourceTerminator] <;>
    first
      | rfl
      | (split at checked <;> simp_all)
      | simp at checked

theorem StackSchedule.Block.check_sound
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    ∃ finalState expectedStack,
      Symbolic.executeAll certificate.vars.statements certificate.stack.instructions
          (Symbolic.State.initial certificate.vars.entryLayout) = some finalState ∧
        StackSchedule.Block.finalStack certificate.vars.terminator certificate.vars.exitLayout finalState.stack =
          some expectedStack ∧
        finalState.firedCount = certificate.vars.statements.size ∧
        StackSchedule.Block.terminatorsAgree certificate.vars.terminator certificate.stack.terminator = true ∧
        finalState.stack = expectedStack ∧ certificate.vars.entryLayout.toList.Nodup := by
  obtain ⟨finalState, _, _, replayed, _, distinct, fired, agree, finalStack⟩ :=
    certificate.check_inv accepted
  refine ⟨finalState, finalState.stack, ?_, ?_, fired, agree, rfl, ?_⟩
  · simpa using (StackSchedule.Block.replay_eq_ok_iff _ _ _ _).mp replayed
  · exact StackSchedule.Block.checkFinalStack_final certificate finalState finalStack
  · exact List.Nodup.of_map Symbolic.Value.identifier
      (List.Nodup.of_append_left ((StackSchedule.firstDuplicate_none_iff _).mp distinct))

theorem StackSchedule.Block.check_source_valid
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    Symbolic.readsAvailable certificate.vars.statements certificate.vars.entryLayout =
        true ∧
      Symbolic.definesOnce certificate.vars.statements certificate.vars.entryLayout =
        true := by
  obtain ⟨_, _, _, _, available, distinct, _⟩ := certificate.check_inv accepted
  refine ⟨?_, ?_⟩
  · change (certificate.vars.statements.toList.foldlM Symbolic.recordDefinitions
        (certificate.vars.entryLayout.toList.map Symbolic.Value.identifier)).isSome = true
    exact (StackSchedule.firstUnavailable_none_iff _ _).mp available
  · simpa [Symbolic.definesOnce] using (StackSchedule.firstDuplicate_none_iff _).mp distinct

theorem StackSchedule.Block.check_boundary_names
    (certificate : StackSchedule.Block) (accepted : certificate.check = .ok ()) :
    certificate.vars.entryLayout.map Symbolic.Value.identifier = certificate.vars.inputs ∧
      certificate.vars.exitLayout.map Symbolic.Value.identifier = certificate.vars.outputs := by
  obtain ⟨_, entryNames, exitNames, _⟩ := certificate.check_inv accepted
  exact ⟨entryNames, exitNames⟩

theorem StackSchedule.checkBlocks_get
    (blocks : List StackSchedule.Block) (accepted : StackSchedule.checkBlocks blocks = .ok ())
    (index : Nat) (indexBound : index < blocks.length) : blocks[index].check = .ok () := by
  induction blocks generalizing index with
  | nil => simp at indexBound
  | cons block blocks inductionHypothesis =>
      simp only [StackSchedule.checkBlocks] at accepted
      cases checked : block.check with
      | error error => simp [checked] at accepted
      | ok result =>
          cases result
          simp only [checked] at accepted
          cases index with
          | zero => simpa using checked
          | succ index =>
              apply inductionHypothesis accepted index

theorem StackSchedule.checkEdge_sound
    (schedule : StackSchedule) (source successor : BlockId)
    (exitLayout : Array Symbolic.Value)
    (accepted : schedule.checkEdge source successor exitLayout = .ok ()) :
    schedule.layoutAgreesAt exitLayout successor = true := by
  cases successorAt : schedule.blocks[successor.id]? with
  | none => simp [StackSchedule.checkEdge, successorAt] at accepted
  | some successorBlock =>
      simp [StackSchedule.checkEdge, successorAt] at accepted
      simp [StackSchedule.layoutAgreesAt, successorAt, accepted]

theorem StackSchedule.checkBlockEdges_sound
    (schedule : StackSchedule) (source : BlockId) (block : StackSchedule.Block)
    (blockAccepted : block.check = .ok ())
    (edgesAccepted : schedule.checkBlockEdges source block = .ok ()) :
    schedule.blockEdgesAgree block = true := by
  cases terminator : block.vars.terminator with
  | halt => simp [StackSchedule.blockEdgesAgree, terminator]
  | jump successor =>
      simp only [StackSchedule.blockEdgesAgree, terminator]
      apply StackSchedule.checkEdge_sound schedule source successor block.vars.exitLayout
      simpa [StackSchedule.checkBlockEdges, terminator] using edgesAccepted
  | branch condition thenSuccessor elseSuccessor =>
      have thenAccepted :
          schedule.checkEdge source thenSuccessor block.vars.exitLayout = .ok () := by
        simp [StackSchedule.checkBlockEdges, terminator] at edgesAccepted
        split at edgesAccepted <;> try contradiction
        assumption
      have elseAccepted :
          schedule.checkEdge source elseSuccessor block.vars.exitLayout = .ok () := by
        simp [StackSchedule.checkBlockEdges, terminator] at edgesAccepted
        split at edgesAccepted <;> try contradiction
        simpa using edgesAccepted
      have thenAgreement :=
        StackSchedule.checkEdge_sound schedule source thenSuccessor block.vars.exitLayout
          thenAccepted
      have elseAgreement :=
        StackSchedule.checkEdge_sound schedule source elseSuccessor block.vars.exitLayout
          elseAccepted
      simp [StackSchedule.blockEdgesAgree, terminator, thenAgreement, elseAgreement]
  | iret =>
      obtain ⟨finalState, expectedStack, replay, expected, rest⟩ :=
        StackSchedule.Block.check_sound block blockAccepted
      simp [StackSchedule.Block.finalStack, terminator] at expected

theorem StackSchedule.checkEdges_get
    (schedule : StackSchedule) (blocks : List StackSchedule.Block) (offset index : Nat)
    (accepted : schedule.checkEdges blocks offset = .ok ())
    (indexBound : index < blocks.length) :
    schedule.checkBlockEdges ⟨offset + index⟩ blocks[index] = .ok () := by
  induction blocks generalizing offset index with
  | nil => simp at indexBound
  | cons block blocks inductionHypothesis =>
      simp only [StackSchedule.checkEdges] at accepted
      cases checked : schedule.checkBlockEdges ⟨offset⟩ block with
      | error error => simp [checked] at accepted
      | ok result =>
          cases result
          simp only [checked] at accepted
          cases index with
          | zero => simpa using checked
          | succ index =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis (offset + 1) index accepted (by simpa using indexBound)

theorem StackSchedule.check_sound
    (certificate : StackSchedule) (accepted : certificate.check = .ok ()) :
    certificate.entry.id < certificate.blocks.size ∧
      (∀ index, (indexBound : index < certificate.blocks.size) →
        certificate.blocks[index].check = .ok ()) ∧
      ∀ index, (indexBound : index < certificate.blocks.size) →
        certificate.blockEdgesAgree certificate.blocks[index] = true := by
  simp only [StackSchedule.check] at accepted
  split at accepted <;> try contradiction
  next entryBound =>
    cases blocksAccepted : StackSchedule.checkBlocks certificate.blocks.toList with
    | error error => simp [blocksAccepted] at accepted
    | ok result =>
      cases result
      have edgesAccepted : certificate.checkEdges certificate.blocks.toList = .ok () := by
        simpa [blocksAccepted] using accepted
      refine ⟨entryBound, ?_, ?_⟩
      · intro index indexBound
        simpa using StackSchedule.checkBlocks_get certificate.blocks.toList blocksAccepted
          index (by simpa using indexBound)
      · intro index indexBound
        apply StackSchedule.checkBlockEdges_sound certificate ⟨index⟩
          certificate.blocks[index]
        · simpa using StackSchedule.checkBlocks_get certificate.blocks.toList blocksAccepted
            index (by simpa using indexBound)
        · simpa using StackSchedule.checkEdges_get certificate certificate.blocks.toList 0
            index edgesAccepted (by simpa using indexBound)

theorem StackSchedule.block_boundary_names
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (index : Nat) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[index]? = some blockCertificate) :
    blockCertificate.vars.entryLayout.map Symbolic.Value.identifier = blockCertificate.vars.inputs ∧
      blockCertificate.vars.exitLayout.map Symbolic.Value.identifier =
        blockCertificate.vars.outputs := by
  have indexBound : index < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := index) blockAt
  have blockGet : certificate.blocks[index] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted := (certificate.check_sound accepted).2.1 index indexBound
  apply StackSchedule.Block.check_boundary_names blockCertificate
  simpa [blockGet] using blockAccepted

theorem StackSchedule.ofBlock_check (block : StackSchedule.Block)
    (accepted : block.check = .ok ()) (halted : block.vars.terminator = .halt) :
    (StackSchedule.ofBlock block).check = .ok () := by
  simp [StackSchedule.ofBlock, StackSchedule.check, StackSchedule.checkBlocks,
    StackSchedule.checkEdges, StackSchedule.checkBlockEdges, accepted, halted]

def Symbolic.Value.interpret (locals : Locals) (value : Symbolic.Value) : Option Word :=
  locals.lookup? value.identifier

theorem Symbolic.Value.interpret_list_eq_of_lookup_eq (values : List Symbolic.Value)
    (firstLocals secondLocals : Locals)
    (agrees : ∀ value ∈ values,
      firstLocals.lookup? value.identifier = secondLocals.lookup? value.identifier) :
    values.mapM (Symbolic.Value.interpret firstLocals) =
      values.mapM (Symbolic.Value.interpret secondLocals) := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.mapM_cons, Symbolic.Value.interpret]
      rw [agrees value (by simp), inductionHypothesis]
      intro candidate member
      exact agrees candidate (by simp [member])

theorem Locals.lookup?_assignPairs_of_not_mem (locals : Locals)
    (pairs : List (VarId × Word)) (identifier : VarId)
    (absent : identifier ∉ pairs.map Prod.fst) :
    (locals.assignPairs pairs).lookup? identifier = locals.lookup? identifier := by
  induction pairs generalizing locals with
  | nil => rfl
  | cons pair pairs inductionHypothesis =>
      obtain ⟨assigned, value⟩ := pair
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      rw [Locals.assignPairs]
      rw [inductionHypothesis (locals.assign assigned value) absent.2]
      simp [Locals.lookup?, Locals.assign, absent.1]

theorem Locals.assignPairs_zip_mapM_lookup? (locals : Locals)
    (identifiers : List VarId) (values : List Word) (nodup : identifiers.Nodup)
    (sameLength : identifiers.length = values.length) :
    identifiers.mapM ((locals.assignPairs (identifiers.zip values)).lookup? ·) = some values := by
  induction identifiers generalizing locals values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at sameLength
  | cons identifier identifiers inductionHypothesis =>
      cases values with
      | nil => simp at sameLength
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp only [List.nodup_cons] at nodup
          rw [List.zip_cons_cons, Locals.assignPairs]
          have headLookup :
              ((locals.assign identifier value).assignPairs (identifiers.zip values)).lookup?
                  identifier = some value := by
            rw [Locals.lookup?_assignPairs_of_not_mem]
            · simp [Locals.lookup?, Locals.assign]
            · simpa [List.map_fst_zip, sameLength] using nodup.1
          rw [List.mapM_cons, headLookup,
            inductionHypothesis (locals.assign identifier value) values nodup.2 sameLength]
          rfl

theorem Locals.bindParams_interprets_symbolic_values (symbolicValues : Array Symbolic.Value)
    (values : Array Word) (locals : Locals) (nodup : symbolicValues.toList.Nodup)
    (bound : Locals.bindParams (symbolicValues.map Symbolic.Value.identifier) values = .ok locals) :
    symbolicValues.toList.mapM (Symbolic.Value.interpret locals) = some values.toList := by
  have sameSize : symbolicValues.size = values.size := by
    by_contra different
    have sizeMismatch : (symbolicValues.size != values.size) = true := bne_iff_ne.mpr different
    simp [Locals.bindParams, Locals.bindValues, sizeMismatch, bind, Except.bind] at bound
  rw [Locals.bindParams, Locals.bindValues_eq_assignPairs (by simpa using sameSize)] at bound
  obtain rfl := Except.ok.inj bound
  simpa [Symbolic.Value.interpret, Symbolic.Value.identifier] using
    Locals.assignPairs_zip_mapM_lookup? Locals.empty
      (symbolicValues.toList.map Symbolic.Value.identifier) values.toList
      (nodup.map (by intro left right equal; cases left; cases right; simpa using equal))
      (by simpa using sameSize)

theorem Symbolic.Value.identifiers_mapM_lookup_of_interpretations
    (symbolicValues : List Symbolic.Value) (values : List Word) (locals : Locals)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values) :
    (symbolicValues.map Symbolic.Value.identifier).mapM (locals.lookup ·) = .ok values ∧
      symbolicValues.length = values.length := by
  induction symbolicValues generalizing values with
  | nil =>
      simp at interpretations
      subst values
      exact ⟨rfl, rfl⟩
  | cons symbolicValue symbolicValues inductionHypothesis =>
      cases valueEq : symbolicValue.interpret locals with
      | none => simp [valueEq] at interpretations
      | some value =>
          cases valuesEq : symbolicValues.mapM (Symbolic.Value.interpret locals) with
          | none => simp [valueEq, valuesEq] at interpretations
          | some values' =>
              simp [valueEq, valuesEq] at interpretations
              subst values
              obtain ⟨lookup, length⟩ := inductionHypothesis values' valuesEq
              have headLookup : locals.lookup symbolicValue.identifier = .ok value := by
                obtain ⟨identifier⟩ := symbolicValue
                simp [Symbolic.Value.interpret, Symbolic.Value.identifier] at valueEq
                change locals.lookup identifier = .ok value
                simp [Locals.lookup, valueEq]
              constructor
              · rw [List.map_cons, List.mapM_cons, headLookup, lookup]
                rfl
              · simp [length]

theorem Locals.bindValues_interprets_symbolic_values
    (symbolicValues : Array Symbolic.Value) (values : Array Word)
    (locals result : Locals) (nodup : symbolicValues.toList.Nodup)
    (bound : Locals.bindValues locals (symbolicValues.map Symbolic.Value.identifier) values =
      .ok result) :
    symbolicValues.toList.mapM (Symbolic.Value.interpret result) = some values.toList := by
  have sameSize : symbolicValues.size = values.size := by
    by_contra different
    have sizeMismatch : (symbolicValues.size != values.size) = true :=
      bne_iff_ne.mpr different
    simp [Locals.bindValues, sizeMismatch, bind, Except.bind] at bound
  rw [Locals.bindValues_eq_assignPairs (by simpa using sameSize)] at bound
  obtain rfl := Except.ok.inj bound
  simpa [Symbolic.Value.interpret, Symbolic.Value.identifier] using
    Locals.assignPairs_zip_mapM_lookup? locals
      (symbolicValues.toList.map Symbolic.Value.identifier) values.toList
      (nodup.map (by intro left right equal; cases left; cases right; simpa using equal))
      (by simpa using sameSize)

theorem Locals.transfer_interprets_renamed_symbolic_values
    (sourceValues targetValues : Array Symbolic.Value) (values : List Word) (locals : Locals)
    (sameSize : sourceValues.size = targetValues.size) (nodup : targetValues.toList.Nodup)
    (interpretations : sourceValues.toList.mapM (Symbolic.Value.interpret locals) = some values) :
    ∃ result,
      Locals.transfer (sourceValues.map Symbolic.Value.identifier)
          (targetValues.map Symbolic.Value.identifier) locals = .ok ((), result) ∧
        targetValues.toList.mapM (Symbolic.Value.interpret result) = some values := by
  obtain ⟨lookups, length⟩ :=
    Symbolic.Value.identifiers_mapM_lookup_of_interpretations
      sourceValues.toList values locals interpretations
  have arrayLookups :
      (sourceValues.map Symbolic.Value.identifier).mapM (locals.lookup ·) =
        .ok values.toArray := by
    rw [Array.mapM_eq_mapM_toList]
    simp only [Array.toList_map]
    rw [lookups]
    rfl
  let result := locals.assignPairs
    ((targetValues.map Symbolic.Value.identifier).toList.zip values)
  have targetLength : targetValues.size = values.toArray.size := by
    calc
      targetValues.size = sourceValues.size := sameSize.symm
      _ = sourceValues.toList.length := by simp
      _ = values.length := length
      _ = values.toArray.size := by simp
  have bound : Locals.bindValues locals (targetValues.map Symbolic.Value.identifier)
      values.toArray = .ok result := by
    rw [Locals.bindValues_eq_assignPairs (by simpa using targetLength)]
  refine ⟨result, ?_, ?_⟩
  · simp [Locals.transfer, arrayLookups, bound, bind, Except.bind, pure, Except.pure]
  · exact Locals.bindValues_interprets_symbolic_values targetValues values.toArray locals
      result nodup bound

def Symbolic.State.Interprets (state : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) : Prop :=
  state.stack.mapM (Symbolic.Value.interpret locals) = some environment.stack ∧
    ∀ slot symbolicValue, state.slotValue? slot = some symbolicValue →
      ∃ value, symbolicValue.interpret locals = some value ∧
        environment.slots slot = some value

theorem Symbolic.State.initial_interprets_in_environment
    (entryLayout : Array Symbolic.Value) (locals : Locals) (environment : Stack.Environment)
    (stackValues : entryLayout.toList.mapM (Symbolic.Value.interpret locals) =
      some environment.stack) :
    (Symbolic.State.initial entryLayout).Interprets locals environment := by
  constructor
  · exact stackValues
  · intro slot symbolicValue lookup
    simp [Symbolic.State.initial, Symbolic.State.slotValue?] at lookup

theorem Symbolic.Value.interpret_at_depth (locals : Locals)
    (symbolicValues : List Symbolic.Value) (values : List Word)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values)
    (depth : Nat) (symbolicValue : Symbolic.Value)
    (symbolicValueAtDepth : symbolicValues[depth]? = some symbolicValue) :
    ∃ value, values[depth]? = some value ∧ symbolicValue.interpret locals = some value := by
  induction symbolicValues generalizing values depth with
  | nil => simp at symbolicValueAtDepth
  | cons head stack inductionHypothesis =>
      cases headValueEq : head.interpret locals with
      | none => simp [headValueEq] at interpretations
      | some headValue =>
          cases stackValuesEq : stack.mapM (Symbolic.Value.interpret locals) with
          | none => simp [headValueEq, stackValuesEq] at interpretations
          | some stackValues =>
              simp [headValueEq, stackValuesEq] at interpretations
              subst values
              cases depth with
              | zero =>
                  simp at symbolicValueAtDepth
                  subst symbolicValue
                  exact ⟨headValue, by simp, headValueEq⟩
              | succ depth =>
                  simp only [List.getElem?_cons_succ] at symbolicValueAtDepth ⊢
                  exact inductionHypothesis stackValues stackValuesEq depth symbolicValueAtDepth

theorem Symbolic.Value.interpret_set (locals : Locals)
    (symbolicValues : List Symbolic.Value) (values : List Word)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values)
    (depth : Nat) (replacement : Symbolic.Value) (value : Word)
    (replacementInterpretation : replacement.interpret locals = some value)
    (depthWithinStack : depth < symbolicValues.length) :
    (symbolicValues.set depth replacement).mapM (Symbolic.Value.interpret locals) =
      some (values.set depth value) := by
  induction symbolicValues generalizing values depth with
  | nil => simp at depthWithinStack
  | cons head stack inductionHypothesis =>
      cases headValueEq : head.interpret locals with
      | none => simp [headValueEq] at interpretations
      | some headValue =>
          cases stackValuesEq : stack.mapM (Symbolic.Value.interpret locals) with
          | none => simp [headValueEq, stackValuesEq] at interpretations
          | some stackValues =>
              simp [headValueEq, stackValuesEq] at interpretations
              subst values
              cases depth with
              | zero => simp [replacementInterpretation, stackValuesEq]
              | succ depth =>
                  simp only [List.length_cons, Nat.succ_lt_succ_iff] at depthWithinStack
                  simp [headValueEq,
                    inductionHypothesis stackValues stackValuesEq depth depthWithinStack]

theorem Symbolic.Value.interpret_assign_of_ne (locals : Locals)
    (symbolicValue : Symbolic.Value) (result : VarId) (value : Word)
    (different : symbolicValue ≠ .variable result) :
    symbolicValue.interpret (locals.assign result value) = symbolicValue.interpret locals := by
  cases symbolicValue
  rename_i identifier
  simp only [Symbolic.Value.interpret, Symbolic.Value.identifier, Locals.lookup?, Locals.assign]
  simp only [ne_eq, Symbolic.Value.variable.injEq] at different
  simp [different]

theorem Symbolic.Value.interpret_list_assign_of_not_mem (locals : Locals)
    (symbolicValues : List Symbolic.Value) (result : VarId) (value : Word)
    (absent : .variable result ∉ symbolicValues) :
    symbolicValues.mapM (Symbolic.Value.interpret (locals.assign result value)) =
      symbolicValues.mapM (Symbolic.Value.interpret locals) := by
  induction symbolicValues with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons, not_or] at absent
      simp [Symbolic.Value.interpret_assign_of_ne locals head result value (Ne.symm absent.1),
        inductionHypothesis absent.2]

theorem Symbolic.State.slotFree_of_eq_true (state : Symbolic.State)
    (operandCount : Nat) (result : Symbolic.Value)
    (absent : state.slotFree operandCount result = true) :
    result ∉ state.stack.drop operandCount ∧
      ∀ binding ∈ state.slotBindings, binding.2 ≠ result := by
  simp [Symbolic.State.slotFree] at absent
  refine ⟨absent.1, ?_⟩
  intro binding member
  rw [Array.mem_iff_getElem] at member
  obtain ⟨index, bound, rfl⟩ := member
  exact absent.2 index bound

theorem Symbolic.Value.interpret_drop (locals : Locals)
    (symbolicValues : List Symbolic.Value) (values : List Word)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values)
    (count : Nat) :
    (symbolicValues.drop count).mapM (Symbolic.Value.interpret locals) =
      some (values.drop count) := by
  induction symbolicValues generalizing values count with
  | nil =>
      simp at interpretations
      subst values
      simp
  | cons symbolicValue symbolicValues inductionHypothesis =>
      cases valueEq : symbolicValue.interpret locals with
      | none => simp [valueEq] at interpretations
      | some value =>
          cases valuesEq : symbolicValues.mapM (Symbolic.Value.interpret locals) with
          | none => simp [valueEq, valuesEq] at interpretations
          | some values' =>
              simp [valueEq, valuesEq] at interpretations
              subst values
              cases count with
              | zero => simp [valueEq, valuesEq]
              | succ count => exact inductionHypothesis values' valuesEq count

theorem Symbolic.Value.interpret_take (locals : Locals)
    (symbolicValues : List Symbolic.Value) (values : List Word)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values)
    (count : Nat) :
    (symbolicValues.take count).mapM (Symbolic.Value.interpret locals) =
      some (values.take count) := by
  induction symbolicValues generalizing values count with
  | nil =>
      simp at interpretations
      subst values
      simp
  | cons symbolicValue symbolicValues inductionHypothesis =>
      cases valueEq : symbolicValue.interpret locals with
      | none => simp [valueEq] at interpretations
      | some value =>
          cases valuesEq : symbolicValues.mapM (Symbolic.Value.interpret locals) with
          | none => simp [valueEq, valuesEq] at interpretations
          | some values' =>
              simp [valueEq, valuesEq] at interpretations
              subst values
              cases count with
              | zero => simp
              | succ count => simp [valueEq, inductionHypothesis values' valuesEq count]

theorem Symbolic.State.slotValue?_member (state : Symbolic.State) (slot : Nat)
    (symbolicValue : Symbolic.Value) (lookup : state.slotValue? slot = some symbolicValue) :
    ∃ binding ∈ state.slotBindings, binding.2 = symbolicValue := by
  unfold Symbolic.State.slotValue? at lookup
  obtain ⟨binding, found, rfl⟩ := Option.map_eq_some_iff.mp lookup
  exact ⟨binding, Array.mem_of_find?_eq_some found, rfl⟩

theorem Symbolic.State.Interprets.after_fire (state nextState : Symbolic.State)
    (locals : Locals) (environment : Stack.Environment)
    (interprets : state.Interprets locals environment) (operands : List Symbolic.Value)
    (statementIndex : Nat) (result : VarId) (resultValue : Word)
    (absent : state.slotFree operands.length (.variable result) = true)
    (nextStateEq : nextState = { state with
      stack := .variable result :: state.stack.drop operands.length
      firedStatementIndices := statementIndex :: state.firedStatementIndices }) :
    nextState.Interprets (locals.assign result resultValue)
      { environment with stack := resultValue :: environment.stack.drop operands.length } := by
  subst nextState
  obtain ⟨stackAbsent, slotsAbsent⟩ := state.slotFree_of_eq_true operands.length
    (.variable result) absent
  constructor
  · simp only [List.mapM_cons]
    rw [show (Symbolic.Value.variable result).interpret (locals.assign result resultValue) =
      some resultValue by simp [Symbolic.Value.interpret, Symbolic.Value.identifier,
        Locals.lookup?, Locals.assign]]
    rw [Symbolic.Value.interpret_list_assign_of_not_mem locals
      (state.stack.drop operands.length) result resultValue stackAbsent]
    rw [Symbolic.Value.interpret_drop locals state.stack environment.stack interprets.1
      operands.length]
    rfl
  · intro slot symbolicValue lookup
    obtain ⟨value, valueEq, slotEq⟩ := interprets.2 slot symbolicValue lookup
    obtain ⟨binding, member, bindingEq⟩ := state.slotValue?_member slot symbolicValue lookup
    have different : symbolicValue ≠ .variable result := by
      rw [← bindingEq]
      exact slotsAbsent binding member
    refine ⟨value, ?_, slotEq⟩
    rw [Symbolic.Value.interpret_assign_of_ne locals symbolicValue result resultValue different]
    exact valueEq

theorem Symbolic.State.Interprets.replay_pop (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (replay : Symbolic.execute sourceStatements state .pop = some nextState) :
    ∃ value stack, environment.stack = value :: stack ∧
      nextState.Interprets locals { environment with stack } := by
  cases stackEq : state.stack with
  | nil => simp [Symbolic.execute, stackEq] at replay
  | cons value stack =>
      simp [Symbolic.execute, stackEq] at replay
      subst nextState
      cases valueEq : Symbolic.Value.interpret locals value with
      | none => simp [Symbolic.State.Interprets, stackEq, valueEq] at interprets
      | some word =>
          cases stackValuesEq : stack.mapM (Symbolic.Value.interpret locals) with
          | none =>
              simp [Symbolic.State.Interprets, stackEq, valueEq, stackValuesEq]
                at interprets
          | some stackValues =>
              have environmentStackEq : word :: stackValues = environment.stack := by
                simpa [Symbolic.State.Interprets, stackEq, valueEq, stackValuesEq]
                  using interprets.1
              refine ⟨word, stackValues, environmentStackEq.symm, ?_⟩
              exact ⟨stackValuesEq, interprets.2⟩

theorem Symbolic.State.Interprets.replay_dup (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (depth : Nat)
    (replay : Symbolic.execute sourceStatements state (.dup depth) = some nextState) :
    ∃ value, environment.stack[depth]? = some value ∧
      nextState.Interprets locals { environment with stack := value :: environment.stack } := by
  simp [Symbolic.execute] at replay
  obtain ⟨depthWithinReach, symbolicValue, symbolicValueAtDepth, rfl⟩ := replay
  obtain ⟨value, valueAtDepth, symbolicValueEq⟩ :=
    Symbolic.Value.interpret_at_depth locals state.stack environment.stack interprets.1 depth
      symbolicValue symbolicValueAtDepth
  refine ⟨value, valueAtDepth, ?_⟩
  constructor
  · simp [symbolicValueEq, interprets.1]
  · exact interprets.2

theorem Symbolic.State.Interprets.replay_swap (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (depth : Nat)
    (replay : Symbolic.execute sourceStatements state (.swap depth) = some nextState) :
    ∃ stack, Stack.exchange environment.stack 0 depth = some stack ∧
      nextState.Interprets locals { environment with stack } := by
  change (if 1 ≤ depth ∧ depth ≤ 16 then
      (Symbolic.exchange state.stack 0 depth).map fun stack => { state with stack }
    else none) = some nextState at replay
  by_cases depthWithinReach : 1 ≤ depth ∧ depth ≤ 16
  · rw [if_pos depthWithinReach] at replay
    cases exchangeEq : Symbolic.exchange state.stack 0 depth with
    | none => rw [exchangeEq] at replay; simp at replay
    | some symbolicStack =>
      rw [exchangeEq] at replay
      simp at replay
      subst nextState
      unfold Symbolic.exchange at exchangeEq
      cases topEq : state.stack[0]? with
      | none => simp [topEq] at exchangeEq
      | some top =>
        cases otherEq : state.stack[depth]? with
        | none => simp [topEq, otherEq] at exchangeEq
        | some other =>
          simp [topEq, otherEq] at exchangeEq
          subst symbolicStack
          obtain ⟨topValue, topValueAt, topInterpretation⟩ :=
            Symbolic.Value.interpret_at_depth locals state.stack environment.stack interprets.1
              0 top topEq
          obtain ⟨otherValue, otherValueAt, otherInterpretation⟩ :=
            Symbolic.Value.interpret_at_depth locals state.stack environment.stack interprets.1
              depth other otherEq
          refine ⟨(environment.stack.set 0 otherValue).set depth topValue, ?_, ?_⟩
          · simp [Stack.exchange, topValueAt, otherValueAt]
          · constructor
            · have zeroWithinStack : 0 < state.stack.length :=
                List.getElem?_eq_some_iff.mp topEq |>.1
              have depthWithinStack : depth < state.stack.length :=
                List.getElem?_eq_some_iff.mp otherEq |>.1
              have firstInterpretations := Symbolic.Value.interpret_set locals state.stack
                environment.stack interprets.1 0 other otherValue otherInterpretation
                zeroWithinStack
              exact Symbolic.Value.interpret_set locals (state.stack.set 0 other)
                (environment.stack.set 0 otherValue) firstInterpretations depth top topValue
                topInterpretation (by simpa using depthWithinStack)
            · exact interprets.2
  · rw [if_neg depthWithinReach] at replay
    simp at replay

theorem Symbolic.State.Interprets.replay_exchange (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (firstDepth secondDepth : Nat)
    (replay : Symbolic.execute sourceStatements state
      (.exchange firstDepth secondDepth) = some nextState) :
    ∃ stack, Stack.exchange environment.stack firstDepth secondDepth = some stack ∧
      nextState.Interprets locals { environment with stack } := by
  change (if firstDepth ≠ secondDepth ∧ max firstDepth secondDepth ≤ 16 then
      (Symbolic.exchange state.stack firstDepth secondDepth).map fun stack =>
        { state with stack }
    else none) = some nextState at replay
  by_cases depthsWithinReach :
      firstDepth ≠ secondDepth ∧ max firstDepth secondDepth ≤ 16
  · rw [if_pos depthsWithinReach] at replay
    cases exchangeEq : Symbolic.exchange state.stack firstDepth secondDepth with
    | none => rw [exchangeEq] at replay; simp at replay
    | some symbolicStack =>
      rw [exchangeEq] at replay
      simp at replay
      subst nextState
      unfold Symbolic.exchange at exchangeEq
      cases firstEq : state.stack[firstDepth]? with
      | none => simp [firstEq] at exchangeEq
      | some first =>
        cases secondEq : state.stack[secondDepth]? with
        | none => simp [firstEq, secondEq] at exchangeEq
        | some second =>
          simp [firstEq, secondEq] at exchangeEq
          subst symbolicStack
          obtain ⟨firstValue, firstValueAt, firstInterpretation⟩ :=
            Symbolic.Value.interpret_at_depth locals state.stack environment.stack interprets.1
              firstDepth first firstEq
          obtain ⟨secondValue, secondValueAt, secondInterpretation⟩ :=
            Symbolic.Value.interpret_at_depth locals state.stack environment.stack interprets.1
              secondDepth second secondEq
          refine ⟨(environment.stack.set firstDepth secondValue).set secondDepth firstValue,
            ?_, ?_⟩
          · simp [Stack.exchange, firstValueAt, secondValueAt]
          · constructor
            · have firstWithinStack : firstDepth < state.stack.length :=
                List.getElem?_eq_some_iff.mp firstEq |>.1
              have secondWithinStack : secondDepth < state.stack.length :=
                List.getElem?_eq_some_iff.mp secondEq |>.1
              have firstInterpretations := Symbolic.Value.interpret_set locals state.stack
                environment.stack interprets.1 firstDepth second secondValue secondInterpretation
                firstWithinStack
              exact Symbolic.Value.interpret_set locals (state.stack.set firstDepth second)
                (environment.stack.set firstDepth secondValue) firstInterpretations secondDepth first
                firstValue firstInterpretation (by simpa using secondWithinStack)
            · exact interprets.2
  · rw [if_neg depthsWithinReach] at replay
    simp at replay

theorem Symbolic.State.slotValue?_push (state : Symbolic.State)
    (slot candidate : Nat) (value : Symbolic.Value) (absent : state.slotValue? slot = none) :
    ({ state with slotBindings := state.slotBindings.push (slot, value) }).slotValue? candidate =
      if candidate = slot then some value else state.slotValue? candidate := by
  by_cases candidateEq : candidate = slot
  · subst candidate
    have foundNone :
        state.slotBindings.find? (fun binding => binding.1 = slot) = none :=
      Option.map_eq_none_iff.mp absent
    simp [Symbolic.State.slotValue?, Array.find?_push, foundNone]
  · have slotNe : slot ≠ candidate := Ne.symm candidateEq
    simp [Symbolic.State.slotValue?, Array.find?_push, candidateEq, slotNe]

theorem Symbolic.State.Interprets.replay_store (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (slot : Nat)
    (replay : Symbolic.execute sourceStatements state (.store slot) = some nextState) :
    ∃ value stack, environment.stack = value :: stack ∧
      nextState.Interprets locals
        (Stack.Environment.mk stack (environment.storeSlot slot value).slots) := by
  simp only [Symbolic.execute] at replay
  cases stackEq : state.stack with
  | nil => simp [stackEq] at replay
  | cons symbolicValue symbolicStack =>
      cases absentEq : state.slotValue? slot with
      | some existing => simp [stackEq, absentEq] at replay
      | none =>
          simp [stackEq, absentEq] at replay
          subst nextState
          cases valueEq : symbolicValue.interpret locals with
          | none => simp [Symbolic.State.Interprets, stackEq, valueEq] at interprets
          | some value =>
              cases stackValuesEq :
                  symbolicStack.mapM (Symbolic.Value.interpret locals) with
              | none =>
                  simp [Symbolic.State.Interprets, stackEq, valueEq, stackValuesEq]
                    at interprets
              | some stack =>
                  have environmentStackEq : value :: stack = environment.stack := by
                    simpa [Symbolic.State.Interprets, stackEq, valueEq, stackValuesEq]
                      using interprets.1
                  refine ⟨value, stack, environmentStackEq.symm, ?_⟩
                  constructor
                  · exact stackValuesEq
                  · intro candidate candidateValue candidateLookup
                    have candidateLookup' :
                        ({ state with
                          slotBindings := state.slotBindings.push (slot, symbolicValue) }).slotValue?
                            candidate = some candidateValue := by
                      simpa [Symbolic.State.slotValue?] using candidateLookup
                    rw [Symbolic.State.slotValue?_push state slot candidate symbolicValue
                      absentEq] at candidateLookup'
                    by_cases candidateEq : candidate = slot
                    · subst candidate
                      have candidateValueEq : symbolicValue = candidateValue := by
                        simpa using candidateLookup'
                      subst candidateValue
                      exact ⟨value, valueEq, by simp [Stack.Environment.storeSlot]⟩
                    · simp only [candidateEq, ↓reduceIte] at candidateLookup'
                      obtain ⟨candidateWord, candidateValueEq, candidateSlotEq⟩ :=
                        interprets.2 candidate candidateValue candidateLookup'
                      exact ⟨candidateWord, candidateValueEq, by
                        simpa [Stack.Environment.storeSlot, candidateEq] using candidateSlotEq⟩

theorem Symbolic.State.Interprets.replay_load (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (slot : Nat)
    (replay : Symbolic.execute sourceStatements state (.load slot) = some nextState) :
    ∃ value, environment.slots slot = some value ∧
      nextState.Interprets locals { environment with stack := value :: environment.stack } := by
  simp only [Symbolic.execute] at replay
  cases bindingEq : state.slotValue? slot with
  | none => simp [bindingEq] at replay
  | some symbolicValue =>
      simp [bindingEq] at replay
      subst nextState
      have slotInterpretation := interprets.2 slot symbolicValue bindingEq
      obtain ⟨value, valueEq, slotValueEq⟩ := slotInterpretation
      refine ⟨value, slotValueEq, ?_⟩
      constructor
      · simp [valueEq, interprets.1]
      · exact interprets.2

theorem Symbolic.State.Interprets.replay_pop_step {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl)
    (replay : Symbolic.execute sourceStatements state .pop = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl = some (targetNext, .pop)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨value, stack, stackEq, nextInterprets⟩ :=
    interprets.replay_pop sourceStatements state nextState locals environment replay
  refine ⟨{ environment with stack }, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, stackEq]

theorem Symbolic.State.Interprets.replay_dup_step {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl) (depth : Nat)
    (replay : Symbolic.execute sourceStatements state (.dup depth) = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl = some (targetNext, .dup depth)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨value, valueAt, nextInterprets⟩ :=
    interprets.replay_dup sourceStatements state nextState locals environment depth replay
  refine ⟨{ environment with stack := value :: environment.stack }, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, valueAt]

theorem Symbolic.State.Interprets.replay_swap_step {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl) (depth : Nat)
    (replay : Symbolic.execute sourceStatements state (.swap depth) = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl = some (targetNext, .swap depth)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨stack, stackEq, nextInterprets⟩ :=
    interprets.replay_swap sourceStatements state nextState locals environment depth replay
  refine ⟨{ environment with stack }, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, stackEq]

theorem Symbolic.State.Interprets.replay_exchange_step
    {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl) (firstDepth secondDepth : Nat)
    (replay : Symbolic.execute sourceStatements state
      (.exchange firstDepth secondDepth) = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl =
      some (targetNext, .exchange firstDepth secondDepth)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨stack, stackEq, nextInterprets⟩ :=
    interprets.replay_exchange sourceStatements state nextState locals environment firstDepth
      secondDepth replay
  have depthsDifferent : firstDepth ≠ secondDepth := by
    intro equal
    subst secondDepth
    simp [Symbolic.execute] at replay
  refine ⟨{ environment with stack }, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, stackEq, depthsDifferent]

theorem Symbolic.State.Interprets.replay_store_step {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl) (slot : Nat)
    (replay : Symbolic.execute sourceStatements state (.store slot) = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl = some (targetNext, .store slot)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨value, stack, stackEq, nextInterprets⟩ :=
    interprets.replay_store sourceStatements state nextState locals environment slot replay
  refine ⟨Stack.Environment.mk stack (environment.storeSlot slot value).slots, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, stackEq,
    Stack.Environment.storeSlot]

theorem Symbolic.State.Interprets.replay_load_step {targetProgram : Stack.Program}
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (targetControl targetNext : Machine.MachineControl) (slot : Nat)
    (replay : Symbolic.execute sourceStatements state (.load slot) = some nextState)
    (targetDecode : targetProgram.decodeInstruction targetControl = some (targetNext, .load slot)) :
    ∃ environment',
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ [] ⟨globals, environment', targetNext⟩ ∧
      nextState.Interprets locals environment' := by
  obtain ⟨value, valueAt, nextInterprets⟩ :=
    interprets.replay_load sourceStatements state nextState locals environment slot replay
  refine ⟨{ environment with stack := value :: environment.stack }, ?_, nextInterprets⟩
  apply Machine.Step.control
  simp [Stack.decoder, Stack.control, targetDecode, valueAt]

def sourceStatementConcreteOperation (locals : Locals) :
    Vars.Stmt → Option (Machine.Operation × List Word × VarId × Word)
  | .assign result (.constant value) => some (.constant value, [], result, value)
  | .assign result (.var source) =>
      (locals.lookup? source).map fun value => (.copy, [value], result, value)
  | .assign result (.add lhs rhs) => do
      let lhsValue ← locals.lookup? lhs
      let rhsValue ← locals.lookup? rhs
      some (.add, [lhsValue, rhsValue], result, Evm.UInt256.add lhsValue rhsValue)
  | .assign result (.lt lhs rhs) => do
      let lhsValue ← locals.lookup? lhs
      let rhsValue ← locals.lookup? rhs
      some (.lt, [lhsValue, rhsValue], result, Evm.UInt256.lt lhsValue rhsValue)
  | _ => none

theorem Symbolic.operationOf_operand_length (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Symbolic.Value) (result : Symbolic.Value)
    (symbolicOperation : Symbolic.operationOf statement =
      some (operation, operands, result)) :
    operands.length = operation.inputCount := by
  cases statement with
  | assign result expression =>
      cases expression with
      | constant value =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          rfl
      | var source =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          rfl
      | add lhs rhs =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          rfl
      | lt lhs rhs =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          rfl
      | sload key => simp [Symbolic.operationOf] at symbolicOperation
  | sstore => simp [Symbolic.operationOf] at symbolicOperation
  | gas => simp [Symbolic.operationOf] at symbolicOperation
  | call => simp [Symbolic.operationOf] at symbolicOperation
  | malloc => simp [Symbolic.operationOf] at symbolicOperation
  | mallocUninit => simp [Symbolic.operationOf] at symbolicOperation
  | mstore32 => simp [Symbolic.operationOf] at symbolicOperation
  | mload32 => simp [Symbolic.operationOf] at symbolicOperation
  | icall => simp [Symbolic.operationOf] at symbolicOperation

theorem Symbolic.operationOf_result_variable (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Symbolic.Value) (result : Symbolic.Value)
    (symbolicOperation : Symbolic.operationOf statement =
      some (operation, operands, result)) :
    ∃ identifier, result = .variable identifier := by
  cases statement with
  | assign identifier expression =>
      cases expression <;> simp [Symbolic.operationOf] at symbolicOperation
      all_goals exact ⟨identifier, symbolicOperation.2.2.symm⟩
  | sstore => simp [Symbolic.operationOf] at symbolicOperation
  | gas => simp [Symbolic.operationOf] at symbolicOperation
  | call => simp [Symbolic.operationOf] at symbolicOperation
  | malloc => simp [Symbolic.operationOf] at symbolicOperation
  | mallocUninit => simp [Symbolic.operationOf] at symbolicOperation
  | mstore32 => simp [Symbolic.operationOf] at symbolicOperation
  | mload32 => simp [Symbolic.operationOf] at symbolicOperation
  | icall => simp [Symbolic.operationOf] at symbolicOperation

theorem Symbolic.operationOf_result_mem (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Symbolic.Value) (result : VarId)
    (symbolicOperation : Symbolic.operationOf statement =
      some (operation, operands, .variable result)) :
    result ∈ statement.variablesDefined := by
  cases statement with
  | assign assigned expression =>
      cases expression <;>
        simp [Symbolic.operationOf, Vars.Stmt.variablesDefined] at symbolicOperation ⊢
      all_goals exact symbolicOperation.2.2.symm
  | sstore => simp [Symbolic.operationOf] at symbolicOperation
  | gas => simp [Symbolic.operationOf] at symbolicOperation
  | call => simp [Symbolic.operationOf] at symbolicOperation
  | malloc => simp [Symbolic.operationOf] at symbolicOperation
  | mallocUninit => simp [Symbolic.operationOf] at symbolicOperation
  | mstore32 => simp [Symbolic.operationOf] at symbolicOperation
  | mload32 => simp [Symbolic.operationOf] at symbolicOperation
  | icall => simp [Symbolic.operationOf] at symbolicOperation

theorem sourceStatementConcreteOperation_of_symbolic (locals : Locals) (statement : Vars.Stmt)
    (operation : Machine.Operation) (symbolicOperands : List Symbolic.Value) (result : VarId)
    (operands : List Word)
    (symbolicOperation : Symbolic.operationOf statement =
      some (operation, symbolicOperands, .variable result))
    (interpretations : symbolicOperands.mapM (Symbolic.Value.interpret locals) = some operands) :
    ∃ resultValue, sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue) := by
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          simp at interpretations
          subst operands
          exact ⟨value, rfl⟩
      | var source =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          cases sourceValueEq : locals.lookup? source with
          | none =>
              simp [Symbolic.Value.interpret, Symbolic.Value.identifier, sourceValueEq]
                at interpretations
          | some sourceValue =>
              simp [Symbolic.Value.interpret, Symbolic.Value.identifier, sourceValueEq]
                at interpretations
              subst operands
              exact ⟨sourceValue, by simp [sourceStatementConcreteOperation, sourceValueEq]⟩
      | add lhs rhs =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          cases lhsValueEq : locals.lookup? lhs with
          | none =>
              simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq]
                at interpretations
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq,
                    rhsValueEq] at interpretations
              | some rhsValue =>
                  simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq,
                    rhsValueEq] at interpretations
                  subst operands
                  exact ⟨Evm.UInt256.add lhsValue rhsValue,
                    by simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]⟩
      | lt lhs rhs =>
          simp [Symbolic.operationOf] at symbolicOperation
          obtain ⟨rfl, rfl, rfl⟩ := symbolicOperation
          cases lhsValueEq : locals.lookup? lhs with
          | none =>
              simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq]
                at interpretations
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq,
                    rhsValueEq] at interpretations
              | some rhsValue =>
                  simp [Symbolic.Value.interpret, Symbolic.Value.identifier, lhsValueEq,
                    rhsValueEq] at interpretations
                  subst operands
                  exact ⟨Evm.UInt256.lt lhsValue rhsValue,
                    by simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]⟩
      | sload key => simp [Symbolic.operationOf] at symbolicOperation
  | sstore => simp [Symbolic.operationOf] at symbolicOperation
  | gas => simp [Symbolic.operationOf] at symbolicOperation
  | call => simp [Symbolic.operationOf] at symbolicOperation
  | malloc => simp [Symbolic.operationOf] at symbolicOperation
  | mallocUninit => simp [Symbolic.operationOf] at symbolicOperation
  | mstore32 => simp [Symbolic.operationOf] at symbolicOperation
  | mload32 => simp [Symbolic.operationOf] at symbolicOperation
  | icall => simp [Symbolic.operationOf] at symbolicOperation

theorem sourceStatementConcreteOperation_eq_of_variablesRead_eq
    (firstLocals secondLocals : Locals) (statement : Vars.Stmt)
    (readsAgree : ∀ identifier ∈ statement.variablesRead,
      firstLocals.lookup? identifier = secondLocals.lookup? identifier) :
    sourceStatementConcreteOperation firstLocals statement =
      sourceStatementConcreteOperation secondLocals statement := by
  cases statement with
  | assign result expression =>
      cases expression with
      | constant value => rfl
      | var source =>
          simp [sourceStatementConcreteOperation,
            readsAgree source (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])]
      | add lhs rhs =>
          simp [sourceStatementConcreteOperation,
            readsAgree lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead]),
            readsAgree rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])]
      | lt lhs rhs =>
          simp [sourceStatementConcreteOperation,
            readsAgree lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead]),
            readsAgree rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])]
      | sload key => rfl
  | sstore => rfl
  | gas => rfl
  | call => rfl
  | malloc => rfl
  | mallocUninit => rfl
  | mstore32 => rfl
  | mload32 => rfl
  | icall => rfl

def evaluateSourceStatement (locals : Locals) (statement : Vars.Stmt) : Option Locals :=
  match sourceStatementConcreteOperation locals statement with
  | some (_, _, result, resultValue) => some (locals.assign result resultValue)
  | none => none

def sourceOrderReferenceLocals (sourceStatements : Array Vars.Stmt) (entryLocals : Locals) :
    Option Locals :=
  sourceStatements.toList.foldlM evaluateSourceStatement entryLocals

theorem Locals.lookup?_eq_some_of_lookup_eq_ok (locals : Locals) (identifier : VarId)
    (value : Word) (lookup : locals.lookup identifier = .ok value) :
    locals.lookup? identifier = some value := by
  unfold Locals.lookup at lookup
  cases lookup' : locals.lookup? identifier with
  | none => simp [lookup'] at lookup
  | some found =>
      simp [lookup'] at lookup
      subst found
      rfl

theorem Symbolic.Value.interpretations_cover_variables (symbolicValues : List Symbolic.Value)
    (values : List Word) (locals : Locals)
    (interpretations : symbolicValues.mapM (Symbolic.Value.interpret locals) = some values) :
    locals.CoversVariables (symbolicValues.map Symbolic.Value.identifier) := by
  induction symbolicValues generalizing values with
  | nil => simp [Locals.CoversVariables]
  | cons symbolicValue symbolicValues inductionHypothesis =>
      cases valueEq : symbolicValue.interpret locals with
      | none => simp [valueEq] at interpretations
      | some value =>
          cases valuesEq : symbolicValues.mapM (Symbolic.Value.interpret locals) with
          | none => simp [valueEq, valuesEq] at interpretations
          | some remainingValues =>
              simp [valueEq, valuesEq] at interpretations
              subst values
              intro identifier member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with identifierEq | member
              · subst identifier
                refine ⟨value, ?_⟩
                have lookup : locals.lookup? symbolicValue.identifier = some value := by
                  simpa [Symbolic.Value.interpret] using valueEq
                simp [Locals.lookup, lookup]
              · exact inductionHypothesis remainingValues valuesEq identifier member

theorem evaluateSourceStatement_exists_of_supported (locals : Locals) (statement : Vars.Stmt)
    (supported : ∃ symbolicOperation,
      Symbolic.operationOf statement = some symbolicOperation)
    (covered : locals.CoversVariables statement.variablesRead) :
    ∃ nextLocals,
      evaluateSourceStatement locals statement = some nextLocals ∧
        (∀ identifier, locals.Defined identifier → nextLocals.Defined identifier) ∧
        nextLocals.CoversVariables statement.variablesDefined := by
  obtain ⟨symbolicOperation, supported⟩ := supported
  cases statement with
  | assign result expression =>
      cases expression with
      | constant value =>
          refine ⟨locals.assign result value, rfl, ?_, ?_⟩
          · exact fun identifier defined => Locals.defined_assign_of_defined defined
          · intro identifier member
            simp [Vars.Stmt.variablesDefined] at member
            subst identifier
            exact Locals.defined_assign locals result value
      | var source =>
          obtain ⟨sourceValue, sourceLookup⟩ :=
            covered source (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have sourceLookup' := Locals.lookup?_eq_some_of_lookup_eq_ok locals source sourceValue
            sourceLookup
          refine ⟨locals.assign result sourceValue, ?_, ?_, ?_⟩
          · simp [evaluateSourceStatement, sourceStatementConcreteOperation, sourceLookup']
          · exact fun identifier defined => Locals.defined_assign_of_defined defined
          · intro identifier member
            simp [Vars.Stmt.variablesDefined] at member
            subst identifier
            exact Locals.defined_assign locals result sourceValue
      | add lhs rhs =>
          obtain ⟨lhsValue, lhsLookup⟩ :=
            covered lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          obtain ⟨rhsValue, rhsLookup⟩ :=
            covered rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have lhsLookup' := Locals.lookup?_eq_some_of_lookup_eq_ok locals lhs lhsValue lhsLookup
          have rhsLookup' := Locals.lookup?_eq_some_of_lookup_eq_ok locals rhs rhsValue rhsLookup
          refine ⟨locals.assign result (Evm.UInt256.add lhsValue rhsValue), ?_, ?_, ?_⟩
          · simp [evaluateSourceStatement, sourceStatementConcreteOperation, lhsLookup', rhsLookup']
          · exact fun identifier defined => Locals.defined_assign_of_defined defined
          · intro identifier member
            simp [Vars.Stmt.variablesDefined] at member
            subst identifier
            exact Locals.defined_assign locals result (Evm.UInt256.add lhsValue rhsValue)
      | lt lhs rhs =>
          obtain ⟨lhsValue, lhsLookup⟩ :=
            covered lhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          obtain ⟨rhsValue, rhsLookup⟩ :=
            covered rhs (by simp [Vars.Stmt.variablesRead, Vars.Expr.variablesRead])
          have lhsLookup' := Locals.lookup?_eq_some_of_lookup_eq_ok locals lhs lhsValue lhsLookup
          have rhsLookup' := Locals.lookup?_eq_some_of_lookup_eq_ok locals rhs rhsValue rhsLookup
          refine ⟨locals.assign result (Evm.UInt256.lt lhsValue rhsValue), ?_, ?_, ?_⟩
          · simp [evaluateSourceStatement, sourceStatementConcreteOperation, lhsLookup', rhsLookup']
          · exact fun identifier defined => Locals.defined_assign_of_defined defined
          · intro identifier member
            simp [Vars.Stmt.variablesDefined] at member
            subst identifier
            exact Locals.defined_assign locals result (Evm.UInt256.lt lhsValue rhsValue)
      | sload key => simp [Symbolic.operationOf] at supported
  | sstore => simp [Symbolic.operationOf] at supported
  | gas => simp [Symbolic.operationOf] at supported
  | call => simp [Symbolic.operationOf] at supported
  | malloc => simp [Symbolic.operationOf] at supported
  | mallocUninit => simp [Symbolic.operationOf] at supported
  | mstore32 => simp [Symbolic.operationOf] at supported
  | mload32 => simp [Symbolic.operationOf] at supported
  | icall => simp [Symbolic.operationOf] at supported

theorem evaluateSourceStatementList_exists (statements : List Vars.Stmt) (locals : Locals)
    (defined finalDefined : List VarId)
    (recorded : statements.foldlM Symbolic.recordDefinitions defined = some finalDefined)
    (supported : ∀ statement ∈ statements, ∃ symbolicOperation,
      Symbolic.operationOf statement = some symbolicOperation)
    (covered : locals.CoversVariables defined) :
    ∃ finalLocals,
      statements.foldlM evaluateSourceStatement locals = some finalLocals := by
  induction statements generalizing locals defined with
  | nil =>
      simp at recorded
      exact ⟨locals, rfl⟩
  | cons statement statements inductionHypothesis =>
      simp only [List.foldlM_cons] at recorded ⊢
      cases recordedStatement : Symbolic.recordDefinitions defined statement with
      | none => simp [recordedStatement] at recorded
      | some nextDefined =>
          rw [recordedStatement] at recorded
          have readsDefined : ∀ identifier ∈ statement.variablesRead, identifier ∈ defined := by
            unfold Symbolic.recordDefinitions at recordedStatement
            split at recordedStatement
            next accepted =>
              intro identifier member
              simpa using List.all_eq_true.mp accepted identifier member
            next rejected => simp at recordedStatement
          have nextDefinedEq : nextDefined = statement.variablesDefined ++ defined := by
            unfold Symbolic.recordDefinitions at recordedStatement
            split at recordedStatement
            next accepted => exact Option.some.inj recordedStatement.symm
            next rejected => simp at recordedStatement
          obtain ⟨nextLocals, evaluated, preserves, defines⟩ :=
            evaluateSourceStatement_exists_of_supported locals statement
              (supported statement (by simp))
              (fun identifier member => covered identifier (readsDefined identifier member))
          rw [evaluated]
          apply inductionHypothesis nextLocals nextDefined recorded
          · intro remaining member
            exact supported remaining (by simp [member])
          · rw [nextDefinedEq]
            exact Locals.coversVariables_append defines
              (fun identifier member => preserves identifier (covered identifier member))

theorem sourceOrderReferenceLocals_exists (sourceStatements : Array Vars.Stmt)
    (entryLayout : Array Symbolic.Value) (entryLocals : Locals)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (supported : ∀ statement ∈ sourceStatements, ∃ symbolicOperation,
      Symbolic.operationOf statement = some symbolicOperation)
    (entryCovered : entryLocals.CoversVariables
      (entryLayout.toList.map Symbolic.Value.identifier)) :
    ∃ referenceLocals,
      sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals := by
  unfold Symbolic.readsAvailable at usesAvailable
  cases recorded : sourceStatements.toList.foldlM Symbolic.recordDefinitions
      (entryLayout.toList.map Symbolic.Value.identifier) with
  | none => simp [recorded] at usesAvailable
  | some finalDefined =>
      apply evaluateSourceStatementList_exists sourceStatements.toList entryLocals
        (entryLayout.toList.map Symbolic.Value.identifier) finalDefined recorded
      · intro statement member
        exact supported statement (by simpa using member)
      · exact entryCovered

def Symbolic.State.AvailableVariablesAgree (state : Symbolic.State)
    (sourceStatements : Array Vars.Stmt) (locals referenceLocals : Locals) : Prop :=
  ∀ identifier, state.available sourceStatements identifier = true →
    locals.lookup? identifier = referenceLocals.lookup? identifier

def Symbolic.State.InterpretsReference (state : Symbolic.State)
    (sourceStatements : Array Vars.Stmt) (locals referenceLocals : Locals)
    (environment : Stack.Environment) : Prop :=
  state.Interprets locals environment ∧
    state.AvailableVariablesAgree sourceStatements locals referenceLocals

theorem Symbolic.State.AvailableVariablesAgree.refl (state : Symbolic.State)
    (sourceStatements : Array Vars.Stmt) (locals : Locals) :
    state.AvailableVariablesAgree sourceStatements locals locals := by
  intro identifier available
  rfl

theorem evaluateSourceStatement_eq_some (locals nextLocals : Locals) (statement : Vars.Stmt)
    (evaluated : evaluateSourceStatement locals statement = some nextLocals) :
    ∃ operation operands result resultValue,
      sourceStatementConcreteOperation locals statement =
        some (operation, operands, result, resultValue) ∧
      nextLocals = locals.assign result resultValue := by
  unfold evaluateSourceStatement at evaluated
  cases operationEq : sourceStatementConcreteOperation locals statement with
  | none => simp [operationEq] at evaluated
  | some concreteOperation =>
      obtain ⟨operation, operands, result, resultValue⟩ := concreteOperation
      rw [operationEq] at evaluated
      simp only [Option.some.injEq] at evaluated
      subst nextLocals
      exact ⟨operation, operands, result, resultValue, rfl, rfl⟩

theorem sourceStatementConcreteOperation_result_mem (locals : Locals) (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Word) (result : VarId)
    (resultValue : Word)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue)) :
    result ∈ statement.variablesDefined := by
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp [sourceStatementConcreteOperation] at concreteOperation
          simpa [Vars.Stmt.variablesDefined] using concreteOperation.2.2.1.symm
      | var source =>
          cases sourceValueEq : locals.lookup? source with
          | none => simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
          | some sourceValue =>
              simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
              simpa [Vars.Stmt.variablesDefined] using concreteOperation.2.2.1.symm
      | add lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  simpa [Vars.Stmt.variablesDefined] using concreteOperation.2.2.1.symm
      | lt lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  simpa [Vars.Stmt.variablesDefined] using concreteOperation.2.2.1.symm
      | sload key => simp [sourceStatementConcreteOperation] at concreteOperation
  | sstore => simp [sourceStatementConcreteOperation] at concreteOperation
  | gas => simp [sourceStatementConcreteOperation] at concreteOperation
  | call => simp [sourceStatementConcreteOperation] at concreteOperation
  | malloc => simp [sourceStatementConcreteOperation] at concreteOperation
  | mallocUninit => simp [sourceStatementConcreteOperation] at concreteOperation
  | mstore32 => simp [sourceStatementConcreteOperation] at concreteOperation
  | mload32 => simp [sourceStatementConcreteOperation] at concreteOperation
  | icall => simp [sourceStatementConcreteOperation] at concreteOperation

theorem sourceStatementConcreteOperation_defined_eq_result (locals : Locals) (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Word) (result identifier : VarId)
    (resultValue : Word)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue))
    (defined : identifier ∈ statement.variablesDefined) :
    identifier = result := by
  cases statement with
  | assign assigned expression =>
      simp only [Vars.Stmt.variablesDefined, List.mem_singleton] at defined
      subst identifier
      cases expression with
      | constant value =>
          simp [sourceStatementConcreteOperation] at concreteOperation
          exact concreteOperation.2.2.1
      | var source =>
          cases sourceValueEq : locals.lookup? source with
          | none => simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
          | some sourceValue =>
              simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
              exact concreteOperation.2.2.1
      | add lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  exact concreteOperation.2.2.1
      | lt lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  exact concreteOperation.2.2.1
      | sload key => simp [sourceStatementConcreteOperation] at concreteOperation
  | sstore => simp [Vars.Stmt.variablesDefined] at defined
  | gas => simp [sourceStatementConcreteOperation] at concreteOperation
  | call => simp [sourceStatementConcreteOperation] at concreteOperation
  | malloc => simp [sourceStatementConcreteOperation] at concreteOperation
  | mallocUninit => simp [sourceStatementConcreteOperation] at concreteOperation
  | mstore32 => simp [Vars.Stmt.variablesDefined] at defined
  | mload32 => simp [sourceStatementConcreteOperation] at concreteOperation
  | icall => simp [sourceStatementConcreteOperation] at concreteOperation

theorem evaluateSourceStatement_lookup?_eq_of_not_mem (locals nextLocals : Locals)
    (statement : Vars.Stmt) (identifier : VarId)
    (evaluated : evaluateSourceStatement locals statement = some nextLocals)
    (absent : identifier ∉ statement.variablesDefined) :
    nextLocals.lookup? identifier = locals.lookup? identifier := by
  obtain ⟨operation, operands, result, resultValue, concreteOperation, rfl⟩ :=
    evaluateSourceStatement_eq_some locals nextLocals statement evaluated
  have different : identifier ≠ result := by
    intro equal
    subst identifier
    exact absent (sourceStatementConcreteOperation_result_mem locals statement operation
      operands result resultValue concreteOperation)
  simp [Locals.lookup?, Locals.assign, different]

theorem evaluateSourceStatementList_lookup?_eq_of_not_mem (statements : List Vars.Stmt)
    (locals finalLocals : Locals) (identifier : VarId)
    (evaluated : statements.foldlM evaluateSourceStatement locals = some finalLocals)
    (absent : identifier ∉ statements.flatMap Vars.Stmt.variablesDefined) :
    finalLocals.lookup? identifier = locals.lookup? identifier := by
  induction statements generalizing locals with
  | nil =>
      simp at evaluated
      subst finalLocals
      rfl
  | cons statement statements inductionHypothesis =>
      simp only [List.foldlM_cons] at evaluated
      cases nextEq : evaluateSourceStatement locals statement with
      | none => simp [nextEq] at evaluated
      | some nextLocals =>
          rw [nextEq] at evaluated
          simp only [List.flatMap_cons, List.mem_append, not_or] at absent
          exact (inductionHypothesis nextLocals evaluated absent.2).trans
            (evaluateSourceStatement_lookup?_eq_of_not_mem locals nextLocals statement
              identifier nextEq absent.1)

theorem evaluateSourceStatementList_result_at (statements : List Vars.Stmt)
    (locals finalLocals : Locals) (index : Nat) (statement : Vars.Stmt)
    (evaluated : statements.foldlM evaluateSourceStatement locals = some finalLocals)
    (definitionsNodup : (statements.flatMap Vars.Stmt.variablesDefined).Nodup)
    (statementAt : statements[index]? = some statement) :
    ∃ statementLocals operation operands result resultValue,
      sourceStatementConcreteOperation statementLocals statement =
          some (operation, operands, result, resultValue) ∧
        finalLocals.lookup? result = some resultValue := by
  induction statements generalizing locals index with
  | nil => simp at statementAt
  | cons head statements inductionHypothesis =>
      simp only [List.foldlM_cons] at evaluated
      cases nextEq : evaluateSourceStatement locals head with
      | none => simp [nextEq] at evaluated
      | some nextLocals =>
          rw [nextEq] at evaluated
          cases index with
          | zero =>
              simp at statementAt
              subst head
              obtain ⟨operation, operands, result, resultValue, concreteOperation, rfl⟩ :=
                evaluateSourceStatement_eq_some locals nextLocals statement nextEq
              refine ⟨locals, operation, operands, result, resultValue, concreteOperation, ?_⟩
              have resultDefined : result ∈ statement.variablesDefined :=
                sourceStatementConcreteOperation_result_mem locals statement operation operands
                  result resultValue concreteOperation
              have resultAbsent : result ∉ statements.flatMap Vars.Stmt.variablesDefined := by
                intro resultInRemaining
                exact (List.nodup_append.mp definitionsNodup).2.2 result resultDefined result
                  resultInRemaining rfl
              rw [evaluateSourceStatementList_lookup?_eq_of_not_mem statements
                (locals.assign result resultValue) finalLocals result evaluated resultAbsent]
              simp [Locals.lookup?, Locals.assign]
          | succ index =>
              simp only [List.getElem?_cons_succ] at statementAt
              exact inductionHypothesis nextLocals index evaluated
                (List.nodup_append.mp definitionsNodup).2.1 statementAt

theorem evaluateSourceStatementList_operation_at (statements : List Vars.Stmt)
    (defined finalDefined : List VarId) (locals finalLocals : Locals)
    (recorded : statements.foldlM Symbolic.recordDefinitions defined = some finalDefined)
    (evaluated : statements.foldlM evaluateSourceStatement locals = some finalLocals)
    (variablesUnique : (defined ++ statements.flatMap Vars.Stmt.variablesDefined).Nodup)
    (index : Nat) (statement : Vars.Stmt) (statementAt : statements[index]? = some statement) :
    ∃ operation operands result resultValue,
      sourceStatementConcreteOperation finalLocals statement =
          some (operation, operands, result, resultValue) ∧
        finalLocals.lookup? result = some resultValue := by
  induction statements generalizing defined finalDefined locals index with
  | nil => simp at statementAt
  | cons head statements inductionHypothesis =>
      simp only [List.foldlM_cons] at recorded evaluated
      cases recordedHead : Symbolic.recordDefinitions defined head with
      | none => simp [recordedHead] at recorded
      | some nextDefined =>
          rw [recordedHead] at recorded
          cases evaluatedHead : evaluateSourceStatement locals head with
          | none => simp [evaluatedHead] at evaluated
          | some nextLocals =>
              rw [evaluatedHead] at evaluated
              have readsDefined : ∀ identifier ∈ head.variablesRead, identifier ∈ defined := by
                unfold Symbolic.recordDefinitions at recordedHead
                split at recordedHead
                next accepted =>
                  intro identifier member
                  simpa using List.all_eq_true.mp accepted identifier member
                next rejected => simp at recordedHead
              have nextDefinedEq : nextDefined = head.variablesDefined ++ defined := by
                unfold Symbolic.recordDefinitions at recordedHead
                split at recordedHead
                next accepted => exact Option.some.inj recordedHead.symm
                next rejected => simp at recordedHead
              cases index with
              | zero =>
                  simp at statementAt
                  subst head
                  obtain ⟨operation, operands, result, resultValue, concreteOperation, rfl⟩ :=
                    evaluateSourceStatement_eq_some locals nextLocals statement evaluatedHead
                  have allEvaluated :
                      (statement :: statements).foldlM evaluateSourceStatement locals =
                        some finalLocals := by
                    simp [evaluatedHead, evaluated]
                  have readsAgree : ∀ identifier ∈ statement.variablesRead,
                      locals.lookup? identifier = finalLocals.lookup? identifier := by
                    intro identifier member
                    apply Eq.symm
                    apply evaluateSourceStatementList_lookup?_eq_of_not_mem
                      (statement :: statements) locals finalLocals identifier allEvaluated
                    intro definedByStatement
                    exact (List.nodup_append.mp variablesUnique).2.2 identifier
                      (readsDefined identifier member) identifier definedByStatement rfl
                  have finalOperation :
                      sourceStatementConcreteOperation finalLocals statement =
                        some (operation, operands, result, resultValue) := by
                    rw [← sourceStatementConcreteOperation_eq_of_variablesRead_eq
                      locals finalLocals statement readsAgree]
                    exact concreteOperation
                  have resultDefined : result ∈ statement.variablesDefined :=
                    sourceStatementConcreteOperation_result_mem locals statement operation operands
                      result resultValue concreteOperation
                  have resultAbsent : result ∉ statements.flatMap Vars.Stmt.variablesDefined := by
                    intro resultInRemaining
                    have definitionsNodup :
                        ((defined ++ statement.variablesDefined) ++
                          statements.flatMap Vars.Stmt.variablesDefined).Nodup := by
                      simpa [List.append_assoc] using variablesUnique
                    exact (List.nodup_append.mp definitionsNodup).2.2 result
                      (by simp [resultDefined]) result resultInRemaining rfl
                  refine ⟨operation, operands, result, resultValue, finalOperation, ?_⟩
                  rw [evaluateSourceStatementList_lookup?_eq_of_not_mem statements
                    (locals.assign result resultValue) finalLocals result evaluated resultAbsent]
                  simp [Locals.lookup?, Locals.assign]
              | succ index =>
                  simp only [List.getElem?_cons_succ] at statementAt
                  have nextVariablesUnique :
                      (nextDefined ++ statements.flatMap Vars.Stmt.variablesDefined).Nodup := by
                    rw [nextDefinedEq]
                    have unique :
                        ((defined ++ head.variablesDefined) ++
                          statements.flatMap Vars.Stmt.variablesDefined).Nodup := by
                      simpa [List.append_assoc] using variablesUnique
                    exact (List.Perm.append_right (statements.flatMap Vars.Stmt.variablesDefined)
                      (List.perm_append_comm (l₁ := defined)
                        (l₂ := head.variablesDefined))).nodup unique
                  exact inductionHypothesis nextDefined finalDefined nextLocals recorded evaluated
                    nextVariablesUnique index statementAt

theorem sourceOrderReferenceLocals_operation_at (sourceStatements : Array Vars.Stmt)
    (entryLayout : Array Symbolic.Value) (entryLocals referenceLocals : Locals)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (index : Nat) (statement : Vars.Stmt) (statementAt : sourceStatements[index]? = some statement) :
    ∃ operation operands result resultValue,
      sourceStatementConcreteOperation referenceLocals statement =
          some (operation, operands, result, resultValue) ∧
        referenceLocals.lookup? result = some resultValue := by
  unfold Symbolic.readsAvailable at usesAvailable
  cases recorded : sourceStatements.toList.foldlM Symbolic.recordDefinitions
      (entryLayout.toList.map Symbolic.Value.identifier) with
  | none => simp [recorded] at usesAvailable
  | some finalDefined =>
      apply evaluateSourceStatementList_operation_at sourceStatements.toList
        (entryLayout.toList.map Symbolic.Value.identifier) finalDefined entryLocals referenceLocals
        recorded evaluated
      · simpa [Symbolic.definesOnce] using variablesUnique
      · simpa only [Array.getElem?_toList] using statementAt

theorem sourceOrderReferenceLocals_preserves_entry (sourceStatements : Array Vars.Stmt)
    (entryLayout : Array Symbolic.Value) (entryLocals referenceLocals : Locals)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (identifier : VarId)
    (entry : identifier ∈ entryLayout.toList.map Symbolic.Value.identifier) :
    referenceLocals.lookup? identifier = entryLocals.lookup? identifier := by
  apply evaluateSourceStatementList_lookup?_eq_of_not_mem sourceStatements.toList
    entryLocals referenceLocals identifier
  · exact evaluated
  · simp only [Symbolic.definesOnce, decide_eq_true_eq] at variablesUnique
    intro defined
    exact (List.nodup_append.mp variablesUnique).2.2 identifier entry identifier defined rfl

theorem Symbolic.State.firstFireable_eq_some
    (state : Symbolic.State) (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation) (statement : Vars.Stmt) (statementIndex : Nat)
    (found : state.firstFireable sourceStatements operation =
      some (statement, statementIndex)) :
    sourceStatements[statementIndex]? = some statement ∧
      state.fireable sourceStatements operation (statement, statementIndex) = true := by
  have member := List.mem_of_find?_eq_some found
  have fires := List.find?_some found
  have zipped := List.mem_zipIdx member
  refine ⟨?_, fires⟩
  obtain ⟨_, bound, statementEq⟩ := zipped
  apply Array.getElem?_eq_some_iff.mpr
  refine ⟨by simpa using bound, ?_⟩
  simpa using statementEq.symm

theorem Symbolic.State.firstFireable_eq_of_prior_fired
    (state : Symbolic.State) (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation) (statement : Vars.Stmt) (statementIndex : Nat)
    (statementAt : sourceStatements[statementIndex]? = some statement)
    (canFire : state.fireable sourceStatements operation
      (statement, statementIndex) = true)
    (priorFired : ∀ index < statementIndex, index ∈ state.firedStatementIndices) :
    state.firstFireable sourceStatements operation =
      some (statement, statementIndex) := by
  unfold Symbolic.State.firstFireable
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨canFire, statementIndex, ?_, ?_, ?_⟩
  · have bound := (Array.getElem?_eq_some_iff.mp statementAt).1
    simpa using bound
  · have statementAtList : sourceStatements.toList[statementIndex]? = some statement := by
      simpa only [Array.getElem?_toList] using statementAt
    have statementEq := (List.getElem?_eq_some_iff.mp statementAtList).2
    simp [List.getElem_zipIdx, statementEq]
  · intro index indexBound
    have statementBound : statementIndex < sourceStatements.size :=
      (Array.getElem?_eq_some_iff.mp statementAt).1
    have indexSourceBound : index < sourceStatements.toList.length := by
      simpa using Nat.lt_trans indexBound statementBound
    simp only [List.getElem_zipIdx]
    unfold Symbolic.State.fireable
    split <;> simp [priorFired index indexBound]

theorem Symbolic.State.AvailableVariablesAgree.after_checker_fire
    (state : Symbolic.State) (sourceStatements : Array Vars.Stmt)
    (entryLayout : Array Symbolic.Value) (entryLocals locals referenceLocals : Locals)
    (usesAvailable : Symbolic.readsAvailable sourceStatements entryLayout = true)
    (variablesUnique : Symbolic.definesOnce sourceStatements entryLayout = true)
    (evaluated : sourceOrderReferenceLocals sourceStatements entryLocals = some referenceLocals)
    (agrees : state.AvailableVariablesAgree sourceStatements locals referenceLocals)
    (statement : Vars.Stmt) (statementIndex : Nat) (operation : Machine.Operation)
    (operands : List Word) (result : VarId) (resultValue : Word)
    (statementAt : sourceStatements[statementIndex]? = some statement)
    (canFire : state.fireable sourceStatements operation
      (statement, statementIndex) = true)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue)) :
    referenceLocals.lookup? result = some resultValue ∧
      Symbolic.State.AvailableVariablesAgree
        { state with firedStatementIndices := statementIndex :: state.firedStatementIndices }
        sourceStatements (locals.assign result resultValue) referenceLocals := by
  cases symbolicOperationEq : Symbolic.operationOf statement with
  | none =>
      simp [Symbolic.State.fireable, symbolicOperationEq] at canFire
  | some symbolicOperation =>
      obtain ⟨expectedOperation, symbolicOperands, symbolicResult⟩ := symbolicOperation
      simp only [Symbolic.State.fireable, symbolicOperationEq,
        decide_eq_true_eq] at canFire
      have readsAgree : ∀ identifier ∈ statement.variablesRead,
          locals.lookup? identifier = referenceLocals.lookup? identifier := by
        intro identifier member
        apply agrees identifier
        exact List.all_eq_true.mp canFire.2.2.2.2.2 identifier member
      obtain ⟨referenceOperation, referenceOperands, referenceResult, referenceResultValue,
          referenceConcreteOperation, referenceResultLookup⟩ :=
        sourceOrderReferenceLocals_operation_at sourceStatements entryLayout entryLocals
          referenceLocals usesAvailable variablesUnique evaluated statementIndex statement
          statementAt
      have operationsAgree := sourceStatementConcreteOperation_eq_of_variablesRead_eq
        locals referenceLocals statement readsAgree
      rw [concreteOperation, referenceConcreteOperation] at operationsAgree
      simp only [Option.some.injEq, Prod.mk.injEq] at operationsAgree
      rcases operationsAgree with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨referenceResultLookup, ?_⟩
      intro identifier available
      by_cases identifierEq : identifier = result
      · subst identifier
        rw [referenceResultLookup]
        simp [Locals.lookup?, Locals.assign]
      · have notDefined : identifier ∉ statement.variablesDefined := by
          intro defined
          exact identifierEq (sourceStatementConcreteOperation_defined_eq_result locals statement
            operation operands result identifier resultValue concreteOperation defined)
        have newNotDefined :
            Symbolic.definesVariable sourceStatements identifier statementIndex = false := by
          simp [Symbolic.definesVariable, statementAt, notDefined]
        have previouslyAvailable : state.available sourceStatements identifier = true := by
          simpa [Symbolic.State.available, newNotDefined] using available
        simpa [Locals.lookup?, Locals.assign, identifierEq] using
          agrees identifier previouslyAvailable

theorem Symbolic.State.Interprets.replay_operation (sourceStatements : Array Vars.Stmt)
    (state nextState : Symbolic.State) (locals : Locals)
    (environment : Stack.Environment) (interprets : state.Interprets locals environment)
    (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.op operation) = some nextState) :
    ∃ (statementIndex : Nat) (statement : Vars.Stmt)
        (symbolicOperands : List Symbolic.Value) (operands : List Word)
        (result : VarId) (resultValue : Word),
      sourceStatements[statementIndex]? = some statement ∧
        Symbolic.operationOf statement =
          some (operation, symbolicOperands, .variable result) ∧
        state.fireable sourceStatements operation (statement, statementIndex) = true ∧
        sourceStatementConcreteOperation locals statement =
          some (operation, operands, result, resultValue) ∧
        environment.stack.take operation.inputCount = operands ∧
        nextState = { state with
          stack := .variable result :: state.stack.drop symbolicOperands.length
          firedStatementIndices := statementIndex :: state.firedStatementIndices } ∧
        nextState.Interprets (locals.assign result resultValue)
          { environment with
            stack := resultValue :: environment.stack.drop operation.inputCount } := by
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
          have canFire' := canFire
          simp only [Symbolic.State.fireable, symbolicOperationEq,
            decide_eq_true_eq] at canFire'
          obtain ⟨notFired, operationEq, stackBound, stackPrefix, resultAbsent,
            readsAvailable⟩ := canFire'
          subst expectedOperation
          obtain ⟨result, rfl⟩ := Symbolic.operationOf_result_variable statement
            operation symbolicOperands symbolicResult symbolicOperationEq
          simp [foundEq, symbolicOperationEq] at replay
          subst nextState
          have operandLength := Symbolic.operationOf_operand_length statement operation
            symbolicOperands (.variable result) symbolicOperationEq
          have interpretations := Symbolic.Value.interpret_take locals state.stack
            environment.stack interprets.1 symbolicOperands.length
          rw [stackPrefix] at interpretations
          obtain ⟨resultValue, concreteOperation⟩ :=
            sourceStatementConcreteOperation_of_symbolic locals statement operation
              symbolicOperands result (environment.stack.take symbolicOperands.length)
              symbolicOperationEq interpretations
          refine ⟨statementIndex, statement, symbolicOperands,
            environment.stack.take symbolicOperands.length, result, resultValue, statementAt,
            symbolicOperationEq, canFire, concreteOperation, ?_, rfl, ?_⟩
          · rw [← operandLength]
          · rw [← operandLength]
            exact Symbolic.State.Interprets.after_fire state _ locals environment interprets
              symbolicOperands statementIndex result resultValue resultAbsent rfl

theorem Stack.exchange_zero_one (environment : Stack.Environment)
    (stack : List Word) (exchange : Stack.exchange environment.stack 0 1 = some stack) :
    Stack.sourceFetch environment .reversedPair = .ok (stack.take 2).toArray ∧
      stack.drop 2 = environment.stack.drop 2 := by
  cases environmentStackEq : environment.stack with
  | nil => simp [Stack.exchange, environmentStackEq] at exchange
  | cons first tail =>
      cases tail with
      | nil => simp [Stack.exchange, environmentStackEq] at exchange
      | cons second rest =>
          simp [Stack.exchange, environmentStackEq] at exchange
          subst stack
          simp [Stack.sourceFetch, environmentStackEq]

theorem Symbolic.State.Interprets.replay_flipped_operation
    (sourceStatements : Array Vars.Stmt) (state nextState : Symbolic.State)
    (locals : Locals) (environment : Stack.Environment)
    (interprets : state.Interprets locals environment) (operation : Machine.Operation)
    (replay : Symbolic.execute sourceStatements state (.flippedOp operation) =
      some nextState) :
    ∃ (statementIndex : Nat) (statement : Vars.Stmt)
        (symbolicOperands : List Symbolic.Value) (operands : List Word)
        (result : VarId) (resultValue : Word) (flippedStack : List Symbolic.Value)
        (flippedState : Symbolic.State),
      operation.inputCount = 2 ∧
        sourceStatements[statementIndex]? = some statement ∧
        Symbolic.operationOf statement =
          some (operation, symbolicOperands, .variable result) ∧
        flippedState.fireable sourceStatements operation
          (statement, statementIndex) = true ∧
        sourceStatementConcreteOperation locals statement =
          some (operation, operands, result, resultValue) ∧
        Stack.sourceFetch environment .reversedPair = .ok operands.toArray ∧
        flippedState = { state with stack := flippedStack } ∧
        nextState = { flippedState with
          stack := .variable result :: flippedState.stack.drop symbolicOperands.length
          firedStatementIndices := statementIndex :: flippedState.firedStatementIndices } ∧
        nextState.Interprets (locals.assign result resultValue)
          { environment with stack := resultValue :: environment.stack.drop 2 } := by
  simp only [Symbolic.execute] at replay
  by_cases binary : operation.inputCount = 2
  · rw [if_pos binary] at replay
    cases symbolicExchange : Symbolic.exchange state.stack 0 1 with
    | none => simp [symbolicExchange] at replay
    | some symbolicStack =>
        rw [symbolicExchange] at replay
        let flippedState : Symbolic.State := { state with stack := symbolicStack }
        have exchangeReplay : Symbolic.execute sourceStatements state (.exchange 0 1) =
            some flippedState := by
          simp [Symbolic.execute, symbolicExchange, flippedState]
        obtain ⟨concreteStack, concreteExchange, flippedInterprets⟩ :=
          interprets.replay_exchange sourceStatements state flippedState locals environment 0 1
            exchangeReplay
        obtain ⟨statementIndex, statement, symbolicOperands, operands, result, resultValue,
            statementAt, symbolicOperation, canFire, concreteOperation, stackPrefix, nextStateEq,
            nextInterprets⟩ :=
          flippedInterprets.replay_operation sourceStatements flippedState nextState locals
            { environment with stack := concreteStack } operation replay
        obtain ⟨fetch, dropEq⟩ :=
          Stack.exchange_zero_one environment concreteStack concreteExchange
        have flippedFetch : Stack.sourceFetch environment .reversedPair =
            .ok operands.toArray := by
          rw [fetch]
          rw [binary] at stackPrefix
          simpa using congrArg List.toArray stackPrefix
        refine ⟨statementIndex, statement, symbolicOperands, operands, result, resultValue,
          symbolicStack, flippedState, binary, statementAt, symbolicOperation, canFire,
          concreteOperation,
          flippedFetch, ?_, nextStateEq, ?_⟩
        · simp [flippedState]
        · simpa [binary, dropEq] using nextInterprets
  · rw [if_neg binary] at replay
    simp at replay

theorem sourceStatementConcreteOperation_source_step {sourceProgram : Vars.Program}
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (sourceControl sourceNext : Machine.MachineControl) (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Word) (result : VarId)
    (resultValue : Word)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue))
    (sourceDecode : sourceProgram.decodeStmt sourceControl = some (sourceNext, statement)) :
    Machine.Step Vars.frame (Vars.decoder sourceProgram) Machine.memoryPolicy ctx
      (⟨globals, locals, sourceControl⟩ : Vars.State) []
      (⟨globals, locals.assign result resultValue, sourceNext⟩ : Vars.State) := by
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp only [sourceStatementConcreteOperation, Option.some.injEq, Prod.mk.injEq]
            at concreteOperation
          rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
          apply Sir.step_assign sourceDecode
          exact fires_of (by
            change (#[] : Array VarId).mapM (locals.lookup ·) = .ok #[]
            rw [Array.mapM_eq_mapM_toList]
            rfl) (by trivial)
            (Machine.Operation.execute_constant_ok ctx value globals #[])
            (by simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]; rfl)
      | var source =>
          cases sourceValueEq : locals.lookup? source with
          | none => simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
          | some sourceValue =>
              simp only [sourceStatementConcreteOperation, sourceValueEq, Option.map_some,
                Option.some.injEq, Prod.mk.injEq] at concreteOperation
              rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
              apply Sir.step_assign sourceDecode
              exact fires_of (by
                change #[source].mapM (locals.lookup ·) = .ok #[sourceValue]
                rw [Array.mapM_eq_mapM_toList]
                simp [Locals.lookup, sourceValueEq]) (by trivial)
                (Machine.Operation.execute_copy_ok ctx sourceValue globals)
                (by simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]; rfl)
      | add lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  apply Sir.step_assign sourceDecode
                  exact fires_of (by
                    change #[lhs, rhs].mapM (locals.lookup ·) = .ok #[lhsValue, rhsValue]
                    rw [Array.mapM_eq_mapM_toList]
                    simp [Locals.lookup, lhsValueEq, rhsValueEq, bind, Except.bind, pure,
                      Except.pure]) (by trivial)
                    (Machine.Operation.execute_add_ok ctx lhsValue rhsValue globals)
                    (by simp only [Locals.bindValues, ← Array.forIn_toList,
                      Array.toList_zip]; rfl)
      | lt lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  apply Sir.step_assign sourceDecode
                  exact fires_of (by
                    change #[lhs, rhs].mapM (locals.lookup ·) = .ok #[lhsValue, rhsValue]
                    rw [Array.mapM_eq_mapM_toList]
                    simp [Locals.lookup, lhsValueEq, rhsValueEq, bind, Except.bind, pure,
                      Except.pure]) (by trivial)
                    (Machine.Operation.execute_lt_ok ctx lhsValue rhsValue globals)
                    (by simp only [Locals.bindValues, ← Array.forIn_toList,
                      Array.toList_zip]; rfl)
      | sload key => simp [sourceStatementConcreteOperation] at concreteOperation
  | sstore key value => simp [sourceStatementConcreteOperation] at concreteOperation
  | gas result => simp [sourceStatementConcreteOperation] at concreteOperation
  | call call => simp [sourceStatementConcreteOperation] at concreteOperation
  | malloc result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mallocUninit result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mstore32 offset value => simp [sourceStatementConcreteOperation] at concreteOperation
  | mload32 result offset => simp [sourceStatementConcreteOperation] at concreteOperation
  | icall callee arguments destinations => simp [sourceStatementConcreteOperation]
      at concreteOperation

theorem sourceStatementConcreteOperation_flipped_target_step
    {targetProgram : Stack.Program} (ctx : CallContext) (globals : Globals)
    (locals : Locals) (environment : Stack.Environment)
    (targetControl targetNext : Machine.MachineControl) (statement : Vars.Stmt)
    (operation : Machine.Operation) (operands : List Word) (result : VarId)
    (resultValue : Word)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue))
    (binary : operation.inputCount = 2)
    (fetch : Stack.sourceFetch environment .reversedPair = .ok operands.toArray)
    (targetDecode : targetProgram.decodeInstruction targetControl =
      some (targetNext, .flippedOp operation)) :
    Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
      ⟨globals, environment, targetControl⟩ []
      ⟨globals, { environment with
        stack := resultValue :: environment.stack.drop 2 }, targetNext⟩ := by
  have stackShape : ∃ first second rest, environment.stack = first :: second :: rest := by
    cases stackEq : environment.stack with
    | nil => simp [Stack.sourceFetch, stackEq] at fetch
    | cons first rest =>
        cases rest with
        | nil => simp [Stack.sourceFetch, stackEq] at fetch
        | cons second rest => exact ⟨first, second, rest, rfl⟩
  obtain ⟨first, second, rest, stackEq⟩ := stackShape
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp only [sourceStatementConcreteOperation, Option.some.injEq, Prod.mk.injEq]
            at concreteOperation
          rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
          simp [Machine.Operation.inputCount] at binary
      | var source =>
          cases sourceValueEq : locals.lookup? source with
          | none => simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
          | some sourceValue =>
              simp only [sourceStatementConcreteOperation, sourceValueEq, Option.map_some,
                Option.some.injEq, Prod.mk.injEq] at concreteOperation
              rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
              simp [Machine.Operation.inputCount] at binary
      | add lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  apply Machine.Step.operation (frame := Stack.frame)
                    (operation := .add) (src := .reversedPair) (dst := ⟨2, 1⟩)
                    (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode])
                  exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial)
                    (by simpa [Stack.frame] using fetch)
                    (Machine.Operation.execute_add_ok ctx lhsValue rhsValue globals)
                    (by simp [Stack.frame, Stack.store, stackEq])
      | lt lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  apply Machine.Step.operation (frame := Stack.frame)
                    (operation := .lt) (src := .reversedPair) (dst := ⟨2, 1⟩)
                    (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode])
                  exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial)
                    (by simpa [Stack.frame] using fetch)
                    (Machine.Operation.execute_lt_ok ctx lhsValue rhsValue globals)
                    (by simp [Stack.frame, Stack.store, stackEq])
      | sload key => simp [sourceStatementConcreteOperation] at concreteOperation
  | sstore key value => simp [sourceStatementConcreteOperation] at concreteOperation
  | gas result => simp [sourceStatementConcreteOperation] at concreteOperation
  | call call => simp [sourceStatementConcreteOperation] at concreteOperation
  | malloc result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mallocUninit result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mstore32 offset value => simp [sourceStatementConcreteOperation] at concreteOperation
  | mload32 result offset => simp [sourceStatementConcreteOperation] at concreteOperation
  | icall callee arguments destinations => simp [sourceStatementConcreteOperation]
      at concreteOperation

theorem sourceStatementConcreteOperation_steps {sourceProgram : Vars.Program}
    {targetProgram : Stack.Program} (ctx : CallContext) (globals : Globals)
    (locals : Locals) (environment : Stack.Environment)
    (sourceControl sourceNext targetControl targetNext : Machine.MachineControl)
    (statement : Vars.Stmt) (operation : Machine.Operation) (operands : List Word)
    (result : VarId) (resultValue : Word)
    (concreteOperation : sourceStatementConcreteOperation locals statement =
      some (operation, operands, result, resultValue))
    (stackPrefix : environment.stack.take operation.inputCount = operands)
    (sourceDecode : sourceProgram.decodeStmt sourceControl = some (sourceNext, statement))
    (targetDecode : targetProgram.decodeInstruction targetControl =
      some (targetNext, .op operation)) :
    Machine.Step Vars.frame (Vars.decoder sourceProgram) Machine.memoryPolicy ctx
        (⟨globals, locals, sourceControl⟩ : Vars.State) []
        (⟨globals, locals.assign result resultValue, sourceNext⟩ : Vars.State) ∧
      Machine.Step Stack.frame (Stack.decoder targetProgram) Machine.memoryPolicy ctx
        ⟨globals, environment, targetControl⟩ []
        ⟨globals,
          { environment with
            stack := resultValue :: environment.stack.drop operation.inputCount }, targetNext⟩ := by
  cases statement with
  | assign assigned expression =>
      cases expression with
      | constant value =>
          simp only [sourceStatementConcreteOperation, Option.some.injEq, Prod.mk.injEq]
            at concreteOperation
          rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
          constructor
          · apply Sir.step_assign sourceDecode
            exact fires_of (by
              change (#[] : Array VarId).mapM (locals.lookup ·) = .ok #[]
              rw [Array.mapM_eq_mapM_toList]
              rfl) (by trivial)
              (Machine.Operation.execute_constant_ok ctx value globals #[])
              (by simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]; rfl)
          · apply Machine.Step.operation (frame := Stack.frame)
              (operation := .constant value) (src := .inOrder 0) (dst := ⟨0, 1⟩)
              (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode,
                Machine.Operation.inputCount, Machine.Operation.outputCount])
            exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial) rfl
              (Machine.Operation.execute_constant_ok ctx value globals #[])
              (by simp [Stack.frame, Stack.store,
                Machine.Operation.inputCount])
      | var source =>
          cases sourceValueEq : locals.lookup? source with
          | none => simp [sourceStatementConcreteOperation, sourceValueEq] at concreteOperation
          | some sourceValue =>
              simp only [sourceStatementConcreteOperation, sourceValueEq, Option.map_some,
                Option.some.injEq, Prod.mk.injEq] at concreteOperation
              rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
              have stackPrefix' : environment.stack.take 1 = [sourceValue] := by
                simpa [Machine.Operation.inputCount] using stackPrefix
              have stackEq : environment.stack = sourceValue :: environment.stack.drop 1 := by
                calc
                  environment.stack = environment.stack.take 1 ++ environment.stack.drop 1 :=
                    (List.take_append_drop 1 environment.stack).symm
                  _ = [sourceValue] ++ environment.stack.drop 1 := by rw [stackPrefix']
                  _ = sourceValue :: environment.stack.drop 1 := rfl
              constructor
              · apply Sir.step_assign sourceDecode
                exact fires_of (by
                  change #[source].mapM (locals.lookup ·) = .ok #[sourceValue]
                  rw [Array.mapM_eq_mapM_toList]
                  simp [Locals.lookup, sourceValueEq]) (by trivial)
                  (Machine.Operation.execute_copy_ok ctx sourceValue globals)
                  (by simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]; rfl)
              · apply Machine.Step.operation (frame := Stack.frame)
                    (operation := .copy) (src := .inOrder 1) (dst := ⟨1, 1⟩)
                    (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode,
                      Machine.Operation.inputCount, Machine.Operation.outputCount])
                exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial)
                  (by
                    change Stack.fetch environment 1 = .ok #[sourceValue]
                    rw [Stack.fetch, if_pos (by rw [stackEq]; simp), stackPrefix'])
                  (Machine.Operation.execute_copy_ok ctx sourceValue globals)
                  (by
                    change Stack.store environment ⟨1, 1⟩ #[sourceValue] = .ok _
                    rw [Stack.store, if_pos (by rw [stackEq]; simp)]
                    simp [Machine.Operation.inputCount])
      | add lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  have stackPrefix' : environment.stack.take 2 = [lhsValue, rhsValue] := by
                    simpa [Machine.Operation.inputCount] using stackPrefix
                  have stackEq : environment.stack =
                      lhsValue :: rhsValue :: environment.stack.drop 2 := by
                    calc
                      environment.stack = environment.stack.take 2 ++ environment.stack.drop 2 :=
                        (List.take_append_drop 2 environment.stack).symm
                      _ = [lhsValue, rhsValue] ++ environment.stack.drop 2 := by rw [stackPrefix']
                      _ = lhsValue :: rhsValue :: environment.stack.drop 2 := rfl
                  constructor
                  · apply Sir.step_assign sourceDecode
                    exact fires_of (by
                      change #[lhs, rhs].mapM (locals.lookup ·) = .ok #[lhsValue, rhsValue]
                      rw [Array.mapM_eq_mapM_toList]
                      simp [Locals.lookup, lhsValueEq, rhsValueEq, bind, Except.bind, pure,
                        Except.pure]) (by trivial)
                      (Machine.Operation.execute_add_ok ctx lhsValue rhsValue globals)
                      (by simp only [Locals.bindValues, ← Array.forIn_toList,
                        Array.toList_zip]; rfl)
                  · apply Machine.Step.operation (frame := Stack.frame)
                        (operation := .add) (src := .inOrder 2) (dst := ⟨2, 1⟩)
                        (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode,
                          Machine.Operation.inputCount, Machine.Operation.outputCount])
                    exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial)
                      (by
                        change Stack.fetch environment 2 = .ok #[lhsValue, rhsValue]
                        rw [Stack.fetch, if_pos (by rw [stackEq]; simp), stackPrefix'])
                      (Machine.Operation.execute_add_ok ctx lhsValue rhsValue globals)
                      (by
                        change Stack.store environment ⟨2, 1⟩
                          #[Evm.UInt256.add lhsValue rhsValue] = .ok _
                        rw [Stack.store, if_pos (by rw [stackEq]; simp)]
                        simp [Machine.Operation.inputCount])
      | lt lhs rhs =>
          cases lhsValueEq : locals.lookup? lhs with
          | none => simp [sourceStatementConcreteOperation, lhsValueEq] at concreteOperation
          | some lhsValue =>
              cases rhsValueEq : locals.lookup? rhs with
              | none =>
                  simp [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
              | some rhsValue =>
                  simp only [sourceStatementConcreteOperation, lhsValueEq, rhsValueEq]
                    at concreteOperation
                  rcases concreteOperation with ⟨rfl, rfl, rfl, rfl⟩
                  have stackPrefix' : environment.stack.take 2 = [lhsValue, rhsValue] := by
                    simpa [Machine.Operation.inputCount] using stackPrefix
                  have stackEq : environment.stack =
                      lhsValue :: rhsValue :: environment.stack.drop 2 := by
                    calc
                      environment.stack = environment.stack.take 2 ++ environment.stack.drop 2 :=
                        (List.take_append_drop 2 environment.stack).symm
                      _ = [lhsValue, rhsValue] ++ environment.stack.drop 2 := by rw [stackPrefix']
                      _ = lhsValue :: rhsValue :: environment.stack.drop 2 := rfl
                  constructor
                  · apply Sir.step_assign sourceDecode
                    exact fires_of (by
                      change #[lhs, rhs].mapM (locals.lookup ·) = .ok #[lhsValue, rhsValue]
                      rw [Array.mapM_eq_mapM_toList]
                      simp [Locals.lookup, lhsValueEq, rhsValueEq, bind, Except.bind, pure,
                        Except.pure]) (by trivial)
                      (Machine.Operation.execute_lt_ok ctx lhsValue rhsValue globals)
                      (by simp only [Locals.bindValues, ← Array.forIn_toList,
                        Array.toList_zip]; rfl)
                  · apply Machine.Step.operation (frame := Stack.frame)
                        (operation := .lt) (src := .inOrder 2) (dst := ⟨2, 1⟩)
                        (hdecode := by simp [Stack.decoder, Stack.decode, targetDecode,
                          Machine.Operation.inputCount, Machine.Operation.outputCount])
                    exact Machine.OperandFrame.Fires.next (oracle := ()) (by trivial)
                      (by
                        change Stack.fetch environment 2 = .ok #[lhsValue, rhsValue]
                        rw [Stack.fetch, if_pos (by rw [stackEq]; simp), stackPrefix'])
                      (Machine.Operation.execute_lt_ok ctx lhsValue rhsValue globals)
                      (by
                        change Stack.store environment ⟨2, 1⟩
                          #[Evm.UInt256.lt lhsValue rhsValue] = .ok _
                        rw [Stack.store, if_pos (by rw [stackEq]; simp)]
                        simp [Machine.Operation.inputCount])
      | sload key => simp [sourceStatementConcreteOperation] at concreteOperation
  | sstore key value => simp [sourceStatementConcreteOperation] at concreteOperation
  | gas result => simp [sourceStatementConcreteOperation] at concreteOperation
  | call call => simp [sourceStatementConcreteOperation] at concreteOperation
  | malloc result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mallocUninit result size => simp [sourceStatementConcreteOperation] at concreteOperation
  | mstore32 offset value => simp [sourceStatementConcreteOperation] at concreteOperation
  | mload32 result offset => simp [sourceStatementConcreteOperation] at concreteOperation
  | icall callee arguments destinations => simp [sourceStatementConcreteOperation]
      at concreteOperation

end Sir.Lowering
