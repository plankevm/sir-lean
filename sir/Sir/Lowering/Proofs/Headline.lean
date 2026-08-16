import Sir.Lowering.Proofs.Block

namespace Sir.Lowering

theorem StackSchedule.forward_halted_path
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) {start final : Vars.State}
    (path : SourcePath certificate.vars ctx start final)
    (finalHalted : final.control = .halted)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (globals : Globals) (locals : Locals) (environment : Stack.Environment)
    (initialPath : SourcePath certificate.vars ctx start
      ⟨globals, locals, blockCertificate.sourceControlAt block 0⟩)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalEnvironment,
      Machine.Steps Stack.frame
        (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
        ⟨globals, environment, blockCertificate.targetControlAt block 0⟩ []
        ⟨final.globals, finalEnvironment, .halted⟩ := by
  have sourcePure := certificate.vars_program_memOracleFree accepted
  induction path generalizing block blockCertificate globals locals environment with
  | refl state =>
      obtain ⟨stateEq, _⟩ := Vars.Steps.eq_of_stuck initialPath.to_steps
        (stuck_of_exit (program := certificate.vars) (outcome := .halted) finalHalted)
      have controlEq := congrArg Machine.State.control stateEq
      rw [finalHalted] at controlEq
      simp [StackSchedule.Block.sourceControlAt] at controlEq
  | @head state middle pathFinal first rest inductionHypothesis =>
      cases initialPath with
      | refl =>
          rcases certificate.block_transition_paths accepted block blockCertificate blockAt ctx
              globals locals environment stackValues with halted | transitioned
          · obtain ⟨certifiedFinalLocals, finalEnvironment, certifiedSource,
                certifiedTarget⟩ := halted
            have remaining := certifiedSource.cancel_prefix sourcePure (.head first rest)
              (stuck_of_exit (program := certificate.vars) (outcome := .halted) finalHalted)
            obtain ⟨stateEq, _⟩ := Vars.Steps.eq_of_stuck remaining.to_steps
              (stuck_of_exit (program := certificate.vars) (outcome := .halted) rfl)
            have globalsEq : pathFinal.globals = globals :=
              congrArg Machine.State.globals stateEq
            simpa [globalsEq] using ⟨finalEnvironment, certifiedTarget⟩
          · obtain ⟨successor, successorCertificate, nextLocals, nextEnvironment,
                successorAt, _, certifiedNonempty, certifiedTarget, _, nextValues⟩ := transitioned
            obtain ⟨firstMiddle, certifiedFirst, certifiedRest⟩ := certifiedNonempty
            have middleEq := Vars.Proofs.SmallStep.trace_det sourcePure first certifiedFirst
            subst firstMiddle
            obtain ⟨finalEnvironment, targetRest⟩ := inductionHypothesis
              finalHalted successor successorCertificate successorAt globals nextLocals nextEnvironment
              certifiedRest nextValues
            exact ⟨finalEnvironment, Machine.Steps.trans certifiedTarget targetRest⟩
      | head prefixFirst prefixRest =>
          have middleEq := Vars.Proofs.SmallStep.trace_det sourcePure first prefixFirst
          subst middleEq
          exact inductionHypothesis finalHalted block blockCertificate blockAt globals locals environment
            prefixRest stackValues

theorem StackSchedule.reverse_halted_path
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext)
    {start final : Machine.State Stack.frame}
    (path : TargetPath certificate.stack ctx start final)
    (finalHalted : final.control = .halted)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (globals : Globals) (locals : Locals) (environment : Stack.Environment)
    (initialPath : TargetPath certificate.stack ctx start
      ⟨globals, environment, blockCertificate.targetControlAt block 0⟩)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals,
      Machine.Steps Vars.frame
        (Vars.decoder certificate.vars) Machine.memoryPolicy ctx
        ((⟨globals, locals, blockCertificate.sourceControlAt block 0⟩ :
          Vars.State)) []
        ((⟨final.globals, finalLocals, .halted⟩ : Vars.State)) := by
  have noMalloc := certificate.stack_program_noMalloc accepted
  have noMload := certificate.stack_program_noMload accepted
  have targetTerminal := Stack.Proofs.decoder_terminal certificate.stack
  induction path generalizing block blockCertificate globals locals environment with
  | refl state =>
      obtain ⟨stateEq, _⟩ := Machine.Steps.eq_of_stuck initialPath.to_steps
        (Machine.stuck_of_exit (outcome := .halted) targetTerminal finalHalted)
      have controlEq := congrArg (Machine.State.control (frame := Stack.frame)) stateEq
      rw [finalHalted] at controlEq
      simp [StackSchedule.Block.targetControlAt] at controlEq
  | @head state middle pathFinal first rest inductionHypothesis =>
      cases initialPath with
      | refl =>
          rcases certificate.block_transition_paths accepted block blockCertificate blockAt ctx
              globals locals environment stackValues with halted | transitioned
          · obtain ⟨certifiedFinalLocals, finalEnvironment, certifiedSource,
                certifiedTarget⟩ := halted
            have remaining := (TargetPath.of_steps certifiedTarget rfl).cancel_prefix
              noMalloc noMload (.head first rest)
              (Machine.stuck_of_exit (outcome := .halted) targetTerminal finalHalted)
            obtain ⟨stateEq, _⟩ := Machine.Steps.eq_of_stuck remaining.to_steps
              (Machine.stuck_of_exit (outcome := .halted) targetTerminal rfl)
            have globalsEq : pathFinal.globals = globals :=
              congrArg (Machine.State.globals (frame := Stack.frame)) stateEq
            simpa [globalsEq] using ⟨certifiedFinalLocals, certifiedSource.to_steps⟩
          · obtain ⟨successor, successorCertificate, nextLocals, nextEnvironment,
                successorAt, certifiedSource, _, _, certifiedNonempty, nextValues⟩ := transitioned
            obtain ⟨certifiedMiddle, certifiedFirst, certifiedRest⟩ := certifiedNonempty
            rcases Machine.Proofs.stepDialogue_all (.inr noMalloc)
                (Stack.Proofs.decoder_exclusive certificate.stack) targetTerminal
                noMload first [] _ certifiedFirst with ⟨_, middleEq⟩ | divergence
            · subst certifiedMiddle
              obtain ⟨finalLocals, sourceRest⟩ := inductionHypothesis
                finalHalted successor successorCertificate successorAt globals nextLocals
                nextEnvironment certifiedRest nextValues
              exact ⟨finalLocals, Machine.Steps.trans certifiedSource.to_steps sourceRest⟩
            · obtain ⟨_, _, _, _, _, firstTrace, _, _, _⟩ := divergence
              simp at firstTrace
      | head prefixFirst prefixRest =>
          rcases Machine.Proofs.stepDialogue_all (.inr noMalloc)
              (Stack.Proofs.decoder_exclusive certificate.stack) targetTerminal
              noMload first [] _ prefixFirst with ⟨_, middleEq⟩ | divergence
          · subst middleEq
            exact inductionHypothesis finalHalted block blockCertificate blockAt globals locals
              environment prefixRest stackValues
          · obtain ⟨_, _, _, _, _, firstTrace, _, _, _⟩ := divergence
            simp at firstTrace

theorem Proofs.StackSchedule.forward_halted_evaluation
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (sourceEvaluation : Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace
      finalGlobals .halted) :
    Stack.EvalFn certificate.stack ctx
      ⟨0⟩ globals args trace finalGlobals .halted := by
  obtain ⟨blockCertificate, blockAt, entryNodup⟩ := certificate.entry_block accepted
  have boundaryNames := certificate.block_boundary_names accepted certificate.entry.id
    blockCertificate blockAt
  cases sourceEvaluation with
  | exit sourceEntry sourceRun finalHalted =>
      rename_i initial exit
      cases bound : Locals.bindParams
          (blockCertificate.vars.entryLayout.map Symbolic.Value.identifier) args with
      | error error =>
          simp [Vars.decoder, StackSchedule.vars,
            Vars.Program.callState?, Vars.Program.function?, Vars.Function.block?, blockAt,
            StackSchedule.Block.Source.toBlock, ← boundaryNames.1, bound] at sourceEntry
      | ok initialLocals =>
          obtain ⟨expectedSourceEntry, targetEntry, entryValues⟩ :=
            certificate.entry_states accepted blockCertificate blockAt globals args initialLocals
              bound
          have initialEq : initial =
              ((⟨globals, initialLocals,
                blockCertificate.sourceControlAt certificate.entry 0⟩ : Vars.State)) :=
            Option.some.inj (sourceEntry.symm.trans expectedSourceEntry)
          subst initial
          let finalState : Vars.State :=
            ⟨exit.globals, exit.environment, exit.control⟩
          have sourceSteps : Vars.Steps certificate.vars ctx
              ⟨globals, initialLocals,
                blockCertificate.sourceControlAt certificate.entry 0⟩ trace finalState := by
            simpa [Vars.Steps, finalState] using sourceRun
          obtain ⟨sourcePath, traceEmpty⟩ :=
            certificate.source_steps_path accepted ctx sourceSteps
          have finalStateHalted : finalState.control = .halted := by
            exact finalHalted
          obtain ⟨finalEnvironment, targetRun⟩ := certificate.forward_halted_path accepted ctx
            sourcePath finalStateHalted certificate.entry blockCertificate blockAt globals
            initialLocals { Stack.Environment.empty with stack := args.toList }
            (.refl _) entryValues
          subst trace
          exact Machine.FunctionEvaluation.exit (outcome := .halted) targetEntry targetRun rfl

theorem Proofs.StackSchedule.reverse_halted_evaluation
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (targetEvaluation : Stack.EvalFn certificate.stack ctx
      ⟨0⟩ globals args trace finalGlobals .halted) :
    Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace finalGlobals .halted := by
  obtain ⟨blockCertificate, blockAt, entryNodup⟩ := certificate.entry_block accepted
  cases targetEvaluation with
  | exit targetEntry targetRun finalHalted =>
      rename_i initial exit
      have argumentSize : args.size = blockCertificate.vars.entryLayout.size := by
        simp [Stack.decoder, Stack.entry,
          StackSchedule.stack, Stack.Program.function?,
          Stack.Function.block?, blockAt, StackSchedule.Block.Target.toBlock]
          at targetEntry
        omega
      let initialLocals := Locals.empty.assignPairs
        ((blockCertificate.vars.entryLayout.map Symbolic.Value.identifier).toList.zip args.toList)
      have bound : Locals.bindParams
          (blockCertificate.vars.entryLayout.map Symbolic.Value.identifier) args = .ok initialLocals := by
        rw [Locals.bindParams,
          Locals.bindValues_eq_assignPairs (by simpa using argumentSize.symm)]
      obtain ⟨sourceEntry, expectedTargetEntry, entryValues⟩ :=
        certificate.entry_states accepted blockCertificate blockAt globals args initialLocals bound
      have initialEq : initial =
          ⟨globals, { Stack.Environment.empty with stack := args.toList },
            blockCertificate.targetControlAt certificate.entry 0⟩ :=
        Option.some.inj (targetEntry.symm.trans expectedTargetEntry)
      subst initial
      obtain ⟨targetPath, traceEmpty⟩ :=
        certificate.target_steps_path accepted ctx targetRun
      obtain ⟨finalLocals, sourceRun⟩ := certificate.reverse_halted_path accepted ctx
        targetPath finalHalted certificate.entry blockCertificate blockAt globals initialLocals
        { Stack.Environment.empty with stack := args.toList } (.refl _) entryValues
      subst trace
      exact Machine.FunctionEvaluation.exit (outcome := .halted) sourceEntry sourceRun rfl

theorem StackSchedule.source_evaluation_not_returned
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args results : Array Word)
    (trace : Trace)
    (sourceEvaluation : Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace
      finalGlobals (.returned results)) :
    False := by
  obtain ⟨entryCertificate, entryAt, _⟩ := certificate.entry_block accepted
  cases sourceEvaluation with
  | exit sourceEntry sourceRun finalReturned =>
      rename_i initial exit
      cases sourceRun with
      | refl =>
          simp [Vars.decoder, StackSchedule.vars,
            Vars.Program.callState?, Vars.Program.function?, Vars.Function.block?, entryAt,
            StackSchedule.Block.Source.toBlock] at sourceEntry
          cases bound : Locals.bindParams entryCertificate.vars.inputs args with
          | error error => simp [bound] at sourceEntry
          | ok initialLocals =>
              simp [bound] at sourceEntry
              subst sourceEntry
              simp [FunctionOutcome.toControl] at finalReturned
      | tail start next =>
          have returnedStep := Vars.SmallStep.returned_inv
            (program := certificate.vars) (ctx := ctx) next
            (by simpa [FunctionOutcome.toControl] using finalReturned)
          obtain ⟨cursor, block, _, blockAt, terminator, _⟩ := returnedStep
          exact certificate.vars_program_terminator_not_iret accepted cursor block blockAt
            terminator

theorem StackSchedule.target_evaluation_not_returned
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args results : Array Word)
    (trace : Trace)
    (targetEvaluation : Stack.EvalFn certificate.stack ctx
      ⟨0⟩ globals args trace finalGlobals (.returned results)) :
    False := by
  cases targetEvaluation with
  | exit targetEntry targetRun finalReturned =>
      cases targetRun with
      | refl =>
          cases functionAt : certificate.stack.function? ⟨0⟩ with
          | none =>
              simp [Stack.decoder, Stack.entry, functionAt] at targetEntry
          | some function =>
              cases blockAt : function.block? function.entry with
              | none =>
                  simp [Stack.decoder, Stack.entry, functionAt, blockAt]
                    at targetEntry
              | some block =>
                  by_cases mismatch : args.size ≠ block.inputCount
                  · simp [Stack.decoder, Stack.entry, functionAt, blockAt, mismatch]
                      at targetEntry
                  · simp [Stack.decoder, Stack.entry, functionAt, blockAt]
                      at targetEntry
                    have controlEq := congrArg
                      (Machine.State.control (frame := Stack.frame)) targetEntry.2
                    rw [finalReturned] at controlEq
                    cases controlEq
      | tail start next =>
          exact certificate.target_step_not_returned accepted ctx next results finalReturned

private theorem Proofs.StackSchedule.forward_evaluation
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome)
    (sourceEvaluation : Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace
      finalGlobals outcome) :
    Stack.EvalFn certificate.stack ctx
      ⟨0⟩ globals args trace finalGlobals outcome := by
  cases outcome with
  | returned results =>
      exact (certificate.source_evaluation_not_returned accepted ctx globals finalGlobals args
        results trace sourceEvaluation).elim
  | halted =>
      exact Proofs.StackSchedule.forward_halted_evaluation certificate accepted ctx globals finalGlobals args
        trace sourceEvaluation

private theorem Proofs.StackSchedule.reverse_evaluation
    (certificate : StackSchedule) (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome)
    (targetEvaluation : Stack.EvalFn certificate.stack ctx
      ⟨0⟩ globals args trace finalGlobals outcome) :
    Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace finalGlobals outcome := by
  cases outcome with
  | returned results =>
      exact (certificate.target_evaluation_not_returned accepted ctx globals finalGlobals args
        results trace targetEvaluation).elim
  | halted =>
      exact Proofs.StackSchedule.reverse_halted_evaluation certificate accepted ctx globals finalGlobals args
        trace targetEvaluation

private theorem StackSchedule.source_evaluation_function_eq_zero
    (certificate : StackSchedule) {ctx : CallContext} {function : FunctionId}
    {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Vars.EvalFn certificate.vars ctx function globals args trace
      finalGlobals outcome) :
    function = ⟨0⟩ := by
  rcases function with ⟨_ | function⟩
  · rfl
  · cases evaluation with
    | exit entry _ _ =>
        simp [Vars.decoder, StackSchedule.vars,
          Vars.Program.callState?, Vars.Program.function?] at entry

private theorem StackSchedule.target_evaluation_function_eq_zero
    (certificate : StackSchedule) {ctx : CallContext} {function : FunctionId}
    {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Stack.EvalFn certificate.stack ctx function globals args trace
      finalGlobals outcome) :
    function = ⟨0⟩ := by
  rcases function with ⟨_ | function⟩
  · rfl
  · cases evaluation with
    | exit entry _ _ =>
        simp [Stack.decoder, Stack.entry, StackSchedule.stack,
          Stack.Program.function?] at entry

theorem Proofs.StackSchedule.equiv
    (certificate : StackSchedule) (accepted : certificate.check = .ok ()) :
    Equiv certificate.vars certificate.stack := by
  intro ctx function globals args trace finalGlobals outcome
  constructor
  · intro sourceEvaluation
    have functionEq := certificate.source_evaluation_function_eq_zero sourceEvaluation
    subst function
    exact Proofs.StackSchedule.forward_evaluation certificate accepted ctx globals
      finalGlobals args trace outcome sourceEvaluation
  · intro targetEvaluation
    have functionEq := certificate.target_evaluation_function_eq_zero targetEvaluation
    subst function
    exact Proofs.StackSchedule.reverse_evaluation certificate accepted ctx globals
      finalGlobals args trace outcome targetEvaluation

theorem Proofs.Scheduler.Accepted.equiv
    {scheduler : Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    Equiv schedule.vars schedule.stack :=
  Proofs.StackSchedule.equiv schedule (accepted statements schedule produced).2

theorem Proofs.Scheduler.Accepted.schedules_input
    {scheduler : Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    schedule.blocks[schedule.entry.id]?.map (fun block => block.vars.statements) =
      some statements :=
  (accepted statements schedule produced).1

end Sir.Lowering
