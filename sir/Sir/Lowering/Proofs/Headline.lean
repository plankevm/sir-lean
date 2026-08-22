import Sir.Lowering.Proofs.Block

namespace Sir.Lowering

theorem StackSchedule.forward_halted_path
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) {start final : Vars.State}
    (path : SourcePath schedule.program.vars ctx start final)
    (finalHalted : final.control = .halted)
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (globals : Globals) (locals : Locals) (environment : Stack.Environment)
    (initialPath : SourcePath schedule.program.vars ctx start
      ⟨globals, locals, blockSchedule.sourceControlAt block 0⟩)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalEnvironment,
      Machine.Steps Stack.frame
        (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
        ⟨globals, environment, blockSchedule.targetControlAt block 0⟩ []
        ⟨final.globals, finalEnvironment, .halted⟩ := by
  have sourcePure := schedule.vars_program_memOracleFree accepted
  induction path generalizing block blockSchedule globals locals environment with
  | refl state =>
      obtain ⟨stateEq, _⟩ := Vars.Steps.eq_of_stuck initialPath.to_steps
        (stuck_of_exit (program := schedule.program.vars) (outcome := .halted) finalHalted)
      have controlEq := congrArg Machine.State.control stateEq
      rw [finalHalted] at controlEq
      simp [StackSchedule.Block.sourceControlAt] at controlEq
  | @head state middle pathFinal first rest inductionHypothesis =>
      cases initialPath with
      | refl =>
          rcases schedule.block_transition_paths accepted block blockSchedule blockAt ctx
              globals locals environment stackValues with halted | transitioned
          · obtain ⟨certifiedFinalLocals, finalEnvironment, certifiedSource,
                certifiedTarget⟩ := halted
            have remaining := certifiedSource.cancel_prefix sourcePure (.head first rest)
              (stuck_of_exit (program := schedule.program.vars) (outcome := .halted) finalHalted)
            obtain ⟨stateEq, _⟩ := Vars.Steps.eq_of_stuck remaining.to_steps
              (stuck_of_exit (program := schedule.program.vars) (outcome := .halted) rfl)
            have globalsEq : pathFinal.globals = globals :=
              congrArg Machine.State.globals stateEq
            simpa [globalsEq] using ⟨finalEnvironment, certifiedTarget⟩
          · obtain ⟨successor, successorSchedule, nextLocals, nextEnvironment,
                successorAt, _, certifiedNonempty, certifiedTarget, _, nextValues⟩ := transitioned
            obtain ⟨firstMiddle, certifiedFirst, certifiedRest⟩ := certifiedNonempty
            have middleEq := Vars.Proofs.SmallStep.trace_det sourcePure first certifiedFirst
            subst firstMiddle
            obtain ⟨finalEnvironment, targetRest⟩ := inductionHypothesis
              finalHalted successor successorSchedule successorAt globals nextLocals nextEnvironment
              certifiedRest nextValues
            exact ⟨finalEnvironment, Machine.Steps.trans certifiedTarget targetRest⟩
      | head prefixFirst prefixRest =>
          have middleEq := Vars.Proofs.SmallStep.trace_det sourcePure first prefixFirst
          subst middleEq
          exact inductionHypothesis finalHalted block blockSchedule blockAt globals locals environment
            prefixRest stackValues

theorem StackSchedule.reverse_halted_path
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext)
    {start final : Machine.State Stack.frame}
    (path : TargetPath schedule.program.stack ctx start final)
    (finalHalted : final.control = .halted)
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (globals : Globals) (locals : Locals) (environment : Stack.Environment)
    (initialPath : TargetPath schedule.program.stack ctx start
      ⟨globals, environment, blockSchedule.targetControlAt block 0⟩)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals,
      Machine.Steps Vars.frame
        (Vars.decoder schedule.program.vars) Machine.memoryPolicy ctx
        ((⟨globals, locals, blockSchedule.sourceControlAt block 0⟩ :
          Vars.State)) []
        ((⟨final.globals, finalLocals, .halted⟩ : Vars.State)) := by
  have noMalloc := schedule.stack_program_noMalloc accepted
  have noMload := schedule.stack_program_noMload accepted
  induction path generalizing block blockSchedule globals locals environment with
  | refl state =>
      obtain ⟨stateEq, _⟩ := Machine.Steps.eq_of_stuck initialPath.to_steps
        (Machine.stuck_of_exit (outcome := .halted) finalHalted)
      have controlEq := congrArg (Machine.State.control (frame := Stack.frame)) stateEq
      rw [finalHalted] at controlEq
      simp [StackSchedule.Block.targetControlAt] at controlEq
  | @head state middle pathFinal first rest inductionHypothesis =>
      cases initialPath with
      | refl =>
          rcases schedule.block_transition_paths accepted block blockSchedule blockAt ctx
              globals locals environment stackValues with halted | transitioned
          · obtain ⟨certifiedFinalLocals, finalEnvironment, certifiedSource,
                certifiedTarget⟩ := halted
            have remaining := (TargetPath.of_steps certifiedTarget rfl).cancel_prefix
              noMalloc noMload (.head first rest)
              (Machine.stuck_of_exit (outcome := .halted) finalHalted)
            obtain ⟨stateEq, _⟩ := Machine.Steps.eq_of_stuck remaining.to_steps
              (Machine.stuck_of_exit (outcome := .halted) rfl)
            have globalsEq : pathFinal.globals = globals :=
              congrArg (Machine.State.globals (frame := Stack.frame)) stateEq
            simpa [globalsEq] using ⟨certifiedFinalLocals, certifiedSource.to_steps⟩
          · obtain ⟨successor, successorSchedule, nextLocals, nextEnvironment,
                successorAt, certifiedSource, _, _, certifiedNonempty, nextValues⟩ := transitioned
            obtain ⟨certifiedMiddle, certifiedFirst, certifiedRest⟩ := certifiedNonempty
            rcases Machine.Proofs.stepDialogue_all (.inr noMalloc)
                noMload first [] _ certifiedFirst with ⟨_, middleEq⟩ | divergence
            · subst certifiedMiddle
              obtain ⟨finalLocals, sourceRest⟩ := inductionHypothesis
                finalHalted successor successorSchedule successorAt globals nextLocals
                nextEnvironment certifiedRest nextValues
              exact ⟨finalLocals, Machine.Steps.trans certifiedSource.to_steps sourceRest⟩
            · obtain ⟨_, _, _, _, _, firstTrace, _, _, _⟩ := divergence
              simp at firstTrace
      | head prefixFirst prefixRest =>
          rcases Machine.Proofs.stepDialogue_all (.inr noMalloc)
              noMload first [] _ prefixFirst with ⟨_, middleEq⟩ | divergence
          · subst middleEq
            exact inductionHypothesis finalHalted block blockSchedule blockAt globals locals
              environment prefixRest stackValues
          · obtain ⟨_, _, _, _, _, firstTrace, _, _, _⟩ := divergence
            simp at firstTrace

theorem Proofs.StackSchedule.forward_halted_evaluation
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (sourceEvaluation : Vars.EvalFn schedule.program.vars ctx ⟨0⟩ globals args trace
      finalGlobals .halted) :
    Stack.EvalFn schedule.program.stack ctx
      ⟨0⟩ globals args trace finalGlobals .halted := by
  have boundaryNames :=
    schedule.block_boundary_names accepted 0 schedule.entry schedule.blocks_zero
  cases sourceEvaluation with
  | exit sourceEntry sourceRun finalHalted =>
      rename_i initial exit
      cases bound : Locals.bindParams
          (schedule.entry.vars.entryLayout.map Symbolic.Value.identifier) args with
      | error error =>
          simp [Vars.decoder, StackSchedule.program, ProgramSchedule.vars,
            StackSchedule.varsFunction, Vars.Program.functions,
            Vars.Program.callState?, Vars.Program.function?,
            StackSchedule.Block.Source.toBlock, ← boundaryNames.1, bound] at sourceEntry
      | ok initialLocals =>
          obtain ⟨expectedSourceEntry, targetEntry, entryValues⟩ :=
            schedule.entry_states accepted globals args initialLocals bound
          have initialEq : initial =
              ((⟨globals, initialLocals,
                schedule.entry.sourceControlAt ⟨0⟩ 0⟩ : Vars.State)) :=
            Option.some.inj (sourceEntry.symm.trans expectedSourceEntry)
          subst initial
          let finalState : Vars.State :=
            ⟨exit.globals, exit.environment, exit.control⟩
          have sourceSteps : Vars.Steps schedule.program.vars ctx
              ⟨globals, initialLocals,
                schedule.entry.sourceControlAt ⟨0⟩ 0⟩ trace finalState := by
            simpa [Vars.Steps, finalState] using sourceRun
          obtain ⟨sourcePath, traceEmpty⟩ :=
            schedule.source_steps_path accepted ctx sourceSteps
          have finalStateHalted : finalState.control = .halted := by
            exact finalHalted
          obtain ⟨finalEnvironment, targetRun⟩ := schedule.forward_halted_path accepted ctx
            sourcePath finalStateHalted ⟨0⟩ schedule.entry schedule.blocks_zero globals
            initialLocals { Stack.Environment.empty with stack := args.toList }
            (.refl _) entryValues
          subst trace
          exact Machine.FunctionEvaluation.exit (outcome := .halted) targetEntry targetRun rfl

theorem Proofs.StackSchedule.reverse_halted_evaluation
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (targetEvaluation : Stack.EvalFn schedule.program.stack ctx
      ⟨0⟩ globals args trace finalGlobals .halted) :
    Vars.EvalFn schedule.program.vars ctx ⟨0⟩ globals args trace finalGlobals .halted := by
  cases targetEvaluation with
  | exit targetEntry targetRun finalHalted =>
      rename_i initial exit
      have argumentSize : args.size = schedule.entry.vars.entryLayout.size := by
        simp [Stack.decoder, Stack.entry,
          StackSchedule.program, ProgramSchedule.stack, StackSchedule.stackFunction,
            Stack.Program.functions, Stack.Program.function?,
          StackSchedule.Block.Target.toBlock]
          at targetEntry
        omega
      let initialLocals := Locals.empty.assignPairs
        ((schedule.entry.vars.entryLayout.map Symbolic.Value.identifier).toList.zip args.toList)
      have bound : Locals.bindParams
          (schedule.entry.vars.entryLayout.map Symbolic.Value.identifier) args =
            .ok initialLocals := by
        rw [Locals.bindParams,
          Locals.bindValues_eq_assignPairs (by simpa using argumentSize.symm)]
      obtain ⟨sourceEntry, expectedTargetEntry, entryValues⟩ :=
        schedule.entry_states accepted globals args initialLocals bound
      have initialEq : initial =
          ⟨globals, { Stack.Environment.empty with stack := args.toList },
            schedule.entry.targetControlAt ⟨0⟩ 0⟩ :=
        Option.some.inj (targetEntry.symm.trans expectedTargetEntry)
      subst initial
      obtain ⟨targetPath, traceEmpty⟩ :=
        schedule.target_steps_path accepted ctx targetRun
      obtain ⟨finalLocals, sourceRun⟩ := schedule.reverse_halted_path accepted ctx
        targetPath finalHalted ⟨0⟩ schedule.entry schedule.blocks_zero globals initialLocals
        { Stack.Environment.empty with stack := args.toList } (.refl _) entryValues
      subst trace
      exact Machine.FunctionEvaluation.exit (outcome := .halted) sourceEntry sourceRun rfl

theorem StackSchedule.source_evaluation_not_returned
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args results : Array Word)
    (trace : Trace)
    (sourceEvaluation : Vars.EvalFn schedule.program.vars ctx ⟨0⟩ globals args trace
      finalGlobals (.returned results)) :
    False := by
  cases sourceEvaluation with
  | exit sourceEntry sourceRun finalReturned =>
      rename_i initial exit
      cases sourceRun with
      | refl =>
          simp [Vars.decoder, StackSchedule.program, ProgramSchedule.vars,
            StackSchedule.varsFunction, Vars.Program.functions,
            Vars.Program.callState?, Vars.Program.function?,
            StackSchedule.Block.Source.toBlock] at sourceEntry
          cases bound : Locals.bindParams schedule.entry.vars.inputs args with
          | error error => simp [bound] at sourceEntry
          | ok initialLocals =>
              simp [bound] at sourceEntry
              subst sourceEntry
              simp [FunctionOutcome.toControl] at finalReturned
      | tail start next =>
          have returnedStep := Vars.SmallStep.returned_inv
            (program := schedule.program.vars) (ctx := ctx) next
            (by simpa [FunctionOutcome.toControl] using finalReturned)
          obtain ⟨cursor, block, _, blockAt, terminator, _⟩ := returnedStep
          exact schedule.vars_program_terminator_not_iret accepted cursor block blockAt
            terminator

theorem StackSchedule.target_evaluation_not_returned
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args results : Array Word)
    (trace : Trace)
    (targetEvaluation : Stack.EvalFn schedule.program.stack ctx
      ⟨0⟩ globals args trace finalGlobals (.returned results)) :
    False := by
  cases targetEvaluation with
  | exit targetEntry targetRun finalReturned =>
      cases targetRun with
      | refl =>
          cases functionAt : schedule.program.stack.function? ⟨0⟩ with
          | none =>
              simp [Stack.decoder, Stack.entry, functionAt] at targetEntry
          | some function =>
              by_cases mismatch : args.size ≠ function.entry.inputCount
              · simp [Stack.decoder, Stack.entry, functionAt, mismatch] at targetEntry
              · simp [Stack.decoder, Stack.entry, functionAt] at targetEntry
                have controlEq := congrArg
                  (Machine.State.control (frame := Stack.frame)) targetEntry.2
                rw [finalReturned] at controlEq
                cases controlEq
      | tail start next =>
          exact schedule.target_step_not_returned accepted ctx next results finalReturned

private theorem Proofs.StackSchedule.forward_evaluation
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome)
    (sourceEvaluation : Vars.EvalFn schedule.program.vars ctx ⟨0⟩ globals args trace
      finalGlobals outcome) :
    Stack.EvalFn schedule.program.stack ctx
      ⟨0⟩ globals args trace finalGlobals outcome := by
  cases outcome with
  | returned results =>
      exact (schedule.source_evaluation_not_returned accepted ctx globals finalGlobals args
        results trace sourceEvaluation).elim
  | halted =>
      exact Proofs.StackSchedule.forward_halted_evaluation schedule accepted ctx globals finalGlobals args
        trace sourceEvaluation

private theorem Proofs.StackSchedule.reverse_evaluation
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome)
    (targetEvaluation : Stack.EvalFn schedule.program.stack ctx
      ⟨0⟩ globals args trace finalGlobals outcome) :
    Vars.EvalFn schedule.program.vars ctx ⟨0⟩ globals args trace finalGlobals outcome := by
  cases outcome with
  | returned results =>
      exact (schedule.target_evaluation_not_returned accepted ctx globals finalGlobals args
        results trace targetEvaluation).elim
  | halted =>
      exact Proofs.StackSchedule.reverse_halted_evaluation schedule accepted ctx globals finalGlobals args
        trace targetEvaluation

private theorem StackSchedule.source_evaluation_function_eq_zero
    (schedule : StackSchedule) {ctx : CallContext} {function : FunctionId}
    {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Vars.EvalFn schedule.program.vars ctx function globals args trace
      finalGlobals outcome) :
    function = ⟨0⟩ := by
  rcases function with ⟨_ | function⟩
  · rfl
  · cases evaluation with
    | exit entry _ _ =>
        simp [Vars.decoder, StackSchedule.program, ProgramSchedule.vars,
          StackSchedule.varsFunction, Vars.Program.functions,
          Vars.Program.callState?, Vars.Program.function?] at entry

private theorem StackSchedule.target_evaluation_function_eq_zero
    (schedule : StackSchedule) {ctx : CallContext} {function : FunctionId}
    {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Stack.EvalFn schedule.program.stack ctx function globals args trace
      finalGlobals outcome) :
    function = ⟨0⟩ := by
  rcases function with ⟨_ | function⟩
  · rfl
  · cases evaluation with
    | exit entry _ _ =>
        simp [Stack.decoder, Stack.entry, StackSchedule.program, ProgramSchedule.stack,
          StackSchedule.stackFunction, Stack.Program.functions,
          Stack.Program.function?] at entry

theorem Proofs.StackSchedule.equiv
    (schedule : StackSchedule) (accepted : schedule.check = .ok ()) :
    Equiv schedule.program.vars schedule.program.stack := by
  intro ctx function globals args trace finalGlobals outcome
  constructor
  · intro sourceEvaluation
    have functionEq := schedule.source_evaluation_function_eq_zero sourceEvaluation
    subst function
    exact Proofs.StackSchedule.forward_evaluation schedule accepted ctx globals
      finalGlobals args trace outcome sourceEvaluation
  · intro targetEvaluation
    have functionEq := schedule.target_evaluation_function_eq_zero targetEvaluation
    subst function
    exact Proofs.StackSchedule.reverse_evaluation schedule accepted ctx globals
      finalGlobals args trace outcome targetEvaluation

theorem Proofs.Scheduler.Accepted.equiv
    {scheduler : Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    Equiv schedule.program.vars schedule.program.stack :=
  Proofs.StackSchedule.equiv schedule (accepted statements schedule produced).2

theorem Proofs.Scheduler.Accepted.schedules_input
    {scheduler : Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    schedule.entry.vars.statements = statements :=
  (accepted statements schedule produced).1

end Sir.Lowering
