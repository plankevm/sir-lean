import Sir.Lowering.Proofs.Paths
import Sir.Vars.Proofs.Determinism
import Sir.Stack.Proofs

namespace Sir.Lowering

inductive SourcePath (program : Vars.Program) (ctx : CallContext) :
    Vars.State → Vars.State → Prop where
  | refl (state : Vars.State) : SourcePath program ctx state state
  | head {state middle final : Vars.State}
      (step : Vars.SmallStep program ctx state [] middle)
      (rest : SourcePath program ctx middle final) :
      SourcePath program ctx state final

def NonemptySourcePath (program : Vars.Program) (ctx : CallContext)
    (state final : Vars.State) : Prop :=
  ∃ middle, Vars.SmallStep program ctx state [] middle ∧ SourcePath program ctx middle final

theorem SourcePath.tail {program : Vars.Program} {ctx : CallContext}
    {state middle final : Vars.State}
    (path : SourcePath program ctx state middle)
    (step : Vars.SmallStep program ctx middle [] final) :
    SourcePath program ctx state final := by
  induction path with
  | refl => exact .head step (.refl final)
  | head first rest inductionHypothesis => exact .head first (inductionHypothesis step)

theorem SourcePath.tail_nonempty {program : Vars.Program} {ctx : CallContext}
    {state middle final : Vars.State}
    (path : SourcePath program ctx state middle)
    (step : Vars.SmallStep program ctx middle [] final) :
    NonemptySourcePath program ctx state final := by
  induction path with
  | refl => exact ⟨_, step, .refl final⟩
  | head first rest inductionHypothesis => exact ⟨_, first, rest.tail step⟩

theorem SourcePath.of_steps {program : Vars.Program} {ctx : CallContext}
    {state final : Vars.State} {trace : Trace}
    (steps : Vars.Steps program ctx state trace final) (traceEmpty : trace = []) :
    SourcePath program ctx state final := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ => trace = [] → SourcePath program ctx state final)
    (fun state _ => .refl state)
    (fun start next inductionHypothesis traceEmpty => by
      simp only [List.append_eq_nil_iff] at traceEmpty
      obtain ⟨trace₁Empty, trace₂Empty⟩ := traceEmpty
      subst_vars
      exact (inductionHypothesis rfl).tail next)
    steps traceEmpty

theorem SourcePath.to_steps {program : Vars.Program} {ctx : CallContext}
    {state final : Vars.State}
    (path : SourcePath program ctx state final) : Vars.Steps program ctx state [] final := by
  induction path with
  | refl => exact .refl
  | head step rest inductionHypothesis =>
      simpa using Machine.Steps.trans (Machine.Steps.single step) inductionHypothesis

theorem SourcePath.cancel_prefix {program : Vars.Program} {ctx : CallContext}
    (memoryOracleFree : program.MemOracleFree)
    {state middle final : Vars.State}
    (initial : SourcePath program ctx state middle)
    (path : SourcePath program ctx state final)
    (finalStuck : Stuck program ctx final) :
    SourcePath program ctx middle final := by
  induction initial generalizing final with
  | refl => exact path
  | head first rest inductionHypothesis =>
      cases path with
      | refl => exact (finalStuck [] _ first).elim
      | head second suffix =>
          have middleEq := Vars.Proofs.SmallStep.trace_det memoryOracleFree first second
          subst middleEq
          exact inductionHypothesis suffix finalStuck

inductive TargetPath (program : Stack.Program) (ctx : CallContext) :
    Machine.State Stack.frame →
      Machine.State Stack.frame → Prop where
  | refl (state : Machine.State Stack.frame) : TargetPath program ctx state state
  | head {state middle final : Machine.State Stack.frame}
      (step : Machine.Step Stack.frame (Stack.decoder program)
        Machine.memoryPolicy ctx state [] middle)
      (rest : TargetPath program ctx middle final) :
      TargetPath program ctx state final

def NonemptyTargetPath (program : Stack.Program) (ctx : CallContext)
    (state final : Machine.State Stack.frame) : Prop :=
  ∃ middle, Machine.Step Stack.frame (Stack.decoder program)
    Machine.memoryPolicy ctx state [] middle ∧ TargetPath program ctx middle final

theorem TargetPath.tail {program : Stack.Program} {ctx : CallContext}
    {state middle final : Machine.State Stack.frame}
    (path : TargetPath program ctx state middle)
    (step : Machine.Step Stack.frame (Stack.decoder program)
      Machine.memoryPolicy ctx middle [] final) :
    TargetPath program ctx state final := by
  induction path with
  | refl => exact .head step (.refl final)
  | head first rest inductionHypothesis => exact .head first (inductionHypothesis step)

theorem TargetPath.tail_nonempty {program : Stack.Program} {ctx : CallContext}
    {state middle final : Machine.State Stack.frame}
    (path : TargetPath program ctx state middle)
    (step : Machine.Step Stack.frame (Stack.decoder program)
      Machine.memoryPolicy ctx middle [] final) :
    NonemptyTargetPath program ctx state final := by
  induction path with
  | refl => exact ⟨_, step, .refl final⟩
  | head first rest inductionHypothesis => exact ⟨_, first, rest.tail step⟩

theorem TargetPath.of_steps {program : Stack.Program} {ctx : CallContext}
    {state final : Machine.State Stack.frame} {trace : Trace}
    (steps : Machine.Steps Stack.frame (Stack.decoder program)
      Machine.memoryPolicy ctx state trace final) (traceEmpty : trace = []) :
    TargetPath program ctx state final := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ => trace = [] → TargetPath program ctx state final)
    (fun state _ => .refl state)
    (fun start next inductionHypothesis traceEmpty => by
      simp only [List.append_eq_nil_iff] at traceEmpty
      obtain ⟨trace₁Empty, trace₂Empty⟩ := traceEmpty
      subst_vars
      exact (inductionHypothesis rfl).tail next)
    steps traceEmpty

theorem TargetPath.to_steps {program : Stack.Program} {ctx : CallContext}
    {state final : Machine.State Stack.frame}
    (path : TargetPath program ctx state final) :
    Machine.Steps Stack.frame (Stack.decoder program)
      Machine.memoryPolicy ctx state [] final := by
  induction path with
  | refl => exact .refl
  | head step rest inductionHypothesis =>
      simpa using Machine.Steps.trans (Machine.Steps.single step) inductionHypothesis

theorem TargetPath.cancel_prefix {program : Stack.Program} {ctx : CallContext}
    (noMalloc : (Stack.decoder program).NoMalloc)
    (noMload : (Stack.decoder program).NoMload)
    {state middle final : Machine.State Stack.frame}
    (initial : TargetPath program ctx state middle)
    (path : TargetPath program ctx state final)
    (finalStuck : Machine.Stuck (Stack.decoder program) Machine.memoryPolicy ctx final) :
    TargetPath program ctx middle final := by
  induction initial generalizing final with
  | refl => exact path
  | head first rest inductionHypothesis =>
      cases path with
      | refl => exact (finalStuck [] _ first).elim
      | head second suffix =>
          rcases Machine.Proofs.stepDialogue_all (.inr noMalloc)
              noMload first [] _ second with ⟨_, middleEq⟩ | divergence
          · subst middleEq
            exact inductionHypothesis suffix finalStuck
          · obtain ⟨pre, firstEvent, firstRest, secondEvent, secondRest,
                firstTrace, _, _, _⟩ := divergence
            simp at firstTrace

def StackSchedule.Block.sourceControlAt
    (schedule : StackSchedule.Block) (block : BlockId) (index : Nat) :
    Machine.MachineControl :=
  .running {
    fn := ⟨0⟩
    block
    position := schedule.vars.toBlock.absoluteToPosition index }

def StackSchedule.Block.targetControlAt
    (schedule : StackSchedule.Block) (block : BlockId) (index : Nat) :
    Machine.MachineControl :=
  .running {
    fn := ⟨0⟩
    block
    position := schedule.stack.toBlock.absoluteToPosition index }

theorem StackSchedule.source_decode_at
    (schedule : StackSchedule) (block : BlockId)
    (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (index : Nat) (statement : Vars.Stmt)
    (statementAt : blockSchedule.vars.statements[index]? = some statement) :
    schedule.program.vars.decodeStmt (blockSchedule.sourceControlAt block index) =
      some (blockSchedule.sourceControlAt block (index + 1), statement) := by
  have indexBound : index < blockSchedule.vars.statements.size :=
    of_getElem?_eq_some (c := blockSchedule.vars.statements) (i := index) statementAt
  have statementGet : blockSchedule.vars.statements[index] = statement :=
    (Array.getElem?_eq_some_iff.mp statementAt).2
  unfold StackSchedule.Block.sourceControlAt Vars.Program.decodeStmt
  simp [Vars.Program.block?, Vars.Program.function?, Vars.Function.block?, blockAt,
    StackSchedule.Block.Source.toBlock, Vars.Block.absoluteToPosition,
    indexBound, statementGet]

theorem StackSchedule.target_decode_at
    (schedule : StackSchedule) (block : BlockId)
    (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (index : Nat) (instruction : Stack.Instr)
    (instructionAt : blockSchedule.stack.instructions[index]? = some instruction) :
    schedule.program.stack.decodeInstruction (blockSchedule.targetControlAt block index) =
      some (blockSchedule.targetControlAt block (index + 1), instruction) := by
  have indexBound : index < blockSchedule.stack.instructions.size :=
    of_getElem?_eq_some (c := blockSchedule.stack.instructions) (i := index) instructionAt
  have instructionGet : blockSchedule.stack.instructions[index] = instruction :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  unfold StackSchedule.Block.targetControlAt Stack.Program.decodeInstruction
  simp [Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
    blockAt, StackSchedule.Block.Target.toBlock, Stack.Block.absoluteToPosition,
    indexBound, instructionGet]

theorem StackSchedule.source_terminator_at_end
    (schedule : StackSchedule) (block : BlockId)
    (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule) :
    schedule.program.vars.terminatorAt
      (blockSchedule.sourceControlAt block blockSchedule.vars.statements.size) =
        some blockSchedule.vars.terminator := by
  unfold StackSchedule.Block.sourceControlAt Vars.Program.terminatorAt
  simp [Vars.Program.block?, Vars.Program.function?, Vars.Function.block?, blockAt,
    StackSchedule.Block.Source.toBlock, Vars.Block.absoluteToPosition]

theorem StackSchedule.target_terminator_at_end
    (schedule : StackSchedule) (block : BlockId)
    (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule) :
    schedule.program.stack.terminatorAt
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size) =
        some blockSchedule.stack.terminator := by
  unfold StackSchedule.Block.targetControlAt Stack.Program.terminatorAt
  simp [Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
    blockAt, StackSchedule.Block.Target.toBlock, Stack.Block.absoluteToPosition]

theorem StackSchedule.target_decode_none_at_end
    (schedule : StackSchedule) (block : BlockId)
    (blockSchedule : StackSchedule.Block) :
    schedule.program.stack.decodeInstruction
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size) = none := by
  unfold StackSchedule.Block.targetControlAt
    Stack.Program.decodeInstruction
  simp [StackSchedule.Block.Target.toBlock, Stack.Block.absoluteToPosition]

theorem StackSchedule.entry_check
    (schedule : StackSchedule) (accepted : schedule.check = .ok ()) :
    schedule.entry.check = .ok () :=
  schedule.mem_blocks_check accepted schedule.entry (by simp [StackSchedule.blocks])

theorem StackSchedule.entry_block
    (schedule : StackSchedule) (accepted : schedule.check = .ok ()) :
    schedule.entry.vars.entryLayout.toList.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, entryNodup⟩ :=
    schedule.entry.check_sound (schedule.entry_check accepted)
  exact entryNodup

theorem StackSchedule.entry_states
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (globals : Globals) (args : Array Word) (locals : Locals)
    (bound : Locals.bindParams
      (schedule.entry.vars.entryLayout.map Symbolic.Value.identifier) args = .ok locals) :
    (Vars.decoder schedule.program.vars).entry ⟨0⟩ globals args =
        some ((⟨globals, locals,
          schedule.entry.sourceControlAt ⟨0⟩ 0⟩ : Vars.State)) ∧
      (Stack.decoder schedule.program.stack).entry ⟨0⟩ globals args =
        some ⟨globals, { Stack.Environment.empty with stack := args.toList },
          schedule.entry.targetControlAt ⟨0⟩ 0⟩ ∧
      schedule.entry.vars.entryLayout.toList.mapM (Symbolic.Value.interpret locals) =
        some args.toList := by
  have entryNodup := schedule.entry_block accepted
  have boundaryNames :=
    schedule.block_boundary_names accepted 0 schedule.entry schedule.blocks_zero
  have argumentSize : args.size = schedule.entry.vars.entryLayout.size := by
    by_contra different
    have sizeMismatch : (schedule.entry.vars.entryLayout.size != args.size) = true :=
      bne_iff_ne.mpr (Ne.symm different)
    simp [Locals.bindParams, Locals.bindValues, sizeMismatch, bind, Except.bind] at bound
  refine ⟨?_, ?_, Locals.bindParams_interprets_symbolic_values
    schedule.entry.vars.entryLayout args locals entryNodup bound⟩
  · simp [Vars.decoder, StackSchedule.program, ProgramSchedule.vars, StackSchedule.varsFunction,
    Vars.Program.functions,
      Vars.Program.callState?, Vars.Program.function?,
      StackSchedule.Block.Source.toBlock, ← boundaryNames.1, bound,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition]
  · simp [Stack.decoder, Stack.entry, StackSchedule.program, ProgramSchedule.stack,
    StackSchedule.stackFunction, Stack.Program.functions,
      Stack.Program.function?, StackSchedule.Block.Target.toBlock, argumentSize,
      StackSchedule.Block.targetControlAt, Stack.Block.startPosition,
      Stack.Environment.empty]

theorem StackSchedule.source_step_trace_empty
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) {state final : Machine.State Vars.frame} {trace : Trace}
    (step : Machine.Step Vars.frame (Vars.decoder schedule.program.vars)
      Machine.memoryPolicy ctx state trace final) :
    trace = [] := by
  cases step with
  | operation hdecode fires =>
      obtain ⟨notGas, notCall⟩ := schedule.source_decode_primitive_pure accepted hdecode
      exact Vars.frame.fires_trace_nil notGas notCall fires
  | operationHalted hdecode fires =>
      exact (Machine.OperandFrame.firesHalt_false _ fires).elim
  | internalCall hdecode fetch evaluation resume =>
      exact (schedule.source_decode_icall_false accepted hdecode).elim
  | control controlStep =>
      obtain ⟨_, _, _, _, traceEmpty, -⟩ := Vars.control_inv.mp controlStep
      exact traceEmpty

theorem StackSchedule.source_steps_path
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) {state final : Vars.State} {trace : Trace}
    (steps : Vars.Steps schedule.program.vars ctx state trace final) :
    SourcePath schedule.program.vars ctx state final ∧ trace = [] := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ =>
      SourcePath schedule.program.vars ctx state final ∧ trace = [])
    (fun state => ⟨.refl state, rfl⟩)
    (fun start next inductionHypothesis => by
      obtain ⟨path, traceEmpty⟩ := inductionHypothesis
      have nextTraceEmpty := schedule.source_step_trace_empty accepted ctx next
      subst_vars
      exact ⟨path.tail next, by simp⟩)
    steps

theorem StackSchedule.target_step_trace_empty
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext)
    {state final : Machine.State Stack.frame} {trace : Trace}
    (step : Machine.Step Stack.frame
      (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx state trace final) :
    trace = [] := by
  cases step with
  | operation hdecode fires =>
      obtain ⟨notGas, notCall⟩ := schedule.target_decode_primitive_pure accepted hdecode
      exact Stack.frame.fires_trace_nil notGas notCall fires
  | operationHalted hdecode fires =>
      exact (Machine.OperandFrame.firesHalt_false _ fires).elim
  | internalCall hdecode fetch evaluation resume =>
      exact (schedule.target_decode_icall_false accepted hdecode).elim
  | control controlStep => exact stackControl_trace_nil controlStep

theorem StackSchedule.target_steps_path
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext)
    {state final : Machine.State Stack.frame} {trace : Trace}
    (steps : Machine.Steps Stack.frame
      (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx state trace final) :
    TargetPath schedule.program.stack ctx state final ∧ trace = [] := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ =>
      TargetPath schedule.program.stack ctx state final ∧ trace = [])
    (fun state => ⟨.refl state, rfl⟩)
    (fun start next inductionHypothesis => by
      obtain ⟨path, traceEmpty⟩ := inductionHypothesis
      have nextTraceEmpty := schedule.target_step_trace_empty accepted ctx next
      subst_vars
      exact ⟨path.tail next, by simp⟩)
    steps

theorem StackSchedule.target_step_not_returned
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (ctx : CallContext) {state final : Machine.State Stack.frame} {trace : Trace}
    (step : Machine.Step Stack.frame
      (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx state trace final)
    (results : Array Word) :
    final.control ≠ .returned results := by
  intro returned
  cases step with
  | operation hdecode fires =>
      obtain ⟨cursor, running⟩ := stackDecode_next_running hdecode
      subst running
      simp at returned
  | operationHalted hdecode fires => cases returned
  | internalCall hdecode fetch evaluation resume =>
      exact schedule.target_decode_icall_false accepted hdecode
  | control controlStep =>
      simp only [] at returned
      subst returned
      obtain ⟨cursor, block, controlEq, blockAt, terminatorEq⟩ :=
        stackControl_returned_inv controlStep
      exact schedule.stack_program_terminator_not_iret accepted cursor block blockAt terminatorEq

theorem StackSchedule.block_execute_steps
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals finalEnvironment expectedStack,
      Machine.Steps Vars.frame (Vars.decoder schedule.program.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockSchedule.sourceControlAt block 0⟩ : Vars.State))
          []
          ((⟨globals, finalLocals,
            blockSchedule.sourceControlAt block blockSchedule.vars.statements.size⟩ :
              Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockSchedule.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment,
            blockSchedule.targetControlAt block blockSchedule.stack.instructions.size⟩ ∧
        StackSchedule.Block.finalStack blockSchedule.vars.terminator blockSchedule.vars.exitLayout
            expectedStack = some expectedStack ∧
        expectedStack.mapM (Symbolic.Value.interpret finalLocals) =
          some finalEnvironment.stack := by
  have blockBound : block.id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
  have blockGet : schedule.blocks[block.id] = blockSchedule :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted : blockSchedule.check = .ok () := by
    have acceptedAt := (schedule.check_sound accepted).1 block.id blockBound
    simpa [blockGet] using acceptedAt
  obtain ⟨usesAvailable, variablesUnique⟩ :=
    StackSchedule.Block.check_source_valid blockSchedule blockAccepted
  obtain ⟨finalState, expectedStack, executed, expected, fired, _, stackEq, _⟩ :=
    blockSchedule.check_sound blockAccepted
  obtain ⟨referenceLocals, evaluated⟩ :=
    blockSchedule.sourceOrderReferenceLocals_exists blockAccepted locals environment.stack
      stackValues
  have interprets := Symbolic.State.initial_interprets_in_environment
    blockSchedule.vars.entryLayout locals environment stackValues
  have initialAgrees :
      (Symbolic.State.initial blockSchedule.vars.entryLayout).AvailableVariablesAgree
        blockSchedule.vars.statements locals referenceLocals := by
    intro identifier available
    have entry : identifier ∈
        blockSchedule.vars.entryLayout.toList.map Symbolic.Value.identifier := by
      simpa [Symbolic.State.initial, Symbolic.State.available] using available
    exact (sourceOrderReferenceLocals_preserves_entry blockSchedule.vars.statements
      blockSchedule.vars.entryLayout locals referenceLocals variablesUnique evaluated identifier
      entry).symm
  have interpretsReference :
      (Symbolic.State.initial blockSchedule.vars.entryLayout).InterpretsReference
        blockSchedule.vars.statements locals referenceLocals environment :=
    ⟨interprets, initialAgrees⟩
  obtain ⟨scheduledLocals, finalEnvironment, targetSteps, finalInterprets⟩ :=
    interpretsReference.execute_symbolic_instructions_target_steps
      (sourceProgram := schedule.program.vars) (targetProgram := schedule.program.stack)
      blockSchedule.vars.statements blockSchedule.vars.entryLayout
      blockSchedule.stack.instructions (Symbolic.State.initial blockSchedule.vars.entryLayout)
      finalState ctx globals locals locals referenceLocals environment usesAvailable variablesUnique
      evaluated
      (blockSchedule.sourceControlAt block) (blockSchedule.targetControlAt block) 0 executed
      (schedule.source_decode_at block blockSchedule blockAt)
      (fun index instruction instructionAt => by
        simpa using schedule.target_decode_at block blockSchedule blockAt index instruction
          instructionAt)
  have sourceSteps := sourceOrderReferenceLocals_source_steps
    (sourceProgram := schedule.program.vars) blockSchedule.vars.statements ctx globals
    locals referenceLocals (blockSchedule.sourceControlAt block) evaluated
    (schedule.source_decode_at block blockSchedule blockAt)
  have finalValuesAvailable := Symbolic.executeAll_preserves_values_available
    blockSchedule.vars.statements blockSchedule.stack.instructions
    (Symbolic.State.initial blockSchedule.vars.entryLayout) finalState executed
    (Symbolic.State.initial_values_available blockSchedule.vars.statements
      blockSchedule.vars.entryLayout)
  have interpretationsEq := Symbolic.Value.interpret_list_eq_of_lookup_eq finalState.stack
    scheduledLocals referenceLocals (fun value member =>
      finalInterprets.2 value.identifier (finalValuesAvailable.1 value member))
  refine ⟨referenceLocals, finalEnvironment, expectedStack, sourceSteps, ?_, ?_, ?_⟩
  · simpa using targetSteps
  · simpa [stackEq] using expected
  · rw [stackEq] at interpretationsEq
    rw [← interpretationsEq]
    simpa [stackEq] using finalInterprets.1.1

theorem StackSchedule.block_jump_step
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block successor : BlockId)
    (blockSchedule successorSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (successorAt : schedule.blocks[successor.id]? = some successorSchedule)
    (jump : blockSchedule.vars.terminator = .jump successor)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (exitValues : blockSchedule.vars.exitLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ nextLocals,
      Machine.Step Vars.frame (Vars.decoder schedule.program.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals,
            blockSchedule.sourceControlAt block blockSchedule.vars.statements.size⟩ :
              Vars.State)) []
          ((⟨globals, nextLocals, successorSchedule.sourceControlAt successor 0⟩ :
              Vars.State)) ∧
        Machine.Step Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockSchedule.targetControlAt block blockSchedule.stack.instructions.size⟩ []
          ⟨globals, environment, successorSchedule.targetControlAt successor 0⟩ ∧
        successorSchedule.vars.entryLayout.toList.mapM
          (Symbolic.Value.interpret nextLocals) = some environment.stack := by
  have blockBound : block.id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
  have successorBound : successor.id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks) (i := successor.id) successorAt
  have blockGet : schedule.blocks[block.id] = blockSchedule :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have successorGet : schedule.blocks[successor.id] = successorSchedule :=
    (Array.getElem?_eq_some_iff.mp successorAt).2
  have blockAccepted : blockSchedule.check = .ok () := by
    have acceptedAt := (schedule.check_sound accepted).1 block.id blockBound
    simpa [blockGet] using acceptedAt
  have successorAccepted : successorSchedule.check = .ok () := by
    have acceptedAt :=
      (schedule.check_sound accepted).1 successor.id successorBound
    simpa [successorGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockSchedule.check_sound blockAccepted
  obtain ⟨_, _, _, _, _, _, _, successorNodup⟩ :=
    successorSchedule.check_sound successorAccepted
  have targetJump : blockSchedule.stack.terminator = .jump successor := by
    cases targetTerminatorEq : blockSchedule.stack.terminator with
    | halt => simp [jump, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | jump target =>
        have successorEq : successor = target := by
          simpa [jump, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] using
            terminatorsAgree
        have targetEq : target = successor := successorEq.symm
        simp [targetEq]
    | branch =>
        simp [jump, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | iret => simp [jump, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  have layoutAgreement :
      blockSchedule.vars.exitLayout.size = successorSchedule.vars.entryLayout.size := by
    have edgesAt :=
      (schedule.check_sound accepted).2 block.id blockBound
    simpa [blockGet, StackSchedule.blockEdgesAgree, jump,
      StackSchedule.layoutAgreesAt, successorAt] using edgesAt
  obtain ⟨nextLocals, sourceTransfer, nextValues⟩ :=
    Locals.transfer_interprets_renamed_symbolic_values blockSchedule.vars.exitLayout
      successorSchedule.vars.entryLayout environment.stack locals layoutAgreement successorNodup
      exitValues
  have blockBoundaryNames :=
    schedule.block_boundary_names accepted block.id blockSchedule blockAt
  have successorBoundaryNames :=
    schedule.block_boundary_names accepted successor.id successorSchedule successorAt
  have sourceBoundaryTransfer :
      Locals.transfer blockSchedule.vars.outputs successorSchedule.vars.inputs locals =
        .ok ((), nextLocals) := by
    rw [← blockBoundaryNames.2, ← successorBoundaryNames.1]
    exact sourceTransfer
  have stackLength : environment.stack.length = blockSchedule.vars.exitLayout.size := by
    obtain ⟨_, length⟩ :=
      Symbolic.Value.identifiers_mapM_lookup_of_interpretations
        blockSchedule.vars.exitLayout.toList environment.stack locals exitValues
    simpa using length.symm
  refine ⟨nextLocals, ?_, ?_, nextValues⟩
  · apply Sir.step_terminator
      (schedule.source_terminator_at_end block blockSchedule blockAt)
    rw [jump]
    simp [Vars.evaluateTerminator, Vars.jump, StateT.run, bind, Except.bind,
      StateT.bind, StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?, blockAt, successorAt,
      StackSchedule.Block.Source.toBlock, sourceBoundaryTransfer,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition,
      pure, Except.pure]
  · apply Machine.Step.control
    change Stack.control schedule.program.stack environment globals
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size) = _
    unfold Stack.control
    rw [schedule.target_decode_none_at_end block blockSchedule]
    change (schedule.program.stack.terminatorAt
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size)).bind _ = _
    rw [schedule.target_terminator_at_end block blockSchedule blockAt, targetJump]
    simp [Stack.jump,
      Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
      blockAt, successorAt, StackSchedule.Block.Target.toBlock, stackLength,
      layoutAgreement,
      StackSchedule.Block.targetControlAt, Stack.Block.startPosition]

theorem StackSchedule.block_branch_step
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block thenSuccessor elseSuccessor : BlockId) (condition : VarId)
    (conditionValue : Word)
    (blockSchedule successorSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (successorAt : schedule.blocks[(if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id]? = some successorSchedule)
    (branch : blockSchedule.vars.terminator =
      .branch condition thenSuccessor elseSuccessor)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (exitStack : List Word)
    (branchValues : (.variable condition :: blockSchedule.vars.exitLayout.toList).mapM
      (Symbolic.Value.interpret locals) = some (conditionValue :: exitStack)) :
    ∃ nextLocals,
      Machine.Step Vars.frame (Vars.decoder schedule.program.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals,
            blockSchedule.sourceControlAt block blockSchedule.vars.statements.size⟩ :
              Vars.State)) []
          ((⟨globals, nextLocals,
            successorSchedule.sourceControlAt
              (if conditionValue = 0 then elseSuccessor else thenSuccessor) 0⟩ :
              Vars.State)) ∧
        Machine.Step Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, { environment with stack := conditionValue :: exitStack },
            blockSchedule.targetControlAt block blockSchedule.stack.instructions.size⟩ []
          ⟨globals, { environment with stack := exitStack },
            successorSchedule.targetControlAt
              (if conditionValue = 0 then elseSuccessor else thenSuccessor) 0⟩ ∧
        successorSchedule.vars.entryLayout.toList.mapM
          (Symbolic.Value.interpret nextLocals) = some exitStack := by
  have blockBound : block.id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
  have successorBound : (if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks)
      (i := (if conditionValue = 0 then elseSuccessor else thenSuccessor).id) successorAt
  have blockGet : schedule.blocks[block.id] = blockSchedule :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have successorGet : schedule.blocks[(if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id] = successorSchedule :=
    (Array.getElem?_eq_some_iff.mp successorAt).2
  have blockAccepted : blockSchedule.check = .ok () := by
    have acceptedAt := (schedule.check_sound accepted).1 block.id blockBound
    simpa [blockGet] using acceptedAt
  have successorAccepted : successorSchedule.check = .ok () := by
    have acceptedAt :=
      (schedule.check_sound accepted).1
        (if conditionValue = 0 then elseSuccessor else thenSuccessor).id successorBound
    simpa [successorGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockSchedule.check_sound blockAccepted
  obtain ⟨_, _, _, _, _, _, _, successorNodup⟩ :=
    successorSchedule.check_sound successorAccepted
  have targetBranch : blockSchedule.stack.terminator =
      .branch thenSuccessor elseSuccessor := by
    cases targetTerminatorEq : blockSchedule.stack.terminator with
    | halt => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | jump => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | branch targetThen targetElse =>
        have targets : thenSuccessor = targetThen ∧ elseSuccessor = targetElse := by
          simpa [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] using terminatorsAgree
        simp [targets.1, targets.2]
    | iret => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  have edgeAgreements :
      schedule.layoutAgreesAt blockSchedule.vars.exitLayout thenSuccessor = true ∧
        schedule.layoutAgreesAt blockSchedule.vars.exitLayout elseSuccessor = true := by
    have edgesAt :=
      (schedule.check_sound accepted).2 block.id blockBound
    simpa [blockGet, StackSchedule.blockEdgesAgree, branch] using edgesAt
  have layoutAgreement :
      blockSchedule.vars.exitLayout.size = successorSchedule.vars.entryLayout.size := by
    by_cases zero : conditionValue = 0
    · have elseAt : schedule.blocks[elseSuccessor.id]? = some successorSchedule := by
        simpa [zero] using successorAt
      simpa [StackSchedule.layoutAgreesAt, elseAt] using edgeAgreements.2
    · have thenAt : schedule.blocks[thenSuccessor.id]? = some successorSchedule := by
        simpa [zero] using successorAt
      simpa [StackSchedule.layoutAgreesAt, thenAt] using edgeAgreements.1
  have interpretations :
      Symbolic.Value.interpret locals (.variable condition) = some conditionValue ∧
        blockSchedule.vars.exitLayout.toList.mapM (Symbolic.Value.interpret locals) =
          some exitStack := by
    cases conditionInterpretation :
        Symbolic.Value.interpret locals (.variable condition) with
    | none => simp [conditionInterpretation] at branchValues
    | some value =>
        cases exitValues : blockSchedule.vars.exitLayout.toList.mapM
            (Symbolic.Value.interpret locals) with
        | none => simp [conditionInterpretation, exitValues] at branchValues
        | some values =>
            simp [conditionInterpretation, exitValues] at branchValues
            rcases branchValues with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩
  have conditionInterpretation := interpretations.1
  have exitValues := interpretations.2
  have conditionLookup : locals.lookup condition = .ok conditionValue := by
    rw [Symbolic.Value.interpret, Symbolic.Value.identifier] at conditionInterpretation
    simp [Locals.lookup, conditionInterpretation]
  obtain ⟨nextLocals, sourceTransfer, nextValues⟩ :=
    Locals.transfer_interprets_renamed_symbolic_values blockSchedule.vars.exitLayout
      successorSchedule.vars.entryLayout exitStack locals layoutAgreement successorNodup exitValues
  have blockBoundaryNames :=
    schedule.block_boundary_names accepted block.id blockSchedule blockAt
  have successorBoundaryNames := schedule.block_boundary_names accepted
    (if conditionValue = 0 then elseSuccessor else thenSuccessor).id
    successorSchedule successorAt
  have sourceBoundaryTransfer :
      Locals.transfer blockSchedule.vars.outputs successorSchedule.vars.inputs locals =
        .ok ((), nextLocals) := by
    rw [← blockBoundaryNames.2, ← successorBoundaryNames.1]
    exact sourceTransfer
  have stackLength : exitStack.length = blockSchedule.vars.exitLayout.size := by
    obtain ⟨_, length⟩ :=
      Symbolic.Value.identifiers_mapM_lookup_of_interpretations
        blockSchedule.vars.exitLayout.toList exitStack locals exitValues
    simpa using length.symm
  refine ⟨nextLocals, ?_, ?_, nextValues⟩
  · apply Sir.step_terminator
      (schedule.source_terminator_at_end block blockSchedule blockAt)
    rw [branch]
    simp [Vars.evaluateTerminator, Locals.lookupM, conditionLookup, Vars.jump, StateT.run, bind, Except.bind,
      StateT.bind, StateT.lift, StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?, blockAt, successorAt,
      StackSchedule.Block.Source.toBlock, sourceBoundaryTransfer,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition,
      pure, Except.pure]
  · apply Machine.Step.control
    change Stack.control schedule.program.stack
      { environment with stack := conditionValue :: exitStack } globals
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size) = _
    unfold Stack.control
    rw [schedule.target_decode_none_at_end block blockSchedule]
    change (schedule.program.stack.terminatorAt
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size)).bind _ = _
    rw [schedule.target_terminator_at_end block blockSchedule blockAt, targetBranch]
    simp [Stack.jump,
      Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
      blockAt, successorAt, StackSchedule.Block.Target.toBlock, stackLength,
      layoutAgreement, StackSchedule.Block.targetControlAt,
      Stack.Block.startPosition]

theorem StackSchedule.block_halted_steps
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (halt : blockSchedule.vars.terminator = .halt)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals finalEnvironment,
      Machine.Steps Vars.frame (Vars.decoder schedule.program.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockSchedule.sourceControlAt block 0⟩ : Vars.State))
          []
          ((⟨globals, finalLocals, .halted⟩ : Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockSchedule.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩ := by
  have blockBound : block.id < schedule.blocks.size :=
    of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
  have blockGet : schedule.blocks[block.id] = blockSchedule :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted : blockSchedule.check = .ok () := by
    have acceptedAt := (schedule.check_sound accepted).1 block.id blockBound
    simpa [blockGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockSchedule.check_sound blockAccepted
  have targetHalt : blockSchedule.stack.terminator = .halt := by
    cases target : blockSchedule.stack.terminator with
    | halt => rfl
    | jump => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | branch => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | iret => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  obtain ⟨finalLocals, finalEnvironment, _, sourceSteps, targetSteps, _, _⟩ :=
    schedule.block_execute_steps accepted block blockSchedule blockAt ctx globals locals
      environment stackValues
  have sourceHalt : Machine.Step Vars.frame
      (Vars.decoder schedule.program.vars) Machine.memoryPolicy ctx
      ((⟨globals, finalLocals,
        blockSchedule.sourceControlAt block blockSchedule.vars.statements.size⟩ :
          Vars.State)) []
      ((⟨globals, finalLocals, .halted⟩ : Vars.State)) := by
    exact Sir.step_terminator (schedule.source_terminator_at_end block blockSchedule blockAt)
      (by rw [halt]; rfl)
  have targetHaltStep : Machine.Step Stack.frame
      (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
      ⟨globals, finalEnvironment,
        blockSchedule.targetControlAt block blockSchedule.stack.instructions.size⟩ []
      ⟨globals, finalEnvironment, .halted⟩ := by
    apply Machine.Step.control
    change Stack.control schedule.program.stack finalEnvironment globals
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size) = _
    unfold Stack.control
    rw [schedule.target_decode_none_at_end block blockSchedule]
    change (schedule.program.stack.terminatorAt
      (blockSchedule.targetControlAt block blockSchedule.stack.instructions.size)).bind _ = _
    rw [schedule.target_terminator_at_end block blockSchedule blockAt, targetHalt]
    rfl
  exact ⟨finalLocals, finalEnvironment, sourceSteps.tail sourceHalt,
    targetSteps.tail targetHaltStep⟩

theorem StackSchedule.block_transition_steps
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    (∃ finalLocals finalEnvironment,
      Machine.Steps Vars.frame (Vars.decoder schedule.program.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockSchedule.sourceControlAt block 0⟩ :
            Vars.State)) []
          ((⟨globals, finalLocals, .halted⟩ : Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, environment, blockSchedule.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩) ∨
      ∃ (successor : BlockId)
          (successorSchedule : StackSchedule.Block)
          (nextLocals : Locals) (nextEnvironment : Stack.Environment),
        schedule.blocks[successor.id]? = some successorSchedule ∧
          Machine.Steps Vars.frame (Vars.decoder schedule.program.vars)
            Machine.memoryPolicy ctx
            ((⟨globals, locals, blockSchedule.sourceControlAt block 0⟩ :
              Vars.State)) []
            ((⟨globals, nextLocals, successorSchedule.sourceControlAt successor 0⟩ :
              Vars.State)) ∧
          NonemptySourcePath schedule.program.vars ctx
            ⟨globals, locals, blockSchedule.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorSchedule.sourceControlAt successor 0⟩ ∧
          Machine.Steps Stack.frame
            (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
            ⟨globals, environment, blockSchedule.targetControlAt block 0⟩ []
            ⟨globals, nextEnvironment,
              successorSchedule.targetControlAt successor 0⟩ ∧
          NonemptyTargetPath schedule.program.stack ctx
            ⟨globals, environment, blockSchedule.targetControlAt block 0⟩
            ⟨globals, nextEnvironment,
              successorSchedule.targetControlAt successor 0⟩ ∧
          successorSchedule.vars.entryLayout.toList.mapM
            (Symbolic.Value.interpret nextLocals) = some nextEnvironment.stack := by
  cases terminator : blockSchedule.vars.terminator with
  | halt =>
      obtain ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩ :=
        schedule.block_halted_steps accepted block blockSchedule blockAt terminator ctx
          globals locals environment stackValues
      exact .inl ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩
  | jump successor =>
      obtain ⟨finalLocals, finalEnvironment, expectedStack, sourceSteps, targetSteps,
          expected, finalStack⟩ :=
        schedule.block_execute_steps accepted block blockSchedule blockAt ctx globals locals
          environment stackValues
      have exitValues : blockSchedule.vars.exitLayout.toList.mapM
          (Symbolic.Value.interpret finalLocals) = some finalEnvironment.stack := by
        have expectedStackEq : expectedStack = blockSchedule.vars.exitLayout.toList := by
          simpa [terminator, StackSchedule.Block.finalStack] using expected.symm
        simpa [expectedStackEq] using finalStack
      have blockBound : block.id < schedule.blocks.size :=
        of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
      have blockGet : schedule.blocks[block.id] = blockSchedule :=
        (Array.getElem?_eq_some_iff.mp blockAt).2
      have edgeAgreement : schedule.layoutAgreesAt blockSchedule.vars.exitLayout successor =
          true := by
        have edgesAt :=
          (schedule.check_sound accepted).2 block.id blockBound
        simpa [blockGet, StackSchedule.blockEdgesAgree, terminator] using edgesAt
      obtain ⟨successorSchedule, successorAt⟩ :
          ∃ successorSchedule, schedule.blocks[successor.id]? = some successorSchedule := by
        cases successorAt : schedule.blocks[successor.id]? with
        | none => simp [StackSchedule.layoutAgreesAt, successorAt] at edgeAgreement
        | some successorSchedule => exact ⟨successorSchedule, rfl⟩
      obtain ⟨nextLocals, sourceStep, targetStep, nextValues⟩ :=
        schedule.block_jump_step accepted block successor blockSchedule
          successorSchedule blockAt successorAt terminator ctx globals finalLocals
          finalEnvironment exitValues
      exact .inr ⟨successor, successorSchedule, nextLocals, finalEnvironment, successorAt,
        sourceSteps.tail sourceStep,
        SourcePath.tail_nonempty (SourcePath.of_steps sourceSteps rfl) sourceStep,
        targetSteps.tail targetStep,
        TargetPath.tail_nonempty (TargetPath.of_steps targetSteps rfl) targetStep, nextValues⟩
  | branch condition thenSuccessor elseSuccessor =>
      obtain ⟨finalLocals, finalEnvironment, expectedStack, sourceSteps, targetSteps,
          expected, finalStack⟩ :=
        schedule.block_execute_steps accepted block blockSchedule blockAt ctx globals locals
          environment stackValues
      have expectedStackEq : expectedStack =
          .variable condition :: blockSchedule.vars.exitLayout.toList := by
        simpa [terminator, StackSchedule.Block.finalStack] using expected.symm
      have branchValues :
          (.variable condition :: blockSchedule.vars.exitLayout.toList).mapM
              (Symbolic.Value.interpret finalLocals) = some finalEnvironment.stack := by
        simpa [expectedStackEq] using finalStack
      cases conditionInterpretation : Symbolic.Value.interpret finalLocals (.variable condition) with
      | none => simp [conditionInterpretation] at branchValues
      | some conditionValue =>
          cases exitInterpretations : blockSchedule.vars.exitLayout.toList.mapM
              (Symbolic.Value.interpret finalLocals) with
          | none => simp [conditionInterpretation, exitInterpretations] at branchValues
          | some exitStack =>
              have stackEq : finalEnvironment.stack = conditionValue :: exitStack := by
                simpa [conditionInterpretation, exitInterpretations] using branchValues.symm
              have concreteBranchValues :
                  (.variable condition :: blockSchedule.vars.exitLayout.toList).mapM
                      (Symbolic.Value.interpret finalLocals) =
                    some (conditionValue :: exitStack) := by
                rw [← stackEq]
                exact branchValues
              have blockBound : block.id < schedule.blocks.size :=
                of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
              have blockGet : schedule.blocks[block.id] = blockSchedule :=
                (Array.getElem?_eq_some_iff.mp blockAt).2
              have edgeAgreements :
                  schedule.layoutAgreesAt blockSchedule.vars.exitLayout thenSuccessor = true ∧
                    schedule.layoutAgreesAt blockSchedule.vars.exitLayout elseSuccessor = true := by
                have edgesAt :=
                  (schedule.check_sound accepted).2 block.id blockBound
                simpa [blockGet, StackSchedule.blockEdgesAgree, terminator] using edgesAt
              have selectedAgreement : schedule.layoutAgreesAt blockSchedule.vars.exitLayout
                    (if conditionValue = 0 then elseSuccessor else thenSuccessor) = true := by
                by_cases zero : conditionValue = 0
                · simpa [zero] using edgeAgreements.2
                · simpa [zero] using edgeAgreements.1
              obtain ⟨successorSchedule, successorAt⟩ : ∃ successorSchedule,
                  schedule.blocks[(if conditionValue = 0 then elseSuccessor
                    else thenSuccessor).id]? = some successorSchedule := by
                cases successorAt : schedule.blocks[(if conditionValue = 0 then elseSuccessor
                    else thenSuccessor).id]? with
                | none =>
                    simp [StackSchedule.layoutAgreesAt, successorAt] at selectedAgreement
                | some successorSchedule => exact ⟨successorSchedule, rfl⟩
              obtain ⟨nextLocals, sourceStep, targetStep, nextValues⟩ :=
                schedule.block_branch_step accepted block thenSuccessor elseSuccessor condition
                  conditionValue blockSchedule successorSchedule blockAt successorAt
                  terminator ctx globals finalLocals finalEnvironment exitStack concreteBranchValues
              have finalEnvironmentWithStack :
                  { finalEnvironment with stack := conditionValue :: exitStack } =
                    finalEnvironment := by
                cases finalEnvironment
                simp_all
              rw [finalEnvironmentWithStack] at targetStep
              exact .inr ⟨if conditionValue = 0 then elseSuccessor else thenSuccessor,
                successorSchedule, nextLocals, { finalEnvironment with stack := exitStack },
                successorAt, sourceSteps.tail sourceStep,
                SourcePath.tail_nonempty (SourcePath.of_steps sourceSteps rfl) sourceStep,
                targetSteps.tail targetStep,
                TargetPath.tail_nonempty (TargetPath.of_steps targetSteps rfl) targetStep,
                nextValues⟩
  | iret =>
      have blockBound : block.id < schedule.blocks.size :=
        of_getElem?_eq_some (c := schedule.blocks) (i := block.id) blockAt
      have blockGet : schedule.blocks[block.id] = blockSchedule :=
        (Array.getElem?_eq_some_iff.mp blockAt).2
      have blockAccepted :=
        (schedule.check_sound accepted).1 block.id blockBound
      have blockAccepted' : blockSchedule.check = .ok () := by
        simpa [blockGet] using blockAccepted
      obtain ⟨_, expectedStack, _, expected, _⟩ :=
        blockSchedule.check_sound blockAccepted'
      simp [terminator, StackSchedule.Block.finalStack] at expected

theorem StackSchedule.block_transition_paths
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    (block : BlockId) (blockSchedule : StackSchedule.Block)
    (blockAt : schedule.blocks[block.id]? = some blockSchedule)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockSchedule.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    (∃ finalLocals finalEnvironment,
      SourcePath schedule.program.vars ctx
          ⟨globals, locals, blockSchedule.sourceControlAt block 0⟩
          ⟨globals, finalLocals, .halted⟩ ∧
        Machine.Steps Stack.frame
          (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
          ⟨globals, environment, blockSchedule.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩) ∨
      ∃ (successor : BlockId)
          (successorSchedule : StackSchedule.Block)
          (nextLocals : Locals) (nextEnvironment : Stack.Environment),
        schedule.blocks[successor.id]? = some successorSchedule ∧
          SourcePath schedule.program.vars ctx
            ⟨globals, locals, blockSchedule.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorSchedule.sourceControlAt successor 0⟩ ∧
          NonemptySourcePath schedule.program.vars ctx
            ⟨globals, locals, blockSchedule.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorSchedule.sourceControlAt successor 0⟩ ∧
          Machine.Steps Stack.frame
            (Stack.decoder schedule.program.stack) Machine.memoryPolicy ctx
            ⟨globals, environment, blockSchedule.targetControlAt block 0⟩ []
            ⟨globals, nextEnvironment,
              successorSchedule.targetControlAt successor 0⟩ ∧
          NonemptyTargetPath schedule.program.stack ctx
            ⟨globals, environment, blockSchedule.targetControlAt block 0⟩
            ⟨globals, nextEnvironment,
              successorSchedule.targetControlAt successor 0⟩ ∧
          successorSchedule.vars.entryLayout.toList.mapM
            (Symbolic.Value.interpret nextLocals) = some nextEnvironment.stack := by
  rcases schedule.block_transition_steps accepted block blockSchedule blockAt ctx globals
      locals environment stackValues with halted | transitioned
  · obtain ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩ := halted
    exact .inl ⟨finalLocals, finalEnvironment, SourcePath.of_steps sourceSteps rfl, targetSteps⟩
  · obtain ⟨successor, successorSchedule, nextLocals, nextEnvironment, successorAt,
        sourceSteps, sourceNonempty, targetSteps, targetNonempty, nextValues⟩ := transitioned
    exact .inr ⟨successor, successorSchedule, nextLocals, nextEnvironment, successorAt,
      SourcePath.of_steps sourceSteps rfl, sourceNonempty, targetSteps, targetNonempty,
      nextValues⟩

end Sir.Lowering
