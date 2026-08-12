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
              (Stack.Proofs.decoder_exclusive program) (Stack.Proofs.decoder_terminal program)
              noMload first [] _ second with ⟨_, middleEq⟩ | divergence
          · subst middleEq
            exact inductionHypothesis suffix finalStuck
          · obtain ⟨pre, firstEvent, firstRest, secondEvent, secondRest,
                firstTrace, _, _, _⟩ := divergence
            simp at firstTrace

def StackSchedule.Block.sourceControlAt
    (certificate : StackSchedule.Block) (block : BlockId) (index : Nat) :
    Machine.MachineControl :=
  .running {
    fn := ⟨0⟩
    block
    position := certificate.vars.toBlock.absoluteToPosition index }

def StackSchedule.Block.targetControlAt
    (certificate : StackSchedule.Block) (block : BlockId) (index : Nat) :
    Machine.MachineControl :=
  .running {
    fn := ⟨0⟩
    block
    position := certificate.stack.toBlock.absoluteToPosition index }

theorem StackSchedule.source_decode_at
    (certificate : StackSchedule) (block : BlockId)
    (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (index : Nat) (statement : Vars.Stmt)
    (statementAt : blockCertificate.vars.statements[index]? = some statement) :
    certificate.vars.decodeStmt (blockCertificate.sourceControlAt block index) =
      some (blockCertificate.sourceControlAt block (index + 1), statement) := by
  have indexBound : index < blockCertificate.vars.statements.size :=
    of_getElem?_eq_some (c := blockCertificate.vars.statements) (i := index) statementAt
  have statementGet : blockCertificate.vars.statements[index] = statement :=
    (Array.getElem?_eq_some_iff.mp statementAt).2
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  unfold StackSchedule.Block.sourceControlAt
    StackSchedule.vars Vars.Program.decodeStmt
  simp [Vars.Program.block?, Vars.Program.function?, Vars.Function.block?, blockBound,
    blockGet, StackSchedule.Block.Source.toBlock, Vars.Block.absoluteToPosition,
    indexBound, statementGet]

theorem StackSchedule.target_decode_at
    (certificate : StackSchedule) (block : BlockId)
    (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (index : Nat) (instruction : Stack.Instr)
    (instructionAt : blockCertificate.stack.instructions[index]? = some instruction) :
    certificate.stack.decodeInstruction (blockCertificate.targetControlAt block index) =
      some (blockCertificate.targetControlAt block (index + 1), instruction) := by
  have indexBound : index < blockCertificate.stack.instructions.size :=
    of_getElem?_eq_some (c := blockCertificate.stack.instructions) (i := index) instructionAt
  have instructionGet : blockCertificate.stack.instructions[index] = instruction :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  unfold StackSchedule.Block.targetControlAt
    StackSchedule.stack Stack.Program.decodeInstruction
  simp [Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
    blockBound, StackSchedule.Block.Target.toBlock,
    Stack.Block.absoluteToPosition]
  rw [blockGet]
  simp [indexBound, instructionGet]

theorem StackSchedule.source_terminator_at_end
    (certificate : StackSchedule) (block : BlockId)
    (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate) :
    certificate.vars.terminatorAt
      (blockCertificate.sourceControlAt block blockCertificate.vars.statements.size) =
        some blockCertificate.vars.terminator := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  unfold StackSchedule.Block.sourceControlAt
    StackSchedule.vars Vars.Program.terminatorAt
  simp [Vars.Program.block?, Vars.Program.function?, Vars.Function.block?, blockBound, blockGet,
    StackSchedule.Block.Source.toBlock, Vars.Block.absoluteToPosition]

theorem StackSchedule.target_terminator_at_end
    (certificate : StackSchedule) (block : BlockId)
    (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate) :
    certificate.stack.terminatorAt
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size) =
        some blockCertificate.stack.terminator := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  unfold StackSchedule.Block.targetControlAt
    StackSchedule.stack Stack.Program.terminatorAt
  simp [Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
    blockBound, StackSchedule.Block.Target.toBlock,
    Stack.Block.absoluteToPosition]
  rw [blockGet]

theorem StackSchedule.target_decode_none_at_end
    (certificate : StackSchedule) (block : BlockId)
    (blockCertificate : StackSchedule.Block) :
    certificate.stack.decodeInstruction
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size) = none := by
  unfold StackSchedule.Block.targetControlAt
    Stack.Program.decodeInstruction
  simp [StackSchedule.Block.Target.toBlock, Stack.Block.absoluteToPosition]

theorem StackSchedule.entry_block
    (certificate : StackSchedule) (accepted : certificate.check = true) :
    ∃ blockCertificate,
      certificate.blocks[certificate.entry.id]? = some blockCertificate ∧
        blockCertificate.vars.entryLayout.toList.Nodup := by
  have entryBound := (certificate.check_sound accepted).1
  let blockCertificate := certificate.blocks[certificate.entry.id]
  have blockAt : certificate.blocks[certificate.entry.id]? = some blockCertificate := by
    rw [Array.getElem?_eq_getElem entryBound]
  have blockGet : certificate.blocks[certificate.entry.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted : blockCertificate.check = true := by
    have acceptedAt :=
      (certificate.check_sound accepted).2.1 certificate.entry.id entryBound
    simpa [blockGet] using acceptedAt
  obtain ⟨_, _, _, _, _, _, _, entryNodup⟩ := blockCertificate.check_sound blockAccepted
  exact ⟨blockCertificate, blockAt, entryNodup⟩

theorem StackSchedule.entry_states
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[certificate.entry.id]? = some blockCertificate)
    (globals : Globals) (args : Array Word) (locals : Locals)
    (bound : Locals.bindParams (blockCertificate.vars.entryLayout.map Symbolic.Value.identifier) args =
      .ok locals) :
    (Vars.decoder certificate.vars).entry ⟨0⟩ globals args =
        some ((⟨globals, locals,
          blockCertificate.sourceControlAt certificate.entry 0⟩ : Vars.State)) ∧
      (Stack.decoder certificate.stack).entry ⟨0⟩ globals args =
        some ⟨globals, { Stack.Environment.empty with stack := args.toList },
          blockCertificate.targetControlAt certificate.entry 0⟩ ∧
      blockCertificate.vars.entryLayout.toList.mapM (Symbolic.Value.interpret locals) =
        some args.toList := by
  obtain ⟨entryCertificate, entryAt, entryNodup⟩ := certificate.entry_block accepted
  have certificateEq : entryCertificate = blockCertificate := by
    rw [blockAt] at entryAt
    exact Option.some.inj entryAt.symm
  subst entryCertificate
  have boundaryNames := certificate.block_boundary_names accepted certificate.entry.id
    blockCertificate blockAt
  have argumentSize : args.size = blockCertificate.vars.entryLayout.size := by
    by_contra different
    have sizeMismatch : (blockCertificate.vars.entryLayout.size != args.size) = true :=
      bne_iff_ne.mpr (Ne.symm different)
    simp [Locals.bindParams, Locals.bindValues, sizeMismatch, bind, Except.bind] at bound
  refine ⟨?_, ?_, Locals.bindParams_interprets_symbolic_values
    blockCertificate.vars.entryLayout args locals entryNodup bound⟩
  · simp [Vars.decoder, StackSchedule.vars,
      Vars.Program.callState?, Vars.Program.function?, Vars.Function.block?, blockAt,
      StackSchedule.Block.Source.toBlock, ← boundaryNames.1, bound,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition]
  · simp [Stack.decoder, Stack.entry, StackSchedule.stack,
      Stack.Program.function?, Stack.Function.block?, blockAt,
      StackSchedule.Block.Target.toBlock, argumentSize,
      StackSchedule.Block.targetControlAt, Stack.Block.startPosition,
      Stack.Environment.empty]

theorem StackSchedule.source_step_trace_empty
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (ctx : CallContext) {state final : Machine.State Vars.frame} {trace : Trace}
    (step : Machine.Step Vars.frame (Vars.decoder certificate.vars)
      Machine.memoryPolicy ctx state trace final) :
    trace = [] := by
  cases step with
  | operation hdecode fires =>
      change Vars.decode certificate.vars state.control = _ at hdecode
      obtain ⟨statement, statementAt, decoded⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨symbolicOperation, supported⟩ :=
        certificate.vars_program_statements_supported accepted statement
          (Vars.Program.decodeStmt_mem statementAt)
      cases statement with
      | assign result expression =>
          cases expression with
          | constant value =>
              simp [Vars.decodeStatement, Vars.decodeExpression] at decoded
              obtain ⟨rfl, rfl, rfl⟩ := decoded
              cases fires with
              | next admissible fetch execute store =>
                  simp [Machine.Operation.execute] at execute
                  exact execute.2.2
          | var source =>
              simp [Vars.decodeStatement, Vars.decodeExpression] at decoded
              obtain ⟨rfl, rfl, rfl⟩ := decoded
              cases fires with
              | next admissible fetch execute store =>
                  cases sourceAt : state.environment.lookup source with
                  | error error =>
                      simp [Vars.frame, sourceAt, bind, Except.bind] at fetch
                  | ok value =>
                      simp [Vars.frame, sourceAt, bind, Except.bind, pure, Except.pure]
                        at fetch
                      subst_vars
                      simp [Machine.Operation.execute, pure, Except.pure] at execute
                      exact execute.2.2
          | add lhs rhs =>
              simp [Vars.decodeStatement, Vars.decodeExpression] at decoded
              obtain ⟨rfl, rfl, rfl⟩ := decoded
              cases fires with
              | next admissible fetch execute store =>
                  cases lhsAt : state.environment.lookup lhs with
                  | error error => simp [Vars.frame, lhsAt, bind, Except.bind] at fetch
                  | ok lhsValue =>
                      cases rhsAt : state.environment.lookup rhs with
                      | error error =>
                          simp [Vars.frame, lhsAt, rhsAt, bind, Except.bind] at fetch
                      | ok rhsValue =>
                          simp [Vars.frame, lhsAt, rhsAt, bind, Except.bind, pure,
                            Except.pure] at fetch
                          subst_vars
                          simp [Machine.Operation.execute, pure, Except.pure] at execute
                          exact execute.2.2
          | lt lhs rhs =>
              simp [Vars.decodeStatement, Vars.decodeExpression] at decoded
              obtain ⟨rfl, rfl, rfl⟩ := decoded
              cases fires with
              | next admissible fetch execute store =>
                  cases lhsAt : state.environment.lookup lhs with
                  | error error => simp [Vars.frame, lhsAt, bind, Except.bind] at fetch
                  | ok lhsValue =>
                      cases rhsAt : state.environment.lookup rhs with
                      | error error =>
                          simp [Vars.frame, lhsAt, rhsAt, bind, Except.bind] at fetch
                      | ok rhsValue =>
                          simp [Vars.frame, lhsAt, rhsAt, bind, Except.bind, pure,
                            Except.pure] at fetch
                          subst_vars
                          simp [Machine.Operation.execute, pure, Except.pure] at execute
                          exact execute.2.2
          | sload key => simp [Symbolic.operationOf] at supported
      | sstore => simp [Symbolic.operationOf] at supported
      | gas => simp [Symbolic.operationOf] at supported
      | call => simp [Symbolic.operationOf] at supported
      | malloc => simp [Symbolic.operationOf] at supported
      | mallocUninit => simp [Symbolic.operationOf] at supported
      | mstore32 => simp [Symbolic.operationOf] at supported
      | mload32 => simp [Symbolic.operationOf] at supported
      | icall => simp [Symbolic.operationOf] at supported
  | operationHalted hdecode fires =>
      exact (Machine.OperandFrame.firesHalt_false _ fires).elim
  | internalCall hdecode fetch evaluation resume =>
      change Vars.decode certificate.vars state.control = _ at hdecode
      obtain ⟨statement, statementAt, decoded⟩ := Vars.decode_inv.mp hdecode
      obtain ⟨symbolicOperation, supported⟩ :=
        certificate.vars_program_statements_supported accepted statement
          (Vars.Program.decodeStmt_mem statementAt)
      cases statement with
      | assign result expression =>
          cases expression <;>
            simp [Symbolic.operationOf] at supported <;>
            simp [Vars.decodeStatement, Vars.decodeExpression] at decoded
      | sstore => simp [Symbolic.operationOf] at supported
      | gas => simp [Symbolic.operationOf] at supported
      | call => simp [Symbolic.operationOf] at supported
      | malloc => simp [Symbolic.operationOf] at supported
      | mallocUninit => simp [Symbolic.operationOf] at supported
      | mstore32 => simp [Symbolic.operationOf] at supported
      | mload32 => simp [Symbolic.operationOf] at supported
      | icall => simp [Symbolic.operationOf] at supported
  | control controlStep =>
      change Vars.control certificate.vars state.environment state.globals state.control = _
        at controlStep
      obtain ⟨terminator, nextState, terminatorAt, evaluated, traceEmpty, environmentEq,
        globalsEq, controlEq⟩ := Vars.control_inv.mp controlStep
      exact traceEmpty

theorem StackSchedule.source_steps_path
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (ctx : CallContext) {state final : Vars.State} {trace : Trace}
    (steps : Vars.Steps certificate.vars ctx state trace final) :
    SourcePath certificate.vars ctx state final ∧ trace = [] := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ =>
      SourcePath certificate.vars ctx state final ∧ trace = [])
    (fun state => ⟨.refl state, rfl⟩)
    (fun start next inductionHypothesis => by
      obtain ⟨path, traceEmpty⟩ := inductionHypothesis
      have nextTraceEmpty := certificate.source_step_trace_empty accepted ctx next
      subst_vars
      exact ⟨path.tail next, by simp⟩)
    steps

theorem StackSchedule.target_step_trace_empty
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (ctx : CallContext)
    {state final : Machine.State Stack.frame} {trace : Trace}
    (step : Machine.Step Stack.frame
      (Stack.decoder certificate.stack) Machine.memoryPolicy ctx state trace final) :
    trace = [] := by
  cases step with
  | operation hdecode fires =>
      rename_i stepOperation src dst next env' globals'
      change Stack.decode certificate.stack state.control = _ at hdecode
      cases instructionDecode : certificate.stack.decodeInstruction state.control with
      | none => simp [Stack.decode, instructionDecode] at hdecode
      | some decoded =>
          obtain ⟨instructionNext, instruction⟩ := decoded
          cases instruction with
          | op operation =>
              simp [Stack.decode, instructionDecode] at hdecode
              have operationEq : operation = stepOperation := hdecode.1.1
              subst stepOperation
              rcases certificate.target_decoded_operation_supported accepted state.control
                  instructionNext operation instructionDecode with ⟨value, rfl⟩ | rfl | rfl | rfl
              · cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    simp [Machine.Operation.execute] at execute
                    exact execute.2.2
              · cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    cases operandAt : operands[0]? with
                    | none =>
                        simp [Machine.Operation.execute, operandAt] at execute
                    | some operand =>
                        simp [Machine.Operation.execute, operandAt, pure, Except.pure] at execute
                        exact execute.2.2
              · cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    cases lhsAt : operands[0]? with
                    | none =>
                        simp [Machine.Operation.execute, lhsAt] at execute
                    | some lhs =>
                        cases rhsAt : operands[1]? with
                        | none =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt]
                              at execute
                        | some rhs =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt, pure, Except.pure]
                              at execute
                            exact execute.2.2
              · cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    cases lhsAt : operands[0]? with
                    | none =>
                        simp [Machine.Operation.execute, lhsAt] at execute
                    | some lhs =>
                        cases rhsAt : operands[1]? with
                        | none =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt] at execute
                        | some rhs =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt, pure, Except.pure]
                              at execute
                            exact execute.2.2
          | flippedOp operation =>
              rcases certificate.target_decoded_flipped_operation_supported accepted state.control
                  instructionNext operation instructionDecode with rfl | rfl
              · simp [Stack.decode, instructionDecode]
                  at hdecode
                have operationEq : Machine.Operation.add = stepOperation := hdecode.1.1
                subst stepOperation
                cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    cases lhsAt : operands[0]? with
                    | none => simp [Machine.Operation.execute, lhsAt] at execute
                    | some lhs =>
                        cases rhsAt : operands[1]? with
                        | none => simp [Machine.Operation.execute, lhsAt, rhsAt] at execute
                        | some rhs =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt, pure, Except.pure]
                              at execute
                            exact execute.2.2
              · simp [Stack.decode, instructionDecode]
                  at hdecode
                have operationEq : Machine.Operation.lt = stepOperation := hdecode.1.1
                subst stepOperation
                cases fires with
                | next admissible fetch execute store =>
                    rename_i operands results oracle
                    cases lhsAt : operands[0]? with
                    | none => simp [Machine.Operation.execute, lhsAt] at execute
                    | some lhs =>
                        cases rhsAt : operands[1]? with
                        | none => simp [Machine.Operation.execute, lhsAt, rhsAt] at execute
                        | some rhs =>
                            simp [Machine.Operation.execute, lhsAt, rhsAt, pure, Except.pure]
                              at execute
                            exact execute.2.2
          | swap depth => simp [Stack.decode, instructionDecode] at hdecode
          | exchange firstDepth secondDepth =>
              simp [Stack.decode, instructionDecode] at hdecode
          | dup depth => simp [Stack.decode, instructionDecode] at hdecode
          | pop => simp [Stack.decode, instructionDecode] at hdecode
          | icall callee argumentCount resultCount =>
              simp [Stack.decode, instructionDecode] at hdecode
          | store slot => simp [Stack.decode, instructionDecode] at hdecode
          | load slot => simp [Stack.decode, instructionDecode] at hdecode
  | operationHalted hdecode fires =>
      exact (Machine.OperandFrame.firesHalt_false _ fires).elim
  | internalCall hdecode fetch evaluation resume =>
      change Stack.decode certificate.stack state.control = _ at hdecode
      cases instructionDecode : certificate.stack.decodeInstruction state.control with
      | none => simp [Stack.decode, instructionDecode] at hdecode
      | some decoded =>
          obtain ⟨instructionNext, instruction⟩ := decoded
          cases instruction with
          | op operation => simp [Stack.decode, instructionDecode] at hdecode
          | flippedOp operation =>
              rcases certificate.target_decoded_flipped_operation_supported accepted state.control
                  instructionNext operation instructionDecode with rfl | rfl <;>
                simp [Stack.decode, instructionDecode] at hdecode
          | swap depth => simp [Stack.decode, instructionDecode] at hdecode
          | exchange firstDepth secondDepth =>
              simp [Stack.decode, instructionDecode] at hdecode
          | dup depth => simp [Stack.decode, instructionDecode] at hdecode
          | pop => simp [Stack.decode, instructionDecode] at hdecode
          | icall callee argumentCount resultCount =>
              simp [Stack.decode, instructionDecode] at hdecode
              exact ((certificate.target_decoded_instruction_excludes_internal_calls accepted
                state.control instructionNext (.icall callee argumentCount resultCount)
                instructionDecode) callee argumentCount resultCount rfl).elim
          | store slot => simp [Stack.decode, instructionDecode] at hdecode
          | load slot => simp [Stack.decode, instructionDecode] at hdecode
  | control controlStep =>
      change Stack.control certificate.stack state.environment state.globals
        state.control = _ at controlStep
      cases instructionDecode : certificate.stack.decodeInstruction state.control with
      | some decoded =>
          obtain ⟨instructionNext, instruction⟩ := decoded
          cases instruction with
          | swap depth =>
              cases stackAt : Stack.exchange state.environment.stack 0 depth <;>
                simp [Stack.control, instructionDecode, stackAt] at controlStep
              exact controlStep.1
          | exchange firstDepth secondDepth =>
              by_cases depthsEqual : firstDepth = secondDepth
              · simp [Stack.control, instructionDecode, depthsEqual] at controlStep
              · cases stackAt : Stack.exchange state.environment.stack firstDepth
                    secondDepth <;>
                  simp [Stack.control, instructionDecode, depthsEqual, stackAt] at controlStep
                exact controlStep.1
          | dup depth =>
              cases valueAt : state.environment.stack[depth]? <;>
                simp [Stack.control, instructionDecode, valueAt] at controlStep
              exact controlStep.1
          | pop =>
              cases stackAt : state.environment.stack <;>
                simp [Stack.control, instructionDecode, stackAt] at controlStep
              exact controlStep.1
          | op operation => simp [Stack.control, instructionDecode] at controlStep
          | flippedOp operation => simp [Stack.control, instructionDecode] at controlStep
          | icall callee argumentCount resultCount =>
              simp [Stack.control, instructionDecode] at controlStep
          | store slot =>
              cases stackAt : state.environment.stack <;>
                simp [Stack.control, instructionDecode, stackAt] at controlStep
              exact controlStep.1
          | load slot =>
              cases valueAt : state.environment.slots slot <;>
                simp [Stack.control, instructionDecode, valueAt] at controlStep
              exact controlStep.1
      | none =>
          cases controlAt : state.control with
          | returned results =>
              rw [controlAt] at instructionDecode controlStep
              simp [Stack.control, instructionDecode] at controlStep
          | halted =>
              rw [controlAt] at instructionDecode controlStep
              simp [Stack.control, instructionDecode] at controlStep
          | running cursor =>
              rw [controlAt] at instructionDecode controlStep
              cases terminatorAt : certificate.stack.terminatorAt state.control with
              | none =>
                  rw [controlAt] at terminatorAt
                  simp [Stack.control, instructionDecode, terminatorAt] at controlStep
              | some terminator =>
                  rw [controlAt] at terminatorAt
                  cases terminator with
                  | halt =>
                      simp [Stack.control, instructionDecode, terminatorAt] at controlStep
                      exact controlStep.1
                  | jump target =>
                      cases jumpAt : Stack.jump certificate.stack state.environment
                          cursor target <;>
                        simp [Stack.control, instructionDecode, terminatorAt, jumpAt]
                          at controlStep
                      exact controlStep.1
                  | branch thenTarget elseTarget =>
                      cases stackAt : state.environment.stack with
                      | nil =>
                          simp [Stack.control, instructionDecode, terminatorAt,
                            stackAt] at controlStep
                      | cons condition stack =>
                          cases jumpAt : Stack.jump certificate.stack
                            { state.environment with stack } cursor
                              (if condition = 0 then elseTarget else thenTarget) <;>
                            simp [Stack.control, instructionDecode, terminatorAt,
                              stackAt, jumpAt] at controlStep
                          exact controlStep.1
                  | iret =>
                      cases blockAt : certificate.stack.block? cursor with
                      | none =>
                          simp [Stack.control, instructionDecode, terminatorAt,
                            blockAt] at controlStep
                      | some block =>
                          by_cases sizeEq : state.environment.stack.length = block.outputCount
                          · simp [Stack.control, instructionDecode, terminatorAt, blockAt,
                              sizeEq] at controlStep
                            exact controlStep.1
                          · simp [Stack.control, instructionDecode, terminatorAt, blockAt,
                              sizeEq] at controlStep

theorem StackSchedule.target_steps_path
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (ctx : CallContext)
    {state final : Machine.State Stack.frame} {trace : Trace}
    (steps : Machine.Steps Stack.frame
      (Stack.decoder certificate.stack) Machine.memoryPolicy ctx state trace final) :
    TargetPath certificate.stack ctx state final ∧ trace = [] := by
  exact Machine.Steps.inductionOn
    (motive := fun state trace final _ =>
      TargetPath certificate.stack ctx state final ∧ trace = [])
    (fun state => ⟨.refl state, rfl⟩)
    (fun start next inductionHypothesis => by
      obtain ⟨path, traceEmpty⟩ := inductionHypothesis
      have nextTraceEmpty := certificate.target_step_trace_empty accepted ctx next
      subst_vars
      exact ⟨path.tail next, by simp⟩)
    steps

theorem StackSchedule.target_control_not_returned
    (certificate : StackSchedule) (accepted : certificate.check = true)
    {environment nextEnvironment : Stack.Environment} {globals nextGlobals : Globals}
    {control nextControl : Machine.MachineControl} {trace : Trace}
    (controlStep : Stack.control certificate.stack environment globals control =
      some (trace, nextEnvironment, nextGlobals, nextControl))
    (results : Array Word) :
    nextControl ≠ .returned results := by
  intro returned
  cases instructionDecode : certificate.stack.decodeInstruction control with
  | some decoded =>
      obtain ⟨instructionNext, instruction⟩ := decoded
      obtain ⟨nextCursor, nextRunning⟩ :=
        stackDecodeInstruction_next_running certificate.stack control instructionNext
          instruction instructionDecode
      cases instruction with
      | swap depth =>
          cases stackAt : Stack.exchange environment.stack 0 depth <;>
            simp [Stack.control, instructionDecode, stackAt] at controlStep
          have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
          cases impossible
      | exchange firstDepth secondDepth =>
          by_cases depthsEqual : firstDepth = secondDepth
          · simp [Stack.control, instructionDecode, depthsEqual] at controlStep
          · cases stackAt : Stack.exchange environment.stack firstDepth secondDepth <;>
              simp [Stack.control, instructionDecode, depthsEqual, stackAt] at controlStep
            have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
            cases impossible
      | dup depth =>
          cases valueAt : environment.stack[depth]? <;>
            simp [Stack.control, instructionDecode, valueAt] at controlStep
          have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
          cases impossible
      | pop =>
          cases stackAt : environment.stack <;>
            simp [Stack.control, instructionDecode, stackAt] at controlStep
          have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
          cases impossible
      | op operation => simp [Stack.control, instructionDecode] at controlStep
      | flippedOp operation => simp [Stack.control, instructionDecode] at controlStep
      | icall callee argumentCount resultCount =>
          simp [Stack.control, instructionDecode] at controlStep
      | store slot =>
          cases stackAt : environment.stack <;>
            simp [Stack.control, instructionDecode, stackAt] at controlStep
          have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
          cases impossible
      | load slot =>
          cases valueAt : environment.slots slot <;>
            simp [Stack.control, instructionDecode, valueAt] at controlStep
          have impossible := nextRunning.symm.trans (controlStep.2.2.2.trans returned)
          cases impossible
  | none =>
      cases controlAt : control with
      | returned values =>
          rw [controlAt] at instructionDecode controlStep
          simp [Stack.control, instructionDecode] at controlStep
      | halted =>
          rw [controlAt] at instructionDecode controlStep
          simp [Stack.control, instructionDecode] at controlStep
      | running cursor =>
          rw [controlAt] at instructionDecode controlStep
          cases terminatorAt : certificate.stack.terminatorAt control with
          | none =>
              rw [controlAt] at terminatorAt
              simp [Stack.control, instructionDecode, terminatorAt] at controlStep
          | some terminator =>
              rw [controlAt] at terminatorAt
              cases terminator with
              | halt =>
                  simp [Stack.control, instructionDecode, terminatorAt] at controlStep
                  have impossible := controlStep.2.2.2.trans returned
                  cases impossible
              | jump target =>
                  cases jumpAt : Stack.jump certificate.stack environment cursor
                      target with
                  | none =>
                      simp [Stack.control, instructionDecode, terminatorAt, jumpAt]
                        at controlStep
                  | some jumpResult =>
                      obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                      simp [Stack.control, instructionDecode, terminatorAt, jumpAt]
                        at controlStep
                      obtain ⟨nextCursor, nextRunning⟩ := stackJump_next_running
                        certificate.stack environment jumpEnvironment cursor target
                          jumpControl jumpAt
                      have impossible := nextRunning.symm.trans
                        (controlStep.2.2.2.trans returned)
                      cases impossible
              | branch thenTarget elseTarget =>
                  cases stackAt : environment.stack with
                  | nil =>
                      simp [Stack.control, instructionDecode, terminatorAt,
                        stackAt] at controlStep
                  | cons condition stack =>
                      cases jumpAt : Stack.jump certificate.stack
                          { environment with stack } cursor
                            (if condition = 0 then elseTarget else thenTarget) with
                      | none =>
                          simp [Stack.control, instructionDecode, terminatorAt,
                            stackAt, jumpAt] at controlStep
                      | some jumpResult =>
                          obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                          simp [Stack.control, instructionDecode, terminatorAt,
                            stackAt, jumpAt] at controlStep
                          obtain ⟨nextCursor, nextRunning⟩ := stackJump_next_running
                            certificate.stack { environment with stack } jumpEnvironment
                              cursor (if condition = 0 then elseTarget else thenTarget)
                              jumpControl jumpAt
                          have impossible := nextRunning.symm.trans
                            (controlStep.2.2.2.trans returned)
                          cases impossible
              | iret =>
                  cases blockAt : certificate.stack.block? cursor with
                  | none =>
                      simp [Stack.control, instructionDecode, terminatorAt,
                        blockAt] at controlStep
                  | some block =>
                      cases positionAt : cursor.position with
                      | statement index =>
                          simp [Stack.Program.terminatorAt, positionAt]
                            at terminatorAt
                      | terminator =>
                          exact (certificate.stack_program_terminator_not_iret accepted cursor block
                            blockAt (by
                              simpa [Stack.Program.terminatorAt, controlAt, positionAt,
                                blockAt] using terminatorAt)).elim

theorem StackSchedule.target_step_not_returned
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (ctx : CallContext) {state final : Machine.State Stack.frame} {trace : Trace}
    (step : Machine.Step Stack.frame
      (Stack.decoder certificate.stack) Machine.memoryPolicy ctx state trace final)
    (results : Array Word) :
    final.control ≠ .returned results := by
  intro returned
  cases step with
  | operation hdecode fires =>
      rename_i stepOperation src dst next environment globals
      change Stack.decode certificate.stack state.control = _ at hdecode
      cases instructionDecode : certificate.stack.decodeInstruction state.control with
      | none => simp [Stack.decode, instructionDecode] at hdecode
      | some decoded =>
          obtain ⟨instructionNext, instruction⟩ := decoded
          cases instruction with
          | op operation =>
              simp [Stack.decode, instructionDecode] at hdecode
              obtain ⟨nextCursor, nextRunning⟩ := stackDecodeInstruction_next_running
                certificate.stack state.control instructionNext (.op operation)
                  instructionDecode
              have impossible := nextRunning.symm.trans (hdecode.2.trans returned)
              cases impossible
          | flippedOp operation =>
              rcases certificate.target_decoded_flipped_operation_supported accepted state.control
                  instructionNext operation instructionDecode with rfl | rfl
              · simp [Stack.decode, instructionDecode]
                  at hdecode
                obtain ⟨nextCursor, nextRunning⟩ := stackDecodeInstruction_next_running
                  certificate.stack state.control instructionNext (.flippedOp .add)
                    instructionDecode
                have impossible := nextRunning.symm.trans (hdecode.2.trans returned)
                cases impossible
              · simp [Stack.decode, instructionDecode]
                  at hdecode
                obtain ⟨nextCursor, nextRunning⟩ := stackDecodeInstruction_next_running
                  certificate.stack state.control instructionNext (.flippedOp .lt)
                    instructionDecode
                have impossible := nextRunning.symm.trans (hdecode.2.trans returned)
                cases impossible
          | swap depth => simp [Stack.decode, instructionDecode] at hdecode
          | exchange firstDepth secondDepth =>
              simp [Stack.decode, instructionDecode] at hdecode
          | dup depth => simp [Stack.decode, instructionDecode] at hdecode
          | pop => simp [Stack.decode, instructionDecode] at hdecode
          | icall callee argumentCount resultCount =>
              simp [Stack.decode, instructionDecode] at hdecode
          | store slot => simp [Stack.decode, instructionDecode] at hdecode
          | load slot => simp [Stack.decode, instructionDecode] at hdecode
  | operationHalted hdecode fires => cases returned
  | internalCall hdecode fetch evaluation resume =>
      change Stack.decode certificate.stack state.control = _ at hdecode
      cases instructionDecode : certificate.stack.decodeInstruction state.control with
      | none => simp [Stack.decode, instructionDecode] at hdecode
      | some decoded =>
          obtain ⟨instructionNext, instruction⟩ := decoded
          cases instruction with
          | op operation => simp [Stack.decode, instructionDecode] at hdecode
          | flippedOp operation =>
              rcases certificate.target_decoded_flipped_operation_supported accepted state.control
                  instructionNext operation instructionDecode with rfl | rfl <;>
                simp [Stack.decode, instructionDecode] at hdecode
          | swap depth => simp [Stack.decode, instructionDecode] at hdecode
          | exchange firstDepth secondDepth =>
              simp [Stack.decode, instructionDecode] at hdecode
          | dup depth => simp [Stack.decode, instructionDecode] at hdecode
          | pop => simp [Stack.decode, instructionDecode] at hdecode
          | icall callee argumentCount resultCount =>
              simp [Stack.decode, instructionDecode] at hdecode
              exact ((certificate.target_decoded_instruction_excludes_internal_calls accepted
                state.control instructionNext (.icall callee argumentCount resultCount)
                instructionDecode) callee argumentCount resultCount rfl).elim
          | store slot => simp [Stack.decode, instructionDecode] at hdecode
          | load slot => simp [Stack.decode, instructionDecode] at hdecode
  | control controlStep =>
      exact certificate.target_control_not_returned accepted controlStep results returned

theorem StackSchedule.block_replay_steps
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals finalEnvironment expectedStack,
      Machine.Steps Vars.frame (Vars.decoder certificate.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockCertificate.sourceControlAt block 0⟩ : Vars.State))
          []
          ((⟨globals, finalLocals,
            blockCertificate.sourceControlAt block blockCertificate.vars.statements.size⟩ :
              Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockCertificate.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment,
            blockCertificate.targetControlAt block blockCertificate.stack.instructions.size⟩ ∧
        StackSchedule.Block.finalStack blockCertificate.vars.terminator blockCertificate.vars.exitLayout
            expectedStack = some expectedStack ∧
        expectedStack.mapM (Symbolic.Value.interpret finalLocals) =
          some finalEnvironment.stack := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted : blockCertificate.check = true := by
    have acceptedAt := (certificate.check_sound accepted).2.1 block.id blockBound
    simpa [blockGet] using acceptedAt
  obtain ⟨usesAvailable, variablesUnique⟩ :=
    StackSchedule.Block.check_source_valid blockCertificate blockAccepted
  obtain ⟨finalState, expectedStack, replay, expected, fired, _, stackEq, _⟩ :=
    blockCertificate.check_sound blockAccepted
  obtain ⟨referenceLocals, evaluated⟩ :=
    blockCertificate.sourceOrderReferenceLocals_exists blockAccepted locals environment.stack
      stackValues
  have interprets := Symbolic.State.initial_interprets_in_environment
    blockCertificate.vars.entryLayout locals environment stackValues
  have initialAgrees :
      (Symbolic.State.initial blockCertificate.vars.entryLayout).AvailableVariablesAgree
        blockCertificate.vars.statements locals referenceLocals := by
    intro identifier available
    have entry : identifier ∈
        blockCertificate.vars.entryLayout.toList.map Symbolic.Value.identifier := by
      simpa [Symbolic.State.initial, Symbolic.State.available] using available
    exact (sourceOrderReferenceLocals_preserves_entry blockCertificate.vars.statements
      blockCertificate.vars.entryLayout locals referenceLocals variablesUnique evaluated identifier
      entry).symm
  have interpretsReference :
      (Symbolic.State.initial blockCertificate.vars.entryLayout).InterpretsReference
        blockCertificate.vars.statements locals referenceLocals environment :=
    ⟨interprets, initialAgrees⟩
  obtain ⟨scheduledLocals, finalEnvironment, targetSteps, finalInterprets⟩ :=
    interpretsReference.replay_symbolic_instructions_target_steps
      (sourceProgram := certificate.vars) (targetProgram := certificate.stack)
      blockCertificate.vars.statements blockCertificate.vars.entryLayout
      blockCertificate.stack.instructions (Symbolic.State.initial blockCertificate.vars.entryLayout)
      finalState ctx globals locals locals referenceLocals environment usesAvailable variablesUnique
      evaluated
      (blockCertificate.sourceControlAt block) (blockCertificate.targetControlAt block) 0 replay
      (certificate.source_decode_at block blockCertificate blockAt)
      (fun index instruction instructionAt => by
        simpa using certificate.target_decode_at block blockCertificate blockAt index instruction
          instructionAt)
  have sourceSteps := sourceOrderReferenceLocals_source_steps
    (sourceProgram := certificate.vars) blockCertificate.vars.statements ctx globals
    locals referenceLocals (blockCertificate.sourceControlAt block) evaluated
    (certificate.source_decode_at block blockCertificate blockAt)
  have finalValuesAvailable := Symbolic.executeAll_preserves_values_available
    blockCertificate.vars.statements blockCertificate.stack.instructions
    (Symbolic.State.initial blockCertificate.vars.entryLayout) finalState replay
    (Symbolic.State.initial_values_available blockCertificate.vars.statements
      blockCertificate.vars.entryLayout)
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
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block successor : BlockId)
    (blockCertificate successorCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (successorAt : certificate.blocks[successor.id]? = some successorCertificate)
    (jump : blockCertificate.vars.terminator = .jump successor)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (exitValues : blockCertificate.vars.exitLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ nextLocals,
      Machine.Step Vars.frame (Vars.decoder certificate.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals,
            blockCertificate.sourceControlAt block blockCertificate.vars.statements.size⟩ :
              Vars.State)) []
          ((⟨globals, nextLocals, successorCertificate.sourceControlAt successor 0⟩ :
              Vars.State)) ∧
        Machine.Step Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockCertificate.targetControlAt block blockCertificate.stack.instructions.size⟩ []
          ⟨globals, environment, successorCertificate.targetControlAt successor 0⟩ ∧
        successorCertificate.vars.entryLayout.toList.mapM
          (Symbolic.Value.interpret nextLocals) = some environment.stack := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have successorBound : successor.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := successor.id) successorAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have successorGet : certificate.blocks[successor.id] = successorCertificate :=
    (Array.getElem?_eq_some_iff.mp successorAt).2
  have blockAccepted : blockCertificate.check = true := by
    have acceptedAt := (certificate.check_sound accepted).2.1 block.id blockBound
    simpa [blockGet] using acceptedAt
  have successorAccepted : successorCertificate.check = true := by
    have acceptedAt :=
      (certificate.check_sound accepted).2.1 successor.id successorBound
    simpa [successorGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockCertificate.check_sound blockAccepted
  obtain ⟨_, _, _, _, _, _, _, successorNodup⟩ :=
    successorCertificate.check_sound successorAccepted
  have targetJump : blockCertificate.stack.terminator = .jump successor := by
    cases targetTerminatorEq : blockCertificate.stack.terminator with
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
      blockCertificate.vars.exitLayout.size = successorCertificate.vars.entryLayout.size := by
    have edgesAt :=
      (certificate.check_sound accepted).2.2 block.id blockBound
    simpa [blockGet, StackSchedule.blockEdgesAgree, jump,
      StackSchedule.layoutAgreesAt, successorAt] using edgesAt
  obtain ⟨nextLocals, sourceTransfer, nextValues⟩ :=
    Locals.transfer_interprets_renamed_symbolic_values blockCertificate.vars.exitLayout
      successorCertificate.vars.entryLayout environment.stack locals layoutAgreement successorNodup
      exitValues
  have blockBoundaryNames :=
    certificate.block_boundary_names accepted block.id blockCertificate blockAt
  have successorBoundaryNames :=
    certificate.block_boundary_names accepted successor.id successorCertificate successorAt
  have sourceBoundaryTransfer :
      Locals.transfer blockCertificate.vars.outputs successorCertificate.vars.inputs locals =
        .ok ((), nextLocals) := by
    rw [← blockBoundaryNames.2, ← successorBoundaryNames.1]
    exact sourceTransfer
  have stackLength : environment.stack.length = blockCertificate.vars.exitLayout.size := by
    obtain ⟨_, length⟩ :=
      Symbolic.Value.identifiers_mapM_lookup_of_interpretations
        blockCertificate.vars.exitLayout.toList environment.stack locals exitValues
    simpa using length.symm
  refine ⟨nextLocals, ?_, ?_, nextValues⟩
  · apply Sir.step_terminator
      (certificate.source_terminator_at_end block blockCertificate blockAt)
    rw [jump]
    simp [Vars.evaluateTerminator, Vars.jump, StateT.run, bind, Except.bind,
      StateT.bind, StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StackSchedule.vars, Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?, blockBound, successorBound, blockGet, successorGet,
      StackSchedule.Block.Source.toBlock, sourceBoundaryTransfer,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition,
      pure, Except.pure]
  · apply Machine.Step.control
    change Stack.control certificate.stack environment globals
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size) = _
    unfold Stack.control
    rw [certificate.target_decode_none_at_end block blockCertificate]
    change (certificate.stack.terminatorAt
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size)).bind _ = _
    rw [certificate.target_terminator_at_end block blockCertificate blockAt, targetJump]
    simp [Stack.jump, StackSchedule.stack,
      Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
      blockAt, successorAt, StackSchedule.Block.Target.toBlock, stackLength,
      layoutAgreement,
      StackSchedule.Block.targetControlAt, Stack.Block.startPosition]

theorem StackSchedule.block_branch_step
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block thenSuccessor elseSuccessor : BlockId) (condition : VarId)
    (conditionValue : Word)
    (blockCertificate successorCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (successorAt : certificate.blocks[(if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id]? = some successorCertificate)
    (branch : blockCertificate.vars.terminator =
      .branch condition thenSuccessor elseSuccessor)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment) (exitStack : List Word)
    (branchValues : (.variable condition :: blockCertificate.vars.exitLayout.toList).mapM
      (Symbolic.Value.interpret locals) = some (conditionValue :: exitStack)) :
    ∃ nextLocals,
      Machine.Step Vars.frame (Vars.decoder certificate.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals,
            blockCertificate.sourceControlAt block blockCertificate.vars.statements.size⟩ :
              Vars.State)) []
          ((⟨globals, nextLocals,
            successorCertificate.sourceControlAt
              (if conditionValue = 0 then elseSuccessor else thenSuccessor) 0⟩ :
              Vars.State)) ∧
        Machine.Step Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, { environment with stack := conditionValue :: exitStack },
            blockCertificate.targetControlAt block blockCertificate.stack.instructions.size⟩ []
          ⟨globals, { environment with stack := exitStack },
            successorCertificate.targetControlAt
              (if conditionValue = 0 then elseSuccessor else thenSuccessor) 0⟩ ∧
        successorCertificate.vars.entryLayout.toList.mapM
          (Symbolic.Value.interpret nextLocals) = some exitStack := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have successorBound : (if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks)
      (i := (if conditionValue = 0 then elseSuccessor else thenSuccessor).id) successorAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have successorGet : certificate.blocks[(if conditionValue = 0 then elseSuccessor
      else thenSuccessor).id] = successorCertificate :=
    (Array.getElem?_eq_some_iff.mp successorAt).2
  have blockAccepted : blockCertificate.check = true := by
    have acceptedAt := (certificate.check_sound accepted).2.1 block.id blockBound
    simpa [blockGet] using acceptedAt
  have successorAccepted : successorCertificate.check = true := by
    have acceptedAt :=
      (certificate.check_sound accepted).2.1
        (if conditionValue = 0 then elseSuccessor else thenSuccessor).id successorBound
    simpa [successorGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockCertificate.check_sound blockAccepted
  obtain ⟨_, _, _, _, _, _, _, successorNodup⟩ :=
    successorCertificate.check_sound successorAccepted
  have targetBranch : blockCertificate.stack.terminator =
      .branch thenSuccessor elseSuccessor := by
    cases targetTerminatorEq : blockCertificate.stack.terminator with
    | halt => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | jump => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | branch targetThen targetElse =>
        have targets : thenSuccessor = targetThen ∧ elseSuccessor = targetElse := by
          simpa [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] using terminatorsAgree
        simp [targets.1, targets.2]
    | iret => simp [branch, targetTerminatorEq, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  have edgeAgreements :
      certificate.layoutAgreesAt blockCertificate.vars.exitLayout thenSuccessor = true ∧
        certificate.layoutAgreesAt blockCertificate.vars.exitLayout elseSuccessor = true := by
    have edgesAt :=
      (certificate.check_sound accepted).2.2 block.id blockBound
    simpa [blockGet, StackSchedule.blockEdgesAgree, branch] using edgesAt
  have layoutAgreement :
      blockCertificate.vars.exitLayout.size = successorCertificate.vars.entryLayout.size := by
    by_cases zero : conditionValue = 0
    · have elseAt : certificate.blocks[elseSuccessor.id]? = some successorCertificate := by
        simpa [zero] using successorAt
      simpa [StackSchedule.layoutAgreesAt, elseAt] using edgeAgreements.2
    · have thenAt : certificate.blocks[thenSuccessor.id]? = some successorCertificate := by
        simpa [zero] using successorAt
      simpa [StackSchedule.layoutAgreesAt, thenAt] using edgeAgreements.1
  have interpretations :
      Symbolic.Value.interpret locals (.variable condition) = some conditionValue ∧
        blockCertificate.vars.exitLayout.toList.mapM (Symbolic.Value.interpret locals) =
          some exitStack := by
    cases conditionInterpretation :
        Symbolic.Value.interpret locals (.variable condition) with
    | none => simp [conditionInterpretation] at branchValues
    | some value =>
        cases exitValues : blockCertificate.vars.exitLayout.toList.mapM
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
    Locals.transfer_interprets_renamed_symbolic_values blockCertificate.vars.exitLayout
      successorCertificate.vars.entryLayout exitStack locals layoutAgreement successorNodup exitValues
  have blockBoundaryNames :=
    certificate.block_boundary_names accepted block.id blockCertificate blockAt
  have successorBoundaryNames := certificate.block_boundary_names accepted
    (if conditionValue = 0 then elseSuccessor else thenSuccessor).id
    successorCertificate successorAt
  have sourceBoundaryTransfer :
      Locals.transfer blockCertificate.vars.outputs successorCertificate.vars.inputs locals =
        .ok ((), nextLocals) := by
    rw [← blockBoundaryNames.2, ← successorBoundaryNames.1]
    exact sourceTransfer
  have stackLength : exitStack.length = blockCertificate.vars.exitLayout.size := by
    obtain ⟨_, length⟩ :=
      Symbolic.Value.identifiers_mapM_lookup_of_interpretations
        blockCertificate.vars.exitLayout.toList exitStack locals exitValues
    simpa using length.symm
  refine ⟨nextLocals, ?_, ?_, nextValues⟩
  · apply Sir.step_terminator
      (certificate.source_terminator_at_end block blockCertificate blockAt)
    rw [branch]
    simp [Vars.evaluateTerminator, Locals.lookupM, conditionLookup, Vars.jump, StateT.run, bind, Except.bind,
      StateT.bind, StateT.lift, StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StackSchedule.vars, Vars.Program.block?, Vars.Program.function?,
      Vars.Function.block?, blockBound, successorBound, blockGet, successorGet,
      StackSchedule.Block.Source.toBlock, sourceBoundaryTransfer,
      StackSchedule.Block.sourceControlAt, Vars.Block.startPosition,
      pure, Except.pure]
  · apply Machine.Step.control
    change Stack.control certificate.stack
      { environment with stack := conditionValue :: exitStack } globals
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size) = _
    unfold Stack.control
    rw [certificate.target_decode_none_at_end block blockCertificate]
    change (certificate.stack.terminatorAt
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size)).bind _ = _
    rw [certificate.target_terminator_at_end block blockCertificate blockAt, targetBranch]
    simp [Stack.jump, StackSchedule.stack,
      Stack.Program.block?, Stack.Program.function?, Stack.Function.block?,
      blockAt, successorAt, StackSchedule.Block.Target.toBlock, stackLength,
      layoutAgreement, StackSchedule.Block.targetControlAt,
      Stack.Block.startPosition]

theorem StackSchedule.block_halted_steps
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (halt : blockCertificate.vars.terminator = .halt)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    ∃ finalLocals finalEnvironment,
      Machine.Steps Vars.frame (Vars.decoder certificate.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockCertificate.sourceControlAt block 0⟩ : Vars.State))
          []
          ((⟨globals, finalLocals, .halted⟩ : Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, environment,
            blockCertificate.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩ := by
  have blockBound : block.id < certificate.blocks.size :=
    of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
  have blockGet : certificate.blocks[block.id] = blockCertificate :=
    (Array.getElem?_eq_some_iff.mp blockAt).2
  have blockAccepted : blockCertificate.check = true := by
    have acceptedAt := (certificate.check_sound accepted).2.1 block.id blockBound
    simpa [blockGet] using acceptedAt
  obtain ⟨_, _, _, _, _, terminatorsAgree, _, _⟩ :=
    blockCertificate.check_sound blockAccepted
  have targetHalt : blockCertificate.stack.terminator = .halt := by
    cases target : blockCertificate.stack.terminator with
    | halt => rfl
    | jump => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | branch => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
    | iret => simp [halt, target, StackSchedule.Block.terminatorsAgree] at terminatorsAgree
  obtain ⟨finalLocals, finalEnvironment, _, sourceSteps, targetSteps, _, _⟩ :=
    certificate.block_replay_steps accepted block blockCertificate blockAt ctx globals locals
      environment stackValues
  have sourceHalt : Machine.Step Vars.frame
      (Vars.decoder certificate.vars) Machine.memoryPolicy ctx
      ((⟨globals, finalLocals,
        blockCertificate.sourceControlAt block blockCertificate.vars.statements.size⟩ :
          Vars.State)) []
      ((⟨globals, finalLocals, .halted⟩ : Vars.State)) := by
    exact Sir.step_terminator (certificate.source_terminator_at_end block blockCertificate blockAt)
      (by rw [halt]; rfl)
  have targetHaltStep : Machine.Step Stack.frame
      (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
      ⟨globals, finalEnvironment,
        blockCertificate.targetControlAt block blockCertificate.stack.instructions.size⟩ []
      ⟨globals, finalEnvironment, .halted⟩ := by
    apply Machine.Step.control
    change Stack.control certificate.stack finalEnvironment globals
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size) = _
    unfold Stack.control
    rw [certificate.target_decode_none_at_end block blockCertificate]
    change (certificate.stack.terminatorAt
      (blockCertificate.targetControlAt block blockCertificate.stack.instructions.size)).bind _ = _
    rw [certificate.target_terminator_at_end block blockCertificate blockAt, targetHalt]
    rfl
  exact ⟨finalLocals, finalEnvironment, sourceSteps.tail sourceHalt,
    targetSteps.tail targetHaltStep⟩

theorem StackSchedule.block_transition_steps
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    (∃ finalLocals finalEnvironment,
      Machine.Steps Vars.frame (Vars.decoder certificate.vars)
          Machine.memoryPolicy ctx
          ((⟨globals, locals, blockCertificate.sourceControlAt block 0⟩ :
            Vars.State)) []
          ((⟨globals, finalLocals, .halted⟩ : Vars.State)) ∧
        Machine.Steps Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, environment, blockCertificate.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩) ∨
      ∃ (successor : BlockId)
          (successorCertificate : StackSchedule.Block)
          (nextLocals : Locals) (nextEnvironment : Stack.Environment),
        certificate.blocks[successor.id]? = some successorCertificate ∧
          Machine.Steps Vars.frame (Vars.decoder certificate.vars)
            Machine.memoryPolicy ctx
            ((⟨globals, locals, blockCertificate.sourceControlAt block 0⟩ :
              Vars.State)) []
            ((⟨globals, nextLocals, successorCertificate.sourceControlAt successor 0⟩ :
              Vars.State)) ∧
          NonemptySourcePath certificate.vars ctx
            ⟨globals, locals, blockCertificate.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorCertificate.sourceControlAt successor 0⟩ ∧
          Machine.Steps Stack.frame
            (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
            ⟨globals, environment, blockCertificate.targetControlAt block 0⟩ []
            ⟨globals, nextEnvironment,
              successorCertificate.targetControlAt successor 0⟩ ∧
          NonemptyTargetPath certificate.stack ctx
            ⟨globals, environment, blockCertificate.targetControlAt block 0⟩
            ⟨globals, nextEnvironment,
              successorCertificate.targetControlAt successor 0⟩ ∧
          successorCertificate.vars.entryLayout.toList.mapM
            (Symbolic.Value.interpret nextLocals) = some nextEnvironment.stack := by
  cases terminator : blockCertificate.vars.terminator with
  | halt =>
      obtain ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩ :=
        certificate.block_halted_steps accepted block blockCertificate blockAt terminator ctx
          globals locals environment stackValues
      exact .inl ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩
  | jump successor =>
      obtain ⟨finalLocals, finalEnvironment, expectedStack, sourceSteps, targetSteps,
          expected, finalStack⟩ :=
        certificate.block_replay_steps accepted block blockCertificate blockAt ctx globals locals
          environment stackValues
      have exitValues : blockCertificate.vars.exitLayout.toList.mapM
          (Symbolic.Value.interpret finalLocals) = some finalEnvironment.stack := by
        have expectedStackEq : expectedStack = blockCertificate.vars.exitLayout.toList := by
          simpa [terminator, StackSchedule.Block.finalStack] using expected.symm
        simpa [expectedStackEq] using finalStack
      have blockBound : block.id < certificate.blocks.size :=
        of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
      have blockGet : certificate.blocks[block.id] = blockCertificate :=
        (Array.getElem?_eq_some_iff.mp blockAt).2
      have edgeAgreement : certificate.layoutAgreesAt blockCertificate.vars.exitLayout successor =
          true := by
        have edgesAt :=
          (certificate.check_sound accepted).2.2 block.id blockBound
        simpa [blockGet, StackSchedule.blockEdgesAgree, terminator] using edgesAt
      obtain ⟨successorCertificate, successorAt⟩ :
          ∃ successorCertificate, certificate.blocks[successor.id]? = some successorCertificate := by
        cases successorAt : certificate.blocks[successor.id]? with
        | none => simp [StackSchedule.layoutAgreesAt, successorAt] at edgeAgreement
        | some successorCertificate => exact ⟨successorCertificate, rfl⟩
      obtain ⟨nextLocals, sourceStep, targetStep, nextValues⟩ :=
        certificate.block_jump_step accepted block successor blockCertificate
          successorCertificate blockAt successorAt terminator ctx globals finalLocals
          finalEnvironment exitValues
      exact .inr ⟨successor, successorCertificate, nextLocals, finalEnvironment, successorAt,
        sourceSteps.tail sourceStep,
        SourcePath.tail_nonempty (SourcePath.of_steps sourceSteps rfl) sourceStep,
        targetSteps.tail targetStep,
        TargetPath.tail_nonempty (TargetPath.of_steps targetSteps rfl) targetStep, nextValues⟩
  | branch condition thenSuccessor elseSuccessor =>
      obtain ⟨finalLocals, finalEnvironment, expectedStack, sourceSteps, targetSteps,
          expected, finalStack⟩ :=
        certificate.block_replay_steps accepted block blockCertificate blockAt ctx globals locals
          environment stackValues
      have expectedStackEq : expectedStack =
          .variable condition :: blockCertificate.vars.exitLayout.toList := by
        simpa [terminator, StackSchedule.Block.finalStack] using expected.symm
      have branchValues :
          (.variable condition :: blockCertificate.vars.exitLayout.toList).mapM
              (Symbolic.Value.interpret finalLocals) = some finalEnvironment.stack := by
        simpa [expectedStackEq] using finalStack
      cases conditionInterpretation : Symbolic.Value.interpret finalLocals (.variable condition) with
      | none => simp [conditionInterpretation] at branchValues
      | some conditionValue =>
          cases exitInterpretations : blockCertificate.vars.exitLayout.toList.mapM
              (Symbolic.Value.interpret finalLocals) with
          | none => simp [conditionInterpretation, exitInterpretations] at branchValues
          | some exitStack =>
              have stackEq : finalEnvironment.stack = conditionValue :: exitStack := by
                simpa [conditionInterpretation, exitInterpretations] using branchValues.symm
              have concreteBranchValues :
                  (.variable condition :: blockCertificate.vars.exitLayout.toList).mapM
                      (Symbolic.Value.interpret finalLocals) =
                    some (conditionValue :: exitStack) := by
                rw [← stackEq]
                exact branchValues
              have blockBound : block.id < certificate.blocks.size :=
                of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
              have blockGet : certificate.blocks[block.id] = blockCertificate :=
                (Array.getElem?_eq_some_iff.mp blockAt).2
              have edgeAgreements :
                  certificate.layoutAgreesAt blockCertificate.vars.exitLayout thenSuccessor = true ∧
                    certificate.layoutAgreesAt blockCertificate.vars.exitLayout elseSuccessor = true := by
                have edgesAt :=
                  (certificate.check_sound accepted).2.2 block.id blockBound
                simpa [blockGet, StackSchedule.blockEdgesAgree, terminator] using edgesAt
              have selectedAgreement : certificate.layoutAgreesAt blockCertificate.vars.exitLayout
                    (if conditionValue = 0 then elseSuccessor else thenSuccessor) = true := by
                by_cases zero : conditionValue = 0
                · simpa [zero] using edgeAgreements.2
                · simpa [zero] using edgeAgreements.1
              obtain ⟨successorCertificate, successorAt⟩ : ∃ successorCertificate,
                  certificate.blocks[(if conditionValue = 0 then elseSuccessor
                    else thenSuccessor).id]? = some successorCertificate := by
                cases successorAt : certificate.blocks[(if conditionValue = 0 then elseSuccessor
                    else thenSuccessor).id]? with
                | none =>
                    simp [StackSchedule.layoutAgreesAt, successorAt] at selectedAgreement
                | some successorCertificate => exact ⟨successorCertificate, rfl⟩
              obtain ⟨nextLocals, sourceStep, targetStep, nextValues⟩ :=
                certificate.block_branch_step accepted block thenSuccessor elseSuccessor condition
                  conditionValue blockCertificate successorCertificate blockAt successorAt
                  terminator ctx globals finalLocals finalEnvironment exitStack concreteBranchValues
              have finalEnvironmentWithStack :
                  { finalEnvironment with stack := conditionValue :: exitStack } =
                    finalEnvironment := by
                cases finalEnvironment
                simp_all
              rw [finalEnvironmentWithStack] at targetStep
              exact .inr ⟨if conditionValue = 0 then elseSuccessor else thenSuccessor,
                successorCertificate, nextLocals, { finalEnvironment with stack := exitStack },
                successorAt, sourceSteps.tail sourceStep,
                SourcePath.tail_nonempty (SourcePath.of_steps sourceSteps rfl) sourceStep,
                targetSteps.tail targetStep,
                TargetPath.tail_nonempty (TargetPath.of_steps targetSteps rfl) targetStep,
                nextValues⟩
  | iret =>
      have blockBound : block.id < certificate.blocks.size :=
        of_getElem?_eq_some (c := certificate.blocks) (i := block.id) blockAt
      have blockGet : certificate.blocks[block.id] = blockCertificate :=
        (Array.getElem?_eq_some_iff.mp blockAt).2
      have blockAccepted :=
        (certificate.check_sound accepted).2.1 block.id blockBound
      have blockAccepted' : blockCertificate.check = true := by
        simpa [blockGet] using blockAccepted
      obtain ⟨_, expectedStack, _, expected, _⟩ :=
        blockCertificate.check_sound blockAccepted'
      simp [terminator, StackSchedule.Block.finalStack] at expected

theorem StackSchedule.block_transition_paths
    (certificate : StackSchedule) (accepted : certificate.check = true)
    (block : BlockId) (blockCertificate : StackSchedule.Block)
    (blockAt : certificate.blocks[block.id]? = some blockCertificate)
    (ctx : CallContext) (globals : Globals) (locals : Locals)
    (environment : Stack.Environment)
    (stackValues : blockCertificate.vars.entryLayout.toList.mapM
      (Symbolic.Value.interpret locals) = some environment.stack) :
    (∃ finalLocals finalEnvironment,
      SourcePath certificate.vars ctx
          ⟨globals, locals, blockCertificate.sourceControlAt block 0⟩
          ⟨globals, finalLocals, .halted⟩ ∧
        Machine.Steps Stack.frame
          (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
          ⟨globals, environment, blockCertificate.targetControlAt block 0⟩ []
          ⟨globals, finalEnvironment, .halted⟩) ∨
      ∃ (successor : BlockId)
          (successorCertificate : StackSchedule.Block)
          (nextLocals : Locals) (nextEnvironment : Stack.Environment),
        certificate.blocks[successor.id]? = some successorCertificate ∧
          SourcePath certificate.vars ctx
            ⟨globals, locals, blockCertificate.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorCertificate.sourceControlAt successor 0⟩ ∧
          NonemptySourcePath certificate.vars ctx
            ⟨globals, locals, blockCertificate.sourceControlAt block 0⟩
            ⟨globals, nextLocals, successorCertificate.sourceControlAt successor 0⟩ ∧
          Machine.Steps Stack.frame
            (Stack.decoder certificate.stack) Machine.memoryPolicy ctx
            ⟨globals, environment, blockCertificate.targetControlAt block 0⟩ []
            ⟨globals, nextEnvironment,
              successorCertificate.targetControlAt successor 0⟩ ∧
          NonemptyTargetPath certificate.stack ctx
            ⟨globals, environment, blockCertificate.targetControlAt block 0⟩
            ⟨globals, nextEnvironment,
              successorCertificate.targetControlAt successor 0⟩ ∧
          successorCertificate.vars.entryLayout.toList.mapM
            (Symbolic.Value.interpret nextLocals) = some nextEnvironment.stack := by
  rcases certificate.block_transition_steps accepted block blockCertificate blockAt ctx globals
      locals environment stackValues with halted | transitioned
  · obtain ⟨finalLocals, finalEnvironment, sourceSteps, targetSteps⟩ := halted
    exact .inl ⟨finalLocals, finalEnvironment, SourcePath.of_steps sourceSteps rfl, targetSteps⟩
  · obtain ⟨successor, successorCertificate, nextLocals, nextEnvironment, successorAt,
        sourceSteps, sourceNonempty, targetSteps, targetNonempty, nextValues⟩ := transitioned
    exact .inr ⟨successor, successorCertificate, nextLocals, nextEnvironment, successorAt,
      SourcePath.of_steps sourceSteps rfl, sourceNonempty, targetSteps, targetNonempty,
      nextValues⟩

end Sir.Lowering
