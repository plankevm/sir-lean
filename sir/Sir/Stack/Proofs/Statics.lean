import Sir.Stack.Proofs.Dialogue

namespace Sir.Stack

variable {program : Program}

theorem push_eq_ok_iff {environment environment' : Environment}
    {destination : Destination} {values : Array Word} :
    push environment destination values = .ok environment' ↔
      destination.consume ≤ environment.stack.length ∧
        values.size = destination.produce ∧
        environment' =
          { environment with
            stack := values.toList ++ environment.stack.drop destination.consume } := by
  by_cases hfits :
      destination.consume ≤ environment.stack.length ∧ values.size = destination.produce
  · simp [push, hfits, eq_comm]
  · simp only [push, hfits, ↓reduceIte]
    constructor
    · intro h
      exact absurd h (by simp)
    · exact fun h => absurd ⟨h.1, h.2.1⟩ hfits

theorem push_ok {environment : Environment} {destination : Destination}
    {values : Array Word}
    (hheight : destination.consume ≤ environment.stack.length)
    (hsize : values.size = destination.produce) :
    ∃ environment', push environment destination values = .ok environment' :=
  ⟨_, push_eq_ok_iff.mpr ⟨hheight, hsize, rfl⟩⟩

theorem push_stack_length {environment environment' : Environment}
    {destination : Destination} {values : Array Word}
    (h : push environment destination values = .ok environment') :
    environment'.stack.length = destination.after environment.stack.length := by
  obtain ⟨hheight, hsize, rfl⟩ := push_eq_ok_iff.mp h
  simp only [Destination.after, List.length_append, List.length_drop, Array.length_toList,
    hsize]
  omega

theorem push_slots {environment environment' : Environment}
    {destination : Destination} {values : Array Word}
    (h : push environment destination values = .ok environment') :
    environment'.slots = environment.slots := by
  obtain ⟨-, -, rfl⟩ := push_eq_ok_iff.mp h
  rfl

theorem stack_cons {environment : Environment} (hheight : 1 ≤ environment.stack.length) :
    ∃ value rest, environment.stack = value :: rest := by
  match hstack : environment.stack with
  | [] => rw [hstack] at hheight; simp at hheight
  | value :: rest => exact ⟨value, rest, rfl⟩

theorem stack_cons_cons {environment : Environment} (hheight : 2 ≤ environment.stack.length) :
    ∃ first second rest, environment.stack = first :: second :: rest := by
  match hstack : environment.stack with
  | [] => rw [hstack] at hheight; simp at hheight
  | [first] => rw [hstack] at hheight; simp at hheight
  | first :: second :: rest => exact ⟨first, second, rest, rfl⟩

theorem fetch_one {state : State} {value : Word} {rest : List Word}
    (hstack : state.environment.stack = value :: rest) :
    state.fetch 1 = .ok #[value] := by
  simp [State.fetch, sourceFetch, hstack]

theorem fetch_two {state : State} {first second : Word} {rest : List Word}
    (hstack : state.environment.stack = first :: second :: rest) :
    state.fetch 2 = .ok #[first, second] := by
  simp [State.fetch, sourceFetch, hstack]

theorem jump_eq_ok {environment : Environment} {cursor : ProgramCursor} {target : BlockId}
    {source targetBlock : Block}
    (hsource : program.block? cursor = some source)
    (htarget : program.block? { cursor with block := target } = some targetBlock)
    (hheight : environment.stack.length = source.outputCount)
    (harity : targetBlock.inputCount = source.outputCount) :
    jump program environment cursor target =
      .ok (environment, .running
        { cursor with block := target, position := targetBlock.startPosition }) := by
  simp [jump, hsource, htarget, hheight, harity]

theorem jump_ok_inv {environment environment' : Environment} {cursor : ProgramCursor}
    {target : BlockId} {control : Control}
    (hjump : jump program environment cursor target = .ok (environment', control)) :
    ∃ source targetBlock,
      program.block? cursor = some source ∧
      program.block? { cursor with block := target } = some targetBlock ∧
      environment.stack.length = source.outputCount ∧
      source.outputCount = targetBlock.inputCount ∧
      environment' = environment ∧
      control = .running
        { cursor with block := target, position := targetBlock.startPosition } := by
  cases hsource : program.block? cursor with
  | none => simp [jump, hsource] at hjump
  | some source =>
      cases htarget : program.block? { cursor with block := target } with
      | none => simp [jump, hsource, htarget] at hjump
      | some targetBlock =>
          by_cases hheight : environment.stack.length = source.outputCount
          · by_cases harity : source.outputCount = targetBlock.inputCount
            · simp [jump, hsource, htarget, hheight, harity] at hjump
              exact ⟨source, targetBlock, rfl, rfl, hheight, harity, hjump.1.symm,
                hjump.2.symm⟩
            · simp [jump, hsource, htarget, hheight, harity, bind, Except.bind,
                pure, Except.pure] at hjump
          · simp [jump, hsource, htarget, hheight, bind, Except.bind] at hjump

theorem resume_returned_eq_ok_iff {results : Array Word}
    {environment environment' : Environment} {destination : Destination}
    {next control : Control} :
    resume (.returned results) environment destination next = .ok (environment', control) ↔
      push environment destination results = .ok environment' ∧ control = next := by
  cases hpush : push environment destination results <;>
    simp [resume, hpush, bind, Except.bind, eq_comm]

theorem resume_halted_eq_ok_iff {environment environment' : Environment}
    {destination : Destination} {next control : Control} :
    resume .halted environment destination next = .ok (environment', control) ↔
      environment' = .empty ∧ control = .halted := by
  simp [resume, eq_comm]

theorem Program.instructionAt_cursor {control next : Control} {instruction : Instr}
    (hinstr : program.instructionAt control = some (next, instruction)) :
    ∃ cursor block index,
      control = .running cursor ∧ cursor.position = .statement index ∧
      program.block? cursor = some block ∧
      block.instructions[index]? = some instruction ∧
      next = .running { cursor with position := block.absoluteToPosition (index + 1) } := by
  cases control with
  | returned values => simp [Program.instructionAt] at hinstr
  | halted => simp [Program.instructionAt] at hinstr
  | running cursor =>
      cases hposition : cursor.position with
      | terminator => simp [Program.instructionAt, hposition] at hinstr
      | statement index =>
          cases hblock : program.block? cursor with
          | none => simp [Program.instructionAt, hposition, hblock] at hinstr
          | some block =>
              cases hfound : block.instructions[index]? with
              | none => simp [Program.instructionAt, hposition, hblock, hfound] at hinstr
              | some found =>
                  simp [Program.instructionAt, hposition, hblock, hfound] at hinstr
                  obtain ⟨rfl, rfl⟩ := hinstr
                  exact ⟨cursor, block, index, rfl, hposition, hblock, hfound, rfl⟩

theorem Program.terminatorAt_cursor {control : Control} {terminator : Terminator}
    (hterm : program.terminatorAt control = some terminator) :
    ∃ cursor block, control = .running cursor ∧ cursor.position = .terminator ∧
      program.block? cursor = some block ∧ block.terminator = terminator := by
  cases control with
  | returned values => simp [Program.terminatorAt] at hterm
  | halted => simp [Program.terminatorAt] at hterm
  | running cursor =>
      cases hposition : cursor.position with
      | statement index => simp [Program.terminatorAt, hposition] at hterm
      | terminator =>
          cases hblock : program.block? cursor with
          | none => simp [Program.terminatorAt, hposition, hblock] at hterm
          | some block =>
              simp [Program.terminatorAt, hposition, hblock] at hterm
              subst terminator
              exact ⟨cursor, block, rfl, hposition, hblock, rfl⟩

theorem Program.mem_functions_of_function? {functionId : FunctionId} {function : Function}
    (h : program.function? functionId = some function) : function ∈ program.functions :=
  Array.mem_of_getElem? h

theorem Program.block?_function {cursor : ProgramCursor} {block : Block}
    (hblock : program.block? cursor = some block) :
    ∃ function, program.function? cursor.fn = some function ∧ block ∈ function.blocks := by
  cases hfunction : program.function? cursor.fn with
  | none => simp [Program.block?, hfunction] at hblock
  | some function =>
      have hlocal : function.block? cursor.block = some block := by
        simpa [Program.block?, hfunction] using hblock
      exact ⟨function, rfl, Array.mem_of_getElem? hlocal⟩

theorem Program.callState?_eq_some_iff {functionId : FunctionId} {globals : Globals}
    {args : Array Word} {state : State} :
    program.callState? functionId globals args = some state ↔
      ∃ function, program.function? functionId = some function ∧
        args.size = function.entry.inputCount ∧
        state =
          ⟨globals, { Environment.empty with stack := args.toList },
            .running
              { fn := functionId, block := ⟨0⟩,
                position := function.entry.startPosition }⟩ := by
  cases hfunction : program.function? functionId with
  | none => simp [Program.callState?, hfunction]
  | some function =>
      by_cases harity : args.size = function.entry.inputCount
      · simp [Program.callState?, hfunction, harity, eq_comm]
      · simp [Program.callState?, hfunction, harity]

end Sir.Stack

namespace Sir

variable {program : Stack.Program}

theorem Stack.Program.WellFormed.callEdge_wellFounded
    (hwf : program.WellFormed) : WellFounded (Function.swap program.callEdge) :=
  wellFounded_swap_of_acyclic
    (index := FunctionId.id) (bound := program.functions.size)
    (fun ⟨_⟩ ⟨_⟩ h => congrArg FunctionId.mk h)
    (fun _ _ hedge => by
      obtain ⟨-, -, _, hfunction, -⟩ := hedge
      exact (Array.getElem?_eq_some_iff.mp hfunction).1)
    hwf.acyclicCalls

end Sir

namespace Sir.Stack

variable {program : Program} {ctx : CallContext}

theorem Program.function?_initId (program : Program) :
    program.function? program.initId = some program.init := by
  simp [Program.function?, Program.functions, Program.initId]

theorem Program.function?_mainId {functionId : FunctionId}
    (hmainId : program.mainId? = some functionId) :
    ∃ main, program.main = some main ∧ program.function? functionId = some main := by
  cases hmain : program.main with
  | none => simp [Program.mainId?, hmain] at hmainId
  | some main =>
      refine ⟨main, rfl, ?_⟩
      simp [Program.mainId?, hmain] at hmainId
      subst hmainId
      simp [Program.function?, Program.functions, hmain, Array.getElem?_append]

theorem sourceFetch_length_le {environment : Environment} {count : Nat}
    {values : Array Word} (hfetch : sourceFetch environment count = .ok values) :
    count ≤ environment.stack.length := by
  by_cases hfits : count ≤ environment.stack.length
  · exact hfits
  · simp [sourceFetch, hfits] at hfetch

theorem Program.instructionAt_next_block {control next : Control} {instruction : Instr}
    {cursor : ProgramCursor}
    (hcontrol : control = .running cursor)
    (hinstr : program.instructionAt control = some (next, instruction)) :
    ∃ position, next = .running { cursor with position := position } := by
  obtain ⟨found, block, index, hfound, -, -, -, hnext⟩ := Program.instructionAt_cursor hinstr
  obtain rfl := Control.running.inj (hfound.symm.trans hcontrol)
  exact ⟨_, hnext⟩

theorem Program.instructionAt_next_running {control next : Control} {instruction : Instr}
    (hinstr : program.instructionAt control = some (next, instruction)) :
    ∃ cursor, next = .running cursor := by
  obtain ⟨cursor, block, index, -, -, -, -, hnext⟩ := Program.instructionAt_cursor hinstr
  exact ⟨_, hnext⟩

theorem evaluateTerminator_iret_inv {state : State} {environment : Environment}
    {control : Control}
    (heval : evaluateTerminator program state.environment state.control .iret =
      .ok (environment, control)) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧
      state.environment.stack.length = block.outputCount ∧
      environment = state.environment ∧
      control = .returned state.environment.stack.toArray := by
  cases hcontrol : state.control with
  | returned _ | halted => simp [evaluateTerminator, hcontrol] at heval
  | running cursor =>
      cases hblock : program.block? cursor with
      | none => simp [evaluateTerminator, hcontrol, hblock] at heval
      | some block =>
          by_cases hheight : state.environment.stack.length = block.outputCount
          · simp [evaluateTerminator, hcontrol, hblock, hheight] at heval
            obtain ⟨rfl, rfl⟩ := heval
            exact ⟨cursor, block, rfl, hblock, hheight, rfl, rfl⟩
          · simp [evaluateTerminator, hcontrol, hblock, hheight, bind, Except.bind] at heval

private theorem evaluateTerminator_preserves_function
    {cursor : ProgramCursor} {state : State} {terminator : Terminator}
    {environment : Environment} {finalControl : Control}
    (hcontrol : state.control = .running cursor)
    (heval : evaluateTerminator program state.environment state.control terminator =
      .ok (environment, finalControl)) :
    finalControl = .halted ∨ (∃ results, finalControl = .returned results) ∨
      ∃ cursor', finalControl = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases terminator with
  | halt =>
      simp [evaluateTerminator] at heval
      obtain ⟨rfl, rfl⟩ := heval
      exact .inl rfl
  | jump target =>
      simp [evaluateTerminator, hcontrol] at heval
      obtain ⟨source, targetBlock, -, -, -, -, -, hfinal⟩ := jump_ok_inv heval
      exact .inr (.inr ⟨_, hfinal, rfl⟩)
  | branch thenTarget elseTarget =>
      cases hstack : state.environment.stack with
      | nil => simp [evaluateTerminator, hcontrol, hstack] at heval
      | cons condition rest =>
          simp [evaluateTerminator, hcontrol, hstack] at heval
          obtain ⟨source, targetBlock, -, -, -, -, -, hfinal⟩ := jump_ok_inv heval
          exact .inr (.inr ⟨_, hfinal, rfl⟩)
  | iret =>
      obtain ⟨cursor', block, -, -, -, -, hfinal⟩ := evaluateTerminator_iret_inv heval
      exact .inr (.inl ⟨_, hfinal⟩)

private theorem evaluateTerminator_returned_inv
    {state : State} {terminator : Terminator} {results : Array Word}
    {environment : Environment} {finalControl : Control}
    (hterm : program.atTerm state = some terminator)
    (heval : evaluateTerminator program state.environment state.control terminator =
      .ok (environment, finalControl))
    (hreturn : finalControl = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      results.size = block.outputCount := by
  cases terminator with
  | halt =>
      simp [evaluateTerminator] at heval
      obtain ⟨rfl, rfl⟩ := heval
      cases hreturn
  | jump target =>
      obtain ⟨cursor, hcontrol⟩ : ∃ cursor, state.control = .running cursor := by
        cases hcontrol : state.control with
        | running cursor => exact ⟨cursor, rfl⟩
        | returned _ | halted => simp [evaluateTerminator, hcontrol] at heval
      simp [evaluateTerminator, hcontrol] at heval
      obtain ⟨source, targetBlock, -, -, -, -, -, hfinal⟩ := jump_ok_inv heval
      rw [hfinal] at hreturn
      cases hreturn
  | branch thenTarget elseTarget =>
      obtain ⟨cursor, hcontrol⟩ : ∃ cursor, state.control = .running cursor := by
        cases hcontrol : state.control with
        | running cursor => exact ⟨cursor, rfl⟩
        | returned _ | halted => simp [evaluateTerminator, hcontrol] at heval
      cases hstack : state.environment.stack with
      | nil => simp [evaluateTerminator, hcontrol, hstack] at heval
      | cons condition rest =>
          simp [evaluateTerminator, hcontrol, hstack] at heval
          obtain ⟨source, targetBlock, -, -, -, -, -, hfinal⟩ := jump_ok_inv heval
          rw [hfinal] at hreturn
          cases hreturn
  | iret =>
      obtain ⟨cursor, block, hcontrol, hblock, hheight, -, hfinal⟩ :=
        evaluateTerminator_iret_inv heval
      rw [hfinal] at hreturn
      obtain rfl := Control.returned.inj hreturn
      refine ⟨cursor, block, hcontrol, hblock, ?_, by simpa using hheight⟩
      obtain ⟨cursor', block', hcontrol', hposition, hblock', hterminator⟩ :=
        Program.terminatorAt_cursor hterm
      obtain rfl := Control.running.inj (hcontrol'.symm.trans hcontrol)
      obtain rfl := Option.some.inj (hblock'.symm.trans hblock)
      exact hterminator

theorem SmallStep.preserves_function
    {cursor : ProgramCursor} {state final : State} {trace : Trace}
    (h : SmallStep program ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | evaluate hinstr _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | gas hinstr _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | call hinstr _ _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | malloc hinstr _ _ _ _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mallocUninit hinstr _ _ _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mstore32 hinstr _ _ _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | mload32 hinstr _ =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      exact .inr (.inr ⟨_, hnext, rfl⟩)
  | icall hinstr hargs hcall hresume =>
      obtain ⟨position, hnext⟩ := Program.instructionAt_next_block hcontrol hinstr
      cases ‹FunctionOutcome› with
      | returned results =>
          obtain ⟨-, hresumed⟩ := resume_returned_eq_ok_iff.mp hresume
          subst hresumed
          exact .inr (.inr ⟨_, hnext, rfl⟩)
      | halted =>
          obtain ⟨-, hresumed⟩ := resume_halted_eq_ok_iff.mp hresume
          subst hresumed
          exact .inl rfl
  | control hterm heval =>
      simpa [State.of] using evaluateTerminator_preserves_function hcontrol heval

theorem Proofs.Steps.preserves_function
    {cursor : ProgramCursor} {state final : State} {trace : Trace}
    (h : Steps program ctx state trace final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  Steps.inductionOn
    (motive := fun state _ final _ => state.control = .running cursor →
      final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
        ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn)
    (fun _ hcontrol => .inr (.inr ⟨cursor, hcontrol, rfl⟩))
    (fun _ next ih hcontrol => by
      rcases ih hcontrol with hhalt | ⟨results, hreturn⟩ | ⟨cursor', hcontrol', hfn⟩
      · exact absurd next (stuck_of_exit (outcome := .halted) hhalt _ _)
      · exact absurd next (stuck_of_exit (outcome := .returned _) hreturn _ _)
      · rcases SmallStep.preserves_function next hcontrol' with
          hhalt | hreturned | ⟨cursor'', hcontrol'', hfn'⟩
        · exact .inl hhalt
        · exact .inr (.inl hreturned)
        · exact .inr (.inr ⟨cursor'', hcontrol'', hfn'.trans hfn⟩))
    h hcontrol

theorem SmallStep.returned_inv
    {state final : State} {trace : Trace} {results : Array Word}
    (h : SmallStep program ctx state trace final)
    (hreturn : final.control = .returned results) :
    ∃ cursor block, state.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      results.size = block.outputCount := by
  cases h with
  | evaluate hinstr _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | gas hinstr _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | call hinstr _ _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | malloc hinstr _ _ _ _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | mallocUninit hinstr _ _ _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | mstore32 hinstr _ _ _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | mload32 hinstr _ =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      rw [hnext] at hreturn
      cases hreturn
  | icall hinstr hargs hcall hresume =>
      obtain ⟨cursor, hnext⟩ := Program.instructionAt_next_running hinstr
      cases ‹FunctionOutcome› with
      | returned actual =>
          obtain ⟨-, hresumed⟩ := resume_returned_eq_ok_iff.mp hresume
          subst hresumed
          rw [hnext] at hreturn
          cases hreturn
      | halted =>
          obtain ⟨-, hresumed⟩ := resume_halted_eq_ok_iff.mp hresume
          subst hresumed
          cases hreturn
  | control hterm heval =>
      exact evaluateTerminator_returned_inv hterm heval (by simpa [State.of] using hreturn)

theorem Proofs.Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {function : FunctionId} {globals globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hrun : EvalFn program ctx function globals args trace globals' (.returned results)) :
    (program.function? function).bind (·.outputs?) = some results.size := by
  cases hrun with
  | exit hentry hsteps hexit =>
      obtain ⟨entry, hfunction, harity, rfl⟩ := Program.callState?_eq_some_iff.mp hentry
      cases hsteps with
      | refl => cases hexit
      | tail start next =>
          obtain ⟨cursor, block, hcontrol, hblock, hterminator, hsize⟩ :=
            SmallStep.returned_inv next hexit
          rcases Proofs.Steps.preserves_function
              (cursor := ⟨function, ⟨0⟩, entry.entry.startPosition⟩) start rfl with
            hhalt | ⟨returnedValues, hreturned⟩ | ⟨cursor', hcontrol', hcursorFn⟩
          · exact absurd next (stuck_of_exit (outcome := .halted) hhalt _ _)
          · exact absurd next (stuck_of_exit (outcome := .returned _) hreturned _ _)
          · have hcursor : cursor' = cursor := Control.running.inj (hcontrol'.symm.trans hcontrol)
            have hcursorFunction : cursor.fn = function := by
              rw [← hcursor]; exact hcursorFn
            simp only [Program.block?, hcursorFunction, hfunction] at hblock
            have hiret := hwf.iretArity entry (Program.mem_functions_of_function? hfunction)
              block (Array.mem_of_getElem? hblock) hterminator
            rw [hfunction]
            simp only [Option.bind_some]
            rw [← hiret]
            exact congrArg some hsize.symm

theorem Proofs.Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initId ∨ program.mainId? = some entry)
    (hrun : EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False := by
  obtain ⟨function, hfunction, houtputs⟩ :
      ∃ function, program.function? entry = some function ∧ function.outputs? = none := by
    rcases hentry with rfl | hmainId
    · exact ⟨program.init, Program.function?_initId program, hwf.entryArity.1.2⟩
    · obtain ⟨main, hmain, hfunction⟩ := Program.function?_mainId hmainId
      exact ⟨main, hfunction, (hwf.entryArity.2 main hmain).2⟩
  have harity := Proofs.Program.WellFormed.evalFn_arity hwf hrun
  rw [hfunction] at harity
  simp [houtputs] at harity

theorem Program.WellFormed.icall_resultCount (hwf : program.WellFormed)
    {state : State} {next : Control} {callee : FunctionId}
    {argumentCount resultCount : Nat} {globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hcallee : EvalFn program ctx callee state.globals args trace globals'
      (.returned results)) :
    results.size = resultCount := by
  obtain ⟨outputs, harity, houtputs⟩ :=
    hwf.icallArity callee argumentCount resultCount (Program.instructionAt_mem hinstr)
  obtain ⟨function, hfunction, -, hfunctionOutputs⟩ := harity
  have hbind := Proofs.Program.WellFormed.evalFn_arity hwf hcallee
  rw [hfunction, Option.bind_some, hfunctionOutputs] at hbind
  rw [hbind] at houtputs
  simpa using houtputs

theorem Proofs.Program.WellFormed.icall_step
    (hwf : program.WellFormed) {state : State} {next : Control}
    {callee : FunctionId} {argumentCount resultCount : Nat}
    {args results : Array Word} {trace : Trace} {globals' : Globals}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hargs : state.fetch argumentCount = .ok args)
    (hcallee : EvalFn program ctx callee state.globals args trace globals'
      (.returned results)) :
    ∃ environment, SmallStep program ctx state trace (State.of globals' environment next) := by
  obtain ⟨environment, hpush⟩ :=
    push_ok (environment := state.environment) (destination := ⟨argumentCount, resultCount⟩)
      (sourceFetch_length_le hargs) (hwf.icall_resultCount hinstr hcallee)
  exact ⟨environment, SmallStep.icall hinstr hargs hcallee
    (resume_returned_eq_ok_iff.mpr ⟨hpush, rfl⟩)⟩

theorem Proofs.Program.icall_halted_step
    {state : State} {next : Control} {callee : FunctionId}
    {argumentCount resultCount : Nat} {args : Array Word} {trace : Trace}
    {globals' : Globals}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hargs : state.fetch argumentCount = .ok args)
    (hcallee : EvalFn program ctx callee state.globals args trace globals' .halted) :
    SmallStep program ctx state trace (State.halted globals') :=
  SmallStep.icall hinstr hargs hcallee (resume_halted_eq_ok_iff.mpr ⟨rfl, rfl⟩)

end Sir.Stack
