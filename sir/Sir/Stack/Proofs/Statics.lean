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

theorem Program.block?_position (cursor : ProgramCursor) (position : BlockPosition) :
    program.block? { cursor with position := position } = program.block? cursor := rfl

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
    (hwf : program.WellFormed) : WellFounded (Function.swap program.callEdge) := by
  classical
  let validFunctions := (Finset.range program.functions.size).image FunctionId.mk
  let ancestors (f : FunctionId) := validFunctions.filter fun predecessor =>
    Relation.TransGen (Function.swap program.callEdge) predecessor f
  let rank (f : FunctionId) :=
    if f.id < program.functions.size then (ancestors f).card + 1 else 0
  apply Subrelation.wf (r := fun predecessor caller => rank predecessor < rank caller) _
    (measure rank).wf
  intro predecessor caller hEdge
  have callerValid : caller.id < program.functions.size := by
    rcases hEdge with ⟨argumentCount, resultCount, function, hfunction, hinstr⟩
    exact (Array.getElem?_eq_some_iff.mp hfunction).1
  by_cases predecessorValid : predecessor.id < program.functions.size
  · have ancestorsSubset : ancestors predecessor ⊆ ancestors caller := by
      intro f hf
      simp only [ancestors, Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.tail hEdge⟩
    have predecessorMem : predecessor ∈ ancestors caller := by
      simp only [ancestors, Finset.mem_filter, validFunctions, Finset.mem_image,
        Finset.mem_range]
      exact ⟨⟨predecessor.id, predecessorValid, rfl⟩,
        Relation.TransGen.single hEdge⟩
    have predecessorNotMem : predecessor ∉ ancestors predecessor := by
      intro h
      exact hwf.acyclicCalls predecessor (Finset.mem_filter.mp h).2.swap
    have ancestorsStrict : ancestors predecessor ⊂ ancestors caller :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨ancestorsSubset, fun h => predecessorNotMem (h ▸ predecessorMem)⟩
    simp only [rank, predecessorValid, callerValid, ↓reduceIte]
    exact Nat.add_lt_add_right (Finset.card_lt_card ancestorsStrict) 1
  · simp [rank, predecessorValid, callerValid]

end Sir
