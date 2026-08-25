import Sir.Stack.Proofs.Progress

namespace Sir.Stack

variable {program : Program} {ctx : CallContext}

def Block.heightAtPosition (block : Block) : BlockPosition → Nat
  | .statement index => block.heightBefore index
  | .terminator => block.heightBefore block.instructions.size

def Block.slotsStoredAtPosition (block : Block) : BlockPosition → List Nat
  | .statement index => block.slotsStoredBefore index
  | .terminator => block.slotsStoredBefore block.instructions.size

def Environment.SlotsDefined (environment : Environment) (slots : List Nat) : Prop :=
  ∀ slot ∈ slots, ∃ value, environment.slots slot = some value

def Environment.SlotsExtend (environment extended : Environment) : Prop :=
  ∀ slot value, environment.slots slot = some value →
    ∃ value', extended.slots slot = some value'

def State.CursorAccounting (program : Program) (state : State) : Prop :=
  match state.control with
  | .running cursor =>
      ∃ block, program.block? cursor = some block ∧
        block.heightAtPosition cursor.position = state.environment.stack.length ∧
        state.environment.SlotsDefined (block.slotsStoredAtPosition cursor.position)
  | .returned _ | .halted => True

theorem Block.heightAtPosition_start (block : Block) :
    block.heightAtPosition block.startPosition = block.inputCount := by
  cases hsize : block.instructions.size with
  | zero =>
      simp [Block.startPosition, Block.absoluteToPosition, Block.heightAtPosition,
        Block.heightBefore, hsize]
  | succ size =>
      simp [Block.startPosition, Block.absoluteToPosition, Block.heightAtPosition,
        Block.heightBefore, hsize]

theorem Block.slotsStoredAtPosition_start (block : Block) :
    block.slotsStoredAtPosition block.startPosition = [] := by
  cases hsize : block.instructions.size with
  | zero =>
      simp [Block.startPosition, Block.absoluteToPosition, Block.slotsStoredAtPosition,
        Block.slotsStoredBefore, hsize]
  | succ size =>
      simp [Block.startPosition, Block.absoluteToPosition, Block.slotsStoredAtPosition,
        Block.slotsStoredBefore, hsize]

theorem Block.heightAtPosition_next {block : Block} {index : Nat} {instruction : Instr}
    (hinstruction : block.instructions[index]? = some instruction) :
    block.heightAtPosition (block.absoluteToPosition (index + 1)) =
      instruction.effect.after (block.heightBefore index) := by
  have hindex : index < block.instructions.size :=
    (Array.getElem?_eq_some_iff.mp hinstruction).choose
  have hbefore :
      block.heightBefore (index + 1) =
        instruction.effect.after (block.heightBefore index) := by
    simp [Block.heightBefore, hinstruction]
  by_cases hnext : index + 1 < block.instructions.size
  · simp [Block.absoluteToPosition, hnext, Block.heightAtPosition, hbefore]
  · have hsize : block.instructions.size = index + 1 := by omega
    simp [Block.absoluteToPosition, Block.heightAtPosition, hsize, hbefore]

theorem Block.slotsStoredAtPosition_next {block : Block} {index : Nat} {instruction : Instr}
    (hinstruction : block.instructions[index]? = some instruction) :
    block.slotsStoredAtPosition (block.absoluteToPosition (index + 1)) =
      block.slotsStoredBefore index ++ instruction.slotsStored := by
  have hindex : index < block.instructions.size :=
    (Array.getElem?_eq_some_iff.mp hinstruction).choose
  have hbefore :
      block.slotsStoredBefore (index + 1) =
        block.slotsStoredBefore index ++ instruction.slotsStored := by
    simp [Block.slotsStoredBefore, hinstruction]
  by_cases hnext : index + 1 < block.instructions.size
  · simp [Block.absoluteToPosition, hnext, Block.slotsStoredAtPosition, hbefore]
  · have hsize : block.instructions.size = index + 1 := by omega
    simp [Block.absoluteToPosition, Block.slotsStoredAtPosition, hsize, hbefore]

theorem State.evaluate_accounting {state : State} {instruction : Instr}
    {globals : Globals} {environment : Environment}
    (hfits : instruction.effect.consume ≤ state.environment.stack.length)
    (heval : state.evaluate ctx instruction = .ok (globals, environment)) :
    environment.stack.length = instruction.effect.after state.environment.stack.length ∧
      state.environment.SlotsExtend environment ∧
      environment.SlotsDefined instruction.slotsStored := by
  cases instruction with
  | push value =>
      simp [State.evaluate, evalInstr, Except.map, push] at heval
      obtain ⟨-, rfl⟩ := heval
      exact ⟨by simp [Instr.effect, Destination.after],
        fun slot value hslot => ⟨value, hslot⟩,
        by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | swap depth =>
      simp only [Instr.effect] at hfits
      obtain ⟨first, hfirst⟩ : ∃ value, state.environment.stack[0]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨second, hsecond⟩ : ∃ value, state.environment.stack[depth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp [State.evaluate, evalInstr, exchange, bind, hfirst, hsecond] at heval
      obtain ⟨-, rfl⟩ := heval
      exact ⟨by simp [Instr.effect, Destination.after]; omega,
        fun slot value hslot => ⟨value, hslot⟩,
        by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | exchange firstDepth secondDepth =>
      simp only [Instr.effect] at hfits
      by_cases hdistinct : firstDepth = secondDepth
      · simp [State.evaluate, evalInstr, hdistinct] at heval
      · obtain ⟨first, hfirst⟩ :
            ∃ value, state.environment.stack[firstDepth]? = some value :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨second, hsecond⟩ :
            ∃ value, state.environment.stack[secondDepth]? = some value :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        simp [State.evaluate, evalInstr, exchange, bind, hdistinct, hfirst, hsecond] at heval
        obtain ⟨-, rfl⟩ := heval
        exact ⟨by simp [Instr.effect, Destination.after]; omega,
          fun slot value hslot => ⟨value, hslot⟩,
          by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | dup depth =>
      simp only [Instr.effect] at hfits
      obtain ⟨value, hvalue⟩ : ∃ value, state.environment.stack[depth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp [State.evaluate, evalInstr, hvalue] at heval
      obtain ⟨-, rfl⟩ := heval
      exact ⟨by simp [Instr.effect, Destination.after]; omega,
        fun slot value hslot => ⟨value, hslot⟩,
        by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | pop =>
      simp only [Instr.effect] at hfits
      obtain ⟨value, rest, hstack⟩ := stack_cons (by omega)
      simp [State.evaluate, evalInstr, hstack] at heval
      obtain ⟨-, rfl⟩ := heval
      exact ⟨by simp [Instr.effect, Destination.after, hstack],
        fun slot value hslot => ⟨value, hslot⟩,
        by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | store slot =>
      simp only [Instr.effect] at hfits
      obtain ⟨value, rest, hstack⟩ := stack_cons (by omega)
      simp [State.evaluate, evalInstr, hstack] at heval
      obtain ⟨-, rfl⟩ := heval
      refine ⟨by simp [Instr.effect, Destination.after, hstack], ?_, ?_⟩
      · intro candidate stored hstored
        by_cases hsame : candidate = slot
        · exact ⟨value, by simp [Environment.storeSlot, hsame]⟩
        · exact ⟨stored, by simpa [Environment.storeSlot, hsame] using hstored⟩
      · intro candidate hcandidate
        simp only [Instr.slotsStored, List.mem_singleton] at hcandidate
        exact ⟨value, by simp [Environment.storeSlot, hcandidate]⟩
  | load slot =>
      cases hslot : state.environment.slots slot with
      | none => simp [State.evaluate, evalInstr, hslot] at heval
      | some value =>
          simp [State.evaluate, evalInstr, hslot] at heval
          obtain ⟨-, rfl⟩ := heval
          exact ⟨by simp [Instr.effect, Destination.after],
            fun slot value hslot => ⟨value, hslot⟩,
            by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | flippedOp operation =>
      simp only [Instr.effect] at hfits
      obtain ⟨first, second, rest, hstack⟩ := stack_cons_cons (by omega)
      simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalBinary,
        sourceFetchFlipped, push, hstack] at heval
      obtain ⟨-, rfl⟩ := heval
      exact ⟨by simp [Instr.effect, Destination.after, hstack],
        fun slot value hslot => ⟨value, hslot⟩,
        by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
  | icall callee argumentCount resultCount =>
      simp [State.evaluate, evalInstr] at heval
  | op operation =>
      cases operation with
      | add | lt =>
          simp only [Instr.effect, Op.effect] at hfits
          obtain ⟨first, second, rest, hstack⟩ := stack_cons_cons (by omega)
          all_goals
            simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalBinary,
              sourceFetch, push, hstack] at heval
          all_goals obtain ⟨-, rfl⟩ := heval
          all_goals
            exact ⟨by simp [Instr.effect, Op.effect, Destination.after, hstack],
              fun slot value hslot => ⟨value, hslot⟩,
              by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
      | sload =>
          simp only [Instr.effect, Op.effect] at hfits
          obtain ⟨key, rest, hstack⟩ := stack_cons (by omega)
          simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalSload,
            sourceFetch, push, hstack] at heval
          obtain ⟨-, rfl⟩ := heval
          exact ⟨by simp [Instr.effect, Op.effect, Destination.after, hstack],
            fun slot value hslot => ⟨value, hslot⟩,
            by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
      | sstore =>
          simp only [Instr.effect, Op.effect] at hfits
          obtain ⟨key, value, rest, hstack⟩ := stack_cons_cons (by omega)
          simp [State.evaluate, evalInstr, bind, Except.bind, pure, Except.pure,
            sourceFetch, push, hstack] at heval
          obtain ⟨-, rfl⟩ := heval
          exact ⟨by simp [Instr.effect, Op.effect, Destination.after, hstack],
            fun slot value hslot => ⟨value, hslot⟩,
            by simp [Instr.slotsStored, Environment.SlotsDefined]⟩
      | gas | call | malloc | mallocUninit | mstore32 | mload32 =>
          all_goals simp [State.evaluate, evalInstr] at heval

theorem slotsExtend_of_push {environment environment' : Environment}
    {destination : Destination} {values : Array Word}
    (hpush : push environment destination values = .ok environment') :
    environment.SlotsExtend environment' :=
  fun slot value hslot => ⟨value, by rw [push_slots hpush]; exact hslot⟩

theorem Program.WellFormed.blockStatics (hwf : program.WellFormed)
    {cursor : ProgramCursor} {block : Block}
    (hblock : program.block? cursor = some block) :
    block.StackHeightsFit ∧ block.SlotsStoredBeforeLoad ∧
      ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, program.block? { cursor with block := target } = some targetBlock ∧
          targetBlock.inputCount = block.outputCount := by
  obtain ⟨function, hfunction, hmembership⟩ := Program.block?_function hblock
  have hmember := Program.mem_functions_of_function? hfunction
  refine ⟨hwf.stackHeightsFit function hmember block hmembership,
    hwf.slotsStoredBeforeLoad function hmember block hmembership, ?_⟩
  intro target htarget
  obtain ⟨targetBlock, htargetBlock, harity⟩ :=
    hwf.validJumpTargets function hmember block hmembership target htarget
  exact ⟨targetBlock, by simp [Program.block?, hfunction, htargetBlock], harity⟩

theorem State.cursorAccounting_after_instr
    {state : State} {globals : Globals} {environment : Environment} {next : Control}
    {instruction : Instr} {cursor : ProgramCursor} {block : Block} {index : Nat}
    (hblock : program.block? cursor = some block)
    (hinstruction : block.instructions[index]? = some instruction)
    (hnext : next = .running { cursor with position := block.absoluteToPosition (index + 1) })
    (hheight : block.heightBefore index = state.environment.stack.length)
    (hslots : state.environment.SlotsDefined (block.slotsStoredBefore index))
    (hlen : environment.stack.length =
      instruction.effect.after state.environment.stack.length)
    (hextend : state.environment.SlotsExtend environment)
    (hstored : environment.SlotsDefined instruction.slotsStored) :
    (State.of globals environment next).CursorAccounting program := by
  subst hnext
  refine ⟨block, hblock, ?_, ?_⟩
  · rw [Block.heightAtPosition_next hinstruction, hheight]
    exact hlen.symm
  · rw [Block.slotsStoredAtPosition_next hinstruction]
    intro slot hslot
    rcases List.mem_append.mp hslot with hslot | hslot
    · obtain ⟨value, hvalue⟩ := hslots slot hslot
      exact hextend slot value hvalue
    · exact hstored slot hslot

theorem Program.WellFormed.instructionAt_fits (hwf : program.WellFormed) {state : State}
    {next : Control} {instruction : Instr}
    (haccounting : state.CursorAccounting program)
    (hinstr : program.atInstr state = some (next, instruction)) :
    ∃ cursor block index,
      program.block? cursor = some block ∧
      block.instructions[index]? = some instruction ∧
      next = .running { cursor with position := block.absoluteToPosition (index + 1) } ∧
      block.heightBefore index = state.environment.stack.length ∧
      state.environment.SlotsDefined (block.slotsStoredBefore index) ∧
      instruction.effect.consume ≤ state.environment.stack.length := by
  obtain ⟨cursor, block, index, hcontrol, hposition, hblock, hinstruction, hnext⟩ :=
    Program.instructionAt_cursor hinstr
  unfold State.CursorAccounting at haccounting
  rw [hcontrol] at haccounting
  obtain ⟨accounted, haccounted, hheight, hslots⟩ := haccounting
  have hsame : accounted = block := Option.some.inj (haccounted.symm.trans hblock)
  subst accounted
  rw [hposition] at hheight hslots
  refine ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, ?_⟩
  rw [← hheight]
  exact (hwf.blockStatics hblock).1.1 index instruction hinstruction

theorem State.cursorAccounting_after_terminator
    {state : State} {terminator : Terminator} {environment : Environment}
    {finalControl : Control}
    (hterm : program.atTerm state = some terminator)
    (heval : evaluateTerminator program state.environment state.control terminator =
      .ok (environment, finalControl)) :
    (State.of state.globals environment finalControl).CursorAccounting program := by
  obtain ⟨cursor, block, hcontrol, hposition, hblock, hblockTerminator⟩ :=
    Program.terminatorAt_cursor hterm
  subst hblockTerminator
  cases hcase : block.terminator with
  | halt =>
      rw [hcase] at heval
      simp [evaluateTerminator] at heval
      obtain ⟨-, rfl⟩ := heval
      trivial
  | jump target =>
      rw [hcase] at heval
      simp only [evaluateTerminator, hcontrol] at heval
      obtain ⟨source, targetBlock, hsource, htarget, hheight, harity, rfl, rfl⟩ :=
        jump_ok_inv heval
      refine ⟨targetBlock, htarget, ?_, ?_⟩
      · rw [Block.heightAtPosition_start]
        exact (hheight.trans harity).symm
      · rw [Block.slotsStoredAtPosition_start]
        simp [Environment.SlotsDefined]
  | branch thenTarget elseTarget =>
      rw [hcase] at heval
      simp only [evaluateTerminator, hcontrol] at heval
      cases hstack : state.environment.stack with
      | nil => rw [hstack] at heval; simp at heval
      | cons condition rest =>
          rw [hstack] at heval
          simp only at heval
          obtain ⟨source, targetBlock, hsource, htarget, hheight, harity, rfl, rfl⟩ :=
            jump_ok_inv heval
          refine ⟨targetBlock, htarget, ?_, ?_⟩
          · rw [Block.heightAtPosition_start]
            exact (hheight.trans harity).symm
          · rw [Block.slotsStoredAtPosition_start]
            simp [Environment.SlotsDefined]
  | iret =>
      rw [hcase] at heval
      by_cases hheight : state.environment.stack.length = block.outputCount
      · simp [evaluateTerminator, hcontrol, hblock, hheight] at heval
        obtain ⟨-, rfl⟩ := heval
        trivial
      · simp [evaluateTerminator, hcontrol, hblock, hheight, bind, Except.bind] at heval

theorem Program.WellFormed.cursorAccounting_step (hwf : program.WellFormed)
    {state final : State} {trace : Trace}
    (haccounting : state.CursorAccounting program)
    (hstep : SmallStep program ctx state trace final) :
    final.CursorAccounting program := by
  cases hstep with
  | evaluate hinstr heval =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, hfits⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      obtain ⟨hlen, hextend, hstored⟩ := State.evaluate_accounting hfits heval
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        hlen hextend hstored
  | gas hinstr hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | call hinstr hfetch hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | malloc hinstr hfetch hallow hzero hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | mallocUninit hinstr hfetch hallow hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | mstore32 hinstr hfetch hbound hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | mload32 hinstr hfetch hpush =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      exact State.cursorAccounting_after_instr hblock hinstruction hnext hheight hslots
        (push_stack_length hpush) (slotsExtend_of_push hpush)
        (by simp [Instr.slotsStored, Environment.SlotsDefined])
  | icall hinstr hargs hcall hresume =>
      obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, -⟩ :=
        hwf.instructionAt_fits haccounting hinstr
      cases ‹FunctionOutcome› with
      | returned results =>
          obtain ⟨hpush, hresumed⟩ := resume_returned_eq_ok_iff.mp hresume
          exact State.cursorAccounting_after_instr hblock hinstruction
            (hresumed.trans hnext) hheight hslots
            (push_stack_length hpush) (slotsExtend_of_push hpush)
            (by simp [Instr.slotsStored, Environment.SlotsDefined])
      | halted =>
          obtain ⟨rfl, rfl⟩ := resume_halted_eq_ok_iff.mp hresume
          trivial
  | control hterm heval =>
      exact State.cursorAccounting_after_terminator hterm heval

theorem Program.WellFormed.cursorAccounting_steps (hwf : program.WellFormed)
    {initial final : State} {trace : Trace}
    (haccounting : initial.CursorAccounting program)
    (hsteps : Steps program ctx initial trace final) :
    final.CursorAccounting program :=
  Steps.inductionOn
    (motive := fun initial _ final _ =>
      initial.CursorAccounting program → final.CursorAccounting program)
    (fun _ haccounting => haccounting)
    (fun _ next ih haccounting => hwf.cursorAccounting_step (ih haccounting) next)
    hsteps haccounting

theorem Program.callState?_cursorAccounting {function : FunctionId} {globals : Globals}
    {args : Array Word} {state : State}
    (hentry : program.callState? function globals args = some state) :
    state.CursorAccounting program := by
  obtain ⟨entry, hfunction, harity, rfl⟩ := Program.callState?_eq_some_iff.mp hentry
  refine ⟨entry.entry,
    by simp [Program.block?, hfunction, Function.block?, Function.blocks], ?_, ?_⟩
  · rw [Block.heightAtPosition_start]
    simp [harity]
  · rw [Block.slotsStoredAtPosition_start]
    simp [Environment.SlotsDefined]

theorem Program.WellFormed.cursorAccounting_runsFunction (hwf : program.WellFormed)
    {function : FunctionId} {globals : Globals} {args : Array Word} {trace : Trace}
    {state : State}
    (hrun : program.RunsFunction ctx function globals args trace state) :
    state.CursorAccounting program := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  exact hwf.cursorAccounting_steps (Program.callState?_cursorAccounting hentry) hsteps

theorem Program.WellFormed.instrReady_of_cursorAccounting (hwf : program.WellFormed)
    {state : State} {next : Control} {instruction : Instr}
    (haccounting : state.CursorAccounting program)
    (hinstr : program.atInstr state = some (next, instruction))
    (hnonIcall : ∀ callee argumentCount resultCount,
      instruction ≠ .icall callee argumentCount resultCount)
    (hallocation : program.AllocationAvailable state)
    (hstore : program.StoreInBounds state) :
    state.InstrReady instruction := by
  obtain ⟨cursor, block, index, hblock, hinstruction, hnext, hheight, hslots, hfits⟩ :=
    hwf.instructionAt_fits haccounting hinstr
  refine ⟨hfits, ?_⟩
  cases instruction with
  | exchange firstDepth secondDepth =>
      exact hwf.exchangeDepthsDistinct firstDepth secondDepth
        (Program.instructionAt_mem hinstr)
  | load slot =>
      have hstatic := (hwf.blockStatics hblock).2.1 index (.load slot) hinstruction
      exact hslots slot (hstatic slot (by simp [Instr.slotsRead]))
  | icall callee argumentCount resultCount =>
      exact absurd rfl (hnonIcall callee argumentCount resultCount)
  | op operation =>
      cases operation with
      | malloc =>
          intro size hfetch
          obtain ⟨allocation, hvalid, hsize, hzero⟩ := hallocation.1 next size hinstr hfetch
          exact ⟨allocation, ⟨hvalid, hsize⟩, hzero⟩
      | mallocUninit =>
          intro size hfetch
          obtain ⟨allocation, hvalid, hsize⟩ := hallocation.2 next size hinstr hfetch
          exact ⟨allocation, hvalid, hsize⟩
      | mstore32 =>
          intro offset value hfetch
          exact hstore next offset value hinstr hfetch
      | add | lt | sload | sstore | gas | call | mload32 => trivial
  | push _ | swap _ | dup _ | pop | store _ | flippedOp _ => trivial

theorem Program.WellFormed.terminatorReady_of_cursorAccounting (hwf : program.WellFormed)
    {state : State} {cursor : ProgramCursor} {block : Block}
    (haccounting : state.CursorAccounting program)
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hblock : program.block? cursor = some block) :
    program.TerminatorReady cursor state block := by
  unfold State.CursorAccounting at haccounting
  rw [hcontrol] at haccounting
  obtain ⟨accounted, haccounted, hheight, -⟩ := haccounting
  have hsame : accounted = block := Option.some.inj (haccounted.symm.trans hblock)
  subst accounted
  rw [hposition] at hheight
  simp only [Block.heightAtPosition] at hheight
  have hstatics := hwf.blockStatics hblock
  have hfit := hstatics.1.2
  unfold Program.TerminatorReady
  cases hcase : block.terminator with
  | halt => trivial
  | jump target =>
      rw [hcase] at hfit
      obtain ⟨targetBlock, htargetBlock, harity⟩ :=
        hstatics.2.2 target (by simp [hcase, Terminator.jumpTargets])
      exact ⟨hheight.symm.trans hfit, targetBlock, htargetBlock, harity⟩
  | branch thenTarget elseTarget =>
      rw [hcase] at hfit
      have hlength : state.environment.stack.length = block.outputCount + 1 :=
        hheight.symm.trans hfit
      obtain ⟨condition, rest, hstack⟩ :=
        stack_cons (environment := state.environment) (by omega)
      have hrest : rest.length = block.outputCount := by
        rw [hstack] at hlength
        simpa using hlength
      obtain ⟨targetBlock, htargetBlock, harity⟩ :=
        hstatics.2.2 (if condition = 0 then elseTarget else thenTarget) (by
          by_cases hzero : condition = 0 <;>
            simp [hzero, hcase, Terminator.jumpTargets])
      exact ⟨condition, rest, hstack, hrest, targetBlock, htargetBlock, harity⟩
  | iret =>
      rw [hcase] at hfit
      exact hheight.symm.trans hfit

theorem Proofs.Program.WellFormed.progress_reachable_nonIcall (hwf : program.WellFormed)
    {function : FunctionId} {globals : Globals} {args : Array Word} {runTrace : Trace}
    {state : State}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hallocation : program.AllocationAvailable state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  have haccounting := hwf.cursorAccounting_runsFunction hrun
  rcases hcontrol with ⟨next, instruction, hinstr, hnonIcall⟩ | ⟨terminator, hterm⟩
  · exact Proofs.progress_instr hinstr
      (hwf.instrReady_of_cursorAccounting haccounting hinstr hnonIcall hallocation hstore)
  · obtain ⟨cursor, block, hcontrol, hposition, hblock, -⟩ :=
      Program.terminatorAt_cursor hterm
    obtain ⟨state', hstep⟩ := Proofs.progress_terminator hcontrol hposition hblock
      (hwf.terminatorReady_of_cursorAccounting haccounting hcontrol hposition hblock)
    exact ⟨[], state', hstep⟩

end Sir.Stack
