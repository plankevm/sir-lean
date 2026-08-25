import Sir.Stack.Proofs.Statics

namespace Sir.Stack

variable {program : Program} {ctx : CallContext}

def State.ExtraReady (state : State) : Instr → Prop
  | .exchange firstDepth secondDepth => firstDepth ≠ secondDepth
  | .load slot => ∃ value, state.environment.slots slot = some value
  | .op .malloc =>
      ∀ size, state.fetch 1 = .ok #[size] →
        ∃ allocation, state.allows size allocation ∧
          allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0)
  | .op .mallocUninit =>
      ∀ size, state.fetch 1 = .ok #[size] → ∃ allocation, state.allows size allocation
  | .op .mstore32 =>
      ∀ offset value, state.fetch 2 = .ok #[offset, value] → state.inBounds offset
  | .icall _ _ _ => False
  | _ => True

def State.InstrReady (state : State) (instruction : Instr) : Prop :=
  instruction.effect.consume ≤ state.environment.stack.length ∧ state.ExtraReady instruction

def Program.JumpReady (program : Program) (cursor : ProgramCursor) (height : Nat)
    (source : Block) (target : BlockId) : Prop :=
  height = source.outputCount ∧
    ∃ targetBlock, program.block? { cursor with block := target } = some targetBlock ∧
      targetBlock.inputCount = source.outputCount

def Program.TerminatorReady (program : Program) (cursor : ProgramCursor) (state : State)
    (source : Block) : Prop :=
  match source.terminator with
  | .halt => True
  | .jump target => program.JumpReady cursor state.environment.stack.length source target
  | .branch thenTarget elseTarget =>
      ∃ condition rest, state.environment.stack = condition :: rest ∧
        program.JumpReady cursor rest.length source
          (if condition = 0 then elseTarget else thenTarget)
  | .iret => state.environment.stack.length = source.outputCount

theorem State.pushValues_ok {state : State} {destination : Destination} {values : Array Word}
    (hheight : destination.consume ≤ state.environment.stack.length)
    (hsize : values.size = destination.produce) :
    ∃ environment, state.pushValues destination values = .ok environment :=
  push_ok hheight hsize

theorem Proofs.progress_evaluate {state : State} {next : Control} {instruction : Instr}
    (hinstr : program.atInstr state = some (next, instruction))
    (heval : ∀ error, state.evaluate ctx instruction ≠ .error error) :
    ∃ trace final, SmallStep program ctx state trace final := by
  cases hcase : state.evaluate ctx instruction with
  | error error => exact absurd hcase (heval error)
  | ok pair =>
      obtain ⟨globals, environment⟩ := pair
      exact ⟨[], _, .evaluate hinstr hcase⟩

theorem Proofs.progress_instr {state : State} {next : Control} {instruction : Instr}
    (hinstr : program.atInstr state = some (next, instruction))
    (hready : state.InstrReady instruction) :
    ∃ trace final, SmallStep program ctx state trace final := by
  obtain ⟨hheight, hextra⟩ := hready
  cases instruction with
  | push value =>
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, Except.map, push])
  | swap depth =>
      simp only [Instr.effect] at hheight
      obtain ⟨first, hfirst⟩ : ∃ value, state.environment.stack[0]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨second, hsecond⟩ : ∃ value, state.environment.stack[depth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, bind, exchange, hfirst, hsecond])
  | exchange firstDepth secondDepth =>
      simp only [Instr.effect] at hheight
      obtain ⟨first, hfirst⟩ : ∃ value, state.environment.stack[firstDepth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨second, hsecond⟩ :
          ∃ value, state.environment.stack[secondDepth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hdistinct : firstDepth ≠ secondDepth := hextra
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, bind, exchange, hdistinct, hfirst, hsecond])
  | dup depth =>
      simp only [Instr.effect] at hheight
      obtain ⟨value, hvalue⟩ : ∃ value, state.environment.stack[depth]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, hvalue])
  | pop =>
      simp only [Instr.effect] at hheight
      obtain ⟨value, rest, hstack⟩ := stack_cons (by omega)
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, hstack])
  | store slot =>
      simp only [Instr.effect] at hheight
      obtain ⟨value, rest, hstack⟩ := stack_cons (by omega)
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, hstack])
  | load slot =>
      obtain ⟨value, hvalue⟩ := hextra
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, hvalue])
  | flippedOp operation =>
      simp only [Instr.effect] at hheight
      obtain ⟨first, second, rest, hstack⟩ := stack_cons_cons (by omega)
      exact Proofs.progress_evaluate hinstr
        (by simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalBinary,
          sourceFetchFlipped, push, hstack])
  | icall callee argumentCount resultCount => exact absurd hextra not_false
  | op operation =>
      cases operation with
      | add =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨first, second, rest, hstack⟩ := stack_cons_cons (by omega)
          exact Proofs.progress_evaluate hinstr
            (by simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalBinary,
              sourceFetch, push, hstack])
      | lt =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨first, second, rest, hstack⟩ := stack_cons_cons (by omega)
          exact Proofs.progress_evaluate hinstr
            (by simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalBinary,
              sourceFetch, push, hstack])
      | sload =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨key, rest, hstack⟩ := stack_cons (by omega)
          exact Proofs.progress_evaluate hinstr
            (by simp [State.evaluate, evalInstr, Except.map, bind, Except.bind, evalSload,
              sourceFetch, push, hstack])
      | sstore =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨key, value, rest, hstack⟩ := stack_cons_cons (by omega)
          exact Proofs.progress_evaluate hinstr
            (by simp [State.evaluate, evalInstr, bind, Except.bind, pure, Except.pure,
              sourceFetch, push, hstack])
      | gas =>
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨0, 1⟩)
              (values := #[(0 : Word)]) (by simp) (by simp)
          exact ⟨[.gas 0], _, .gas hinstr hpush⟩
      | call =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨target, gasLimit, rest, hstack⟩ :
              ∃ target gasLimit rest,
                state.environment.stack = target :: gasLimit :: rest := by
            match hstack : state.environment.stack with
            | [] => rw [hstack] at hheight; simp at hheight
            | [target] => rw [hstack] at hheight; simp at hheight
            | target :: gasLimit :: rest => exact ⟨target, gasLimit, rest, rfl⟩
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨2, 1⟩)
              (values := #[Evm.UInt256.fromBool true]) (by omega) (by simp)
          exact ⟨_, _, .call
            (answer :=
              { world' := state.globals.world, success := true, output := ByteArray.empty })
            hinstr (fetch_two hstack) hpush⟩
      | malloc =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨size, rest, hstack⟩ := stack_cons (by omega)
          obtain ⟨allocation, hallow, hzero⟩ := hextra size (fetch_one hstack)
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨1, 1⟩)
              (values := #[allocation.offset]) (by omega) (by simp)
          exact ⟨[], _, .malloc hinstr (fetch_one hstack) hallow hzero hpush⟩
      | mallocUninit =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨size, rest, hstack⟩ := stack_cons (by omega)
          obtain ⟨allocation, hallow⟩ := hextra size (fetch_one hstack)
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨1, 1⟩)
              (values := #[allocation.offset]) (by omega) (by simp)
          exact ⟨[], _, .mallocUninit hinstr (fetch_one hstack) hallow hpush⟩
      | mstore32 =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨offset, value, rest, hstack⟩ := stack_cons_cons (by omega)
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨2, 0⟩)
              (values := #[]) (by omega) (by simp)
          exact ⟨[], _, .mstore32 hinstr (fetch_two hstack)
            (hextra offset value (fetch_two hstack)) hpush⟩
      | mload32 =>
          simp only [Instr.effect, Op.effect] at hheight
          obtain ⟨offset, rest, hstack⟩ := stack_cons (by omega)
          obtain ⟨environment, hpush⟩ :=
            State.pushValues_ok (state := state) (destination := ⟨1, 1⟩)
              (values :=
                #[state.globals.readWord32 offset ⟨Array.replicate 32 0, by simp⟩])
              (by omega) (by simp)
          exact ⟨[], _, .mload32 (assumed := ⟨Array.replicate 32 0, by simp⟩) hinstr
            (fetch_one hstack) hpush⟩

theorem Proofs.progress_terminator {state : State} {cursor : ProgramCursor} {source : Block}
    (hcontrol : state.control = .running cursor)
    (hposition : cursor.position = .terminator)
    (hsource : program.block? cursor = some source)
    (hready : program.TerminatorReady cursor state source) :
    ∃ final, SmallStep program ctx state [] final := by
  have hterm : program.atTerm state = some source.terminator := by
    simp [Program.atTerm, Program.terminatorAt, hcontrol, hposition, hsource]
  unfold Program.TerminatorReady at hready
  cases hcase : source.terminator with
  | halt =>
      rw [hcase] at hterm
      exact ⟨_, .control hterm rfl⟩
  | jump target =>
      rw [hcase] at hterm hready
      obtain ⟨hheight, targetBlock, htarget, harity⟩ := hready
      have heval :
          evaluateTerminator program state.environment state.control (.jump target) =
            .ok (state.environment, .running
              { cursor with block := target, position := targetBlock.startPosition }) := by
        simp only [evaluateTerminator, hcontrol]
        exact jump_eq_ok hsource htarget hheight harity
      exact ⟨_, .control hterm heval⟩
  | branch thenTarget elseTarget =>
      rw [hcase] at hterm hready
      obtain ⟨condition, rest, hstack, hheight, targetBlock, htarget, harity⟩ := hready
      have heval :
          evaluateTerminator program state.environment state.control
              (.branch thenTarget elseTarget) =
            .ok ({ state.environment with stack := rest }, .running
              { cursor with
                block := (if condition = 0 then elseTarget else thenTarget),
                position := targetBlock.startPosition }) := by
        simp only [evaluateTerminator, hcontrol, hstack]
        exact jump_eq_ok hsource htarget hheight harity
      exact ⟨_, .control hterm heval⟩
  | iret =>
      rw [hcase] at hterm hready
      have heval :
          evaluateTerminator program state.environment state.control .iret =
            .ok (state.environment, .returned state.environment.stack.toArray) := by
        simp [evaluateTerminator, hcontrol, hsource, hready]
      exact ⟨_, .control hterm heval⟩

end Sir.Stack
