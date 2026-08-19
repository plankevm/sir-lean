import Sir.Lowering.Proofs.Relocate

namespace Sir.Lowering

section VarsRelocation

variable {P Q : Vars.Program} {a b : FunctionId} {fn : Vars.Function}

theorem Vars.Program.decodeStmt_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor}
    {next : Machine.MachineControl} {statement : Vars.Stmt} (located : cursor.fn = a)
    (hdecode : P.decodeStmt (.running cursor) = some (next, statement)) :
    Q.decodeStmt (.running { cursor with fn := b }) =
      some (relabelTo b next, statement) := by
  obtain ⟨cursor', block, index, hcursor, hposition, hblock, hstatement, rfl⟩ :=
    Vars.Program.decodeStmt_cursor hdecode
  obtain rfl := Machine.MachineControl.running.inj hcursor
  rw [Vars.Program.block?] at hblock
  simp [located, hP] at hblock
  simp [Vars.Program.decodeStmt, Vars.Program.block?, hposition, hQ, hblock, hstatement,
    relabelTo]

theorem Vars.Program.terminatorAt_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor}
    {terminator : Vars.Terminator} (located : cursor.fn = a)
    (hterminator : P.terminatorAt (.running cursor) = some terminator) :
    Q.terminatorAt (.running { cursor with fn := b }) = some terminator := by
  obtain ⟨cursor', block, hcursor, hposition, hblock, rfl⟩ :=
    Vars.Program.terminatorAt_cursor hterminator
  obtain rfl := Machine.MachineControl.running.inj hcursor
  rw [Vars.Program.block?] at hblock
  simp [located, hP] at hblock
  simp [Vars.Program.terminatorAt, Vars.Program.block?, hposition, hQ, hblock]

private theorem Vars.jump_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {s s' : Vars.State}
    {cursor : Machine.ProgramCursor} {target : BlockId}
    (hcontrol : s.control = .running cursor) (located : cursor.fn = a)
    (heval : (Vars.jump P target).run s = .ok ((), s')) :
    (Vars.jump Q target).run (relabelState b s) = .ok ((), relabelState b s') := by
  have hcontrol' : (relabelState b s).control = .running { cursor with fn := b } := by
    simp [relabelState, hcontrol, relabelTo]
  cases hsrc : fn.block? cursor.block with
  | none =>
      simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
        getThe, MonadStateOf.get, hcontrol, Vars.Program.block?, located, hP, hsrc,
        throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at heval
  | some sourceBlock =>
      cases htgt : fn.block? target with
      | none =>
          simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
            getThe, MonadStateOf.get, hcontrol, Vars.Program.block?, located, hP, hsrc, htgt,
            throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at heval
      | some targetBlock =>
          cases htr : Locals.transfer sourceBlock.outputs targetBlock.inputs s.environment with
          | error e =>
              simp [Vars.jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
                get, getThe, MonadStateOf.get, hcontrol, Vars.Program.block?, located, hP,
                hsrc, htgt, liftM, monadLift,
                MonadLift.monadLift, htr, pure, Except.pure, modify, modifyGet,
                MonadStateOf.modifyGet] at heval
          | ok res =>
              obtain ⟨⟨⟩, locals'⟩ := res
              simp only [Vars.jump, StateT.run, bind, StateT.bind, Except.bind, StateT.get,
                get, getThe, MonadStateOf.get, hcontrol, Vars.Program.block?, located, hP,
                hsrc, htgt, liftM, monadLift, Option.bind_some,
                MonadLift.monadLift, htr, modify, modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
                true_and] at heval
              simp only [Vars.jump, StateT.run, bind, StateT.bind, Except.bind, StateT.get,
                get, getThe, MonadStateOf.get, hcontrol', Vars.Program.block?, hQ, hsrc, htgt,
                liftM, monadLift, Option.bind_some, MonadLift.monadLift, modify, modifyGet,
                MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure]
              rw [← heval]
              simp [relabelState, relabelTo, htr]

private theorem Vars.evaluateTerminator_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {s s' : Vars.State}
    {cursor : Machine.ProgramCursor} {terminator : Vars.Terminator}
    (hcontrol : s.control = .running cursor) (located : cursor.fn = a)
    (heval : (Vars.evaluateTerminator P terminator).run s = .ok ((), s')) :
    (Vars.evaluateTerminator Q terminator).run (relabelState b s) =
      .ok ((), relabelState b s') := by
  cases terminator with
  | halt =>
      have hhalt : (Vars.evaluateTerminator P .halt).run s =
          .ok ((), { s with control := .halted }) := rfl
      rw [hhalt] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      exact Vars.evaluateTerminator_halt_ok (relabelState b s)
  | jump target =>
      exact Vars.jump_relabel hP hQ hcontrol located heval
  | branch condition thenTarget elseTarget =>
      cases hcondition : s.environment.lookup condition with
      | error error =>
          simp only [Vars.evaluateTerminator, StateT.run, bind, StateT.bind, Locals.lookupM,
            liftM, monadLift, MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          simp at heval
      | ok value =>
          simp only [Vars.evaluateTerminator, StateT.run, bind, StateT.bind, Locals.lookupM,
            liftM, monadLift, MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, hcondition] at heval
          have henv : (relabelState b s).environment = s.environment := rfl
          simp only [Vars.evaluateTerminator, StateT.run, bind, StateT.bind, Locals.lookupM,
            liftM, monadLift, MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
            Except.pure, henv, hcondition]
          exact Vars.jump_relabel hP hQ hcontrol located heval
  | iret =>
      obtain ⟨cursor', block, rs, hcursor, hblock, houtputs, rfl⟩ :=
        Vars.evaluateTerminator_iret_inv heval
      obtain rfl := Machine.MachineControl.running.inj (hcursor.symm.trans hcontrol).symm
      rw [Vars.Program.block?] at hblock
      simp [located, hP] at hblock
      have hblock' : Q.block? { cursor with fn := b } = some block := by
        simp [Vars.Program.block?, hQ, hblock]
      have hcontrol' : (relabelState b s).control = .running { cursor with fn := b } := by
        simp [relabelState, hcontrol, relabelTo]
      have result := Vars.evaluateTerminator_iret_ok (program := Q) hcontrol' hblock'
        (rs := rs) houtputs
      simpa [relabelState, relabelTo] using result

theorem Vars.relocation (ctx : CallContext)
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    (hsupported : ∀ statement, fn.HasStmt statement →
      ∃ operation, Symbolic.operationOf statement = some operation) :
    Relocation (Vars.decoder P) (Vars.decoder Q) Machine.memoryPolicy ctx a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cursor instruction next located hdecode
    obtain ⟨statement, hstatement, rfl⟩ := Vars.decode_inv.mp hdecode
    exact Vars.decode_inv.mpr
      ⟨statement, Vars.Program.decodeStmt_relabel hP hQ located hstatement, rfl⟩
  · intro env globals cursor trace env' globals' next located hcontrol
    obtain ⟨terminator, state', hterminator, heval, rfl, rfl, rfl, rfl⟩ :=
      Vars.control_inv.mp hcontrol
    have heval' := Vars.evaluateTerminator_relabel hP hQ
      (s := ⟨globals, env, .running cursor⟩) rfl located heval
    exact Vars.control_inv.mpr ⟨terminator, relabelState b state',
      Vars.Program.terminatorAt_relabel hP hQ located hterminator, heval', rfl, rfl, rfl, rfl⟩
  · intro cursor callee src dst next located hdecode
    obtain ⟨statement, hstatement, hdecoded⟩ := Vars.decode_inv.mp hdecode
    obtain ⟨cursor', block, index, hcursor, hposition, hblock, hstatement', -⟩ :=
      Vars.Program.decodeStmt_cursor hstatement
    obtain rfl := Machine.MachineControl.running.inj hcursor
    rw [Vars.Program.block?] at hblock
    simp [located, hP] at hblock
    have hmem : block ∈ fn.blocks := by
      rw [Vars.Function.block?] at hblock
      exact Array.mem_of_getElem? hblock
    have hasStmt : fn.HasStmt statement :=
      ⟨block, hmem, Array.mem_of_getElem? hstatement'⟩
    obtain ⟨operation, hoperation⟩ := hsupported statement hasStmt
    cases statement with
    | assign result expr =>
        cases expr <;> simp [Vars.decodeStatement, Vars.decodeExpression] at hdecoded
    | icall callee' args dests => simp [Symbolic.operationOf] at hoperation
    | sstore key value => simp [Vars.decodeStatement] at hdecoded
    | gas result => simp [Vars.decodeStatement] at hdecoded
    | call c => simp [Vars.decodeStatement] at hdecoded
    | malloc result size => simp [Vars.decodeStatement] at hdecoded
    | mallocUninit result size => simp [Vars.decodeStatement] at hdecoded
    | mstore32 offset value => simp [Vars.decodeStatement] at hdecoded
    | mload32 result offset => simp [Vars.decodeStatement] at hdecoded
  · intro state trace final step located
    cases hcontrol : state.control with
    | halted =>
        exact absurd step (Machine.stuck_of_exit (outcome := .halted) hcontrol _ _)
    | returned results =>
        exact absurd step (Machine.stuck_of_exit (outcome := .returned results) hcontrol _ _)
    | running cursor =>
        rw [hcontrol] at located
        rcases Vars.SmallStep.preserves_function step hcontrol with
          hhalted | ⟨results, hreturned⟩ | ⟨cursor', hrunning, hfn⟩
        · simp [AtFunction, hhalted]
        · simp [AtFunction, hreturned]
        · rw [hrunning]
          exact hfn.trans located
  · intro globals args state hentry
    rw [Vars.entry_eq] at hentry
    obtain ⟨fn', locals₀, hfn', hbind, rfl⟩ := Vars.Program.callState?_eq_some_iff.mp hentry
    obtain rfl := Option.some.inj (hP.symm.trans hfn')
    refine ⟨?_, rfl⟩
    rw [Vars.entry_eq]
    refine Vars.Program.callState?_eq_some_iff.mpr ⟨fn, locals₀, hQ, hbind, ?_⟩
    simp [relabelState, relabelTo]

end VarsRelocation

section StackRelocation

variable {P Q : Stack.Program} {a b : FunctionId} {fn : Stack.Function}

theorem Stack.Program.decodeInstruction_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor} (located : cursor.fn = a) :
    Q.decodeInstruction (.running { cursor with fn := b }) =
      (P.decodeInstruction (.running cursor)).map fun result =>
        (relabelTo b result.1, result.2) := by
  cases hposition : cursor.position with
  | terminator =>
      simp [Stack.Program.decodeInstruction, hposition]
  | statement index =>
      cases hblockAt : fn.block? cursor.block with
      | none =>
          simp [Stack.Program.decodeInstruction, Stack.Program.block?, hposition,
            located, hP, hQ, hblockAt]
      | some block =>
          cases hinstruction : block.instructions[index]? with
          | none =>
              simp [Stack.Program.decodeInstruction, Stack.Program.block?, hposition,
                located, hP, hQ, hblockAt, hinstruction]
          | some instruction =>
              simp [Stack.Program.decodeInstruction, Stack.Program.block?, hposition,
                located, hP, hQ, hblockAt, hinstruction, relabelTo]

theorem Stack.Program.terminatorAt_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor} (located : cursor.fn = a) :
    Q.terminatorAt (.running { cursor with fn := b }) =
      P.terminatorAt (.running cursor) := by
  cases hposition : cursor.position with
  | statement index => simp [Stack.Program.terminatorAt, hposition]
  | terminator =>
      cases hblockAt : fn.block? cursor.block <;>
        simp [Stack.Program.terminatorAt, Stack.Program.block?, hposition,
          located, hP, hQ, hblockAt]

theorem Stack.Program.block?_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor} (located : cursor.fn = a) :
    Q.block? { cursor with fn := b } = P.block? cursor := by
  simp [Stack.Program.block?, located, hP, hQ]

private theorem Stack.jump_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor}
    (located : cursor.fn = a) (env : Stack.Environment) (target : BlockId) :
    Stack.jump Q env { cursor with fn := b } target =
      (Stack.jump P env cursor target).map fun result =>
        (result.1, relabelTo b result.2) := by
  have hsource := Stack.Program.block?_relabel hP hQ located
  have htarget : Q.block? { cursor with fn := b, block := target } =
      P.block? { cursor with block := target } :=
    Stack.Program.block?_relabel hP hQ (cursor := { cursor with block := target }) located
  cases hsrc : P.block? cursor with
  | none => simp [Stack.jump, hsource, hsrc, htarget]
  | some sourceBlock =>
      cases htgt : P.block? { cursor with block := target } with
      | none => simp [Stack.jump, hsource, hsrc, htarget, htgt]
      | some targetBlock =>
          by_cases mismatch : env.stack.length ≠ sourceBlock.outputCount ∨
              sourceBlock.outputCount ≠ targetBlock.inputCount
          · simp [Stack.jump, hsource, hsrc, htarget, htgt, mismatch]
          · simp [Stack.jump, hsource, hsrc, htarget, htgt, mismatch, relabelTo]

theorem Stack.control_relabel
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    {cursor : Machine.ProgramCursor}
    {env env' : Stack.Environment} {globals globals' : Globals} {trace : Trace}
    {next : Machine.MachineControl} (located : cursor.fn = a)
    (hcontrol : Stack.control P env globals (.running cursor) =
      some (trace, env', globals', next)) :
    Stack.control Q env globals (.running { cursor with fn := b }) =
      some (trace, env', globals', relabelTo b next) := by
  have hdecode := Stack.Program.decodeInstruction_relabel hP hQ located
  cases hinstruction : P.decodeInstruction (.running cursor) with
  | some decoded =>
      obtain ⟨instructionNext, instruction⟩ := decoded
      rw [hinstruction, Option.map_some] at hdecode
      cases instruction <;>
        simp only [Stack.control, hinstruction, hdecode] at hcontrol ⊢ <;>
        (repeat' split at hcontrol) <;> simp_all [Option.bind_eq_some_iff] <;> grind
  | none =>
      rw [hinstruction] at hdecode
      have hterminator := Stack.Program.terminatorAt_relabel hP hQ located
      cases hterminatorAt : P.terminatorAt (.running cursor) with
      | none => simp [Stack.control, hinstruction, hterminatorAt] at hcontrol
      | some terminator =>
          rw [hterminatorAt] at hterminator
          cases terminator with
          | halt =>
              simp [Stack.control, hinstruction, hterminatorAt] at hcontrol
              obtain ⟨rfl, rfl, rfl, rfl⟩ := hcontrol
              simp [Stack.control, hdecode, hterminator, relabelTo]
          | jump target =>
              have hjump := Stack.jump_relabel hP hQ located env target
              cases hjumpAt : Stack.jump P env cursor target with
              | none => simp [Stack.control, hinstruction, hterminatorAt, hjumpAt] at hcontrol
              | some jumpResult =>
                  obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                  simp [Stack.control, hinstruction, hterminatorAt, hjumpAt] at hcontrol
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcontrol
                  rw [hjumpAt] at hjump
                  simp [Stack.control, hdecode, hterminator, hjump]
          | branch thenTarget elseTarget =>
              cases hstack : env.stack with
              | nil => simp [Stack.control, hinstruction, hterminatorAt, hstack] at hcontrol
              | cons condition stack =>
                  have hjump := Stack.jump_relabel hP hQ located { env with stack }
                    (if condition = 0 then elseTarget else thenTarget)
                  cases hjumpAt : Stack.jump P { env with stack } cursor
                      (if condition = 0 then elseTarget else thenTarget) with
                  | none =>
                      simp [Stack.control, hinstruction, hterminatorAt, hstack, hjumpAt]
                        at hcontrol
                  | some jumpResult =>
                      obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                      simp [Stack.control, hinstruction, hterminatorAt, hstack, hjumpAt]
                        at hcontrol
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcontrol
                      rw [hjumpAt] at hjump
                      simp [Stack.control, hdecode, hterminator, hstack, hjump]
          | iret =>
              obtain ⟨cursor', block, hcursor, hblockAt, hblockTerminator⟩ :=
                stackTerminatorAt_inv hterminatorAt
              obtain rfl := Machine.MachineControl.running.inj hcursor
              have hblock' : Q.block? { cursor with fn := b } = some block := by
                rw [Stack.Program.block?_relabel hP hQ located, hblockAt]
              by_cases hlength : env.stack.length = block.outputCount
              · simp [Stack.control, hinstruction, hterminatorAt, hblockAt, hlength]
                  at hcontrol
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hcontrol
                simp [Stack.control, hdecode, hterminator, hblock', hlength, relabelTo]
              · simp [Stack.control, hinstruction, hterminatorAt, hblockAt, hlength]
                  at hcontrol

theorem Stack.Program.decodeInstruction_next
    {control next : Machine.MachineControl} {instruction : Stack.Instr}
    (hdecode : P.decodeInstruction control = some (next, instruction)) :
    ∃ cursor position, control = .running cursor ∧
      next = .running { cursor with position := position } := by
  cases control with
  | returned results => simp [Stack.Program.decodeInstruction] at hdecode
  | halted => simp [Stack.Program.decodeInstruction] at hdecode
  | running cursor =>
      cases hposition : cursor.position with
      | terminator => simp [Stack.Program.decodeInstruction, hposition] at hdecode
      | statement index =>
          cases hblockAt : P.block? cursor with
          | none => simp [Stack.Program.decodeInstruction, hposition, hblockAt] at hdecode
          | some block =>
              cases hinstruction : block.instructions[index]? with
              | none =>
                  simp [Stack.Program.decodeInstruction, hposition, hblockAt, hinstruction]
                    at hdecode
              | some found =>
                  simp [Stack.Program.decodeInstruction, hposition, hblockAt, hinstruction]
                    at hdecode
                  exact ⟨cursor, _, rfl, hdecode.1.symm⟩

theorem Stack.decode_next_fn
    {control next : Machine.MachineControl} {instruction : Machine.Instruction Stack.frame}
    (hdecode : Stack.decode P control = some (instruction, next)) :
    ∃ cursor position, control = .running cursor ∧
      next = .running { cursor with position := position } := by
  obtain ⟨decodedInstruction, hinstruction⟩ := stackDecode_decodeInstruction hdecode
  exact Stack.Program.decodeInstruction_next hinstruction

private theorem Stack.jump_next
    {env env' : Stack.Environment} {cursor : Machine.ProgramCursor} {target : BlockId}
    {next : Machine.MachineControl}
    (hjump : Stack.jump P env cursor target = some (env', next)) :
    ∃ position, next = .running { cursor with block := target, position := position } := by
  unfold Stack.jump at hjump
  cases hsrc : P.block? cursor with
  | none => simp [hsrc] at hjump
  | some sourceBlock =>
      cases htgt : P.block? { cursor with block := target } with
      | none => simp [hsrc, htgt] at hjump
      | some targetBlock =>
          by_cases mismatch : env.stack.length ≠ sourceBlock.outputCount ∨
              sourceBlock.outputCount ≠ targetBlock.inputCount
          · simp [hsrc, htgt, mismatch] at hjump
          · simp [hsrc, htgt, mismatch] at hjump
            exact ⟨targetBlock.startPosition, hjump.2.symm⟩

theorem Stack.control_next_fn
    {cursor : Machine.ProgramCursor} {env env' : Stack.Environment}
    {globals globals' : Globals} {trace : Trace} {next : Machine.MachineControl}
    (hcontrol : Stack.control P env globals (.running cursor) =
      some (trace, env', globals', next)) :
    next = .halted ∨ (∃ results, next = .returned results) ∨
      ∃ cursor', next = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases hinstruction : P.decodeInstruction (.running cursor) with
  | some decoded =>
      obtain ⟨instructionNext, instruction⟩ := decoded
      obtain ⟨cursor', position, hcursor, rfl⟩ :=
        Stack.Program.decodeInstruction_next hinstruction
      obtain rfl := Machine.MachineControl.running.inj hcursor
      cases instruction <;>
        simp only [Stack.control, hinstruction] at hcontrol <;>
        (repeat' split at hcontrol) <;> simp_all [Option.bind_eq_some_iff] <;> grind
  | none =>
      cases hterminatorAt : P.terminatorAt (.running cursor) with
      | none => simp [Stack.control, hinstruction, hterminatorAt] at hcontrol
      | some terminator =>
          cases terminator with
          | halt =>
              simp [Stack.control, hinstruction, hterminatorAt] at hcontrol
              exact .inl hcontrol.2.2.2.symm
          | jump target =>
              cases hjumpAt : Stack.jump P env cursor target with
              | none => simp [Stack.control, hinstruction, hterminatorAt, hjumpAt] at hcontrol
              | some jumpResult =>
                  obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                  simp [Stack.control, hinstruction, hterminatorAt, hjumpAt] at hcontrol
                  obtain ⟨-, -, -, rfl⟩ := hcontrol
                  obtain ⟨position, rfl⟩ := Stack.jump_next hjumpAt
                  exact .inr (.inr ⟨_, rfl, rfl⟩)
          | branch thenTarget elseTarget =>
              cases hstack : env.stack with
              | nil => simp [Stack.control, hinstruction, hterminatorAt, hstack] at hcontrol
              | cons condition stack =>
                  cases hjumpAt : Stack.jump P { env with stack } cursor
                      (if condition = 0 then elseTarget else thenTarget) with
                  | none =>
                      simp [Stack.control, hinstruction, hterminatorAt, hstack, hjumpAt]
                        at hcontrol
                  | some jumpResult =>
                      obtain ⟨jumpEnvironment, jumpControl⟩ := jumpResult
                      simp [Stack.control, hinstruction, hterminatorAt, hstack, hjumpAt]
                        at hcontrol
                      obtain ⟨-, -, -, rfl⟩ := hcontrol
                      obtain ⟨position, rfl⟩ := Stack.jump_next hjumpAt
                      exact .inr (.inr ⟨_, rfl, rfl⟩)
          | iret =>
              cases hblockAt : P.block? cursor with
              | none => simp [Stack.control, hinstruction, hterminatorAt, hblockAt] at hcontrol
              | some block =>
                  by_cases hlength : env.stack.length ≠ block.outputCount
                  · simp [Stack.control, hinstruction, hterminatorAt, hblockAt, hlength]
                      at hcontrol
                  · simp [Stack.control, hinstruction, hterminatorAt, hblockAt]
                      at hcontrol
                    exact .inr (.inl ⟨env.stack.toArray, hcontrol.2.2.2.2.symm⟩)

theorem Stack.step_atFunction {policy : Machine.MemoryPolicy} {ctx : CallContext}
    {state final : Machine.State Stack.frame} {trace : Trace}
    (step : Machine.Step Stack.frame (Stack.decoder P) policy ctx state trace final)
    (located : AtFunction a state.control) : AtFunction a final.control := by
  cases hcontrol : state.control with
  | halted =>
      exact absurd step (Machine.stuck_of_exit (outcome := .halted) hcontrol _ _)
  | returned results =>
      exact absurd step (Machine.stuck_of_exit (outcome := .returned results) hcontrol _ _)
  | running cursor =>
      rw [hcontrol] at located
      cases step with
      | operation hdecode hfires =>
          rw [hcontrol] at hdecode
          obtain ⟨cursor', position, hcursor, rfl⟩ := Stack.decode_next_fn hdecode
          obtain rfl := Machine.MachineControl.running.inj hcursor
          exact located
      | operationHalted hdecode hfires => trivial
      | internalCall hdecode hfetch hcallee hresume =>
          rename_i callee src dst next values globals' outcome env' control'
          rw [hcontrol] at hdecode
          obtain ⟨cursor', position, hcursor, rfl⟩ := Stack.decode_next_fn hdecode
          obtain rfl := Machine.MachineControl.running.inj hcursor
          change Stack.resume outcome state.environment dst _ = some (env', control') at hresume
          cases outcome with
          | returned results =>
              cases hstore : Stack.store state.environment dst results with
              | error error => simp [Stack.resume, hstore] at hresume
              | ok stored =>
                  simp [Stack.resume, hstore] at hresume
                  rw [← hresume.2]
                  exact located
          | halted =>
              simp [Stack.resume] at hresume
              rw [← hresume.2]
              trivial
      | control hstep =>
          rw [hcontrol] at hstep
          rcases Stack.control_next_fn hstep with hhalted | ⟨results, hreturned⟩ |
              ⟨cursor', hrunning, hfn⟩
          · simp [AtFunction, hhalted]
          · simp [AtFunction, hreturned]
          · rw [hrunning]
            exact hfn.trans located

theorem Stack.relocation (ctx : CallContext)
    (hP : P.function? a = some fn) (hQ : Q.function? b = some fn)
    (hnoCall : ∀ instruction, fn.HasInstr instruction →
      ∀ callee argumentCount resultCount,
        instruction ≠ .icall callee argumentCount resultCount) :
    Relocation (Stack.decoder P) (Stack.decoder Q) Machine.memoryPolicy ctx a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cursor instruction next located hdecode
    have hrelabel := Stack.Program.decodeInstruction_relabel hP hQ located
    change Stack.decode P (.running cursor) = some (instruction, next) at hdecode
    change Stack.decode Q (.running { cursor with fn := b }) =
      some (instruction, relabelTo b next)
    cases hinstruction : P.decodeInstruction (.running cursor) with
    | none => simp [Stack.decode, hinstruction] at hdecode
    | some decoded =>
        obtain ⟨instructionNext, decodedInstruction⟩ := decoded
        rw [hinstruction, Option.map_some] at hrelabel
        cases decodedInstruction with
        | op operation => simp_all [Stack.decode]
        | flippedOp operation => cases operation <;> simp_all [Stack.decode]
        | icall callee argumentCount resultCount => simp_all [Stack.decode]
        | swap depth => simp_all [Stack.decode]
        | exchange firstDepth secondDepth => simp_all [Stack.decode]
        | dup depth => simp_all [Stack.decode]
        | pop => simp_all [Stack.decode]
        | store slot => simp_all [Stack.decode]
        | load slot => simp_all [Stack.decode]
  · intro env globals cursor trace env' globals' next located hcontrol
    exact Stack.control_relabel hP hQ located hcontrol
  · intro cursor callee src dst next located hdecode
    obtain ⟨argumentCount, resultCount, hinstruction⟩ := stackDecode_icall_inv hdecode
    obtain ⟨cursor', position, hcursor, -⟩ :=
      Stack.Program.decodeInstruction_next hinstruction
    obtain rfl := Machine.MachineControl.running.inj hcursor
    cases hposition : cursor.position with
    | terminator => simp [Stack.Program.decodeInstruction, hposition] at hinstruction
    | statement index =>
        cases hblockAt : P.block? cursor with
        | none => simp [Stack.Program.decodeInstruction, hposition, hblockAt] at hinstruction
        | some block =>
            cases hfound : block.instructions[index]? with
            | none =>
                simp [Stack.Program.decodeInstruction, hposition, hblockAt, hfound]
                  at hinstruction
            | some found =>
                simp [Stack.Program.decodeInstruction, hposition, hblockAt, hfound]
                  at hinstruction
                have hfnBlock : fn.block? cursor.block = some block := by
                  rw [Stack.Program.block?] at hblockAt
                  simpa [located, hP] using hblockAt
                have hmem : block ∈ fn.blocks := by
                  rw [Stack.Function.block?] at hfnBlock
                  exact Array.mem_of_getElem? hfnBlock
                exact hnoCall found ⟨block, hmem, Array.mem_of_getElem? hfound⟩
                  callee argumentCount resultCount (by simp [hinstruction.2])
  · intro state trace final step located
    exact Stack.step_atFunction step located
  · intro globals args state hentry
    change Stack.entry P a globals args = some state at hentry
    unfold Stack.entry at hentry
    rw [hP] at hentry
    simp at hentry
    obtain ⟨hsize, rfl⟩ := hentry
    constructor
    · change Stack.entry Q b globals args = some _
      unfold Stack.entry
      rw [hQ]
      simp [hsize, relabelState, relabelTo]
    · simp [AtFunction]

end StackRelocation

section ProgramSchedule

theorem ProgramSchedule.check_init {schedule : ProgramSchedule}
    (accepted : schedule.check = .ok ()) : schedule.init.check = .ok () := by
  unfold ProgramSchedule.check at accepted
  cases hinit : schedule.init.check with
  | error error => simp [hinit] at accepted
  | ok result => cases result; rfl

theorem ProgramSchedule.check_main {schedule : ProgramSchedule} {main : StackSchedule}
    (accepted : schedule.check = .ok ()) (hmain : schedule.main = some main) :
    main.check = .ok () := by
  unfold ProgramSchedule.check at accepted
  cases hinit : schedule.init.check with
  | error error => simp [hinit] at accepted
  | ok result =>
      cases result
      simpa [hinit, hmain] using accepted

@[simp]
theorem ProgramSchedule.vars_function?_zero (schedule : ProgramSchedule) :
    schedule.vars.function? ⟨0⟩ = some schedule.init.varsFunction := by
  simp [ProgramSchedule.vars, Vars.Program.function?, Vars.Program.functions]

@[simp]
theorem ProgramSchedule.stack_function?_zero (schedule : ProgramSchedule) :
    schedule.stack.function? ⟨0⟩ = some schedule.init.stackFunction := by
  simp [ProgramSchedule.stack, Stack.Program.function?, Stack.Program.functions]

theorem ProgramSchedule.vars_function?_one {schedule : ProgramSchedule} {main : StackSchedule}
    (hmain : schedule.main = some main) :
    schedule.vars.function? ⟨1⟩ = some main.varsFunction := by
  simp [ProgramSchedule.vars, Vars.Program.function?, Vars.Program.functions, hmain]

theorem ProgramSchedule.stack_function?_one {schedule : ProgramSchedule} {main : StackSchedule}
    (hmain : schedule.main = some main) :
    schedule.stack.function? ⟨1⟩ = some main.stackFunction := by
  simp [ProgramSchedule.stack, Stack.Program.function?, Stack.Program.functions, hmain]

theorem ProgramSchedule.vars_function?_absent {schedule : ProgramSchedule} {f : FunctionId}
    (hbound : schedule.vars.functions.size ≤ f.id) :
    schedule.vars.function? f = none := by
  simp [Vars.Program.function?, Array.getElem?_eq_none hbound]

theorem ProgramSchedule.stack_function?_absent {schedule : ProgramSchedule} {f : FunctionId}
    (hbound : schedule.stack.functions.size ≤ f.id) :
    schedule.stack.function? f = none := by
  simp [Stack.Program.function?, Array.getElem?_eq_none hbound]

@[simp]
theorem StackSchedule.program_vars_function?_zero (schedule : StackSchedule) :
    schedule.program.vars.function? ⟨0⟩ = some schedule.varsFunction :=
  ProgramSchedule.vars_function?_zero schedule.program

@[simp]
theorem StackSchedule.program_stack_function?_zero (schedule : StackSchedule) :
    schedule.program.stack.function? ⟨0⟩ = some schedule.stackFunction :=
  ProgramSchedule.stack_function?_zero schedule.program

theorem Vars.EvalFn.function?_ne_none {P : Vars.Program} {ctx : CallContext}
    {f : FunctionId} {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Vars.EvalFn P ctx f globals args trace finalGlobals outcome)
    (habsent : P.function? f = none) : False := by
  cases evaluation with
  | exit hentry hrun hexit =>
      rw [Vars.entry_eq] at hentry
      simp [Vars.Program.callState?, habsent] at hentry

theorem Stack.EvalFn.function?_ne_none {P : Stack.Program} {ctx : CallContext}
    {f : FunctionId} {globals finalGlobals : Globals} {args : Array Word} {trace : Trace}
    {outcome : FunctionOutcome}
    (evaluation : Stack.EvalFn P ctx f globals args trace finalGlobals outcome)
    (habsent : P.function? f = none) : False := by
  cases evaluation with
  | exit hentry hrun hexit =>
      change Stack.entry P f globals args = some _ at hentry
      simp [Stack.entry, habsent] at hentry

theorem StackSchedule.varsFunction_statements_supported
    (schedule : StackSchedule) (accepted : schedule.check = .ok ()) :
    ∀ statement, schedule.varsFunction.HasStmt statement →
      ∃ operation, Symbolic.operationOf statement = some operation := by
  intro statement hasStmt
  exact schedule.vars_program_statements_supported accepted statement
    ⟨schedule.varsFunction, by
      simp [StackSchedule.program, ProgramSchedule.vars, Vars.Program.functions], hasStmt⟩

theorem StackSchedule.stackFunction_no_icall
    (schedule : StackSchedule) (accepted : schedule.check = .ok ()) :
    ∀ instruction, schedule.stackFunction.HasInstr instruction →
      ∀ callee argumentCount resultCount,
        instruction ≠ .icall callee argumentCount resultCount := by
  intro instruction hasInstr callee argumentCount resultCount
  obtain ⟨block, hblockMem, hinstrMem⟩ := hasInstr
  have hblocks : schedule.stackFunction.blocks =
      schedule.blocks.map fun blockSchedule => blockSchedule.stack.toBlock := by
    simp [StackSchedule.stackFunction, StackSchedule.blocks, Stack.Function.blocks]
  rw [hblocks, Array.mem_map] at hblockMem
  obtain ⟨blockSchedule, hmem, rfl⟩ := hblockMem
  have hblockAccepted := schedule.mem_blocks_check accepted blockSchedule hmem
  exact blockSchedule.instructions_exclude_internal_calls hblockAccepted instruction
    (by simpa [StackSchedule.Block.Target.toBlock] using hinstrMem)
    callee argumentCount resultCount

theorem StackSchedule.function_equiv
    (schedule : StackSchedule) (accepted : schedule.check = .ok ())
    {P : Vars.Program} {S : Stack.Program} {f : FunctionId} (ctx : CallContext)
    (hvars : P.function? f = some schedule.varsFunction)
    (hstack : S.function? f = some schedule.stackFunction)
    (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn P ctx f globals args trace finalGlobals outcome ↔
      Stack.EvalFn S ctx f globals args trace finalGlobals outcome := by
  have hsupported := schedule.varsFunction_statements_supported accepted
  have hnoCall := schedule.stackFunction_no_icall accepted
  constructor
  · intro sourceEvaluation
    have inward := (Vars.relocation ctx hvars
      schedule.program_vars_function?_zero hsupported).evaluation sourceEvaluation
    have lowered := (Proofs.StackSchedule.equiv schedule accepted ctx ⟨0⟩ globals args trace
      finalGlobals outcome).mp inward
    exact (Stack.relocation ctx schedule.program_stack_function?_zero
      hstack hnoCall).evaluation lowered
  · intro targetEvaluation
    have inward := (Stack.relocation ctx hstack
      schedule.program_stack_function?_zero hnoCall).evaluation targetEvaluation
    have lifted := (Proofs.StackSchedule.equiv schedule accepted ctx ⟨0⟩ globals args trace
      finalGlobals outcome).mpr inward
    exact (Vars.relocation ctx schedule.program_vars_function?_zero
      hvars hsupported).evaluation lifted

theorem Proofs.ProgramSchedule.equiv
    (schedule : ProgramSchedule) (accepted : schedule.check = .ok ()) :
    Equiv schedule.vars schedule.stack := by
  intro ctx f globals args trace finalGlobals outcome
  rcases f with ⟨_ | _ | index⟩
  · exact schedule.init.function_equiv (ProgramSchedule.check_init accepted) ctx
      (ProgramSchedule.vars_function?_zero schedule)
      (ProgramSchedule.stack_function?_zero schedule) globals finalGlobals args trace outcome
  · cases hmain : schedule.main with
    | some main =>
        exact main.function_equiv (ProgramSchedule.check_main accepted hmain) ctx
          (ProgramSchedule.vars_function?_one hmain)
          (ProgramSchedule.stack_function?_one hmain) globals finalGlobals args trace outcome
    | none =>
        constructor
        · intro evaluation
          exact (Vars.EvalFn.function?_ne_none evaluation (by
            simp [ProgramSchedule.vars, Vars.Program.function?, Vars.Program.functions,
              hmain])).elim
        · intro evaluation
          exact (Stack.EvalFn.function?_ne_none evaluation (by
            simp [ProgramSchedule.stack, Stack.Program.function?, Stack.Program.functions,
              hmain])).elim
  · constructor
    · intro evaluation
      refine (Vars.EvalFn.function?_ne_none evaluation ?_).elim
      apply ProgramSchedule.vars_function?_absent
      simp [ProgramSchedule.vars, Vars.Program.functions]
      cases schedule.main <;> simp
    · intro evaluation
      refine (Stack.EvalFn.function?_ne_none evaluation ?_).elim
      apply ProgramSchedule.stack_function?_absent
      simp [ProgramSchedule.stack, Stack.Program.functions]
      cases schedule.main <;> simp

end ProgramSchedule

end Sir.Lowering
