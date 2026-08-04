import Sir.Proofs.Steps

namespace Sir

variable {program : Program} {ctx : CallContext}

def Program.paramsOf (program : Program) (function : FunctionId) : Option (Array VarId) := do
  let fn ← program.function? function
  fn.paramsOf

theorem Program.mem_functions_of_function? {p : Program} {f : FunctionId} {fn : Function}
    (h : p.function? f = some fn) : fn ∈ p.functions :=
  Array.mem_of_getElem? h

theorem Program.functionInputOutputArity_iff
    {p : Program} {inputCount : Nat} {outputCount : Option Nat}
    {functionId : FunctionId} :
    p.FunctionInputOutputArity inputCount outputCount functionId ↔
      ∃ fn, p.function? functionId = some fn ∧
        fn.paramsOf.map (·.size) = some inputCount ∧ fn.outputs? = outputCount := by
  rfl

theorem Program.WellFormed.callEdge_wellFounded
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
    rcases hEdge with ⟨args, dests, fn, hfn, hstmt⟩
    exact (Array.getElem?_eq_some_iff.mp hfn).1
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

private theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = .ok bs → bs.length = l.length
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      simp [← h]
  | a :: l, bs, h => by
      simp only [List.mapM_cons] at h
      cases hfa : f a with
      | error e => simp [hfa, bind, Except.bind] at h
      | ok b =>
        cases hml : l.mapM f with
        | error e => simp [hfa, hml, bind, Except.bind] at h
        | ok bs' =>
          simp only [hfa, hml, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at h
          simp [← h, mapM_ok_length hml]

theorem mapM_ok_size {α β ε : Type} {f : α → Except ε β}
    {as : Array α} {bs : Array β} (h : as.mapM f = .ok bs) : bs.size = as.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hml : as.toList.mapM f with
  | error e => simp [hml, Functor.map, Except.map] at h
  | ok l =>
    simp only [hml, Functor.map, Except.map, Except.ok.injEq] at h
    simpa [← h] using mapM_ok_length hml

theorem Locals.bindValues_total (dst : Locals) {targetVars : Array VarId}
    {vs : Array Word} (h : targetVars.size = vs.size) :
    ∃ l', Locals.bindValues dst targetVars vs = .ok l' :=
  ⟨_, by simp [Locals.bindValues, h]; rfl⟩

theorem Program.WellFormed.icall_paramsOf
    (hwf : program.WellFormed) {control nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId}
    (hstmt : program.decodeStmt control = some (nextControl, .icall callee args dests)) :
    (∃ ps, program.paramsOf callee = some ps ∧ ps.size = args.size) ∧
      ((program.function? callee).bind (·.outputs?)).getD 0 = dests.size := by
  obtain ⟨outputs, harity, hdests⟩ :=
    hwf.icallArity callee args dests (Program.decodeStmt_mem hstmt)
  rcases Program.functionInputOutputArity_iff.mp harity with
    ⟨fn, hfn, hparams, houtputs⟩
  cases hps : fn.paramsOf with
  | none => simp [hps] at hparams
  | some ps =>
      refine ⟨⟨ps, ?_, by simpa [hps] using hparams⟩, ?_⟩
      · simp [Program.paramsOf, hfn, hps]
      · simp [hfn, houtputs, hdests]

theorem Program.WellFormed.icall_bindParams
    (hwf : program.WellFormed) {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.locals.lookup ·) = .ok vs) :
    ∃ ps locals₀, program.paramsOf callee = some ps ∧
      Locals.bindParams ps vs = .ok locals₀ := by
  obtain ⟨⟨ps, hps, hsize⟩, -⟩ := hwf.icall_paramsOf hstmt
  obtain ⟨locals₀, hbind⟩ :=
    Locals.bindValues_total Locals.empty (hsize.trans (mapM_ok_size hargs).symm)
  exact ⟨ps, locals₀, hps, hbind⟩

theorem Program.WellFormed.evalFn_arity_proof
    (hwf : program.WellFormed) {function : FunctionId} {globals globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hrun : Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder program) Generic.MemoryPolicy.permissive ctx
      function globals args trace globals' (.returned results)) :
    (program.function? function).bind (·.outputs?) = some results.size := by
  cases hrun with
  | returned hentry hsteps hreturn =>
      rw [sirEntry_eq] at hentry
      obtain ⟨initial, hcallState, rfl⟩ := Option.map_eq_some_iff.mp hentry
      obtain ⟨fn, entryBlock, locals₀, hfn, hentryBlock, hbind, rfl⟩ :=
        Program.callState?_eq_some_iff.mp hcallState
      cases hsteps with
      | refl => cases hreturn
      | tail start next =>
          have hinv := SmallStep.returned_inv
            (state := Generic.GenericState.toMachine _) (final := Generic.GenericState.toMachine _)
            next hreturn
          obtain ⟨cursor, block, hcontrol, hblock, hterm, houtputs⟩ := hinv
          rcases Steps.preserves_function_proof
              (cursor := ⟨function, fn.entry, entryBlock.startPosition⟩)
              (state := (⟨globals, locals₀,
                .running ⟨function, fn.entry, entryBlock.startPosition⟩⟩ : MachineState))
              (final := Generic.GenericState.toMachine _) start rfl with
            hhalt | ⟨returnedValues, hreturned⟩ | ⟨cursor', hcontrol', hcursorFn⟩
          · exact absurd next
              (Generic.stuck_of_halted (Generic.sirDecoder_terminal program) hhalt _ _)
          · exact absurd next
              (Generic.stuck_of_returned (Generic.sirDecoder_terminal program) hreturned _ _)
          · have hsame : cursor' = cursor :=
              MachineControl.running.inj (hcontrol'.symm.trans hcontrol)
            subst cursor'
            change cursor.fn = function at hcursorFn
            simp only [Program.block?, hcursorFn, hfn] at hblock
            have harity := hwf.iretArity fn (Program.mem_functions_of_function? hfn)
              block (Array.mem_of_getElem? hblock) hterm
            rw [hfn]
            simp only [Option.bind_some]
            rw [← harity, mapM_ok_size houtputs]

theorem Program.WellFormed.evalFn_entry_not_returned_proof
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initEntry ∨ program.mainEntry = some entry)
    (hrun : EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False := by
  have harity : program.FunctionInputOutputArity 0 none entry := by
    rcases hentry with rfl | hmain
    · exact hwf.entryArity.1
    · exact hwf.entryArity.2 entry hmain
  rcases Program.functionInputOutputArity_iff.mp harity with
    ⟨fn, hfn, -, houtputs⟩
  have hreturn := hwf.evalFn_arity_proof hrun
  rw [hfn] at hreturn
  simp [houtputs] at hreturn

theorem Program.WellFormed.icall_bindReturns
    (hwf : program.WellFormed) {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId}
    {g g' : Globals} {vs rs : Array Word} {t : Trace}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hcallee : EvalFn program ctx callee g vs t g' (.returned rs)) :
    ∃ locals', Locals.bindReturns s.locals dests rs = .ok locals' := by
  obtain ⟨-, houtputs⟩ := hwf.icall_paramsOf hstmt
  rw [hwf.evalFn_arity_proof hcallee, Option.getD_some] at houtputs
  exact Locals.bindValues_total s.locals houtputs.symm

theorem Program.WellFormed.icall_step_proof
    (hwf : program.WellFormed) {state : MachineState} {next : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {values results : Array Word}
    {trace : Trace} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder program) Generic.MemoryPolicy.permissive ctx
      callee state.globals values trace globals' (.returned results)) :
    ∃ locals', Generic.GenericStep localOperandFrame (sirDecoder program) Generic.MemoryPolicy.permissive ctx
      state.toGenericState trace
        { state with globals := globals', locals := locals', control := next }.toGenericState := by
  obtain ⟨locals', hbind⟩ := hwf.icall_bindReturns hdecode hcallee
  exact ⟨locals', step_icall hdecode hargs hcallee hbind⟩

theorem Program.icall_halted_step_proof
    {state : MachineState} {next : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {values : Array Word}
    {trace : Trace} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.locals.lookup ·) = .ok values)
    (hcallee : Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder program) Generic.MemoryPolicy.permissive ctx
      callee state.globals values trace globals' .halted) :
    Generic.GenericStep localOperandFrame (sirDecoder program) Generic.MemoryPolicy.permissive ctx state.toGenericState trace
      ({ globals := globals', control := .halted } : MachineState).toGenericState :=
  step_icallHalted hdecode hargs hcallee
end Sir
