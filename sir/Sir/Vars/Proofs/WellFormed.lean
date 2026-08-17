import Sir.Vars.Proofs.Steps

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

def Vars.Program.paramsOf (program : Vars.Program) (function : FunctionId) : Option (Array VarId) :=
  (program.function? function).map (·.paramsOf)

theorem Vars.Program.mem_functions_of_function? {p : Vars.Program} {f : FunctionId} {fn : Vars.Function}
    (h : p.function? f = some fn) : fn ∈ p.functions :=
  Array.mem_of_getElem? h

theorem Vars.Program.functionInputOutputArity_iff
    {p : Vars.Program} {inputCount : Nat} {outputCount : Option Nat}
    {functionId : FunctionId} :
    p.FunctionInputOutputArity inputCount outputCount functionId ↔
      ∃ fn, p.function? functionId = some fn ∧
        fn.paramsOf.size = inputCount ∧ fn.outputs? = outputCount := by
  rfl

theorem Vars.Program.WellFormed.callEdge_wellFounded
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

theorem Vars.Program.WellFormed.icall_paramsOf
    (hwf : program.WellFormed) {control nextControl : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId}
    (hstmt : program.decodeStmt control = some (nextControl, .icall callee args dests)) :
    (∃ ps, program.paramsOf callee = some ps ∧ ps.size = args.size) ∧
      ((program.function? callee).bind (·.outputs?)).getD 0 = dests.size := by
  obtain ⟨outputs, harity, hdests⟩ :=
    hwf.icallArity callee args dests (Vars.Program.decodeStmt_mem hstmt)
  rcases Vars.Program.functionInputOutputArity_iff.mp harity with
    ⟨fn, hfn, hparams, houtputs⟩
  refine ⟨⟨fn.paramsOf, ?_, hparams⟩, ?_⟩
  · simp [Vars.Program.paramsOf, hfn]
  · simp [hfn, houtputs, hdests]

theorem Vars.Program.WellFormed.icall_bindParams
    (hwf : program.WellFormed) {s : Vars.State} {nextControl : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.environment.lookup ·) = .ok vs) :
    ∃ ps locals₀, program.paramsOf callee = some ps ∧
      Locals.bindParams ps vs = .ok locals₀ := by
  obtain ⟨⟨ps, hps, hsize⟩, -⟩ := hwf.icall_paramsOf hstmt
  obtain ⟨locals₀, hbind⟩ :=
    Locals.bindValues_total Locals.empty (hsize.trans (mapM_ok_size hargs).symm)
  exact ⟨ps, locals₀, hps, hbind⟩

theorem Vars.Proofs.Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {function : FunctionId} {globals globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hrun : Vars.EvalFn program ctx
      function globals args trace globals' (.returned results)) :
    (program.function? function).bind (·.outputs?) = some results.size := by
  cases hrun with
  | exit hentry hsteps hreturn =>
      rw [Vars.entry_eq] at hentry
      obtain ⟨fn, locals₀, hfn, hbind, rfl⟩ :=
        Vars.Program.callState?_eq_some_iff.mp hentry
      cases hsteps with
      | refl => cases hreturn
      | tail start next =>
          have hinv := Vars.SmallStep.returned_inv next hreturn
          obtain ⟨cursor, block, hcontrol, hblock, hterm, houtputs⟩ := hinv
          rcases Vars.Proofs.Steps.preserves_function
              (cursor := ⟨function, ⟨0⟩, fn.entry.startPosition⟩)
              (state := (⟨globals, locals₀,
                .running ⟨function, ⟨0⟩, fn.entry.startPosition⟩⟩ : Vars.State))
              start rfl with
            hhalt | ⟨returnedValues, hreturned⟩ | ⟨cursor', hcontrol', hcursorFn⟩
          · exact absurd next
              (Machine.stuck_of_exit (outcome := .halted) (Vars.decoder_terminal program)
                hhalt _ _)
          · exact absurd next
              (Machine.stuck_of_exit (outcome := .returned _) (Vars.decoder_terminal program)
                hreturned _ _)
          · have hsame : cursor' = cursor :=
              Machine.MachineControl.running.inj (hcontrol'.symm.trans hcontrol)
            subst cursor'
            change cursor.fn = function at hcursorFn
            simp only [Vars.Program.block?, hcursorFn, hfn] at hblock
            have harity := hwf.iretArity fn (Vars.Program.mem_functions_of_function? hfn)
              block (Array.mem_of_getElem? hblock) hterm
            rw [hfn]
            simp only [Option.bind_some]
            rw [← harity, mapM_ok_size houtputs]

theorem Vars.Proofs.Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initId ∨ program.mainId? = some entry)
    (hrun : Vars.EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False := by
  obtain ⟨fn, hfn, houtputs⟩ :
      ∃ fn, program.function? entry = some fn ∧ fn.outputs? = none := by
    rcases hentry with rfl | hmain
    · exact ⟨program.init, Vars.Program.function?_initId program, hwf.entryArity.1.2⟩
    · obtain ⟨m, hmain', hfn⟩ := Vars.Program.function?_mainId hmain
      exact ⟨m, hfn, (hwf.entryArity.2 m hmain').2⟩
  have hreturn := Vars.Proofs.Program.WellFormed.evalFn_arity hwf hrun
  rw [hfn] at hreturn
  simp [houtputs] at hreturn

theorem Vars.Program.WellFormed.icall_bindReturns
    (hwf : program.WellFormed) {s : Vars.State} {nextControl : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId}
    {g g' : Globals} {vs rs : Array Word} {t : Trace}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hcallee : Vars.EvalFn program ctx callee g vs t g' (.returned rs)) :
    ∃ locals', Locals.bindReturns s.environment dests rs = .ok locals' := by
  obtain ⟨-, houtputs⟩ := hwf.icall_paramsOf hstmt
  rw [Vars.Proofs.Program.WellFormed.evalFn_arity hwf hcallee, Option.getD_some] at houtputs
  exact Locals.bindValues_total s.environment houtputs.symm

theorem Vars.Proofs.Program.WellFormed.icall_step
    (hwf : program.WellFormed) {state : Vars.State} {next : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {values results : Array Word}
    {trace : Trace} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.environment.lookup ·) = .ok values)
    (hcallee : Vars.EvalFn program ctx
      callee state.globals values trace globals' (.returned results)) :
    ∃ locals', Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx
      state trace
        { state with globals := globals', environment := locals', control := next } := by
  obtain ⟨locals', hbind⟩ := hwf.icall_bindReturns hdecode hcallee
  exact ⟨locals', step_icall hdecode hargs hcallee hbind⟩

theorem Vars.Proofs.Program.icall_halted_step
    {state : Vars.State} {next : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {values : Array Word}
    {trace : Trace} {globals' : Globals}
    (hdecode : program.decodeStmt state.control = some (next, .icall callee args dests))
    (hargs : args.mapM (state.environment.lookup ·) = .ok values)
    (hcallee : Vars.EvalFn program ctx
      callee state.globals values trace globals' .halted) :
    Machine.Step Vars.frame (Vars.decoder program) Machine.memoryPolicy ctx state trace
      ({ globals := globals', environment := .empty, control := .halted } : Vars.State) :=
  step_icallHalted hdecode hargs hcallee
end Sir
