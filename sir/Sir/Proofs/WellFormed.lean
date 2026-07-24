import Sir.Proofs.StepDet

namespace Sir

variable {program : Program} {ctx : CallContext}

theorem Program.functionInputOutputArity_iff
    {p : Program} {inputCount : Nat} {outputCount : Option Nat}
    {functionId : FunctionId} :
    p.FunctionInputOutputArity inputCount outputCount functionId ↔
      ∃ fn, p.function? functionId = some fn ∧
        fn.paramsOf.map (·.size) = some inputCount ∧ fn.outputs = outputCount := by
  rfl

theorem Program.WellFormed.callEdge_wellFounded
    (hwf : program.WellFormed) : WellFounded program.callEdge := by
  classical
  let validFunctions := (Finset.range program.functions.size).image FunctionId.mk
  let ancestors (f : FunctionId) := validFunctions.filter fun predecessor =>
    Relation.TransGen program.callEdge predecessor f
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
      exact hwf.acyclicCalls predecessor (Finset.mem_filter.mp h).2
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
      (program.function? callee).bind (·.outputs) = some dests.size := by
  have harity := hwf.icallArity callee args dests (Program.decodeStmt_mem hstmt)
  rcases Program.functionInputOutputArity_iff.mp harity with
    ⟨fn, hfn, hparams, houtputs⟩
  cases hps : fn.paramsOf with
  | none => simp [hps] at hparams
  | some ps =>
      refine ⟨⟨ps, ?_, by simpa [hps] using hparams⟩, ?_⟩
      · simp [Program.paramsOf, hfn, hps]
      · simp [hfn, houtputs]

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
    (hwf : program.WellFormed) {f : FunctionId} {g g' : Globals}
    {args rs : Array Word} {t : Trace}
    (hrun : EvalFn program ctx f g args t g' (.returned rs)) :
    (program.function? f).bind (·.outputs) = some rs.size := by
  cases hrun with
  | returned hentry hsteps hret =>
    obtain ⟨fn, entryBlock, locals₀, hfn, hentryBlock, hbind, rfl⟩ :=
      Program.callState?_eq_some_iff.mp hentry
    cases hsteps with
    | refl => cases hret
    | tail start next =>
      obtain ⟨cursor, block, hctrl, hblock, hterm, houts⟩ := next.returned_inv hret
      rcases Steps.preserves_function_proof start rfl with
        hhalt | ⟨returnedValues, hreturned⟩ | ⟨cursor', hctrl', hcursorFn⟩
      · exact absurd next (stuck_of_halted hhalt _ _)
      · exact absurd next (stuck_of_returned hreturned _ _)
      · have hsame : cursor' = cursor :=
          MachineControl.running.inj (hctrl'.symm.trans hctrl)
        subst cursor'
        change cursor.fn = f at hcursorFn
        simp only [Program.block?, hcursorFn, hfn] at hblock
        obtain ⟨hsome, hnone⟩ := hwf.iretArity f fn hfn
        cases houtputs : fn.outputs with
        | none => exact ((hnone houtputs block (Array.mem_of_getElem? hblock)) hterm).elim
        | some n =>
          have harity := hsome n houtputs block (Array.mem_of_getElem? hblock) hterm
          rw [hfn]
          simp only [Option.bind_some]
          rw [houtputs]
          simp only [Option.some.injEq]
          exact harity.symm.trans (mapM_ok_size houts).symm

theorem Program.WellFormed.evalFn_entry_not_returned
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
  have harity := (hwf.evalFn_arity_proof hcallee).symm.trans houtputs
  simp only [Option.some.injEq] at harity
  exact Locals.bindValues_total s.locals harity.symm

theorem Program.WellFormed.icall_step_proof
    (hwf : program.WellFormed) {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs rs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.locals.lookup ·) = .ok vs)
    (hcallee : EvalFn program ctx callee s.globals vs t g' (.returned rs)) :
    ∃ locals', SmallStep program ctx s t
      { s with globals := g', locals := locals', control := nextControl } := by
  obtain ⟨locals', hbind⟩ := hwf.icall_bindReturns hstmt hcallee
  exact ⟨locals', .icall hstmt hargs hcallee hbind⟩

theorem Program.WellFormed.icall_halted_step_proof
    (_hwf : program.WellFormed) {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.locals.lookup ·) = .ok vs)
    (hcallee : EvalFn program ctx callee s.globals vs t g' .halted) :
    SmallStep program ctx s t { globals := g', control := .halted } :=
  .icallHalted hstmt hargs hcallee
end Sir
