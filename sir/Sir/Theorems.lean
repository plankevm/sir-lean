import Sir.Proofs.Determinism
import Sir.Proofs.Readiness
import Sir.Proofs.Bump

namespace Sir

variable {program : Program} {ctx : CallContext}

theorem Generic.MemoryPolicy.bump_deterministic :
    Generic.MemoryPolicy.bump.Deterministic :=
  Generic.MemoryPolicy.bump_deterministic_proof

theorem Generic.MemoryPolicy.bump_sound : Generic.MemoryPolicy.bump.Sound :=
  Generic.MemoryPolicy.bump_sound_proof

theorem Generic.MemoryPolicy.bump_satisfiable : Generic.MemoryPolicy.bump.Satisfiable :=
  Generic.MemoryPolicy.bump_satisfiable_proof

theorem Generic.MemoryPolicy.permissive_not_deterministic :
    ¬ Generic.MemoryPolicy.permissive.Deterministic :=
  Generic.MemoryPolicy.permissive_not_deterministic_proof

theorem Generic.MemoryPolicy.permissive_sound :
    Generic.MemoryPolicy.permissive.Sound :=
  Generic.MemoryPolicy.permissive_sound_proof

theorem Generic.MemoryPolicy.permissive_satisfiable :
    Generic.MemoryPolicy.permissive.Satisfiable :=
  Generic.MemoryPolicy.permissive_satisfiable_proof

theorem Program.deterministic_of_memOracleFree
    (hfree : program.AllocationFree) : program.Deterministic :=
  Program.deterministic_of_memOracleFree_proof hfree

theorem Program.functionDeterministic_of_memOracleFree
    (hfree : program.AllocationFree) (function : FunctionId) :
    program.FunctionDeterministic function :=
  Program.functionDeterministic_of_memOracleFree_proof hfree function

theorem Program.functionDeterministicFrom_of_memOracleFree
    (hfree : program.AllocationFree) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args :=
  Program.functionDeterministicFrom_of_memOracleFree_proof
    hfree ctx function globals args

theorem Program.AllocationFree.deterministicFrom
    (hfree : program.AllocationFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ :=
  Program.AllocationFree.deterministicFrom_proof hfree ctx entry world₀

theorem Program.RunsTo.unique_or_queryDivergence
    {entry : FunctionId} {world₀ : World}
    {t₁ t₂ : Trace} {final₁ final₂ : MachineState}
    (hfree : program.AllocationFree)
    (h₁ : program.RunsTo ctx entry world₀ t₁ final₁)
    (h₂ : program.RunsTo ctx entry world₀ t₂ final₂) :
    (t₁ = t₂ ∧ final₁ = final₂) ∨ Trace.QueryDivergence t₁ t₂ :=
  Program.RunsTo.unique_or_queryDivergence_proof hfree h₁ h₂

theorem Program.RunsTo.trace_det
    (hfree : program.AllocationFree)
    {entry : FunctionId} {world₀ : World} {t : Trace}
    {final₁ final₂ : MachineState}
    (h₁ : program.RunsTo ctx entry world₀ t final₁)
    (h₂ : program.RunsTo ctx entry world₀ t final₂) : final₁ = final₂ :=
  Program.RunsTo.trace_det_proof hfree h₁ h₂

theorem Steps.confluence_or_queryDivergence
    (hfree : program.AllocationFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ : Trace}
    (h₁ : Steps program ctx s t₁ e₁) (h₂ : Steps program ctx s t₂ e₂) :
    (∃ u, Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) ∨
        Trace.QueryDivergence t₁ t₂ :=
  Steps.confluence_or_queryDivergence_proof hfree h₁ h₂

theorem Steps.prefix_confluence
    (hfree : program.AllocationFree)
    {s e₁ e₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Steps program ctx s t₁ e₁)
    (h₂ : Steps program ctx s t₂ e₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    (∃ u, Steps program ctx e₁ u e₂ ∧ t₁ ++ u = t₂) ∨
      (∃ u, Steps program ctx e₂ u e₁ ∧ t₂ ++ u = t₁) :=
  Steps.prefix_confluence_proof hfree h₁ h₂ htr

theorem SmallStep.prefix_det
    (hfree : program.AllocationFree)
    {s s₁ s₂ : MachineState} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : SmallStep program ctx s t₁ s₁)
    (h₂ : SmallStep program ctx s t₂ s₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ s₁ = s₂ :=
  SmallStep.prefix_det_proof hfree h₁ h₂ htr

theorem SmallStep.trace_det
    (hfree : program.AllocationFree)
    {s s₁ s₂ : MachineState} {t : Trace}
    (h₁ : SmallStep program ctx s t s₁)
    (h₂ : SmallStep program ctx s t s₂) : s₁ = s₂ :=
  SmallStep.trace_det_proof hfree h₁ h₂

theorem EvalFn.prefix_det
    (hfree : program.AllocationFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome}
    {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : EvalFn program ctx f g args t₁ g₁ outcome₁)
    (h₂ : EvalFn program ctx f g args t₂ g₂ outcome₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  EvalFn.prefix_det_proof hfree h₁ h₂ htr

theorem EvalFn.trace_det
    (hfree : program.AllocationFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome} {t : Trace}
    (h₁ : EvalFn program ctx f g args t g₁ outcome₁)
    (h₂ : EvalFn program ctx f g args t g₂ outcome₂) :
    g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  EvalFn.trace_det_proof hfree h₁ h₂

theorem Steps.preserves_function
    {cursor : ProgramCursor} {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e)
    (hctrl : s.control = .running cursor) :
    e.control = .halted ∨ (∃ rs, e.control = .returned rs) ∨
      ∃ cursor', e.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  Steps.preserves_function_proof h hctrl

theorem Program.WellFormed.progress_reachable_nonIcall
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hfreshAllocation : program.AllocationAvailable state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program ctx state trace state' :=
  Program.WellFormed.progress_reachable_nonIcall_proof
    hwf hrun hcontrol hfreshAllocation hstore

theorem Program.WellFormed.progress_reachable_nonIcall_bump
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program ctx state trace state' :=
  Program.WellFormed.progress_reachable_nonIcall_bump_proof
    hwf hrun hcontrol hspace hstore

theorem Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {f : FunctionId} {g g' : Globals}
    {args rs : Array Word} {t : Trace}
    (hrun : EvalFn program ctx f g args t g' (.returned rs)) :
    (program.function? f).bind (·.outputs?) = some rs.size :=
  Program.WellFormed.evalFn_arity_proof hwf hrun

theorem Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initEntry ∨ program.mainEntry = some entry)
    (hrun : EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False :=
  Program.WellFormed.evalFn_entry_not_returned_proof hwf hentry hrun

theorem Program.WellFormed.icall_step
    (hwf : program.WellFormed) {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs rs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.locals.lookup ·) = .ok vs)
    (hcallee : EvalFn program ctx callee s.globals vs t g' (.returned rs)) :
    ∃ locals', SmallStep program ctx s t
      { s with globals := g', locals := locals', control := nextControl } :=
  Program.WellFormed.icall_step_proof hwf hstmt hargs hcallee

theorem Program.icall_halted_step
    {s : MachineState} {nextControl : MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.locals.lookup ·) = .ok vs)
    (hcallee : EvalFn program ctx callee s.globals vs t g' .halted) :
    SmallStep program ctx s t { globals := g', control := .halted } :=
  Program.icall_halted_step_proof hstmt hargs hcallee

end Sir
