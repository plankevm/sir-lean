import Sir.Vars.Proofs.Determinism
import Sir.Vars.Proofs.Readiness
import Sir.Vars.Proofs.Bump
import Sir.Vars.Proofs.Check
import Sir.Vars.Proofs.Quotient

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

local notation:50 s " =[" t "]=>* " f => Vars.Steps program ctx s t f

local notation:50 s " =[" t "]=> " f => Vars.SmallStep program ctx s t f

theorem Vars.Program.deterministic_of_memOracleFree
    (hfree : program.MemOracleFree) : program.Deterministic :=
  Vars.Proofs.Program.deterministic_of_memOracleFree hfree

theorem Vars.Program.functionDeterministic_of_memOracleFree
    (hfree : program.MemOracleFree) (function : FunctionId) :
    program.FunctionDeterministic function :=
  Vars.Proofs.Program.functionDeterministic_of_memOracleFree hfree function

theorem Vars.Program.functionDeterministicFrom_of_memOracleFree
    (hfree : program.MemOracleFree) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args :=
  Vars.Proofs.Program.functionDeterministicFrom_of_memOracleFree
    hfree ctx function globals args

theorem Vars.Program.MemOracleFree.deterministicFrom
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ :=
  Vars.Proofs.Program.MemOracleFree.deterministicFrom hfree ctx entry world₀

theorem Vars.Program.RunsTo.unique_or_queryDivergence
    {entry : FunctionId} {world₀ : World}
    {t₁ t₂ : Trace} {final₁ final₂ : Vars.State}
    (hfree : program.MemOracleFree)
    (h₁ : program.RunsTo ctx entry world₀ t₁ final₁)
    (h₂ : program.RunsTo ctx entry world₀ t₂ final₂) :
    (t₁ = t₂ ∧ final₁ = final₂) ∨ Trace.QueryDivergence t₁ t₂ :=
  Vars.Proofs.Program.RunsTo.unique_or_queryDivergence hfree h₁ h₂

theorem Vars.Program.RunsTo.trace_det
    (hfree : program.MemOracleFree)
    {entry : FunctionId} {world₀ : World} {t : Trace}
    {final₁ final₂ : Vars.State}
    (h₁ : program.RunsTo ctx entry world₀ t final₁)
    (h₂ : program.RunsTo ctx entry world₀ t final₂) : final₁ = final₂ :=
  Vars.Proofs.Program.RunsTo.trace_det hfree h₁ h₂

theorem Vars.Steps.confluence_or_queryDivergence
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : Vars.State} {t₁ t₂ : Trace}
    (h₁ : s =[t₁]=>* e₁) (h₂ : s =[t₂]=>* e₂) :
    Vars.Steps.Extends program ctx e₁ t₁ e₂ t₂ ∨
      Vars.Steps.Extends program ctx e₂ t₂ e₁ t₁ ∨
        Trace.QueryDivergence t₁ t₂ :=
  Vars.Proofs.Steps.confluence_or_queryDivergence hfree h₁ h₂

theorem Vars.Steps.prefix_confluence
    (hfree : program.MemOracleFree)
    {s e₁ e₂ : Vars.State} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : s =[t₁]=>* e₁)
    (h₂ : s =[t₂]=>* e₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    Vars.Steps.Extends program ctx e₁ t₁ e₂ t₂ ∨
      Vars.Steps.Extends program ctx e₂ t₂ e₁ t₁ :=
  Vars.Proofs.Steps.prefix_confluence hfree h₁ h₂ htr

theorem Vars.SmallStep.prefix_det
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : Vars.State} {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : s =[t₁]=> s₁)
    (h₂ : s =[t₂]=> s₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ s₁ = s₂ :=
  Vars.Proofs.SmallStep.prefix_det hfree h₁ h₂ htr

theorem Vars.SmallStep.trace_det
    (hfree : program.MemOracleFree)
    {s s₁ s₂ : Vars.State} {t : Trace}
    (h₁ : s =[t]=> s₁)
    (h₂ : s =[t]=> s₂) : s₁ = s₂ :=
  Vars.Proofs.SmallStep.trace_det hfree h₁ h₂

theorem Vars.EvalFn.prefix_det
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome}
    {t₁ t₂ r₁ r₂ : Trace}
    (h₁ : Vars.EvalFn program ctx f g args t₁ g₁ outcome₁)
    (h₂ : Vars.EvalFn program ctx f g args t₂ g₂ outcome₂)
    (htr : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  Vars.Proofs.EvalFn.prefix_det hfree h₁ h₂ htr

theorem Vars.EvalFn.trace_det
    (hfree : program.MemOracleFree)
    {f : FunctionId} {g g₁ g₂ : Globals} {args : Array Word}
    {outcome₁ outcome₂ : FunctionOutcome} {t : Trace}
    (h₁ : Vars.EvalFn program ctx f g args t g₁ outcome₁)
    (h₂ : Vars.EvalFn program ctx f g args t g₂ outcome₂) :
    g₁ = g₂ ∧ outcome₁ = outcome₂ :=
  Vars.Proofs.EvalFn.trace_det hfree h₁ h₂

theorem Vars.Steps.preserves_function
    {cursor : Machine.ProgramCursor} {s e : Vars.State} {t : Trace}
    (h : s =[t]=>* e)
    (hctrl : s.control = .running cursor) :
    e.control = .halted ∨ (∃ rs, e.control = .returned rs) ∨
      ∃ cursor', e.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  Vars.Proofs.Steps.preserves_function h hctrl

theorem Vars.Program.WellFormed.progress
    (hwf : program.WellFormed) {state : Vars.State}
    (ready : program.ReadyState ctx state) :
    ∃ trace state', state =[trace]=> state' :=
  Vars.Proofs.Program.WellFormed.progress hwf ready

theorem Vars.Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {f : FunctionId} {g g' : Globals}
    {args rs : Array Word} {t : Trace}
    (hrun : Vars.EvalFn program ctx f g args t g' (.returned rs)) :
    (program.function? f).bind (·.outputs?) = some rs.size :=
  Vars.Proofs.Program.WellFormed.evalFn_arity hwf hrun

theorem Vars.Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initId ∨ program.mainId? = some entry)
    (hrun : Vars.EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False :=
  Vars.Proofs.Program.WellFormed.evalFn_entry_not_returned hwf hentry hrun

theorem Vars.Program.WellFormed.icall_step
    (hwf : program.WellFormed) {s : Vars.State} {nextControl : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs rs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.environment.lookup ·) = .ok vs)
    (hcallee : Vars.EvalFn program ctx callee s.globals vs t g' (.returned rs)) :
    ∃ locals', s =[t]=>
      { s with globals := g', environment := locals', control := nextControl } :=
  Vars.Proofs.Program.WellFormed.icall_step hwf hstmt hargs hcallee

theorem Vars.Program.icall_halted_step
    {s : Vars.State} {nextControl : Machine.MachineControl}
    {callee : FunctionId} {args dests : Array VarId} {vs : Array Word}
    {t : Trace} {g' : Globals}
    (hstmt : program.decodeStmt s.control = some (nextControl, .icall callee args dests))
    (hargs : args.mapM (s.environment.lookup ·) = .ok vs)
    (hcallee : Vars.EvalFn program ctx callee s.globals vs t g' .halted) :
    s =[t]=> { globals := g', environment := .empty, control := .halted } :=
  Vars.Proofs.Program.icall_halted_step hstmt hargs hcallee

theorem Vars.rank_lt_of_transGen {rank : FunctionId → Nat}
    (decreasing : Vars.RankDecreases program rank) {f g}
    (path : Relation.TransGen program.callEdge f g) : rank g < rank f :=
  Vars.Proofs.rank_lt_of_transGen decreasing path

theorem Vars.acyclic_of_rank {rank : FunctionId → Nat}
    (decreasing : Vars.RankDecreases program rank) (f : FunctionId) :
    ¬ Relation.TransGen program.callEdge f f :=
  Vars.Proofs.acyclic_of_rank decreasing f

theorem Vars.Program.canonicalize_alphaEquiv (program : Vars.Program) :
    Vars.Program.AlphaEquiv program.canonicalize program :=
  Vars.Proofs.Program.canonicalize_alphaEquiv program

theorem Vars.Program.alphaEquiv_iff_canonicalize_eq {left right : Vars.Program} :
    Vars.Program.AlphaEquiv left right ↔ left.canonicalize = right.canonicalize :=
  Vars.Proofs.Program.alphaEquiv_iff_canonicalize_eq

theorem Vars.Program.canonicalizeEquivalenceClass_bijective :
    (∀ left right : Quotient Vars.Program.alphaEquivalenceSetoid,
        Vars.Program.canonicalizeEquivalenceClass left =
          Vars.Program.canonicalizeEquivalenceClass right → left = right) ∧
      ∀ canonical : { program : Vars.Program // program.Canonical },
        ∃ equivalenceClass,
          Vars.Program.canonicalizeEquivalenceClass equivalenceClass = canonical :=
  ⟨fun _ _ equal => Vars.Proofs.Program.canonicalizeEquivalenceClass_bijective.1 equal,
    Vars.Proofs.Program.canonicalizeEquivalenceClass_bijective.2⟩

end Sir
