import Sir.Stack.Proofs.Determinism
import Sir.Stack.Proofs.Bump

namespace Sir.Stack

open Sir

variable {program : Program} {ctx : CallContext}

local notation:50 s " =[" t "]=>* " f => Steps program ctx s t f

local notation:50 s " =[" t "]=> " f => SmallStep program ctx s t f



theorem Steps.confluence_or_queryDivergence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ : Trace}
    (h₁ : state =[trace₁]=>* final₁) (h₂ : state =[trace₂]=>* final₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends program ctx final₂ trace₂ final₁ trace₁ ∨
        Trace.QueryDivergence trace₁ trace₂ :=
  Proofs.Steps.confluence_or_queryDivergence hfree h₁ h₂

theorem Steps.prefix_confluence
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : state =[trace₁]=>* final₁) (h₂ : state =[trace₂]=>* final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    Steps.Extends program ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends program ctx final₂ trace₂ final₁ trace₁ :=
  Proofs.Steps.prefix_confluence hfree h₁ h₂ htrace

theorem SmallStep.prefix_det
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : state =[trace₁]=> final₁) (h₂ : state =[trace₂]=> final₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ final₁ = final₂ :=
  Proofs.SmallStep.prefix_det hfree h₁ h₂ htrace

theorem SmallStep.trace_det
    (hfree : program.MemOracleFree)
    {state final₁ final₂ : State} {trace : Trace}
    (h₁ : state =[trace]=> final₁) (h₂ : state =[trace]=> final₂) :
    final₁ = final₂ :=
  Proofs.SmallStep.trace_det hfree h₁ h₂

theorem EvalFn.prefix_det
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome}
    {trace₁ trace₂ rest₁ rest₂ : Trace}
    (h₁ : EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂)
    (htrace : trace₁ ++ rest₁ = trace₂ ++ rest₂) :
    trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  Proofs.EvalFn.prefix_det hfree h₁ h₂ htrace

theorem EvalFn.trace_det
    (hfree : program.MemOracleFree)
    {function : FunctionId} {globals finalGlobals₁ finalGlobals₂ : Globals}
    {args : Array Word} {outcome₁ outcome₂ : FunctionOutcome} {trace : Trace}
    (h₁ : EvalFn program ctx function globals args trace finalGlobals₁ outcome₁)
    (h₂ : EvalFn program ctx function globals args trace finalGlobals₂ outcome₂) :
    finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂ :=
  Proofs.EvalFn.trace_det hfree h₁ h₂

theorem Program.deterministic_of_memOracleFree
    (hfree : program.MemOracleFree) : program.Deterministic :=
  Proofs.Program.deterministic_of_memOracleFree hfree

theorem Program.functionDeterministic_of_memOracleFree
    (hfree : program.MemOracleFree) (function : FunctionId) :
    program.FunctionDeterministic function :=
  Proofs.Program.functionDeterministic_of_memOracleFree hfree function

theorem Program.functionDeterministicFrom_of_memOracleFree
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) :
    program.FunctionDeterministicFrom ctx function globals args :=
  Proofs.Program.functionDeterministicFrom_of_memOracleFree
    hfree ctx function globals args

theorem Program.MemOracleFree.deterministicFrom
    (hfree : program.MemOracleFree) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) :
    program.DeterministicFrom ctx entry world₀ :=
  Proofs.Program.MemOracleFree.deterministicFrom hfree ctx entry world₀

variable {entry : FunctionId} {world₀ : World}

local notation:50 e " =[" t "]=>! " f => program.RunsTo ctx e world₀ t f

theorem Program.RunsTo.unique_or_queryDivergence
    {t₁ t₂ : Trace} {final₁ final₂ : State}
    (hfree : program.MemOracleFree)
    (h₁ : entry =[t₁]=>! final₁)
    (h₂ : entry =[t₂]=>! final₂) :
    (t₁ = t₂ ∧ final₁ = final₂) ∨ Trace.QueryDivergence t₁ t₂ :=
  Proofs.Program.RunsTo.unique_or_queryDivergence hfree h₁ h₂

theorem Program.RunsTo.trace_det
    (hfree : program.MemOracleFree)
    {t : Trace} {final₁ final₂ : State}
    (h₁ : entry =[t]=>! final₁)
    (h₂ : entry =[t]=>! final₂) : final₁ = final₂ :=
  Proofs.Program.RunsTo.trace_det hfree h₁ h₂

theorem Steps.preserves_function
    {cursor : ProgramCursor} {state final : State} {trace : Trace}
    (h : state =[trace]=>* final)
    (hcontrol : state.control = .running cursor) :
    final.control = .halted ∨ (∃ results, final.control = .returned results) ∨
      ∃ cursor', final.control = .running cursor' ∧ cursor'.fn = cursor.fn :=
  Proofs.Steps.preserves_function h hcontrol

theorem Program.WellFormed.progress
    (hwf : program.WellFormed) {state : State}
    (ready : program.ReadyState ctx state) :
    ∃ trace state', state =[trace]=> state' :=
  Proofs.Program.WellFormed.progress hwf ready

theorem Program.WellFormed.evalFn_arity
    (hwf : program.WellFormed) {function : FunctionId} {globals globals' : Globals}
    {args results : Array Word} {trace : Trace}
    (hrun : EvalFn program ctx function globals args trace globals' (.returned results)) :
    (program.function? function).bind (·.outputs?) = some results.size :=
  Proofs.Program.WellFormed.evalFn_arity hwf hrun

theorem Program.WellFormed.evalFn_entry_not_returned
    (hwf : program.WellFormed) {entry : FunctionId} {globals finalGlobals : Globals}
    {values : Array Word} {trace : Trace}
    (hentry : entry = program.initId ∨ program.mainId? = some entry)
    (hrun : EvalFn program ctx entry globals #[] trace finalGlobals (.returned values)) :
    False :=
  Proofs.Program.WellFormed.evalFn_entry_not_returned hwf hentry hrun

theorem Program.WellFormed.icall_step
    (hwf : program.WellFormed) {state : State} {next : Control}
    {callee : FunctionId} {argumentCount resultCount : Nat}
    {args results : Array Word} {trace : Trace} {globals' : Globals}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hargs : state.fetch argumentCount = .ok args)
    (hcallee : EvalFn program ctx callee state.globals args trace globals'
      (.returned results)) :
    ∃ environment, state =[trace]=> State.of globals' environment next :=
  Proofs.Program.WellFormed.icall_step hwf hinstr hargs hcallee

theorem Program.icall_halted_step
    {state : State} {next : Control} {callee : FunctionId}
    {argumentCount resultCount : Nat} {args : Array Word} {trace : Trace}
    {globals' : Globals}
    (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
    (hargs : state.fetch argumentCount = .ok args)
    (hcallee : EvalFn program ctx callee state.globals args trace globals' .halted) :
    state =[trace]=> State.halted globals' :=
  Proofs.Program.icall_halted_step hinstr hargs hcallee



end Sir.Stack
