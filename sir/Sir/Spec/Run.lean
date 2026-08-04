import Sir.Spec.Step

namespace Sir

def Program.RunsFunction (program : Program) (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : MachineState) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program policy ctx initial trace state

def Program.Runs (program : Program) (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (entry : FunctionId)
    (world : World) (trace : Trace) (state : MachineState) : Prop :=
  program.RunsFunction policy ctx entry { world := world } #[] trace state

def Program.RunsTo (program : Program) (policy : Generic.MemoryPolicy) (ctx : CallContext)
    (entry : FunctionId)
    (world : World) (trace : Trace) (final : MachineState) : Prop :=
  program.Runs policy ctx entry world trace final ∧ final.control = .halted

end Sir
