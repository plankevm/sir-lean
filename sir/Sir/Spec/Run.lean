import Sir.Spec.Step

namespace Sir

def Program.RunsFunction (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : MachineState) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program ctx initial trace state

def Program.Runs (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (state : MachineState) : Prop :=
  program.RunsFunction ctx entry { world := world } #[] trace state

def Program.RunsTo (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (final : MachineState) : Prop :=
  program.Runs ctx entry world trace final ∧ final.control = .halted

end Sir
