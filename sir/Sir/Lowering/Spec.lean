import Sir.Lowering.Spec.Symbolic
import Sir.Lowering.Spec.StackSchedule
import Sir.Lowering.Spec.Scheduler

namespace Sir.Lowering

def Equiv (vars : Vars.Program) (stack : Stack.Program) : Prop :=
  ∀ ctx function globals args trace finalGlobals outcome,
    Vars.EvalFn vars ctx function globals args trace finalGlobals outcome ↔
      Stack.EvalFn stack ctx function globals args trace finalGlobals outcome

end Sir.Lowering
