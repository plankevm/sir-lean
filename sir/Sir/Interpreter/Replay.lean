import Sir.Semantics.Step

namespace Sir.Interpreter.Replay

structure Effects (World : Type) where
  calls : List (Sir.CallResponse World) := []
  creates : List (Sir.CreateResponse World) := []

structure ExecutionResult (World : Type) where
  result : Sir.Result World
  remainingEffects : Effects World

private def drive {World : Type} [Sir.WorldModel World] (program : Sir.Program) :
    Nat → Sir.ResumePoint World → Effects World → Except Sir.Error (ExecutionResult World)
  | 0, _, _ => .error .outOfFuel
  | fuel + 1, state, effects => do
      match ← Sir.step program state with
      | .continue next => drive program fuel next effects
      | .needsCall _ continuation =>
          match effects.calls with
          | [] => throw (.missingEffect .call)
          | response :: rest =>
              drive program fuel (continuation.resumeWith response) { effects with calls := rest }
      | .needsCreate _ continuation =>
          match effects.creates with
          | [] => throw (.missingEffect .create)
          | response :: rest =>
              drive program fuel (continuation.resumeWith response) { effects with creates := rest }
      | .halted state halt =>
          return { result := { state, halt }, remainingEffects := effects }

/-- Replay an execution by supplying recorded call and create responses at suspension points. -/
def run {World : Type} [Sir.WorldModel World] (program : Sir.Program)
    (initial : Sir.ResumePoint World) (effects : Effects World := {}) (fuel : Nat) :
    Except Sir.Error (ExecutionResult World) :=
  drive program fuel initial effects

end Sir.Interpreter.Replay
