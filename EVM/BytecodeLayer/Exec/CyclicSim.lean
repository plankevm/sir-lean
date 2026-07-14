import BytecodeLayer.Hoare

namespace BytecodeLayer.Exec.CyclicSim

open Evm
open BytecodeLayer.Hoare

/-- An invariant preserved by ordinary steps and completed CALL/CREATE descents
is preserved by a whole cyclic execution path. -/
theorem invariant_of_runs {Inv : Frame → Prop}
    (step : ∀ {fr fr'}, StepsTo fr fr' → Inv fr → Inv fr')
    (call : ∀ {fr fr'}, CallReturns fr fr' → Inv fr → Inv fr')
    (create : ∀ {fr fr'}, CreateReturns fr fr' → Inv fr → Inv fr')
    {fr fr' : Frame} (run : Runs fr fr') :
    Inv fr → Inv fr' := by
  induction run with
  | refl _ => exact id
  | step edge _ ih => exact fun hfr => ih (step edge hfr)
  | call edge _ ih => exact fun hfr => ih (call edge hfr)
  | create edge _ ih => exact fun hfr => ih (create edge hfr)

end BytecodeLayer.Exec.CyclicSim
