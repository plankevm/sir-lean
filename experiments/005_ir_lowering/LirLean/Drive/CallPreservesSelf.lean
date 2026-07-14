import LirLean.Drive.SelfPresent
import BytecodeLayer.Exec.CallPreservesSelf

namespace Lir

export BytecodeLayer.Exec.Invariants
  (StepPreservesSelf stepPreservesSelf CallPreservesSelf callPreservesSelf_success
   callPreservesSelf callPreservesSelf_modGuards CreatePreservesSelf createPreservesSelf
   createPreservesSelf_modGuards selfPresent_runs selfPresent_runs_of_call)

end Lir
