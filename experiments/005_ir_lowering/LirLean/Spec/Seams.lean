import BytecodeLayer.Exec.CallPreservesSelf
import LirLean.Spec.IR

namespace Lir.Spec

abbrev SelfPresent : Evm.Frame → Prop := BytecodeLayer.Exec.Invariants.SelfPresent

abbrev CallPreservesSelf : Prop := BytecodeLayer.Exec.Invariants.CallPreservesSelf

abbrev PrecompilesPreservePresence : Prop :=
  BytecodeLayer.Exec.Invariants.PrecompilesPreservePresence

export BytecodeLayer.Exec.Invariants (callPreservesSelf_of_precompiles)

abbrev CallsCode : Evm.Frame → Prop := BytecodeLayer.Exec.Invariants.CallsCode

abbrev CleanHaltsNonException : Evm.Frame → Prop :=
  BytecodeLayer.Exec.Invariants.CleanHaltsNonException

end Lir.Spec

namespace Lir

abbrev ReachableFrom := BytecodeLayer.Exec.Invariants.ReachableFrom

abbrev PrecompileAssumptions (_prog : Program) (params : Evm.CallParams) : Prop :=
  BytecodeLayer.Exec.Invariants.PrecompileAssumptions params

end Lir
