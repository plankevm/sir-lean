import LirLean.V2.Drive.CallPreservesSelf
import LirLean.Decode.Modellable
import BytecodeLayer.Hoare.CleanHalt

namespace Lir.Spec

def SelfPresent : Evm.Frame → Prop := Lir.V2.SelfPresent

def CallPreservesSelf : Prop := Lir.V2.CallPreservesSelf

def PrecompilesPreservePresence : Prop :=
  ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
    Evm.beginCall cp = .inr imm →
    ∀ a, Lir.V2.AccPresent a cp.accounts → Lir.V2.AccPresent a imm.accounts

theorem callPreservesSelf_of_precompiles :
    PrecompilesPreservePresence → CallPreservesSelf :=
  fun h => Lir.V2.callPreservesSelf_modGuards h

def CallsCode : Evm.Frame → Prop := BytecodeLayer.Interpreter.CallsCode

def CleanHaltsNonException : Evm.Frame → Prop := Lir.V2.CleanHaltsNonException

end Lir.Spec

namespace Lir.V2

def ReachableFrom (params : Evm.CallParams) (fr' : Evm.Frame) : Prop :=
  ∃ fr₀, Evm.beginCall params = .inl fr₀ ∧ BytecodeLayer.Hoare.Runs fr₀ fr'

structure PrecompileAssumptions (prog : Program) (params : Evm.CallParams) : Prop where
  noErase : Lir.Spec.PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'

end Lir.V2
