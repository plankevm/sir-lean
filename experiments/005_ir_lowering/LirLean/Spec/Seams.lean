import LirLean.Drive.CallPreservesSelf
import LirLean.Decode.Modellable
import BytecodeLayer.Hoare.CleanHalt

namespace Lir.Spec

def SelfPresent : Evm.Frame → Prop := Lir.SelfPresent

def CallPreservesSelf : Prop := Lir.CallPreservesSelf

def PrecompilesPreservePresence : Prop :=
  ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
    Evm.beginCall cp = .inr imm →
    ∀ a, BytecodeLayer.Hoare.AccPresent a cp.accounts → BytecodeLayer.Hoare.AccPresent a imm.accounts

theorem callPreservesSelf_of_precompiles :
    PrecompilesPreservePresence → CallPreservesSelf :=
  fun h => Lir.callPreservesSelf_modGuards h

def CallsCode : Evm.Frame → Prop := BytecodeLayer.Interpreter.CallsCode

def CleanHaltsNonException : Evm.Frame → Prop := BytecodeLayer.Hoare.CleanHaltsNonException

end Lir.Spec

namespace Lir

def ReachableFrom (params : Evm.CallParams) (fr' : Evm.Frame) : Prop :=
  ∃ fr₀, Evm.beginCall params = .inl fr₀ ∧ BytecodeLayer.Hoare.Runs fr₀ fr'

structure PrecompileAssumptions (prog : Program) (params : Evm.CallParams) : Prop where
  noErase : Lir.Spec.PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'

end Lir
