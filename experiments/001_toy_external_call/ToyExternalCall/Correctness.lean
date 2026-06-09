import EvmYul.EVM.Semantics
import ToyExternalCall.Bytecode

namespace ToyExternalCall

open EvmYul

namespace Correctness

def withLoweredCode (state : EVM.State) (program : Program) : EVM.State :=
  { state with
    pc := UInt256.ofNat 0
    stack := []
    execLength := 0
    executionEnv := { state.executionEnv with code := Bytecode.lower program }
  }

def LocalRel (locals : Local → Word) (evm : EVM.State) : Prop :=
  ∀ x, evm.toMachineState.lookupMemory (Bytecode.localSlot x) = locals x

def StateRel (toy : ToyState) (evm : EVM.State) : Prop :=
  LocalRel toy.locals evm ∧
  evm.accountMap = toy.evm.accountMap ∧
  evm.substate = toy.evm.substate ∧
  evm.returnData = toy.evm.returnData

def ResultRel
    (source : RunResult)
    (target : Except EVM.ExecutionException (EVM.ExecutionResult EVM.State)) : Prop :=
  match source, target with
  | .ok toy, .ok (.success evm _output) =>
      StateRel toy evm
  | .exceptional _sourceState sourceError, .error targetError =>
      sourceError = targetError
  | .outOfFuel _sourceState, .error .OutOfFuel =>
      True
  | _, _ =>
      False

def LoweringPreservesSemantics
    (oracle : CallOracle)
    (sourceFuel evmFuel : Nat)
    (program : Program)
    (initial : ToyState) : Prop :=
  ResultRel
    (run oracle sourceFuel initial program)
    (EVM.X evmFuel (EVM.D_J (Bytecode.lower program) (UInt256.ofNat 0))
      (withLoweredCode initial.evm program))

theorem lowering_preservation_false_with_zero_evm_fuel
    (oracle : CallOracle)
    (initial : ToyState) :
    ¬ LoweringPreservesSemantics oracle 1 0 [] initial := by
  simp [LoweringPreservesSemantics, ResultRel, run, EVM.X]

end Correctness

end ToyExternalCall
