import EvmYul.EVM.Semantics
import ToyExternalCall.Bytecode

namespace ToyExternalCall

open EvmYul

namespace Correctness

def prefixProgram (constant : Word) : Program :=
  [ .inputLoad 0 (.const (UInt256.ofNat 0))
  , .add 1 (.const constant) (.local 0)
  ]

def noCallOracle : CallOracle :=
  fun state _ =>
    .ok { successFlag := UInt256.ofNat 0, returnData := state.evm.returnData, evm := state.evm }

def withCode (state : EVM.State) (code : ByteArray) : EVM.State :=
  { state with
    pc := UInt256.ofNat 0
    stack := []
    execLength := 0
    executionEnv := { state.executionEnv with code := code }
  }

def prefixEvmInitial (state : ToyState) (constant : Word) : EVM.State :=
  withCode state.evm (Bytecode.lower (prefixProgram constant))

def prefixExpectedLocalValue (state : ToyState) (constant : Word) : Word :=
  constant + state.callDataLoad (UInt256.ofNat 0)

def prefixObservation (state : ToyState) (constant : Word) : Prop :=
  match run noCallOracle 3 state (prefixProgram constant) with
  | .ok state' => state'.readLocal 1 = constant + state.callDataLoad (UInt256.ofNat 0)
  | _ => False

theorem prefix_source_semantics (state : ToyState) (constant : Word) :
    prefixObservation state constant := by
  simp [prefixObservation, prefixProgram, run, evalInstr,
    ToyState.readLocal, ToyState.writeLocal, ToyState.evalOperand, ToyState.callDataLoad]

def prefixEvmResultMatches (state : ToyState) (constant : Word)
    (result : EVM.ExecutionResult EVM.State) : Prop :=
  match result with
  | .success evmState output =>
      evmState.toMachineState.lookupMemory (Bytecode.localSlot 1) =
        prefixExpectedLocalValue state constant ∧
      output = ByteArray.empty
  | .revert _ _ => False

theorem prefix_lowering_has_expected_code (state : ToyState) (constant : Word) :
    (prefixEvmInitial state constant).executionEnv.code = Bytecode.lower (prefixProgram constant) := by
  rfl

def RunsPrefixThroughEvmX (state : ToyState) (constant : Word) : Prop :=
  ∃ result,
    EVM.X 32 (EVM.D_J (Bytecode.lower (prefixProgram constant)) (UInt256.ofNat 0))
      (prefixEvmInitial state constant) =
      .ok result ∧
    prefixEvmResultMatches state constant result

def FixedCallOracle : CallOracle :=
  fun state request =>
    .ok
      { successFlag := UInt256.ofNat 1
        returnData := request.input
        evm := { state.evm with
          toMachineState :=
            { writeBytes request.input 0 state.evm.toMachineState request.outOffset.toNat
                (min request.outSize.toNat request.input.size) with
              returnData := request.input } } }

def canonicalSourceResultMatches
    (callArgs : CallArgs) (constant : Word) (state : ToyState) : Prop :=
  match run FixedCallOracle 4 state (canonicalProgram callArgs constant) with
  | .ok finalState =>
      finalState.readLocal 1 = constant + state.callDataLoad (UInt256.ofNat 0) ∧
      finalState.readLocal 2 = UInt256.ofNat 1
  | _ => False

theorem canonical_source_semantics
    (callArgs : CallArgs) (constant : Word) (state : ToyState) :
    canonicalSourceResultMatches callArgs constant state := by
  simp [canonicalSourceResultMatches, canonicalProgram, run, evalInstr, FixedCallOracle,
    ToyState.readLocal, ToyState.writeLocal, ToyState.evalOperand, ToyState.callDataLoad,
    ToyState.evalCallRequest, ToyState.callInput, ToyState.setEvm, ToyState.setReturnData]

end Correctness

end ToyExternalCall
