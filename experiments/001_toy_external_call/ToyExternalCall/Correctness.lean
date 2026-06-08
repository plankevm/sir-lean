import EvmYul.EVM.Semantics
import ToyExternalCall.Bytecode

namespace ToyExternalCall

open EvmYul

namespace Correctness

def prefixProgram (constant : Word) : Program :=
  [ .inputLoad 0 (.const (UInt256.ofNat 0))
  , .addConst 1 0 constant
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
  withCode state.evm (Bytecode.prefixAddConst constant)

def prefixExpectedStack (state : ToyState) (constant : Word) : Stack Word :=
  [constant + state.callDataLoad (UInt256.ofNat 0)]

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
      evmState.stack = prefixExpectedStack state constant ∧
      output = ByteArray.empty
  | .revert _ _ => False

theorem prefix_lowering_has_expected_code (state : ToyState) (constant : Word) :
    (prefixEvmInitial state constant).executionEnv.code = Bytecode.prefixAddConst constant := by
  rfl

theorem lower_prefixProgram (constant : Word) :
    Bytecode.lower (prefixProgram constant) = some (Bytecode.prefixAddConst constant) := by
  simp [Bytecode.lower, prefixProgram]

def RunsPrefixThroughEvmX (state : ToyState) (constant : Word) : Prop :=
  ∃ result,
    EVM.X 6 (EVM.D_J (Bytecode.prefixAddConst constant) (UInt256.ofNat 0))
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

def CanonicalLoweringSourceAndCodeAgree
    (callArgs : CallArgs) (constant : Word) (state : ToyState) : Prop :=
  Bytecode.canonicalProgramLowerable callArgs →
  canonicalSourceResultMatches callArgs constant state ∧
  ∃ concrete,
    Bytecode.concreteCanonicalCallArgs? { callArgs with target := .local 1 } = some concrete ∧
    Bytecode.lower (canonicalProgram callArgs constant) = some (Bytecode.lowerCanonical concrete constant)

theorem canonical_lowering_source_and_code_agree
    (callArgs : CallArgs) (constant : Word) (state : ToyState) :
    CanonicalLoweringSourceAndCodeAgree callArgs constant state := by
  intro hLowerable
  rcases hLowerable with ⟨concrete, hConcrete⟩
  refine ⟨canonical_source_semantics callArgs constant state, concrete, hConcrete, ?_⟩
  simp [Bytecode.lower, canonicalProgram, hConcrete]

end Correctness

end ToyExternalCall
