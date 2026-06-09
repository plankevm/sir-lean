import EvmYul.EVM.Semantics
import ToyExternalCall.Bytecode

namespace ToyExternalCall

open EvmYul

namespace Correctness

def writeLocalSlot (evm : EVM.State) (x : Local) (value : Word) : EVM.State :=
  { evm with toMachineState := evm.toMachineState.writeWord (Bytecode.localSlot x) value }

def seedLocals (locals : Local → Word) (xs : List Local) (evm : EVM.State) : EVM.State :=
  xs.foldl (fun evm x => writeLocalSlot evm x (locals x)) evm

def withLoweredCodeAndLocals (state : ToyState) (program : Program) : EVM.State :=
  let evm := seedLocals state.locals program.readLocals state.evm
  { evm with
    pc := UInt256.ofNat 0
    stack := []
    execLength := 0
    executionEnv := { evm.executionEnv with code := Bytecode.lower program }
  }

def LocalRelOn (xs : List Local) (locals : Local → Word) (evm : EVM.State) : Prop :=
  ∀ x, x ∈ xs → evm.toMachineState.lookupMemory (Bytecode.localSlot x) = locals x

def StateRelOn (xs : List Local) (toy : ToyState) (evm : EVM.State) : Prop :=
  LocalRelOn xs toy.locals evm ∧
  evm.accountMap = toy.evm.accountMap ∧
  evm.substate = toy.evm.substate ∧
  evm.returnData = toy.evm.returnData

def ResultRelOn
    (xs : List Local)
    (source : RunResult)
    (target : Except EVM.ExecutionException (EVM.ExecutionResult EVM.State)) : Prop :=
  match source, target with
  | .ok toy, .ok (.success evm _output) =>
      StateRelOn xs toy evm
  | .exceptional _sourceState sourceError, .error targetError =>
      sourceError = targetError
  | .outOfFuel _sourceState, .error .OutOfFuel =>
      True
  | _, _ =>
      False

def evmCall
    (fuel gasCost : Nat)
    (state : ToyState)
    (request : CallRequest) :
    Except EVM.ExecutionException (Word × EVM.State) :=
  EVM.call fuel gasCost state.evm.executionEnv.blobVersionedHashes
    request.gas
    (.ofNat state.evm.executionEnv.codeOwner)
    request.targetWord
    request.targetWord
    request.value
    request.value
    request.inOffset
    request.inSize
    request.outOffset
    request.outSize
    state.evm.executionEnv.perm
    state.evm

/--
Calls are the semantic boundary where the source interpreter uses an oracle
and lowered bytecode uses EVMYulLean's `CALL`.

The oracle is sound only when every oracle answer can be reproduced by the
EVMYulLean call semantics under some call fuel and precomputed dynamic gas
cost. The theorem for a concrete backend should replace the existential fuel
and gas-cost witnesses with the exact values obtained from the compiled stack
and `EVM.C'`.
-/
def CallOracleSoundForLowering
    (oracle : CallOracle) : Prop :=
  ∀ state request,
    match oracle state request with
    | .ok result =>
        ∃ fuel gasCost evmAfter successFlag,
          evmCall fuel gasCost state request = .ok (successFlag, evmAfter) ∧
          result.successFlag = successFlag ∧
          result.returnData = evmAfter.returnData ∧
          result.evm = evmAfter
    | .error error =>
        ∃ fuel gasCost,
          evmCall fuel gasCost state request = .error error

/--
The lowered program uses reserved memory slots for source locals. A real proof
must show calls do not clobber the reserved slots observed by the program, or
must replace this allocator with a frame discipline that makes clobbering
impossible by construction.
-/
def CallOraclePreservesReservedLocalSlots
    (oracle : CallOracle)
    (xs : List Local) : Prop :=
  ∀ state request result x,
    oracle state request = .ok result →
    x ∈ xs →
    result.evm.toMachineState.lookupMemory (Bytecode.localSlot x) =
      state.evm.toMachineState.lookupMemory (Bytecode.localSlot x)

def LoweringPreservationSpec
    (oracle : CallOracle)
    (program : Program)
    (initial : ToyState) : Prop :=
  CallOracleSoundForLowering oracle →
  CallOraclePreservesReservedLocalSlots oracle program.touchedLocals →
  ResultRelOn
    program.touchedLocals
    (run oracle (program.length + 1) initial program)
    (EVM.X (Bytecode.lowerFuel program)
      (EVM.D_J (Bytecode.lower program) (UInt256.ofNat 0))
      (withLoweredCodeAndLocals initial program))

end Correctness

end ToyExternalCall
