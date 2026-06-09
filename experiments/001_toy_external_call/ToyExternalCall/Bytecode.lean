import EvmYul.EVM.Semantics
import ToyExternalCall.IR

namespace ToyExternalCall

open EvmYul

namespace Bytecode

def constOperand? : Operand → Option Word
  | .const value => some value
  | .local _ => none

structure ConcreteCallArgs where
  gas : Word
  value : Word
  inOffset : Word
  inSize : Word
  outOffset : Word
  outSize : Word

def concreteCanonicalCallArgs? (callArgs : CallArgs) : Option ConcreteCallArgs := do
  match callArgs.target with
  | .local 1 => pure ()
  | _ => none
  pure
    { gas := ← constOperand? callArgs.gas
      value := ← constOperand? callArgs.value
      inOffset := ← constOperand? callArgs.inOffset
      inSize := ← constOperand? callArgs.inSize
      outOffset := ← constOperand? callArgs.outOffset
      outSize := ← constOperand? callArgs.outSize }

def opcode (op : Operation .EVM) : UInt8 :=
  EVM.serializeInstr op

def op (operation : Operation .EVM) : ByteArray :=
  ⟨#[opcode operation]⟩

def push32 (value : Word) : ByteArray :=
  ⟨#[opcode .PUSH32] ++ value.toByteArray.data⟩

def appendMany : List ByteArray → ByteArray :=
  fun parts => ⟨parts.foldl (fun acc part => acc ++ part.data) #[]⟩

def prefixAddConst (constant : Word) : ByteArray :=
  appendMany
    [ op .PUSH0
    , op .CALLDATALOAD
    , push32 constant
    , op .ADD
    , op .STOP
    ]

def lowerCanonical (callArgs : ConcreteCallArgs) (constant : Word) : ByteArray :=
  appendMany
    [ op .PUSH0
    , op .CALLDATALOAD
    , push32 constant
    , op .ADD
    , push32 callArgs.outSize
    , push32 callArgs.outOffset
    , push32 callArgs.inSize
    , push32 callArgs.inOffset
    , push32 callArgs.value
    , op .DUP6
    , push32 callArgs.gas
    , op .CALL
    , op .SWAP1
    , op .POP
    , op .STOP
    ]

def canonicalProgramLowerable (callArgs : CallArgs) : Prop :=
  ∃ concrete, concreteCanonicalCallArgs? { callArgs with target := .local 1 } = some concrete

def lower : Program → Option ByteArray
  | [ .inputLoad 0 (.const offset)
    , .add 1 (.const constant) (.local 0)
    ] =>
      if offset = UInt256.ofNat 0 then
        some (prefixAddConst constant)
      else
        none
  | [ .inputLoad 0 (.const offset)
    , .add 1 (.const constant) (.local 0)
    , .call 2 callArgs
    ] =>
      if offset = UInt256.ofNat 0 then
        match concreteCanonicalCallArgs? callArgs with
        | some concrete => some (lowerCanonical concrete constant)
        | none => none
      else
        none
  | _ => none

def prefixPushedConstant (constant : Word) : Word :=
  uInt256OfByteArray ((prefixAddConst constant).extract' 3 35)

end Bytecode

end ToyExternalCall
