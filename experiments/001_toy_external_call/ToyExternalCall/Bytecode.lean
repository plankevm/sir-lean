import EvmYul.EVM.Semantics
import ToyExternalCall.IR

namespace ToyExternalCall

open EvmYul

namespace Bytecode

def opcode (op : Operation .EVM) : UInt8 :=
  EVM.serializeInstr op

def op (operation : Operation .EVM) : ByteArray :=
  ⟨#[opcode operation]⟩

def push32 (value : Word) : ByteArray :=
  ⟨#[opcode .PUSH32] ++ value.toByteArray.data⟩

def appendMany : List ByteArray → ByteArray :=
  fun parts => ⟨parts.foldl (fun acc part => acc ++ part.data) #[]⟩

def localBase : Nat :=
  1048576

def localSlot (x : Local) : Word :=
  UInt256.ofNat (localBase + 32 * x)

def loadLocal (x : Local) : ByteArray :=
  appendMany
    [ push32 (localSlot x)
    , op .MLOAD
    ]

def storeLocal (x : Local) : ByteArray :=
  appendMany
    [ push32 (localSlot x)
    , op .MSTORE
    ]

def compileOperand : Operand → ByteArray
  | .const value => push32 value
  | .local x => loadLocal x

def compileAdd (dst : Local) (lhs rhs : Operand) : ByteArray :=
  appendMany
    [ compileOperand rhs
    , compileOperand lhs
    , op .ADD
    , storeLocal dst
    ]

def compileCall (dst : Local) (args : CallArgs) : ByteArray :=
  appendMany
    [ compileOperand args.outSize
    , compileOperand args.outOffset
    , compileOperand args.inSize
    , compileOperand args.inOffset
    , compileOperand args.value
    , compileOperand args.target
    , compileOperand args.gas
    , op .CALL
    , storeLocal dst
    ]

def compileInstr : Instr → ByteArray
  | .inputLoad dst offset =>
      appendMany
        [ compileOperand offset
        , op .CALLDATALOAD
        , storeLocal dst
        ]
  | .add dst lhs rhs =>
      compileAdd dst lhs rhs
  | .call dst args =>
      compileCall dst args

def lowerBody : Program → ByteArray :=
  fun program => appendMany (program.map compileInstr)

def lower (program : Program) : ByteArray :=
  appendMany [lowerBody program, op .STOP]

def prefixPushedConstant (constant : Word) : Word :=
  uInt256OfByteArray ((push32 constant).extract' 1 33)

end Bytecode

end ToyExternalCall
