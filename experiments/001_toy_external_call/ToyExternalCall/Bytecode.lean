import EvmYul.EVM.Semantics
import ToyExternalCall.IR

namespace ToyExternalCall

open EvmYul

namespace Bytecode

inductive Op where
  | push (value : Word)
  | loadLocal (x : Local)
  | storeLocal (x : Local)
  | calldataload
  | add
  | call
  | stop
  deriving Repr

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

def assembleOperand : Operand → ByteArray
  | .const value => push32 value
  | .local x => loadLocal x

def assembleOp : Op → ByteArray
  | .push value => push32 value
  | .loadLocal x => loadLocal x
  | .storeLocal x => storeLocal x
  | .calldataload => op .CALLDATALOAD
  | .add => op .ADD
  | .call => op .CALL
  | .stop => op .STOP

def assemble (ops : List Op) : ByteArray :=
  appendMany (ops.map assembleOp)

def compileOperandOps : Operand → List Op
  | .const value => [.push value]
  | .local x => [.loadLocal x]

def compileOperand (operand : Operand) : ByteArray :=
  assembleOperand operand

def operandFuel : Operand → Nat
  | .const _ => 1
  | .local _ => 2

def compileAddOps (dst : Local) (lhs rhs : Operand) : List Op :=
  compileOperandOps rhs ++
  compileOperandOps lhs ++
  [.add, .storeLocal dst]

def compileAdd (dst : Local) (lhs rhs : Operand) : ByteArray :=
  assemble (compileAddOps dst lhs rhs)

def addFuel (lhs rhs : Operand) : Nat :=
  operandFuel rhs + operandFuel lhs + 3

def compileCallOps (dst : Local) (args : CallArgs) : List Op :=
  compileOperandOps args.outSize ++
  compileOperandOps args.outOffset ++
  compileOperandOps args.inSize ++
  compileOperandOps args.inOffset ++
  compileOperandOps args.value ++
  compileOperandOps args.target ++
  compileOperandOps args.gas ++
  [.call, .storeLocal dst]

def compileCall (dst : Local) (args : CallArgs) : ByteArray :=
  assemble (compileCallOps dst args)

def callFuel (args : CallArgs) : Nat :=
  operandFuel args.outSize +
  operandFuel args.outOffset +
  operandFuel args.inSize +
  operandFuel args.inOffset +
  operandFuel args.value +
  operandFuel args.target +
  operandFuel args.gas +
  3

def compileInstrOps : Instr → List Op
  | .inputLoad dst offset =>
      compileOperandOps offset ++ [.calldataload, .storeLocal dst]
  | .add dst lhs rhs =>
      compileAddOps dst lhs rhs
  | .call dst args =>
      compileCallOps dst args

def compileInstr : Instr → ByteArray
  | instr => assemble (compileInstrOps instr)

def instrFuel : Instr → Nat
  | .inputLoad _ offset => operandFuel offset + 3
  | .add _ lhs rhs => addFuel lhs rhs
  | .call _ args => callFuel args

def lowerBody : Program → ByteArray :=
  fun program => assemble (program.foldr (fun instr ops => compileInstrOps instr ++ ops) [])

def lowerOps : Program → List Op
  | [] => [.stop]
  | instr :: rest => compileInstrOps instr ++ lowerOps rest

def lower (program : Program) : ByteArray :=
  assemble (lowerOps program)

def lowerFuel (program : Program) : Nat :=
  program.foldl (fun fuel instr => fuel + instrFuel instr) 2

end Bytecode

end ToyExternalCall
