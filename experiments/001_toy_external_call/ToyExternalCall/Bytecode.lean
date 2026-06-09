import EvmYul.EVM.Semantics
import ToyExternalCall.IR

/-!
# Lowering the toy IR to EVM bytecode

The lowering is total. Each IR instruction compiles to a straight-line
sequence of opcode-level `Op`s (each `Op` is exactly one EVM instruction),
and a program is terminated by a single `STOP`.

The byte encoding is defined at the `List UInt8` level (`codeBytes`) so that
all decode reasoning can be done with plain list arithmetic; the `ByteArray`
is only wrapped around the final list.
-/

namespace ToyExternalCall

open EvmYul

namespace Bytecode

/-- Opcode-level operations; each corresponds to exactly one EVM
instruction of the lowered code. -/
inductive Op where
  | push (value : Word)
  | calldataload
  | add
  | mload
  | mstore
  | call
  | stop
  deriving Repr

def opcode (op : Operation .EVM) : UInt8 :=
  EVM.serializeInstr op

/-- Byte encoding of one op. `push` is `PUSH32` followed by the value in
big-endian (the byte order of `UInt256.toByteArray`). -/
def opBytes : Op → List UInt8
  | .push v => opcode .PUSH32 :: (EvmYul.toBytes! v).reverse
  | .calldataload => [opcode .CALLDATALOAD]
  | .add => [opcode .ADD]
  | .mload => [opcode .MLOAD]
  | .mstore => [opcode .MSTORE]
  | .call => [opcode .CALL]
  | .stop => [opcode .STOP]

def opSize : Op → Nat
  | .push _ => 33
  | _ => 1

theorem opBytes_length (op : Op) : (opBytes op).length = opSize op := by
  cases op <;> simp [opBytes, opSize, EvmYul.toBytes!_length]

def codeBytes (ops : List Op) : List UInt8 :=
  ops.flatMap opBytes

@[simp] theorem codeBytes_nil : codeBytes [] = [] := rfl

@[simp] theorem codeBytes_cons (op : Op) (ops : List Op) :
    codeBytes (op :: ops) = opBytes op ++ codeBytes ops := rfl

@[simp] theorem codeBytes_append (ops₁ ops₂ : List Op) :
    codeBytes (ops₁ ++ ops₂) = codeBytes ops₁ ++ codeBytes ops₂ := by
  simp [codeBytes]

def assemble (ops : List Op) : ByteArray :=
  ⟨⟨codeBytes ops⟩⟩

@[simp] theorem assemble_data_toList (ops : List Op) :
    (assemble ops).data.toList = codeBytes ops := rfl

/-! ## Compilation -/

def compileOperandOps : Operand → List Op
  | .const v => [.push v]
  | .local x => [.push (localSlot x), .mload]

def storeLocalOps (x : Local) : List Op :=
  [.push (localSlot x), .mstore]

def compileInstrOps : Instr → List Op
  | .inputLoad dst offset =>
      compileOperandOps offset ++ [.calldataload] ++ storeLocalOps dst
  | .add dst lhs rhs =>
      compileOperandOps rhs ++ compileOperandOps lhs ++ [.add] ++ storeLocalOps dst
  | .call dst args =>
      compileOperandOps args.outSize ++
      compileOperandOps args.outOffset ++
      compileOperandOps args.inSize ++
      compileOperandOps args.inOffset ++
      compileOperandOps args.value ++
      compileOperandOps args.target ++
      compileOperandOps args.gas ++
      [.call] ++ storeLocalOps dst

def lowerOps : Program → List Op
  | [] => [.stop]
  | instr :: rest => compileInstrOps instr ++ lowerOps rest

/-- The lowered bytecode of a program. -/
def lower (program : Program) : ByteArray :=
  assemble (lowerOps program)

end Bytecode

end ToyExternalCall
