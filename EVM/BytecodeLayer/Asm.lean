import BytecodeLayer.Exec

namespace BytecodeLayer.Asm

open Evm

/-- The non-immediate instructions emitted by the current assembler surface. -/
inductive Op where
  | stop
  | add
  | lt
  | pop
  | mload
  | mstore
  | sload
  | sstore
  | jump
  | jumpi
  | gas
  | call
  | create2
  | ret
deriving DecidableEq, Repr

def Op.byte : Op → UInt8
  | .stop    => 0x00
  | .add     => 0x01
  | .lt      => 0x10
  | .pop     => 0x50
  | .mload   => 0x51
  | .mstore  => 0x52
  | .sload   => 0x54
  | .sstore  => 0x55
  | .jump    => 0x56
  | .jumpi   => 0x57
  | .gas     => 0x5a
  | .call    => 0xf1
  | .create2 => 0xf5
  | .ret     => 0xf3

/-- An instruction or fixed-width block relocation. -/
inductive AsmInstr where
  | push (value : UInt256)
  | pushLabel (label : Nat)
  | op (operation : Op)
deriving DecidableEq, Repr

def AsmInstr.byteLength : AsmInstr → Nat
  | .push _      => 33
  | .pushLabel _ => 5
  | .op _        => 1

structure AsmBlock where
  body : List AsmInstr
deriving Repr

structure AsmProgram where
  blocks : Array AsmBlock
deriving Repr

def blockLength (block : AsmBlock) : Nat :=
  1 + (block.body.map AsmInstr.byteLength).sum

/-- Byte offset of a block's leading `JUMPDEST`. -/
def blockOffset (program : AsmProgram) (label : Nat) : Nat :=
  ((program.blocks.toList.take label).map blockLength).sum

def encodeInstr (labelOffset : Nat → Nat) : AsmInstr → List UInt8
  | .push value =>
      0x7f :: BytecodeLayer.Exec.wordBytesBE value
  | .pushLabel label =>
      0x63 :: BytecodeLayer.Exec.offsetBytesBE (labelOffset label)
  | .op operation =>
      [operation.byte]

def encodeInstrs (labelOffset : Nat → Nat) (instructions : List AsmInstr) : List UInt8 :=
  instructions.flatMap (encodeInstr labelOffset)

@[simp] theorem encodeInstrs_nil (labelOffset : Nat → Nat) :
    encodeInstrs labelOffset [] = [] := rfl

@[simp] theorem encodeInstrs_singleton (labelOffset : Nat → Nat) (instr : AsmInstr) :
    encodeInstrs labelOffset [instr] = encodeInstr labelOffset instr := by
  simp [encodeInstrs]

@[simp] theorem encodeInstrs_cons (labelOffset : Nat → Nat)
    (instr : AsmInstr) (rest : List AsmInstr) :
    encodeInstrs labelOffset (instr :: rest) =
      encodeInstr labelOffset instr ++ encodeInstrs labelOffset rest := by
  simp [encodeInstrs]

def encodeBlock (labelOffset : Nat → Nat) (block : AsmBlock) : List UInt8 :=
  0x5b :: encodeInstrs labelOffset block.body

def bytes (program : AsmProgram) : List UInt8 :=
  let labelOffset := blockOffset program
  program.blocks.toList.flatMap (encodeBlock labelOffset)

/-- Resolve block relocations and encode a structured assembly program. -/
def assemble (program : AsmProgram) : ByteArray :=
  ⟨(bytes program).toArray⟩

@[simp] theorem encodeInstr_length (labelOffset : Nat → Nat) (instr : AsmInstr) :
    (encodeInstr labelOffset instr).length = instr.byteLength := by
  cases instr <;> simp [encodeInstr, AsmInstr.byteLength,
    BytecodeLayer.Exec.wordBytesBE, BytecodeLayer.Exec.offsetBytesBE]

@[simp] theorem encodeInstrs_append (labelOffset : Nat → Nat) (left right : List AsmInstr) :
    encodeInstrs labelOffset (left ++ right) =
      encodeInstrs labelOffset left ++ encodeInstrs labelOffset right := by
  simp [encodeInstrs]

@[simp] theorem encodeInstrs_length (labelOffset : Nat → Nat) (instructions : List AsmInstr) :
    (encodeInstrs labelOffset instructions).length =
      (instructions.map AsmInstr.byteLength).sum := by
  simp [encodeInstrs, List.length_flatMap]

@[simp] theorem encodeBlock_length (labelOffset : Nat → Nat) (block : AsmBlock) :
    (encodeBlock labelOffset block).length = blockLength block := by
  simp [encodeBlock, blockLength, Nat.add_comm]

end BytecodeLayer.Asm
