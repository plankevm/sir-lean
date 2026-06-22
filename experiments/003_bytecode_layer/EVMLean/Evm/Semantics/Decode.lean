import Evm.Exception
import Evm.Instr
import Evm.Operations
import Evm.State.ExecutionEnv
import Evm.UInt256
import Evm.Wheels

namespace Evm

def pushArgWidth : Operation → UInt8
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def nextInstrPos (pc : UInt32) (instr : Operation) := pc + 1 + (pushArgWidth instr).toUInt32

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt32) :
  Option (Operation × Option (UInt256 × UInt8)) := do
  let byte ← arr.get? pc.toNat
  let instr := Evm.parseInstr byte
  let argWidth := pushArgWidth instr
  let immediate :=
    if argWidth > 0
    then
      let pc' := pc.toNat + 1
      .some (Evm.uInt256OfByteArray (arr.extract pc' (pc' + argWidth.toNat)), argWidth)
    else .none
  .some (instr, immediate)

partial def validJumpDestsAux (c : ByteArray) (i : UInt32) (result : Array UInt32) : Array UInt32 :=
  match c.get? i.toNat with
    | none => result
    | some byte =>
      let cᵢ := Evm.parseInstr byte
      validJumpDestsAux c (nextInstrPos i cᵢ) (if cᵢ = .JUMPDEST then result.push i else result)

def validJumpDests (c : ByteArray) (i : UInt32) : Array UInt32 :=
  validJumpDestsAux c i #[]

end Evm
