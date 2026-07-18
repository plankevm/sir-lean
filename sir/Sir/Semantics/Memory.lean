import Sir.Core.Types
import Evm.Maps.AccountMap

namespace Sir

structure Allocation where
  offset: Word
  bytes: ByteArray


def Allocation.size (a : Allocation) : Nat := a.bytes.size

def Allocation.start (a : Allocation) : Nat := a.offset.toNat

def Allocation.endExclusive (a : Allocation) : Nat := a.start + a.size

def Allocation.readByte? (a : Allocation) (address : Nat) : Option UInt8 :=
  if a.start ≤ address ∧ address < a.endExclusive then
    a.bytes.get? (address - a.start)
  else
    none

def Allocation.writeByte (a : Allocation) (address : Nat) (value : UInt8) : Allocation :=
  if a.start ≤ address ∧ address < a.endExclusive then
    { a with bytes := ⟨a.bytes.data.setIfInBounds (address - a.start) value⟩ }
  else
    a

def Allocation.IsDisjoint (a1 a2 : Allocation) : Prop :=
  a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start

structure MemoryState where
  provisioned : Array Allocation

def MemoryState.empty : MemoryState := { provisioned := #[] }

def MemoryState.IsValidNewAlloc (m : MemoryState) (a : Allocation) : Prop :=
  a.endExclusive ≤ Evm.UInt256.size ∧ ∀ a' ∈ m.provisioned, Allocation.IsDisjoint a a'

def MemoryState.push (m : MemoryState) (a : Allocation) : MemoryState :=
  { provisioned := m.provisioned.push a }

def MemoryState.readByte? (m : MemoryState) (address : Nat) : Option UInt8 :=
  m.provisioned.findSome? (·.readByte? address)

def MemoryState.writeByte (m : MemoryState) (address : Nat) (value : UInt8) : MemoryState :=
  { provisioned := m.provisioned.map (·.writeByte address value) }

def MemoryState.writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray) : MemoryState :=
  bytes.toList.zipIdx.foldl
    (fun memory (byte, index) => memory.writeByte (offset.toNat + index) byte)
    m

def MemoryState.readBytes (m : MemoryState) (offset : Word) (assumed : ByteArray) : ByteArray :=
  List.toByteArray <| assumed.toList.zipIdx.map fun (byte, index) =>
    (m.readByte? (offset.toNat + index)).getD byte

end Sir
