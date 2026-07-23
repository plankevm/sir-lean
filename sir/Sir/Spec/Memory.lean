import Sir.Spec.Ir

namespace Sir

structure Allocation where
  offset : Word
  bytes : ByteArray

namespace Allocation

def size (a : Allocation) : Nat := a.bytes.size

def start (a : Allocation) : Nat := a.offset.toNat

def endExclusive (a : Allocation) : Nat := a.start + a.size

def readByte? (a : Allocation) (address : Nat) : Option UInt8 :=
  if a.start ≤ address ∧ address < a.endExclusive then
    a.bytes.get? (address - a.start)
  else
    none

def writeByte (a : Allocation) (address : Nat) (value : UInt8) : Allocation :=
  if a.start ≤ address ∧ address < a.endExclusive then
    { a with bytes := ⟨a.bytes.data.setIfInBounds (address - a.start) value⟩ }
  else
    a

def IsDisjoint (a1 a2 : Allocation) : Prop :=
  a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start

instance (a1 a2 : Allocation) : Decidable (a1.IsDisjoint a2) :=
  decidable_of_iff (a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start) Iff.rfl

end Allocation

structure MemoryState where
  provisioned : Array Allocation

namespace MemoryState

def empty : MemoryState := { provisioned := #[] }

def IsValidNewAlloc (m : MemoryState) (a : Allocation) : Prop :=
  a.endExclusive ≤ Evm.UInt256.size ∧ ∀ a' ∈ m.provisioned, Allocation.IsDisjoint a a'

instance (m : MemoryState) (a : Allocation) : Decidable (m.IsValidNewAlloc a) :=
  decidable_of_iff
    (a.endExclusive ≤ Evm.UInt256.size ∧ ∀ a' ∈ m.provisioned.toList, a.IsDisjoint a')
    (by simp [MemoryState.IsValidNewAlloc])

def push (m : MemoryState) (a : Allocation) : MemoryState :=
  { provisioned := m.provisioned.push a }

def readByte? (m : MemoryState) (address : Nat) : Option UInt8 :=
  m.provisioned.findSome? (·.readByte? address)

def writeByte (m : MemoryState) (address : Nat) (value : UInt8) : MemoryState :=
  { provisioned := m.provisioned.map (·.writeByte address value) }

def writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray) : MemoryState :=
  bytes.toList.zipIdx.foldl
    (fun memory (byte, index) => memory.writeByte (offset.toNat + index) byte)
    m

def readBytes (m : MemoryState) (offset : Word) (assumed : ByteArray) : ByteArray :=
  List.toByteArray <| assumed.toList.zipIdx.map fun (byte, index) =>
    (m.readByte? (offset.toNat + index)).getD byte

end MemoryState

end Sir
