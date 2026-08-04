import Sir.Spec.Ir

namespace Sir

structure Allocation where
  offset : Word
  size : Nat

namespace Allocation

def start (a : Allocation) : Nat := a.offset.toNat

def endExclusive (a : Allocation) : Nat := a.start + a.size

/-- Whole-range containment keeps access authority tied to one allocation. -/
def Contains (a : Allocation) (start len : Nat) : Prop :=
  a.start ≤ start ∧ start + len ≤ a.endExclusive

instance (a : Allocation) (start len : Nat) : Decidable (a.Contains start len) :=
  decidable_of_iff (a.start ≤ start ∧ start + len ≤ a.endExclusive) Iff.rfl

def IsDisjoint (a1 a2 : Allocation) : Prop :=
  a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start

instance (a1 a2 : Allocation) : Decidable (a1.IsDisjoint a2) :=
  decidable_of_iff (a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start) Iff.rfl

end Allocation

/--
Byte contents are separate from allocation authority so reads can be total while writes remain
guarded. The total store is unconstrained in an arbitrary state; `empty` supplies zero-initialized
contents.
-/
structure MemoryState where
  store : Nat → UInt8
  provisioned : Array Allocation

namespace MemoryState

def empty : MemoryState := { store := fun _ => 0, provisioned := #[] }

def IsValidNewAlloc (m : MemoryState) (a : Allocation) : Prop :=
  a.endExclusive ≤ Evm.UInt256.size ∧ ∀ a' ∈ m.provisioned, Allocation.IsDisjoint a a'

instance (m : MemoryState) (a : Allocation) : Decidable (m.IsValidNewAlloc a) :=
  decidable_of_iff
    (a.endExclusive ≤ Evm.UInt256.size ∧ ∀ a' ∈ m.provisioned.toList, a.IsDisjoint a')
    (by simp [MemoryState.IsValidNewAlloc])

def watermark (m : MemoryState) : Nat :=
  m.provisioned.foldl (fun watermark allocation => max watermark allocation.endExclusive) 0

/-- Watermark placement makes the next region canonical without adding allocator state to memory. -/
def bumpAllocation (m : MemoryState) (size : Nat) : Allocation :=
  { offset := .ofNat m.watermark, size }

def push (m : MemoryState) (a : Allocation) : MemoryState :=
  { m with provisioned := m.provisioned.push a }

/-- Store authorization requires a single provisioned allocation to contain the whole range. -/
def InBounds (m : MemoryState) (start len : Nat) : Prop :=
  ∃ a ∈ m.provisioned, a.Contains start len

instance (m : MemoryState) (start len : Nat) : Decidable (m.InBounds start len) :=
  decidable_of_iff (∃ a ∈ m.provisioned.toList, a.Contains start len)
    (by simp [MemoryState.InBounds])

def readByte (m : MemoryState) (address : Nat) : UInt8 := m.store address

def writeByte (m : MemoryState) (address : Nat) (value : UInt8) : MemoryState :=
  { m with store := fun candidate => if candidate = address then value else m.store candidate }

def writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray) : MemoryState :=
  bytes.toList.zipIdx.foldl
    (fun memory (byte, index) => memory.writeByte (offset.toNat + index) byte)
    m

def readBytes (m : MemoryState) (offset : Word) (len : Nat) : ByteArray :=
  List.toByteArray <| (List.range len).map fun index => m.readByte (offset.toNat + index)

end MemoryState

end Sir
