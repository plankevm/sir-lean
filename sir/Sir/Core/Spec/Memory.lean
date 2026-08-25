import Sir.Core.Spec.Base

namespace Sir

structure Allocation where
  offset : Word
  bytes : ByteArray

namespace Allocation

def size (a : Allocation) : Nat := a.bytes.size

def start (a : Allocation) : Nat := a.offset.toNat

def endExclusive (a : Allocation) : Nat := a.start + a.size

def Contains (a : Allocation) (start len : Nat) : Prop :=
  a.start ≤ start ∧ start + len ≤ a.endExclusive

instance (a : Allocation) (start len : Nat) : Decidable (a.Contains start len) :=
  decidable_of_iff (a.start ≤ start ∧ start + len ≤ a.endExclusive) Iff.rfl

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

def watermark (m : MemoryState) : Nat :=
  m.provisioned.foldl (fun watermark allocation => max watermark allocation.endExclusive) 0

def bumpAlloc (m : MemoryState) (size : Nat) : Allocation :=
  { offset := .ofNat m.watermark, bytes := ByteArray.mk (Array.replicate size 0) }

def push (m : MemoryState) (a : Allocation) : MemoryState :=
  { provisioned := m.provisioned.push a }

def InBounds (m : MemoryState) (start len : Nat) : Prop :=
  ∃ a ∈ m.provisioned, a.Contains start len

instance (m : MemoryState) (start len : Nat) : Decidable (m.InBounds start len) :=
  decidable_of_iff (∃ a ∈ m.provisioned.toList, a.Contains start len)
    (by simp [MemoryState.InBounds])

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

structure Globals where
  world : World
  memory : MemoryState := .empty
  returnData : ByteArray := ByteArray.empty

namespace Globals

def storeStorage (globals : Globals) (context : CallContext) (key value : Word) : Globals :=
  { globals with world := globals.world.storeStorage context.self key value }

def pushAlloc (globals : Globals) (allocation : Allocation) : Globals :=
  { globals with memory := globals.memory.push allocation }

def writeWord32 (globals : Globals) (offset value : Word) : Globals :=
  { globals with memory := globals.memory.writeBytes offset value.toByteArray }

def readWord32 (globals : Globals) (offset : Word) (assumed : Vector UInt8 32) : Word :=
  .ofNat (Evm.fromByteArrayBigEndian (globals.memory.readBytes offset ⟨assumed.toArray⟩))

def callInput (globals : Globals) (target gas : Word) : CallInput :=
  { target := .ofUInt256 target, gas, world := globals.world }

def applyCall (globals : Globals) (result : CallResult) : Globals :=
  { globals with returnData := result.output, world := result.world' }

end Globals

/-- Permitted representations of a fresh region: any disjoint placement of the
requested size. A concrete allocator is a policy that refines this one. -/
structure MemoryPolicy where
  Allows : MemoryState → Nat → Allocation → Prop

namespace MemoryPolicy

def Refines (finer coarser : MemoryPolicy) : Prop :=
  ∀ memory size allocation,
    finer.Allows memory size allocation →
    coarser.Allows memory size allocation

end MemoryPolicy

def memoryPolicy : MemoryPolicy where
  Allows memory size allocation :=
    memory.IsValidNewAlloc allocation ∧ allocation.size = size

/-- The release bump: the next unused address, zero-filled. -/
def bumpPolicy : MemoryPolicy where
  Allows memory size allocation :=
    allocation = memory.bumpAlloc size ∧ memory.IsValidNewAlloc allocation

end Sir
