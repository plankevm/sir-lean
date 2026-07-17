import Sir.Core.Types
import Evm.Maps.AccountMap

namespace Sir

structure Allocation where
  offset: Word
  bytes: ByteArray


def Allocation.size (a : Allocation) : Nat := a.bytes.size

def Allocation.start (a : Allocation) : Nat := a.offset.toNat

def Allocation.endExclusive (a : Allocation) : Nat := a.start + a.size

def Allocation.IsDisjoint (a1 a2 : Allocation) : Prop :=
  a1.endExclusive ≤ a2.start ∨ a2.endExclusive ≤ a1.start

structure MemoryState where
  provisioned : Array Allocation

def MemoryState.empty : MemoryState := { provisioned := #[] }

def MemoryState.IsValidNewAlloc (m : MemoryState) (a : Allocation) : Prop :=
  ∀ a' ∈ m.provisioned, Allocation.IsDisjoint a a'

def MemoryState.push (m : MemoryState) (a : Allocation) : MemoryState :=
  { provisioned := m.provisioned.push a }

end Sir
