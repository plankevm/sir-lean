import Sir.Core.Proofs.Bump

namespace Sir

theorem bumpAlloc_isValidNewAlloc (memory : MemoryState) (size : Nat)
    (hspace : memory.watermark + size ≤ Evm.UInt256.size) :
    memory.IsValidNewAlloc (memory.bumpAlloc size) :=
  memory.isValidNewAlloc_bumpAlloc size hspace

theorem memoryPolicy_allows_bumpAlloc (memory : MemoryState) (size : Nat)
    (hspace : memory.watermark + size ≤ Evm.UInt256.size) :
    memoryPolicy.Allows memory size (memory.bumpAlloc size) :=
  memory.memoryPolicy_allows_bumpAlloc size hspace

theorem bumpPolicy_allows_bumpAlloc (memory : MemoryState) (size : Nat)
    (hspace : memory.watermark + size ≤ Evm.UInt256.size) :
    bumpPolicy.Allows memory size (memory.bumpAlloc size) :=
  memory.bumpPolicy_allows_bumpAlloc size hspace

theorem bumpPolicy_refines_memoryPolicy : bumpPolicy.Refines memoryPolicy :=
  MemoryPolicy.bump_refines

theorem bumpAlloc_size (memory : MemoryState) (size : Nat) :
    (memory.bumpAlloc size).size = size :=
  memory.bumpAlloc_size size

theorem bumpAlloc_bytes (memory : MemoryState) (size : Nat) :
    (memory.bumpAlloc size).bytes = ByteArray.mk (Array.replicate size 0) :=
  memory.bumpAlloc_bytes size

end Sir
