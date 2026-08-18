import Sir.Machine.Proofs
import Sir.Machine.Proofs.Bump

namespace Sir.Machine

open Sir

theorem bumpAlloc_isValidNewAlloc (memory : MemoryState) (size : Nat)
    (hspace : memory.watermark + size ≤ Evm.UInt256.size) :
    memory.IsValidNewAlloc (memory.bumpAlloc size) :=
  memory.isValidNewAlloc_bumpAlloc size hspace

theorem memoryPolicy_allows_bumpAlloc (memory : MemoryState) (size : Nat)
    (hspace : memory.watermark + size ≤ Evm.UInt256.size) :
    memoryPolicy.Allows memory size (memory.bumpAlloc size) :=
  memory.memoryPolicy_allows_bumpAlloc size hspace

theorem bumpAlloc_size (memory : MemoryState) (size : Nat) :
    (memory.bumpAlloc size).size = size :=
  memory.bumpAlloc_size size

theorem bumpAlloc_bytes (memory : MemoryState) (size : Nat) :
    (memory.bumpAlloc size).bytes = ByteArray.mk (Array.replicate size 0) :=
  memory.bumpAlloc_bytes size

variable {frame : OperandFrame} {decoder : Decoder frame} {policy : MemoryPolicy}
  {ctx : CallContext}

local notation:50 s " =[" t "]=>* " f => Steps frame decoder policy ctx s t f

theorem Steps.confluence_or_queryDivergence
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hnomload : decoder.NoMload)
    {state final₁ final₂ : State frame} {trace₁ trace₂ : Trace}
    (h₁ : state =[trace₁]=>* final₁) (h₂ : state =[trace₂]=>* final₂) :
    Steps.Extends frame decoder policy ctx final₁ trace₁ final₂ trace₂ ∨
      Steps.Extends frame decoder policy ctx final₂ trace₂ final₁ trace₁ ∨
        Trace.QueryDivergence trace₁ trace₂ :=
  Proofs.Steps.confluence_or_queryDivergence halloc hnomload h₁ h₂

end Sir.Machine
