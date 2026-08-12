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

theorem stepDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hexclusive : decoder.Exclusive)
    (hterminal : decoder.Terminal) (hnomload : decoder.NoMload)
    {state final : State frame} {trace : Trace}
    (h : Step frame decoder policy ctx state trace final) :
    StepDialogue decoder policy ctx state trace final :=
  Proofs.stepDialogue_all halloc hexclusive hterminal hnomload h

theorem runDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hexclusive : decoder.Exclusive)
    (hterminal : decoder.Terminal) (hnomload : decoder.NoMload)
    {state final : State frame} {trace : Trace}
    (h : Steps frame decoder policy ctx state trace final) :
    RunDialogue decoder policy ctx state trace final :=
  Proofs.runDialogue_all halloc hexclusive hterminal hnomload h

theorem evalDialogue_all {frame : OperandFrame} {decoder : Decoder frame}
    {policy : MemoryPolicy} {ctx : CallContext}
    (halloc : policy.Deterministic ∨ decoder.NoMalloc) (hexclusive : decoder.Exclusive)
    (hterminal : decoder.Terminal) (hnomload : decoder.NoMload)
    {function : FunctionId} {globals globals' : Globals} {args : Array Word}
    {trace : Trace} {outcome : FunctionOutcome}
    (h : FunctionEvaluation frame decoder policy ctx function globals args trace globals' outcome) :
    EvalDialogue decoder policy ctx function globals args trace globals' outcome :=
  Proofs.evalDialogue_all halloc hexclusive hterminal hnomload h

theorem Steps.confluence_or_queryDivergence
    {frame : OperandFrame} {decoder : Decoder frame} {policy : MemoryPolicy}
    {ctx : CallContext} (halloc : policy.Deterministic ∨ decoder.NoMalloc)
    (hexclusive : decoder.Exclusive) (hterminal : decoder.Terminal)
    (hnomload : decoder.NoMload)
    {state final₁ final₂ : State frame} {trace₁ trace₂ : Trace}
    (h₁ : Steps frame decoder policy ctx state trace₁ final₁)
    (h₂ : Steps frame decoder policy ctx state trace₂ final₂) :
    (∃ suffix, Steps frame decoder policy ctx final₁ suffix final₂ ∧
      trace₁ ++ suffix = trace₂) ∨
    (∃ suffix, Steps frame decoder policy ctx final₂ suffix final₁ ∧
      trace₂ ++ suffix = trace₁) ∨
    Trace.QueryDivergence trace₁ trace₂ :=
  Proofs.Steps.confluence_or_queryDivergence halloc hexclusive hterminal hnomload h₁ h₂

end Sir.Machine
