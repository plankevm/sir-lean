import SirLean.Source.IR
import SirLean.Source.State

namespace Sir.Source

def Op.defs : Op → Array VarId
  | .const var _ => #[var]
  | .add32 res _ _ => #[res]
  | .lt res _ _ => #[res]
  | .memwrite _ _ => #[]
  | .memread out _ => #[out]
  | .malloc out _ => #[out]
  | .sload out _ => #[out]
  | .sstore _ _ => #[]

def Op.refs : Op → Array VarId
  | .const _ _ => #[]
  | .add32 _ lhs rhs => #[lhs, rhs]
  | .lt _ lhs rhs => #[lhs, rhs]
  | .memwrite addr value => #[addr, value]
  | .memread _ addr => #[addr]
  | .malloc _ size => #[size]
  | .sload _ addr => #[addr]
  | .sstore addr value => #[addr, value]

def EndOp.refs : EndOp → Array VarId
  | .exit => #[]
  | .jump _ => #[]
  | .jump_if j => #[j.cond]

def BasicBlock.successors (bb : BasicBlock): Array BasicBlockId :=
  match bb.last with
  | .exit => #[]
  | .jump to => #[to]
  | .jump_if j => #[j.dst_if_zero, j.dst_if_non_zero]

def BasicBlock.defs (bb : BasicBlock) : Array VarId := bb.inputs ++ bb.ops.flatMap Op.defs

def BasicBlock.defs_up_to (bb : BasicBlock) (i : Fin bb.ops.size) : Array VarId :=
  bb.inputs ++ (bb.ops.take i).flatMap Op.defs

structure BasicBlock.LocalWF (bb : BasicBlock) : Prop where
  op_refs_valid : ∀ opi : Fin bb.ops.size, ∀ ref ∈ bb.ops[opi].refs, ref ∈ bb.defs_up_to opi
  last_refs_valid : ∀ ref ∈ bb.last.refs, ref ∈ bb.defs
  outputs_valid : ∀ out ∈ bb.outputs, out ∈ bb.defs

structure BasicBlock.WF (bb : BasicBlock) (cfg_blocks : Array BasicBlock) : Prop where
  local_wf : bb.LocalWF
  valid_successors : ∀ succ ∈ bb.successors,
    ∃ h : succ.idx < cfg_blocks.size, bb.outputs.size = cfg_blocks[succ.idx].inputs.size

structure ControlFlowGraph.WF (cfg: ControlFlowGraph) : Prop where
  entry_in_bounds : cfg.entry.idx < cfg.blocks.size
  entry_no_inputs : cfg.blocks[cfg.entry.idx].inputs.isEmpty = true
  blocks_wf : ∀ bb ∈ cfg.blocks, bb.WF cfg.blocks

def MemoryRange.start (r : MemoryRange) : Nat := r.addr.toNat
def MemoryRange.length (r : MemoryRange) : Nat := r.size.toNat
def MemoryRange.endExclusive (r : MemoryRange) : Nat := r.start + r.length

def MemoryRange.WF (r : MemoryRange) : Prop :=
  r.endExclusive ≤ UInt32.size

def MemoryRange.Disjoint (a b : MemoryRange) : Prop :=
     a.endExclusive ≤ b.start ∨ b.endExclusive ≤ a.start

theorem MemoryRange.Disjoint_comm (a b : MemoryRange) : a.Disjoint b ↔ b.Disjoint a := by
  grind [Disjoint]

def OccupiedRanges.Fresh (ranges : OccupiedRanges) (r : MemoryRange) : Prop :=
  let ranges : Array MemoryRange := ranges
  ∀ r' ∈ ranges, MemoryRange.Disjoint r r'

def OccupiedRanges.WF (ranges : OccupiedRanges) : Prop :=
  let ranges : Array MemoryRange := ranges
  ranges.toList.Pairwise MemoryRange.Disjoint

inductive Allocator.Provenance (allocator : Allocator) : OccupiedRanges → Prop where
  | empty : Allocator.Provenance allocator #[]
  | alloc {ranges : OccupiedRanges} {size addr : Word} :
    Allocator.Provenance allocator ranges →
    allocator ranges size = some addr →
    Allocator.Provenance allocator (ranges.push ⟨addr, size⟩)

def Allocator.Sound (allocator : Allocator) : Prop :=
   ∀ ranges size addr,
     allocator.Provenance ranges →
     allocator ranges size = some addr →
     let r' := ⟨addr, size⟩
     ranges.Fresh r' ∧ r'.WF


end Sir.Source
