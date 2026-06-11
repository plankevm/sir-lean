import Init.Data.UInt
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain

namespace Sir

abbrev Word := UInt32

structure BasicBlockId where
  idx : Nat
deriving DecidableEq, Repr

def BasicBlockId.ofNat (n : Nat) : BasicBlockId := ⟨n⟩
def BasicBlockId.toNat (v : BasicBlockId) : Nat := v.idx

structure VarId where
  id : Nat
deriving DecidableEq, Repr

def VarId.ofNat (n : Nat) : VarId := ⟨n⟩
def VarId.toNat (v : VarId) : Nat := v.id

inductive Op where
  | const (var : VarId) (value: Word)
  | add32 (res lhs rhs : VarId)
  | lessThan (res lhs rhs : VarId)
  | persistentLoad (out addr : VarId)
  | persistentStore (addr value : VarId)


def Op.defs : Op → Array VarId
  | .const var _ => #[var]
  | .add32 res _ _ => #[res]
  | .lessThan res _ _ => #[res]
  | .persistentLoad out _ => #[out]
  | .persistentStore _ _ => #[]

def Op.refs : Op → List VarId
  | .const _ _ => []
  | .add32 _ lhs rhs => [lhs, rhs]
  | .lessThan _ lhs rhs => [lhs, rhs]
  | .persistentLoad _ addr => [addr]
  | .persistentStore addr value => [addr, value]



structure JumpIf where
  cond : VarId
  dst_if_zero : BasicBlockId
  dst_if_non_zero : BasicBlockId

inductive EndOp where
  | exit (exit_code_var : VarId)
  | jump (dst : BasicBlockId)
  | jump_if (j : JumpIf)

def EndOp.var_refs : EndOp → Array VarId
  | .exit exit_code_var => #[exit_code_var]
  | .jump _ => #[]
  | .jump_if j => #[j.cond]

def EndOp.successors : EndOp → Array BasicBlockId
  | .exit _ => #[]
  | .jump bb => #[bb]
  | .jump_if j => #[j.dst_if_zero, j.dst_if_non_zero]


def EndOp.outputs_match  (outputs : Array VarId) : (op : EndOp) →  Prop
  | .exit _ => outputs.isEmpty = true
  | .jump _ => True
  | .jump_if _ => True

instance : Decidable (EndOp.outputs_match outputs op) := by
  unfold EndOp.outputs_match
  cases op <;> infer_instance

structure BasicBlock where
  inputs : Array VarId
  ops : Array Op
  last : EndOp
  outputs : Array VarId
  outputs_valid_for_last : EndOp.outputs_match outputs last := by decide

def BasicBlock.defs_up_to (bb : BasicBlock) (i : Fin bb.ops.size) : Array VarId := bb.inputs ++ (bb.ops.take i).flatMap Op.defs
def BasicBlock.defs (bb : BasicBlock) : Array VarId := bb.inputs ++ bb.ops.flatMap Op.defs
def BasicBlock.successors (bb : BasicBlock) : Array BasicBlockId := bb.last.successors

def BasicBlock.valid_in_cfg (bb : BasicBlock) (blocks : Array BasicBlock) : Prop :=
  ∀ succ ∈ bb.successors,
    ∃ succ_valid : succ.idx < blocks.size, bb.outputs.size = blocks[succ.idx].inputs.size

structure InnerCFG where
  blocks: Array BasicBlock
  entry : Fin blocks.size
  blocks_valid : ∀ block ∈ blocks, block.valid_in_cfg blocks


def InnerCFG.PathWhereUndef (cfg : InnerCFG) (var : VarId) :=
  Relation.ReflTransGen (fun (pred succ : Fin cfg.blocks.size) =>
    ⟨ succ ⟩ ∈ cfg.blocks[pred].successors ∧ var ∉ cfg.blocks[pred].defs)

def InnerCFG.DefinedOnAllPaths (cfg : InnerCFG) (var : VarId)
    (bb : Fin cfg.blocks.size) : Prop :=
  ¬ cfg.PathWhereUndef var cfg.entry bb

theorem InnerCFG.undef_at_entry :
    ∀ cfg : InnerCFG, ∀ var : VarId, InnerCFG.PathWhereUndef cfg var cfg.entry cfg.entry := by
    simp [InnerCFG.PathWhereUndef]
    grind

def InnerCFG.op_refs_valid (cfg : InnerCFG) : Prop :=
  ∀ bi : Fin cfg.blocks.size,
  ∀ opi : Fin cfg.blocks[bi].ops.size,
  ∀ ref ∈ cfg.blocks[bi].ops[opi].refs,
  ref ∈ cfg.blocks[bi].defs_up_to opi ∨ cfg.DefinedOnAllPaths ref bi

def InnerCFG.end_op_refs_valid (cfg : InnerCFG) : Prop :=
  ∀ bi : Fin cfg.blocks.size,
  ∀ ref ∈ cfg.blocks[bi].last.var_refs,
  ref ∈ cfg.blocks[bi].defs ∨ cfg.DefinedOnAllPaths ref bi

def InnerCFG.block_output_refs_valid (cfg : InnerCFG) : Prop :=
  ∀ bi : Fin cfg.blocks.size,
  ∀ ref ∈ cfg.blocks[bi].outputs,
  ref ∈ cfg.blocks[bi].defs ∨ cfg.DefinedOnAllPaths ref bi

def InnerCFG.refs_valid (cfg : InnerCFG) : Prop :=
  cfg.op_refs_valid ∧ cfg.end_op_refs_valid ∧ cfg.block_output_refs_valid

structure ControlFlowGraph where
  blocks: Array BasicBlock
  entry : Fin blocks.size
  entry_no_inputs : blocks[entry].inputs.isEmpty = true
  blocks_valid : ∀ block ∈ blocks, block.valid_in_cfg blocks
  refs_valid : InnerCFG.refs_valid ⟨ blocks, entry, blocks_valid ⟩

def ControlFlowGraph.inner (cfg : ControlFlowGraph) : InnerCFG :=
  ⟨cfg.blocks, cfg.entry, cfg.blocks_valid⟩

def ControlFlowGraph.is_ssa (cfg : ControlFlowGraph) : Prop := (cfg.blocks.flatMap BasicBlock.defs).toList.Nodup

def ControlFlowGraph.succ_to_idx
  (cfg : ControlFlowGraph)
  { bb : Fin cfg.blocks.size }
  { s : BasicBlockId }
  (hs : s ∈ cfg.blocks[bb].successors) : Fin cfg.blocks.size :=
  ⟨ s.idx, by {
    have := cfg.blocks_valid cfg.blocks[bb] (by simp) s
    grind
  }⟩

theorem ControlFlowGraph.succ_io_size_eq
  (cfg : ControlFlowGraph)
  (bb : Fin cfg.blocks.size)
  (hsucc : succ ∈ cfg.blocks[bb].successors)
  : cfg.blocks[bb].outputs.size = (cfg.blocks[cfg.succ_to_idx hsucc]).inputs.size := by
  have succ_size_eq := cfg.blocks_valid cfg.blocks[bb] (by simp) succ hsucc
  grind [ControlFlowGraph.succ_to_idx]


end Sir
