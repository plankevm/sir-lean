import SirLean.Source.IR
import SirLean.Source.State

namespace Sir.Source

inductive CFGEvalError where
  | outOfFuel
  | mallocFail
  | stuck
deriving DecidableEq, Repr

abbrev EvalResult := Except CFGEvalError

/-- `none` from a partial operation means evaluation got stuck. -/
instance : MonadLift Option (EvalResult) where
  monadLift
    | some x => .ok x
    | none => .error .stuck

def Op.eval? (vars₀ : VarCtx) : Op → StateT Runtime EvalResult VarCtx
  | .const var value =>
      return vars₀.set var value
  | .add32 out lhs rhs => do
      let lhs ← vars₀.get? lhs
      let rhs ← vars₀.get? rhs
      return vars₀.set out (lhs + rhs)
  | .lt out lhs rhs => do
      let lhs ← vars₀.get? lhs
      let rhs ← vars₀.get? rhs
      return vars₀.set out (if lhs < rhs then 1 else 0)
  | .memwrite addr value => do
      let addr ← vars₀.get? addr
      let value ← vars₀.get? value
      modify fun rt => { rt with heap := rt.heap.set addr (UInt8.ofNat value.toNat) }
      return vars₀
  | .memread out addr => do
      let addr ← vars₀.get? addr
      let rt ← get
      return vars₀.set out (rt.heap.read addr |> UInt8.toNat |> UInt32.ofNat)
  | .malloc out size => do
      let size ← vars₀.get? size
      let rt ← get
      match rt.heap.alloc size with
      | .some (addr, heap') =>
          set { rt with heap := heap' }
          return vars₀.set out addr
      | .none => throw .mallocFail
  | .sload out addr => do
      let addr ← vars₀.get? addr
      let rt ← get
      return vars₀.set out (rt.world.get addr)
  | .sstore addr value => do
      let addr ← vars₀.get? addr
      let value ← vars₀.get? value
      modify fun rt => { rt with world := rt.world.set addr value }
      return vars₀

def EndOp.eval? : EndOp → VarCtx → Option Continuation
  | .exit, _ => some .exited
  | .jump dst, _ => some (.goto dst)
  | .jump_if j, vars => do
      let cond ← vars.get? j.cond
      let dst :=
        if cond = 0
        then j.dst_if_zero
        else j.dst_if_non_zero
      some (.goto dst)

def BasicBlock.eval? (bb : BasicBlock) (inputs : List Word) :
    StateT Runtime EvalResult (Continuation × List Word) := do
  let vars₀ ← VarCtx.fromInputs bb.inputs inputs
  let vars₁ ← bb.ops.foldlM Op.eval? vars₀
  let cont ← bb.last.eval? vars₁
  let outputs ← vars₁.resolveOutputs bb.outputs
  return (cont, outputs)

abbrev ControlFlowGraph.BlockIdx (cfg : ControlFlowGraph) : Type := Fin cfg.blocks.size

def ControlFlowGraph.bb_id_to_idx (cfg : ControlFlowGraph) (id : BasicBlockId) : Option cfg.BlockIdx :=
  if valid : id.idx < cfg.blocks.size
  then .some ⟨ id.idx, valid ⟩
  else .none

def ControlFlowGraph.evalFrom (cfg : ControlFlowGraph) (bb : cfg.BlockIdx) (inputs : List Word) :
  Nat → StateT Runtime EvalResult (List Word)
  | 0 => fun _ => .error .outOfFuel
  | fuel + 1 => do
    let bb := cfg.blocks[bb]
    let (cont, outputs) ← bb.eval? inputs
    match cont with
    | .exited => return outputs
    | .goto dst =>
      let dst ← cfg.bb_id_to_idx dst
      cfg.evalFrom dst outputs fuel

def ControlFlowGraph.eval
  (allocator : Allocator)
  (cfg : ControlFlowGraph)
  (fuel : Nat) : StateT World EvalResult (List Word) :=
  fun world => do
    let entry ← cfg.bb_id_to_idx cfg.entry
    let zeroed := fun _ => 0
    let heap := { allocator := allocator, bytes := zeroed, occupied := #[] }
    let (result, runtime') ← cfg.evalFrom entry [] fuel { world := world, heap := heap }
    return (result, runtime'.world)

end Sir.Source
