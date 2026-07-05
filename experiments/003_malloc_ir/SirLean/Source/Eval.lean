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

def Op.eval? (env₀ : Env) : Op → EvalResult Env
  | .const var value =>
      let vars' := env₀.vars.set var value
      .ok { env₀ with vars := vars' }
  | .add32 out lhs rhs => do
      let lhs ← env₀.vars.get? lhs
      let rhs ← env₀.vars.get? rhs
      let vars' := env₀.vars.set out (lhs + rhs)
      .ok { env₀ with vars := vars' }
  | .lt out lhs rhs => do
      let lhs ← env₀.vars.get? lhs
      let rhs ← env₀.vars.get? rhs
      let vars' := env₀.vars.set out (if lhs < rhs then 1 else 0)
      .ok { env₀ with vars := vars' }
  | .memwrite addr value => do
    let addr ← env₀.vars.get? addr
    let value ← env₀.vars.get? value
    let heap' := env₀.heap.set addr (UInt8.ofNat value.toNat)
    .ok { env₀ with heap := heap' }
  | .memread out addr => do
    let addr ← env₀.vars.get? addr
    let vars' := env₀.vars.set out (env₀.heap.bytes addr |> UInt8.toNat |> UInt32.ofNat)
    .ok { env₀ with vars := vars' }
  | .malloc out size => do
    let size ← env₀.vars.get? size
    let (addr, heap') ← match env₀.heap.alloc size with
      | .some (addr, heap') => .ok (addr, heap')
      | .none => .error .mallocFail
    let vars' := env₀.vars.set out addr
    .ok { env₀ with vars := vars', heap := heap' }
  | .sload out addr => do
      let addr ← env₀.vars.get? addr
      .ok { env₀ with vars := env₀.vars.set out (env₀.world.get addr) }
  | .sstore addr value => do
      let addr ← env₀.vars.get? addr
      let value ← env₀.vars.get? value
      .ok { env₀ with world := env₀.world.set addr value }

def EndOp.eval? : EndOp → Env → Option Continuation
  | .exit codeVar, e => do
      let code ← e.vars.get? codeVar
      .some (.exited ⟨ code ⟩)
  | .jump dst, _ => some (.goto dst)
  | .jump_if j, e =>
    do
      let cond_value ← e.vars.get? j.cond
      let dst :=
        if cond_value = 0
        then j.dst_if_zero
        else j.dst_if_non_zero
      .some (.goto dst)


def BasicBlock.eval? (bb : BasicBlock) : StateT Env EvalResult Continuation :=
  fun env₀ => do
    let env₁ ← bb.ops.foldlM Op.eval? env₀
    let cont ← bb.last.eval? env₁
    return (cont, env₁)

abbrev ControlFlowGraph.BlockIdx (cfg : ControlFlowGraph) : Type := Fin cfg.blocks.size

def ControlFlowGraph.bb_id_to_idx (cfg : ControlFlowGraph) (id : BasicBlockId) : Option cfg.BlockIdx :=
  if valid : id.idx < cfg.blocks.size
  then .some ⟨ id.idx, valid ⟩
  else .none

def ControlFlowGraph.evalWithEnv (cfg : ControlFlowGraph) (bb : cfg.BlockIdx) :
  Nat → StateT Env EvalResult ExitCode
  | 0 => fun _ => .error .outOfFuel
  | fuel + 1 => do
    let bb := cfg.blocks[bb]
    match ← bb.eval? with
    | .exited code => return code
    | .goto dst =>
      let dst ← cfg.bb_id_to_idx dst
      let env ← get
      let vars' ← env.vars.transfer_block_io bb.outputs cfg.blocks[dst].inputs
      modify fun env => { env with vars := vars' }
      cfg.evalWithEnv dst fuel

def ControlFlowGraph.eval
  (allocator : Allocator)
  (cfg : ControlFlowGraph)
  (fuel : Nat) : StateT World EvalResult ExitCode :=
  fun world => do
    let entry ← cfg.bb_id_to_idx cfg.entry
    let heap := { allocator := allocator, bytes := fun _ => 0, occupied := #[] }
    let (code, env') ← cfg.evalWithEnv entry fuel { world := world, vars := .empty, heap := heap }
    return (code, env'.world)

end Sir.Source
