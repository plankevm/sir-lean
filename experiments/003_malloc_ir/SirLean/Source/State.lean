import SirLean.World
import SirLean.Source.IR

namespace Sir.Source

structure VarCtx where
  vars : VarId → Option Word

def VarCtx.empty : VarCtx := { vars := fun _ => .none }
def VarCtx.get? (vars : VarCtx) (key : VarId) : Option Word := vars.vars key

instance : Membership VarId VarCtx where
  mem vars key := (vars.get? key).isSome = true

def VarCtx.set (vars : VarCtx) (key : VarId) (value : Word) : VarCtx :=
  { vars := fun k =>
      if key = k
      then .some value
      else vars.get? k }

def VarCtx.get (vars : VarCtx) (key : VarId) (is_present : key ∈ vars) : Word :=
  (vars.get? key).get is_present


structure MemoryRange where
  addr: Word
  size: Word

def OccupiedMemory := Array MemoryRange

def Allocator : Type := OccupiedMemory → Word → Option Word

structure Heap where
  bytes: Word → UInt8
  occupied: OccupiedMemory
  allocator : Allocator

def Heap.read (heap : Heap) := heap.bytes
def Heap.set (heap : Heap) (offset : Word) (byte : UInt8) : Heap :=
  { heap with bytes := fun i =>
    if offset = i
    then byte
    else heap.bytes i
  }

def Heap.alloc (size : Word) : StateT Heap Option Word :=
  fun heap => do
    let addr ← heap.allocator heap.occupied size
    let occupied' := heap.occupied.push { addr := addr, size := size }
    return (addr, { heap with occupied := occupied' })


structure Env where
  heap: Heap
  vars : VarCtx
  world : World


def VarCtx.transfer_var (start_vars vars : VarCtx) : VarId × VarId → Option VarCtx
  | (out, inp) => (start_vars.get? out).map fun out_val => vars.set inp out_val

def VarCtx.transfer_block_io (start_vars : VarCtx) (outputs inputs : Array VarId) : Option VarCtx :=
  do
    -- `Array.zip` would silently truncate on a size mismatch
    guard (outputs.size = inputs.size)
    (outputs.zip inputs).foldlM start_vars.transfer_var start_vars

def Env.transfer_block_io (env : Env) (outputs inputs : Array VarId) : Option Env := do
  let vars' ← env.vars.transfer_block_io outputs inputs
  some { env with vars := vars' }



structure ExitCode where
  code: Word

inductive Continuation where
  | exited (code : ExitCode)
  | goto (bb : BasicBlockId)

end Sir.Source
