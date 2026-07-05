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

def VarCtx.fromInputs (inputs : Array VarId) (values : List Word) : Option VarCtx := do
  guard (inputs.size = values.length)
  (inputs.toList.zip values).foldlM
    (fun vars (var, value) => some (vars.set var value))
    VarCtx.empty

def VarCtx.resolveOutputs (vars : VarCtx) (outputs : Array VarId) : Option (List Word) :=
  outputs.toList.mapM fun out => vars.get? out

structure MemoryRange where
  addr: Word
  size: Word

def OccupiedRanges := Array MemoryRange

def Allocator : Type := OccupiedRanges → Word → Option Word

structure Heap where
  bytes: Word → UInt8
  occupied: OccupiedRanges
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

structure Runtime where
  heap: Heap
  world : World

inductive Continuation where
  | exited
  | goto (bb : BasicBlockId)

end Sir.Source
