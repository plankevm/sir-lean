import SirLean.IR

namespace Sir

structure World where
  data : Word → Word

def World.get (w : World) (key : Word) := w.data key
def World.set (w : World) (key : Word) (value : Word) : World :=
  { data := fun k =>
      if key = k
      then value
      else w.get k }

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

structure Env where
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

inductive Termination where
  | exited (code : Word)

inductive Continuation where
  | terminated (t : Termination)
  | goto (bb : BasicBlockId)

end Sir
