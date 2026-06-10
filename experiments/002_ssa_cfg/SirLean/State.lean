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

def VarCtx.transfer_block_io
  (start_vars : VarCtx)
  (outputs inputs : Array VarId)
  (_in_eq_out : outputs.size = inputs.size) : Option VarCtx :=
  do
    let transfer_var (vars : VarCtx) (out_in : VarId × VarId): Option VarCtx := do
      let (out, inp) := out_in
      let out_val ← start_vars.get? out
      let vars' := vars.set inp out_val
      some vars'
    (outputs.zip inputs).foldlM transfer_var start_vars

inductive Termination where
  | exited (code : Word)

inductive Continuation where
  | terminated (t : Termination)
  | goto (bb : BasicBlockId)

end Sir
