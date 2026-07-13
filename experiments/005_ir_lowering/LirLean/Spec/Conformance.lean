import LirLean.Spec.Recorder

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter

def entryState (params : CallParams) : IRState :=
  { locals := fun _ => none
    world  := fun k => (params.accounts.find? params.recipient).option 0 (·.lookupStorage k) }

def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world
  ∧ O.result = (observe self log.observable).result

def NoGasReads (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ (pc : Nat) (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) → e ≠ .gas

end Lir
