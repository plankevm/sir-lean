import Evm.Exception
import Evm.Machine.Stack
import Evm.Machine.ExecutionState
import Evm.Machine.ExecutionStateOps
import Evm.Machine.MachineStateOps
import Evm.Semantics.Frame
import Evm.Semantics.Gas
import Evm.Semantics.GasConstants
import Evm.State
import Evm.StateOps

/-!
The building blocks of the instruction dispatcher (`Evm.Semantics.Dispatch`):
gas-charging helpers and the higher-order wrappers shared by the simple
instruction arms. Every wrapper charges its (defaulted) cost itself, with the
already-popped operands in hand.
-/

namespace Evm

open GasConstants

abbrev Step := Except ExecutionException Signal

instance : MonadLift Option (Except ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

@[inline] def continueWith (exec : ExecutionState) : Step := .ok (.next exec)

@[inline] def charge (cost : ℕ) (exec : ExecutionState) :
    Except ExecutionException ExecutionState :=
  if exec.gasAvailable.toNat < cost then .error .OutOfGas
  else .ok { exec with gasAvailable := exec.gasAvailable - .ofNat cost }

@[inline] def memoryExpansionWords? (activeWords : UInt64) (offset size : UInt256) : Option UInt64 := do
  if size == 0 then
    some activeWords
  else
    let offset ← offset.toUInt64?
    let size ← size.toUInt64?
    let maxUInt64 := (0xffffffffffffffff : UInt64)
    if offset > maxUInt64 - size || offset + size > maxUInt64 - 31 then
      none
    else
      some (MachineState.M activeWords offset size)

@[inline] def chargeMemExpansion (exec : ExecutionState) (offset size : UInt256) :
    Except ExecutionException ExecutionState :=
  match memoryExpansionWords? exec.activeWords offset size with
    | none => .error .OutOfGas
    | some words' => charge (Cₘ words' - Cₘ exec.activeWords) exec

@[inline] def requireStateMod (exec : ExecutionState) : Except ExecutionException Unit :=
  if exec.executionEnv.canModifyState then .ok () else .error .StaticModeViolation

def unOp (f : UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a) ← exec.stack.pop
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a))

def binOp (f : UInt256 → UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a, b) ← exec.stack.pop2
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a b))

def ternOp (f : UInt256 → UInt256 → UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a, b, c) ← exec.stack.pop3
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a b c))

def pushOp (v : ExecutionState → UInt256) (exec : ExecutionState) (cost : ℕ := Gbase) : Step := do
  let exec ← charge cost exec
  continueWith <| exec.replaceStackAndIncrPC (exec.stack.push (v exec))

/--
Pop one word, apply a world-state operation returning the new state and the
pushed value; the cost may depend on the popped operand (warm/cold access).
-/
def unStateOp (f : Evm.State → UInt256 → Evm.State × UInt256)
    (cost : ExecutionState → UInt256 → ℕ) (exec : ExecutionState) : Step := do
  let (stack, a) ← exec.stack.pop
  let exec ← charge (cost exec a) exec
  let (state', v) := f exec.toState a
  continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toState := state' } (stack.push v)

def dup (n : ℕ) (exec : ExecutionState) : Step := do
  let exec ← charge Gverylow exec
  let some v := exec.stack[n-1]? | throw .StackUnderflow
  continueWith <| exec.replaceStackAndIncrPC (v :: exec.stack)

def swap (n : ℕ) (exec : ExecutionState) : Step := do
  let exec ← charge Gverylow exec
  let top := exec.stack.take (n + 1)
  let bottom := exec.stack.drop (n + 1)
  if List.length top = (n + 1) then
    continueWith <| exec.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    throw .StackUnderflow

def logArm (exec : ExecutionState) (stack : Stack UInt256) (offset size : UInt256)
    (topics : Array UInt256) : Step := do
  requireStateMod exec
  let exec ← chargeMemExpansion exec offset size
  let exec ← charge (logCost topics.size size) exec
  let exec' := exec.logOp offset size topics
  continueWith <| exec'.replaceStackAndIncrPC stack

end Evm
