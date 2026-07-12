import Evm.Semantics.Frame
import Evm.Semantics.PrimOps

namespace Evm

open GasConstants
open Operation

def smsfOp (op : SmsfOp) (fr : Frame) (exec : ExecutionState) : Step :=
  match op with
    | .POP => do
      let exec ← charge Gbase exec
      let (stack, _) ← exec.stack.pop
      continueWith <| exec.replaceStackAndIncrPC stack
    | .MLOAD => do
      let (stack, addr) ← exec.stack.pop
      let exec ← chargeMemExpansion exec addr 32
      let exec ← charge Gverylow exec
      let (v, machine') := exec.toMachineState.mload addr
      continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine' } (stack.push v)
    | .MSTORE => do
      let (stack, addr, val) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec addr 32
      let exec ← charge Gverylow exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mstore addr val } stack
    | .MSTORE8 => do
      let (stack, addr, val) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec addr 1
      let exec ← charge Gverylow exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mstore8 addr val } stack
    | .SLOAD =>
      unStateOp Evm.State.sload
        (λ s key ↦ sloadCost (s.substate.accessedStorageKeys.contains (s.executionEnv.address, key))) exec
    | .SSTORE => do
      requireStateMod exec
      if exec.gasAvailable.toNat ≤ Gcallstipend then throw .OutOfGas
      let (stack, key, newValue) ← exec.stack.pop2
      let self := exec.executionEnv.address
      let originalValue := exec.originalAccounts.find? self |>.option 0 (·.storage.findD key 0)
      let currentValue := exec.accounts.find? self |>.option 0 (·.storage.findD key 0)
      let warm := exec.substate.accessedStorageKeys.contains (self, key)
      let exec ← charge (sstoreCost originalValue currentValue newValue warm) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toState := exec.toState.sstore key newValue } stack
    | .TLOAD => unStateOp Evm.State.tload (λ _ _ ↦ tloadCost) exec
    | .TSTORE => do
      requireStateMod exec
      let exec ← charge tstoreCost exec
      let (stack, key, val) ← exec.stack.pop2
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toState := exec.toState.tstore key val } stack
    | .MSIZE => pushOp (λ s ↦ s.toMachineState.msize) exec
    | .GAS => pushOp (λ s ↦ UInt256.ofUInt64 s.gasAvailable) exec
    | .JUMP => do
      let exec ← charge Gmid exec
      let (stack, dest) ← exec.stack.pop
      match fr.get_dest dest with
      | .some new_pc => continueWith { exec with pc := new_pc, stack := stack }
      | .none => .error .BadJumpDestination
    | .JUMPI => do
      let exec ← charge Ghigh exec
      let (stack, dest, cond) ← exec.stack.pop2
      if cond != 0 then
        match fr.get_dest dest with
        | .some new_pc => continueWith { exec with pc := new_pc, stack := stack }
        | .none => .error .BadJumpDestination
      else
        continueWith { exec with pc := exec.pc + 1, stack := stack }
    | .PC => pushOp (λ s ↦ UInt256.ofUInt32 s.pc) exec
    | .JUMPDEST => do
      let exec ← charge Gjumpdest exec
      continueWith exec.incrPC
    | .MCOPY => do
      let (stack, dest, src, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec (max dest src) size
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mcopy dest src size } stack

end Evm
