import Evm.Instr
import Evm.Semantics.Frame
import Evm.Semantics.PrimOps

namespace Evm

open GasConstants
open Operation

def returnOrRevertOp (op : SystemOp) (exec : ExecutionState) : Step := do
  let (stack, offset, size) ← exec.stack.pop2
  let exec ← chargeMemExpansion exec offset size
  let output := exec.memory.readWithPadding offset.toNat size.toNat
  let machine :=
    { exec.toMachineState with
        activeWords := MachineState.M exec.activeWords offset.toUInt64 size.toUInt64 }
  let exec := ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine } stack
  if op = .REVERT then
    return .halted (.revert exec.gasAvailable output)
  else
    return .halted (.success exec output)

def selfdestructOp (exec : ExecutionState) : Step := do
  requireStateMod exec
  let (stack, recipientWord) ← exec.stack.pop
  let self := exec.executionEnv.address
  let r : AccountAddress := AccountAddress.ofUInt256 recipientWord
  let warm := exec.substate.accessedAccounts.contains r
  let createsAccount :=
    Evm.State.dead exec.accounts r ∧ (exec.accounts.find? self |>.option 0 (·.balance)) ≠ 0
  let exec ← charge (selfdestructCost warm createsAccount) exec
  let exec' :=
    if exec.createdAccounts.contains self then
      let substate' : Substate :=
        { exec.substate with
            selfDestructSet := exec.substate.selfDestructSet.insert self
            accessedAccounts := exec.substate.accessedAccounts.insert r }
      let accountMap' :=
        match exec.lookupAccount self with
          | none =>
            dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; exec.accounts
          | some selfAccount  =>
            match exec.lookupAccount r with
              | none =>
                if selfAccount.balance == 0 then
                  exec.accounts
                else
                  exec.accounts.insert r
                    {(default : Account) with balance := selfAccount.balance}
                      |>.insert self {selfAccount with balance := 0}
              | some recipientAccount =>
                if r ≠ self then
                  exec.accounts.insert r
                    {recipientAccount with balance := recipientAccount.balance + selfAccount.balance}
                      |>.insert self {selfAccount with balance := 0}
                else
                  exec.accounts.insert r {recipientAccount with balance := 0}
                    |>.insert self {selfAccount with balance := 0}
      { exec with accounts := accountMap', substate := substate' }
    else
      let substate' : Substate :=
        { exec.substate with
            accessedAccounts := exec.substate.accessedAccounts.insert r }
      let accountMap' :=
        match exec.lookupAccount self with
          | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; exec.accounts
          | some selfAccount  =>
            match exec.lookupAccount r with
              | none =>
                if selfAccount.balance == 0 then
                  exec.accounts
                else
                  exec.accounts.insert r
                    {(default : Account) with balance := selfAccount.balance}
                      |>.insert self {selfAccount with balance := 0}
              | some recipientAccount =>
                if r ≠ self then
                  exec.accounts.insert r
                    {recipientAccount with balance := recipientAccount.balance + selfAccount.balance}
                      |>.insert self {selfAccount with balance := 0}
                else
                  exec.accounts
      { exec with accounts := accountMap', substate := substate' }
  return .halted (.success (exec'.replaceStackAndIncrPC stack) .empty)

def haltOp (op : SystemOp) (exec : ExecutionState) : Step :=
  match op with
    | .STOP => .ok <| .halted (.success exec .empty)
    | .RETURN | .REVERT => returnOrRevertOp op exec
    | .SELFDESTRUCT => selfdestructOp exec
    | .INVALID => throw .InvalidInstruction
    | _ => throw .InvalidInstruction

end Evm
