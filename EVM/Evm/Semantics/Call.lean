import Evm.Machine.ExecutionStateOps
import Evm.Machine.MachineStateOps
import Evm.Maps.AccountMap
import Evm.Semantics.Precompiles
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Params

namespace Evm

/--
Enter a message call up to recursive code execution: apply value transfer,
construct the child environment, and dispatch precompiles.

Returns `.inl frame` when EVM code must run (the driver descends into it) or
`.inr result` when the call completes without code execution (precompiles).
-/
def beginCall (params : CallParams) : Frame ⊕ CallResult :=
  let accounts := params.accounts
  let accountsAfterCredit :=
    match accounts.find? params.recipient with
      | none =>
        if params.value != (0 : UInt256) then
          accounts.insert params.recipient { (default : Account) with balance := params.value }
        else
          accounts
      | some acc =>
        accounts.insert params.recipient { acc with balance := acc.balance + params.value }

  let accountsAfterTransfer :=
    match accountsAfterCredit.find? params.caller with
      | none => accountsAfterCredit
      | some acc =>
        accountsAfterCredit.insert params.caller { acc with balance := acc.balance - params.value }

  let env : ExecutionEnv :=
    {
      address := params.recipient
      origin    := params.origin
      gasPrice  := params.gasPrice.toNat
      calldata  := params.calldata
      caller    := params.caller
      value  := params.apparentValue
      depth     := params.depth
      canModifyState      := params.canModifyState
      code      :=
        match params.codeSource with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      blockHeader := params.blockHeader
      blobVersionedHashes := params.blobVersionedHashes
      chainId   := params.chainId
    }

  match params.codeSource with
    | ToExecute.Precompiled p =>
      let (success, accounts'', gasRemaining, substate'', output) :=
        match p with
          | 1  => Precompiles.ecRecover        accountsAfterTransfer params.gas params.substate env
          | 2  => Precompiles.sha256           accountsAfterTransfer params.gas params.substate env
          | 3  => Precompiles.ripemd160        accountsAfterTransfer params.gas params.substate env
          | 4  => Precompiles.identity         accountsAfterTransfer params.gas params.substate env
          | 5  => Precompiles.modExp           accountsAfterTransfer params.gas params.substate env
          | 6  => Precompiles.ecAdd            accountsAfterTransfer params.gas params.substate env
          | 7  => Precompiles.ecMul            accountsAfterTransfer params.gas params.substate env
          | 8  => Precompiles.ecPairing        accountsAfterTransfer params.gas params.substate env
          | 9  => Precompiles.blake2f          accountsAfterTransfer params.gas params.substate env
          | 10 => Precompiles.pointEvaluation  accountsAfterTransfer params.gas params.substate env
          | _  => (false, ∅, 0, params.substate, .empty)
      .inr
        -- NB the precompile path historically clears `createdAccounts`; kept verbatim.
        { createdAccounts := ∅
          accounts := if accounts'' == ∅ then accounts else accounts''
          gasRemaining := gasRemaining
          substate := if accounts'' == ∅ then params.substate else substate''
          success := success
          output := output }
    | ToExecute.Code _ =>
      .inl
        { kind := .call ⟨params.createdAccounts, accounts, params.substate⟩
          validJumps := validJumpDests env.code 0
          exec :=
            { (default : ExecutionState) with
                accounts := accountsAfterTransfer
                originalAccounts := params.originalAccounts
                executionEnv := env
                substate := params.substate
                createdAccounts := params.createdAccounts
                gasAvailable := params.gas
                blocks := params.blocks
                genesisBlockHeader := params.genesisBlockHeader } }

def endCall (checkpoint : Checkpoint) : FrameHalt → CallResult
  | .success exec output =>
    let accounts'' := exec.accounts
    { createdAccounts := exec.createdAccounts
      accounts := if accounts'' == ∅ then checkpoint.accounts else accounts''
      gasRemaining := exec.gasAvailable
      substate := if accounts'' == ∅ then checkpoint.substate else exec.substate
      success := true
      output := output }
  | .revert gasRemaining output =>
    { createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := gasRemaining
      substate := checkpoint.substate
      success := false
      output := output }
  | .exception _ =>
    { createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := 0
      substate := checkpoint.substate
      success := false
      output := .empty }

/--
Resume a frame suspended on a CALL-family instruction: write the call output
to memory, restore the returned gas, push the success flag, and advance the
pc.
-/
def resumeAfterCall (result : CallResult) (pd : PendingCall) : Frame :=
  let evmState := pd.frame.exec
  let output := result.output
  let outputWriteLen : ℕ := min pd.outSize.toNat output.size
  let machineWithOutput := writeBytes output 0 evmState.toMachineState pd.outOffset.toNat outputWriteLen
  let gasAfterReturn := machineWithOutput.gasAvailable + result.gasRemaining
  let codeExecutionFailed   : Bool := !result.success
  let notEnoughFunds        : Bool :=
    pd.value > (pd.callerAccounts.find? evmState.executionEnv.address |>.elim 0 (·.balance))
  let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
  -- Push 0 on failure, insufficient funds, or call-depth limit; otherwise push 1.
  let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then 0 else 1

  let machine' : MachineState :=
    { machineWithOutput with
        returnData   := output
        gasAvailable := gasAfterReturn
        activeWords :=
          let m := MachineState.M evmState.toMachineState.activeWords pd.inOffset pd.inSize
          MachineState.M m pd.outOffset pd.outSize }

  let exec' : ExecutionState :=
    { evmState with
        accounts := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        toMachineState := machine' }
  { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push x) }

end Evm
