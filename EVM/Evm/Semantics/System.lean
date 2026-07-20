import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Frame
import Evm.Semantics.Halt
import Evm.Semantics.PrimOps

namespace Evm

open GasConstants
open Operation

def callArm (fr : Frame) (exec : ExecutionState) (stack : Stack UInt256)
    (gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) : Step := do
  let some words' := memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)
    | throw .OutOfGas
  let exec ← charge (Cₘ words' - Cₘ exec.activeWords) exec
  let codeAddress : AccountAddress := AccountAddress.ofUInt256 codeAddress
  let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
  let caller : AccountAddress := AccountAddress.ofUInt256 caller
  let self := exec.executionEnv.address
  let accounts := exec.accounts
  let depth := exec.executionEnv.depth
  let extraCost := callExtraCost codeAddress recipient value accounts exec.substate
  let gasCap := callGasCap codeAddress recipient value gas accounts exec.gasAvailable exec.substate
  let childGas := if value = 0 then gasCap else gasCap + Gcallstipend
  let exec ← charge (gasCap + extraCost) exec
  let inputData := exec.memory.readWithPadding inOffset.toNat inSize.toNat
  let substate' := exec.addAccessedAccount codeAddress |>.substate
  let pending : PendingCall :=
    { frame := { fr with exec := exec }
      stack := stack
      callerAccounts := accounts
      value := value
      inOffset := inOffset.toUInt64
      inSize := inSize.toUInt64
      outOffset := outOffset.toUInt64
      outSize := outSize.toUInt64 }
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 then
    .ok <| .needsCall
      { blobVersionedHashes := exec.executionEnv.blobVersionedHashes
        createdAccounts := exec.createdAccounts
        genesisBlockHeader := exec.genesisBlockHeader
        blocks := exec.blocks
        accounts := accounts
        originalAccounts := exec.originalAccounts
        substate := substate'
        caller := caller
        origin := exec.executionEnv.origin
        recipient := recipient
        codeSource := toExecute accounts codeAddress
        gas := .ofNat childGas
        gasPrice := .ofNat exec.executionEnv.gasPrice
        value := value
        apparentValue := apparentValue
        calldata := inputData
        depth := depth + 1
        blockHeader := exec.executionEnv.blockHeader
        chainId := exec.executionEnv.chainId
        canModifyState := permission }
      pending
  else
    let failed : CallResult :=
      { createdAccounts := exec.createdAccounts
        accounts := accounts
        gasRemaining := .ofNat childGas
        substate := substate'
        success := false
        output := .empty }
    .ok <| .next (resumeAfterCall failed pending).exec

/-- The failure `CreateResult` a CREATE/CREATE2 soft-fail resumes with: the
caller's world/createdAccounts/substate unchanged (no nonce bump), `success :=
false`, and the would-be child gas (`allButOneSixtyFourth`) returned so the
resume restores the parent's full gas. Shared by `createArm`'s two fallback arms
and the recorder's `softFailCreateRecord` rebuild. -/
def createSoftFailResult (exec : ExecutionState) : CreateResult :=
  { address := default
    createdAccounts := exec.createdAccounts
    accounts := exec.accounts
    gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
    substate := exec.toState.substate
    success := false
    output := .empty }

/-- The suspended-parent `PendingCreate` for a CREATE/CREATE2 issued at frame
`fr` with working state `exec` and popped operands `stack`/`value`/`initOffset`/
`initSize`: the caller world snapshot plus the init-code window. Shared by every
`createArm` arm and the recorder's `softFailCreateRecord` rebuild (which passes
`fr` itself, so `{ fr with exec := exec }` collapses by structure eta). -/
def createPendingOf (fr : Frame) (exec : ExecutionState) (stack : Stack UInt256)
    (value initOffset initSize : UInt256) : PendingCreate :=
  { frame := { fr with exec := exec }
    stack := stack
    callerAccounts := exec.accounts
    value := value
    initOffset := initOffset.toUInt64
    initSize := initSize.toUInt64
    initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }

def createArm (fr : Frame) (exec : ExecutionState)
    (stack : Stack UInt256) (value initOffset initSize : UInt256)
    (salt : Option ByteArray) : Step := do
  let initCode := exec.memory.readWithPadding initOffset.toNat initSize.toNat
  let env := exec.executionEnv
  let self := env.address
  let depth := env.depth
  let accounts := exec.accounts
  let selfAccount : Account := accounts.find? self |>.getD default
  let accountsWithBump := accounts.insert self { selfAccount with nonce := selfAccount.nonce + 1 }
  let pending : PendingCreate := createPendingOf fr exec stack value initOffset initSize
  let failed : CreateResult := createSoftFailResult exec
  if selfAccount.nonce.toNat ≥ 2^64-1 then
    return .next (← resumeAfterCreate failed pending).exec
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 ∧ initCode.size ≤ 49152 then
    return .needsCreate
      { blobVersionedHashes := env.blobVersionedHashes
        createdAccounts := exec.createdAccounts
        genesisBlockHeader := exec.genesisBlockHeader
        blocks := exec.blocks
        accounts := accountsWithBump
        originalAccounts := exec.originalAccounts
        substate := exec.toState.substate
        caller := self
        origin := env.origin
        gas := .ofNat <| allButOneSixtyFourth exec.gasAvailable.toNat
        gasPrice := .ofNat env.gasPrice
        value := value
        initCode := initCode
        depth := depth + 1
        salt := salt
        blockHeader := env.blockHeader
        chainId := env.chainId
        canModifyState := env.canModifyState }
      pending
  return .next (← resumeAfterCreate failed pending).exec

def systemOp (op : SystemOp) (fr : Frame) (exec : ExecutionState) : Step :=
  match op with
    | .STOP | .RETURN | .REVERT | .SELFDESTRUCT | .INVALID => haltOp op exec
    | .CALL => do
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← exec.stack.pop7
      if value ≠ 0 ∧ ¬ exec.executionEnv.canModifyState then throw .StaticModeViolation
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) toAddress toAddress value value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .CALLCODE => do
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← exec.stack.pop7
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) (.ofNat exec.executionEnv.address) toAddress value value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .DELEGATECALL => do
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← exec.stack.pop6
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.caller) (.ofNat exec.executionEnv.address) toAddress 0 exec.executionEnv.value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .STATICCALL => do
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← exec.stack.pop6
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) toAddress toAddress 0 0 inOffset inSize outOffset outSize
        false
    | .CREATE => do
      requireStateMod exec
      let (stack, value, initOffset, initSize) ← exec.stack.pop3
      if initSize > 49152 then throw .OutOfGas
      let exec ← chargeMemExpansion exec initOffset initSize
      let exec ← charge (createCost initSize) exec
      createArm fr exec stack value initOffset initSize none
    | .CREATE2 => do
      requireStateMod exec
      let (stack, value, initOffset, initSize, salt) ← exec.stack.pop4
      if initSize > 49152 then throw .OutOfGas
      let exec ← chargeMemExpansion exec initOffset initSize
      let exec ← charge (create2Cost initSize) exec
      createArm fr exec stack value initOffset initSize (some <| Evm.UInt256.toByteArray salt)

end Evm
