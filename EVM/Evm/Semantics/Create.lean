import Evm.Rlp
import Evm.Machine.ExecutionStateOps
import Evm.Semantics.Gas
import Evm.Semantics.GasConstants
import Evm.Machine.MachineStateOps
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Params
import Evm.Crypto.Keccak256

namespace Evm

/--
The address preimage hashed to derive a created contract's address.

`Rlp.encode` is `Option`-typed only to model the RLP length ceiling, but on the
CREATE inputs — a 20-byte address and a `≤ 32`-byte nonce — it never overflows,
so the encoder is total here (`Rlp.encode_list_pair_isSome`, applied at the call
site via `contractAddressBytes_create`). `getD default` extracts the bytes
without an `Option` fault path; the `default` fallback is provably unreachable.
-/
private def contractAddressBytes (creator : AccountAddress) (creatorNonce : UInt256) (salt : Option ByteArray) (initCode : ByteArray) :
  ByteArray
:=
  let creator := creator.toByteArray
  let creatorNonce := BE creatorNonce.toNat
  match salt with
    | none   => (Rlp.encode <| .list [.bytes creator, .bytes creatorNonce]).getD default
    | some salt => BE 255 ++ creator ++ salt ++ ffi.KEC initCode

/--
The CREATE preimage RLP-encode is always `some`: a 20-byte address and a
`< 2^64`-nonce word are both below 56 bytes, with a 30-byte-or-less payload —
well within the RLP ceiling (`Rlp.encode_list_pair_isSome`). Hence the
`getD default` in `contractAddressBytes` (CREATE arm) never hits its `default`
fallback: the extracted bytes are the real RLP encoding, so making the encoder
total changes no executable behavior. -/
theorem contractAddressBytes_create_isSome (creator : AccountAddress) (creatorNonce : UInt256)
    (hnonce : creatorNonce.toNat < 2 ^ 64) :
    (Rlp.encode <| .list [.bytes creator.toByteArray, .bytes (BE creatorNonce.toNat)]).isSome := by
  apply Rlp.encode_list_pair_isSome
  · -- address is exactly 20 bytes < 56
    rw [AccountAddress.toByteArray_size]; omega
  · -- nonce word fits in 8 bytes < 56 (2^64 = 256^8)
    have : (BE creatorNonce.toNat).size ≤ 8 :=
      BE_size_le (by simpa using hnonce)
    omega
  · -- payload ≤ (1+20) + (1+8) = 30 < 2^64
    rw [AccountAddress.toByteArray_size]
    have hb : (BE creatorNonce.toNat).size ≤ 8 := BE_size_le (by simpa using hnonce)
    omega

/--
Enter a contract creation up to recursive code execution: derive the address,
apply occupied-address checks, initialise the account, and construct the child
environment.

Total: the only former `.error` path was the `contractAddressBytes = none`
address-derivation guard, now removed — `contractAddressBytes` is total
(`contractAddressBytes_create_isSome`: the CREATE preimage always RLP-encodes to
`some`, CREATE2's preimage is unconditional). So `beginCreate` always begins a
child; there is no soft CREATE-begin fault.
-/
def beginCreate (params : CreateParams) : Frame :=
  let accounts := params.accounts
  let creator := params.caller

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let creatorNonce : UInt64 := (accounts.find? creator |>.option 0 (·.nonce)) - 1
  let creatorNonceWord : UInt256 := UInt256.ofUInt64 creatorNonce
  let addressPreimage := contractAddressBytes creator creatorNonceWord params.salt params.initCode
  let newAddress : AccountAddress :=
    (ffi.KEC addressPreimage).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  let substateWithNew := params.substate.addAccessedAccount newAddress
  let existentAccount := accounts.findD newAddress default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (initCode, createdAccounts) :=
    if
      existentAccount.nonce ≠ 0
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, params.createdAccounts)
    else (params.initCode, params.createdAccounts.insert newAddress)

  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + 1
        balance := params.value + existentAccount.balance
    }

  let accountsWithNew :=
    match accounts.find? creator with
      | none => accounts
      | some ac =>
        accounts.insert creator { ac with balance := ac.balance - params.value }
          |>.insert newAddress newAccount
  let env : ExecutionEnv :=
    { address := newAddress
    , origin    := params.origin
    , caller    := creator
    , value  := params.value
    , calldata  := default
    , code      := initCode
    , gasPrice  := params.gasPrice.toNat
    , blockHeader := params.blockHeader
    , depth     := params.depth
    , canModifyState      := params.canModifyState
    , blobVersionedHashes := params.blobVersionedHashes
    , chainId   := params.chainId
    }
  { kind := .create newAddress ⟨createdAccounts, accounts, substateWithNew⟩,
    validJumps := validJumpDests initCode 0,
    exec :=
      { (default : ExecutionState) with
          accounts := accountsWithNew
          originalAccounts := params.originalAccounts
          executionEnv := env
          substate := substateWithNew
          createdAccounts := createdAccounts
          gasAvailable := params.gas
          blocks := params.blocks
          genesisBlockHeader := params.genesisBlockHeader } }

/--
Finish a contract creation after init-code execution: charge code deposit,
check deployment failure conditions, and either store the code or roll back.
-/
def endCreate (address : AccountAddress) (checkpoint : Checkpoint) : FrameHalt → CreateResult
  | .success exec returnedData =>
    let depositCost := GasConstants.Gcodedeposit * returnedData.size

    let deploymentFailed : Bool := Id.run do
      let addressOccupied : Bool :=
        match checkpoint.accounts.find? address with
        | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ 0
        | .none => false
      let cannotAffordDeposit : Bool := exec.gasAvailable.toNat < depositCost
      let MAX_CODE_SIZE := 24576
      let codeTooLong : Bool := returnedData.size > MAX_CODE_SIZE
      let startsWith0xef : Bool := ¬codeTooLong && returnedData[0]? = some 0xef
      pure (addressOccupied ∨ cannotAffordDeposit ∨ codeTooLong ∨ startsWith0xef)

    let accounts' : AccountMap :=
      if deploymentFailed then checkpoint.accounts else
        let newAccount' := exec.accounts.findD address default
        exec.accounts.insert address { newAccount' with code := returnedData }

    { address := address
      createdAccounts := exec.createdAccounts
      accounts := accounts'
      gasRemaining := .ofNat <| if deploymentFailed then 0 else exec.gasAvailable.toNat - depositCost
      substate := if deploymentFailed then checkpoint.substate else exec.substate
      success := !deploymentFailed
      output := .empty }
  | .revert gasRemaining output =>
    { address := address
      createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := gasRemaining
      substate := checkpoint.substate
      success := false
      output := output }
  | .exception _ =>
    { address := address
      createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := 0
      substate := checkpoint.substate
      success := false
      output := .empty }

/--
Resume a frame suspended on CREATE/CREATE2: restore unused gas, set the return
data on failure, push the new contract address (or 0), and advance the pc.
-/
def resumeAfterCreate (result : CreateResult) (pd : PendingCreate) :
    Except ExecutionException Frame := do
  let evmState := pd.frame.exec
  let gas := evmState.gasAvailable
  let gasRemaining := result.gasRemaining
  let success := result.success
  let pushedValue : UInt256 :=
    let balance := pd.callerAccounts.find? evmState.executionEnv.address |>.option 0 (·.balance)
    if success = false ∨ evmState.executionEnv.depth = 1024 ∨ pd.value > balance ∨ pd.initCodeSize > 49152
    then 0 else .ofNat result.address
  let newReturnData : ByteArray := if success then .empty else result.output
  if (gas + gasRemaining).toNat < allButOneSixtyFourth gas.toNat then
    throw .OutOfGas
  let exec' :=
    { evmState with
        accounts := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        activeWords := MachineState.M evmState.activeWords pd.initOffset pd.initSize
        returnData := newReturnData
        gasAvailable := .ofNat <| gas.toNat - allButOneSixtyFourth gas.toNat + gasRemaining.toNat }
  return { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push pushedValue) }

end Evm

-- Axiom guard: the CREATE-preimage totality bridge stays within the standard kernel.
#print axioms Evm.contractAddressBytes_create_isSome
