import Evm.Machine.ExecutionState
import Evm.Semantics
import Evm.Semantics.Gas
import Evm.Rlp
import Evm.Wheels

import Evm.State.TransactionOps
import Evm.State.Withdrawal

import Evm.Maps.AccountMap

import Evm.Pretty
import Evm.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace Evm

namespace Conform

def VerySlowTests : Array String := #[]

def GlobalBlacklist : Array String := VerySlowTests

abbrev TestId : Type := System.FilePath × String

def PersistentAccountMap.toAccountMap (self : PersistentAccountMap) : AccountMap :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage.toEvmStorage
      }
    s.insert addr account

def PersistentAccountMap.toEVMState (self : PersistentAccountMap) : ExecutionState :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage.toEvmStorage
      }
    { s with toState := s.setAccount addr account }

def Pre.toEVMState : Pre → ExecutionState := PersistentAccountMap.toEVMState

def TestMap.toTests (self : TestMap) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → ExecutionState := PersistentAccountMap.toEVMState

def storageComplement (left right : PersistentAccountMap) : PersistentAccountMap := Id.run do
  let mut result : PersistentAccountMap := left
  for ⟨key, rightValue⟩ in right.toList do
    match left.find? key with
    | .none => continue
    | .some leftValue => if leftValue == rightValue then result := result.erase key else continue
  return result

/--
Difference between two persistent account maps, used for reporting mismatches
between expected and actual post state.
-/
def storageDelta (left right : PersistentAccountMap) : PersistentAccountMap × PersistentAccountMap :=
  (storageComplement left right, storageComplement right left)

section

private def statesAlmostBEq (left right : PersistentAccountMap) : Except String Bool := do
  if left == right then .ok true else throw "state mismatch"

private def almostBEqButNotQuite (left right : PersistentAccountMap) : Except String Bool := do
  discard <| statesAlmostBEq left right
  pure true

end

def chainId : UInt256 := 1

def applyTransaction
  (transaction : Transaction)
  (sender : AccountAddress)
  (s : ExecutionState)
  (header : BlockHeader)
  : Except Evm.Exception ExecutionState
:= do
  let { accounts := ypState, substate, success := statusCode, gasUsed := totalGasUsed } ←
    executeTransaction
      chainId
      s.accounts
      header.baseFeePerGas
      header
      s.genesisBlockHeader
      s.blocks
      transaction
      sender

  let result : ExecutionState :=
    { s with
      accounts := ypState
      totalGasUsedInBlock := s.totalGasUsedInBlock + totalGasUsed.toNat
      transactionReceipts :=
        s.transactionReceipts.push
          ⟨ transaction.type
          , statusCode
          , s.totalGasUsedInBlock + totalGasUsed.toNat
          , bloomFilter substate.joinLogs
          , substate.logSeries
          ⟩
      substate
    }
  pure result

/-
  `baseFeePerGas`, `gasLimit` and `excessBlobGas` are used in transaction
  validation, so have to validated before.
-/
def validateHeaderBeforeTransactions
  (blocks : ProcessedBlocks)
  (header : BlockHeader)
  : Except Evm.Exception ProcessedBlock
:= do
  if header.parentHash = 0 then
    throw <| .BlockException .UNKNOWN_PARENT_ZERO

  let (some parent : Option ProcessedBlock) :=
    blocks.findRev? λ b ↦ b.hash = header.parentHash
    | throw <| .BlockException .UNKNOWN_PARENT

  let parentGasLimit := parent.blockHeader.gasLimit

  let elasticity := 2; let gasTarget := parentGasLimit / elasticity; let denominator := 8
  let baseFeeDelta :=
    if parent.blockHeader.gasUsed < gasTarget then
      (parent.blockHeader.baseFeePerGas * (gasTarget - parent.blockHeader.gasUsed)) / gasTarget
    else
      (parent.blockHeader.baseFeePerGas * (parent.blockHeader.gasUsed - gasTarget)) / gasTarget
  let ν :=
    if parent.blockHeader.gasUsed < gasTarget then baseFeeDelta / denominator else max (baseFeeDelta / denominator) 1
  let expectedBaseFeePerGas :=
    if parent.blockHeader.gasUsed = gasTarget then parent.blockHeader.baseFeePerGas else
    if parent.blockHeader.gasUsed < gasTarget then parent.blockHeader.baseFeePerGas - ν else
      parent.blockHeader.baseFeePerGas + ν
  if
    header.gasLimit < 5000
      ∨ header.gasLimit ≥ parentGasLimit + parentGasLimit / 1024
      ∨ header.gasLimit ≤ parentGasLimit - parentGasLimit / 1024
  then
    throw <| .BlockException .INVALID_GASLIMIT
  if header.baseFeePerGas ≠ expectedBaseFeePerGas then
    throw <| .BlockException .INVALID_BASEFEE_PER_GAS
  if calcExcessBlobGas parent.blockHeader != header.excessBlobGas then
    throw <| .BlockException .INCORRECT_EXCESS_BLOB_GAS
  pure parent

def validateTransaction
  (accounts : AccountMap)
  (chainId : ℕ)
  (header : BlockHeader)
  (totalGasUsedInBlock : ℕ)
  (T : Transaction)
  (senderHint : Option AccountAddress := none)
  : Except Evm.Exception AccountAddress
:= do
  let H_f := header.baseFeePerGas
  if T.base.gasLimit.toNat + totalGasUsedInBlock > header.gasLimit then
    throw <| .TransactionException .GAS_ALLOWANCE_EXCEEDED
  if T.base.nonce.toNat ≥ 2^64-1 then
    throw <| .TransactionException .NONCE_IS_MAX

  let maxFeePerGas :=
    /-
      The test `lowGasPriceOldTypes_d0g0v0_Cancun` expects an
      `INSUFFICIENT_MAX_FEE_PER_GAS`, but its transaction doesn't have a
      `maxFeePerGas` field. We use `gasPrice` instead.
    -/
    match T with
      | .dynamic t | .blob t => t.maxFeePerGas
      | .legacy t | .access t => t.gasPrice
  if H_f > maxFeePerGas.toNat then
    throw <| .TransactionException .INSUFFICIENT_MAX_FEE_PER_GAS

  let intrinsic := intrinsicGas T
  if T.base.gasLimit.toNat < intrinsic then
    throw <| .TransactionException .INTRINSIC_GAS_TOO_LOW
  match T with
    | .dynamic t =>
      if t.maxPriorityFeePerGas > t.maxFeePerGas then
        throw <| .TransactionException .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
    | .blob bt => do
      if T.base.recipient = none then
        throw <| .TransactionException .TYPE_3_TX_CONTRACT_CREATION
      if bt.maxFeePerBlobGas.toNat < header.getBlobGasprice then
        .error (.TransactionException .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS)
      if bt.blobVersionedHashes.length > 6 then
        throw <| .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED
      if bt.blobVersionedHashes.length = 0 then
        throw <| .TransactionException .TYPE_3_TX_ZERO_BLOBS
      if bt.blobVersionedHashes.any (λ h ↦ h[0]? != .some VERSIONED_HASH_VERSION_KZG) then
        throw <| .TransactionException .TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
    | _ => pure ()

  match T.base.recipient with
    | none => do
      let MAX_CODE_SIZE := 24576
      let MAX_INITCODE_SIZE := 2 * MAX_CODE_SIZE
      if T.base.data.size > MAX_INITCODE_SIZE then
        throw <| .TransactionException .INITCODE_SIZE_EXCEEDED
    | some _ => pure ()

  let some T_RLP := Rlp.encode (← (txSigningData T)) | throw <| .TransactionException .IllFormedRLP

  let r : ℕ := fromByteArrayBigEndian T.base.r
  let s : ℕ := fromByteArrayBigEndian T.base.s
  if 0 ≥ r ∨ r ≥ secp256k1n then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  if 0 ≥ s ∨ s > secp256k1n / 2 then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  let v : ℕ :=
    match T with
      | .legacy t =>
        let w := t.w.toNat
        if w ∈ [27, 28] then
          w - 27
        else
          if w = 35 + chainId * 2 ∨ w = 36 + chainId * 2 then
            (w - 35) % 2
          else
            w
      | .access t | .dynamic t | .blob t => t.yParity.toNat
  if v ∉ [0, 1] then throw <| .TransactionException .INVALID_SIGNATURE_VRS

  let txHash :=
    match T with
      | .legacy _ => ffi.KEC T_RLP
      | _ => ffi.KEC <| ByteArray.mk #[T.type] ++ T_RLP

  let (sender : AccountAddress) ←
    -- Fixture-provided sender (when present) replaces the evmrs-backed ECDSA
    -- recovery; the v/r/s validity checks above still run either way.
    match senderHint with
      | some sender => pure sender
      | none =>
        match ECDSARECOVER txHash (ByteArray.mk #[.ofNat v]) T.base.r T.base.s with
          | .ok s =>
            pure <| Fin.ofNat _ <| fromByteArrayBigEndian <|
              (ffi.KEC s).extract 12 32 /- 160 bits = 20 bytes -/
          | .error s => throw <| .SenderRecoverError s

  let (senderCode, senderNonce, senderBalance) :=
    match accounts.find? sender with
      | some sender => (sender.code, sender.nonce, sender.balance)
      | none => (.empty, 0, 0)

  if senderCode ≠ .empty then throw <| .TransactionException .SENDER_NOT_EOA
  if T.base.nonce < senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_LOW
  if T.base.nonce > senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_HIGH
  let upfrontCost ← do
    match T with
      | .legacy t | .access t =>
        if t.gasLimit.toNat * t.gasPrice.toNat > 2^256 then
          throw <| .TransactionException .GASLIMIT_PRICE_PRODUCT_OVERFLOW
        pure <| UInt256.ofUInt64 t.gasLimit * t.gasPrice + t.value
      | .dynamic t => pure <|  UInt256.ofUInt64 t.gasLimit * t.maxFeePerGas + t.value
      | .blob t =>
        pure <|
          UInt256.ofUInt64 t.gasLimit * t.maxFeePerGas
          + t.value
          + (UInt256.ofNat (getTotalBlobGas T)) * t.maxFeePerBlobGas
  if upfrontCost > senderBalance then
    throw <| .TransactionException .INSUFFICIENT_ACCOUNT_FUNDS

  pure sender

 where
  txSigningData (T : Transaction) : Except Evm.Exception Rlp :=
    let accessEntryRLP : AccountAddress × Array UInt256 → Rlp
      | ⟨a, s⟩ => .list [.bytes a.toByteArray, .list (s.map (.bytes ∘ UInt256.toByteArray)).toList]
    let accessEntriesRLP (aEs : List (AccountAddress × Array UInt256)) : Rlp :=
      .list (aEs.map accessEntryRLP)
    match T with
      | .legacy t =>
        if t.w.toNat ∈ [27, 28] then
          .ok ∘ .list ∘ List.map .bytes <|
            [ BE t.nonce.toNat
            , BE t.gasPrice.toNat
            , BE t.gasLimit.toNat
            , t.recipient.option .empty AccountAddress.toByteArray
            , BE t.value.toNat
            , t.data
            ]
        else
          if t.w = .ofNat (35 + chainId * 2) ∨ t.w = .ofNat (36 + chainId * 2) then
            .ok ∘ .list ∘ List.map .bytes <|
              [ BE t.nonce.toNat
              , BE t.gasPrice.toNat
              , BE t.gasLimit.toNat
              , t.recipient.option .empty AccountAddress.toByteArray
              , BE t.value.toNat
              , t.data
              , BE chainId
              , .empty
              , .empty
              ]
          else
            dbg_trace "IllFormedRLP legacy transacion: Tw = {t.w}; chainId = {chainId}"
            throw <| .TransactionException .IllFormedRLP

      | .access t =>
        .ok ∘ .list <|
          [ .bytes (BE t.chainId.toNat)
          , .bytes (BE t.nonce.toNat)
          , .bytes (BE t.gasPrice.toNat)
          , .bytes (BE t.gasLimit.toNat)
          , .bytes (t.recipient.option .empty AccountAddress.toByteArray)
          , .bytes (BE t.value.toNat)
          , .bytes t.data
          , accessEntriesRLP t.accessList
          ]
      | .dynamic t =>
        .ok ∘ .list <|
          [ .bytes (BE t.chainId.toNat)
          , .bytes (BE t.nonce.toNat)
          , .bytes (BE t.maxPriorityFeePerGas.toNat)
          , .bytes (BE t.maxFeePerGas.toNat)
          , .bytes (BE t.gasLimit.toNat)
          , .bytes (t.recipient.option .empty AccountAddress.toByteArray)
          , .bytes (BE t.value.toNat)
          , .bytes t.data
          , accessEntriesRLP t.accessList
          ]
      | .blob t =>
        .ok ∘ .list <|
          [ .bytes (BE t.chainId.toNat)
          , .bytes (BE t.nonce.toNat)
          , .bytes (BE t.maxPriorityFeePerGas.toNat)
          , .bytes (BE t.maxFeePerGas.toNat)
          , .bytes (BE t.gasLimit.toNat)
          , .bytes (t.recipient.option .empty AccountAddress.toByteArray)
          , .bytes (BE t.value.toNat)
          , .bytes t.data
          , accessEntriesRLP t.accessList
          , .bytes (BE t.maxFeePerBlobGas.toNat)
          , .list (t.blobVersionedHashes.map .bytes)
          ]

def validateBlock
  (state : ExecutionState)
  (parentHeader : BlockHeader)
  (block : DeserializedBlock)
  : Except Evm.Exception Unit
:= do

  let MAX_BLOB_GAS_PER_BLOCK := 786432
  let blobGasUsed ← block.transactions.array.foldlM (init := 0) λ blobSum t ↦ do
    let blobSum := blobSum + getTotalBlobGas t
    if blobSum > MAX_BLOB_GAS_PER_BLOCK then
      throw <| .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
    pure blobSum

  if state.totalGasUsedInBlock ≠ block.blockHeader.gasUsed then
    throw <| .BlockException .INVALID_GAS_USED
  if block.blockHeader.timestamp ≤ parentHeader.timestamp then
    throw <| .BlockException .INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
  if block.blockHeader.number ≠ parentHeader.number + 1 then
    throw <| .BlockException .INVALID_BLOCK_NUMBER
  if block.blockHeader.extraData.size > 32 then
    throw <| .BlockException .EXTRA_DATA_TOO_BIG
  if block.blockHeader.gasLimit > 0x7fffffffffffffff then
    throw <| .BlockException .GASLIMIT_TOO_BIG
  if block.blockHeader.difficulty != 0 then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
  -- KEC (RLP []) = 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
  if
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
      != block.blockHeader.ommersHash.toNat
  then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS

  if blobGasUsed != block.blockHeader.blobGasUsed.toNat then
      throw <| .BlockException .INCORRECT_BLOB_GAS_USED

  if blobGasUsed > MAX_BLOB_GAS_PER_BLOCK then
    throw <| .BlockException .BLOB_GAS_USED_ABOVE_LIMIT
  -- Full root checks are expensive, so only run them when an expected block
  -- exception needs the specific exception as an oracle.
  let runExpensiveRootChecks := ¬block.exception.isEmpty

  if runExpensiveRootChecks then
    if block.withdrawals.trieRoot ≠ block.blockHeader.withdrawalsRoot then
      throw <| .BlockException .INVALID_WITHDRAWALS_ROOT

    let computedStateHash : UInt256 :=
      stateTrieRoot state.accounts.toPersistentAccountMap
      |>.option 0 fromByteArrayBigEndian
      |> .ofNat
    if block.blockHeader.stateRoot ≠ computedStateHash then
      throw <| .BlockException .INVALID_STATE_ROOT

  let expectedBloom := block.blockHeader.logsBloom
  let actualBloom := bloomFilter state.substate.joinLogs
  if expectedBloom ≠ actualBloom then
    throw <| .BlockException .INVALID_LOG_BLOOM

  if runExpensiveRootChecks then
    if block.transactions.trieRoot ≠ block.blockHeader.transRoot then
      throw <| .BlockException .INVALID_TRANSACTIONS_ROOT

    let receiptsRoot :=
      TransactionReceipt.computeTrieRoot <|
        state.transactionReceipts.map TransactionReceipt.toTrieValue
    if receiptsRoot ≠ some block.blockHeader.receiptRoot then
      throw <| .BlockException .INVALID_RECEIPTS_ROOT

  pure ()

def deserializeRawBlock (rawBlock : RawBlock)
  : Except Evm.Exception DeserializedBlock
:= do
  let (blockHash, blockHeader, transactions, withdrawals) ←
    deserializeBlock rawBlock.rlp (computeRoots := ¬rawBlock.exception.isEmpty)
  pure <| .mk blockHash blockHeader transactions withdrawals rawBlock.exception rawBlock.senders

def processBlocks
  (pre : Pre)
  (blocks : RawBlocks)
  (genesisRLP : ByteArray)
  : Except Evm.Exception ExecutionState
:= do
  let (genesisHash, genesisBlockHeader, _) ← deserializeBlock genesisRLP (computeRoots := false)
  let state0 :=
    { pre.toEVMState with
        genesisBlockHeader := genesisBlockHeader
        blocks :=
          #[
            ⟨ genesisHash
            , genesisBlockHeader
            , PersistentAccountMap.toAccountMap pre
            ⟩
          ]
    }
  let state ←
    blocks.foldlM (init := state0)
      λ accState rawBlock ↦ do
        try
          let block ← deserializeRawBlock rawBlock
          let parent ←
            validateHeaderBeforeTransactions accState.blocks block.blockHeader
          let accState ← processBlock {accState with accounts := parent.accounts} block
          validateBlock accState parent.blockHeader block
          if ¬block.exception.isEmpty then
            throw <| .MissedExpectedException block.exception
          pure
            { accState with
                blocks :=
                  accState.blocks.push
                    ⟨block.hash, block.blockHeader, accState.accounts⟩
            }
        catch e =>
          match e with
            | .MissedExpectedException _  => throw e
            | _ =>
              if rawBlock.exception.contains (repr e).pretty then
                pure accState
              else
                throw e
  pure state
 where
  processBlock
    (initialState : ExecutionState)
    (block : DeserializedBlock)
    : Except Evm.Exception ExecutionState
  := do
    let s ← do
      let BEACON_ROOTS_ADDRESS : AccountAddress :=
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
      let SYSTEM_ADDRESS : AccountAddress :=
        0xfffffffffffffffffffffffffffffffffffffffe
      match initialState.accounts.find? BEACON_ROOTS_ADDRESS with
        | none => pure initialState
        | some roots =>
          let beaconRootsAddressCode := roots.code
          let beaconCallResult :=
            messageCall
              { blobVersionedHashes := []
                createdAccounts := .empty
                genesisBlockHeader := initialState.genesisBlockHeader
                blocks := initialState.blocks
                accounts := initialState.accounts
                originalAccounts := initialState.accounts
                substate := default
                caller := SYSTEM_ADDRESS
                origin := SYSTEM_ADDRESS
                recipient := BEACON_ROOTS_ADDRESS
                codeSource := .Code beaconRootsAddressCode
                gas := 30000000
                gasPrice := 0xe8d4a51000
                value := 0
                apparentValue := 0
                calldata := block.blockHeader.parentBeaconBlockRoot
                depth := 0
                blockHeader := block.blockHeader
                chainId := chainId
                canModifyState := true }
          let accounts ←
            match beaconCallResult with
              | .ok r => pure r.accounts
              | .error e => throw <| .ExecutionException e
          let s := {initialState with accounts := accounts}
          pure s
    let s ←
      block.transactions.array.zipIdx.foldlM
        (λ s' (tx, i) ↦ do
          let sender ←
            validateTransaction
              s'.accounts
              chainId.toNat
              block.blockHeader
              s'.totalGasUsedInBlock
              tx
              (senderHint := (block.senders.getD i none))
          applyTransaction tx sender s' block.blockHeader
        )
        {s with totalGasUsedInBlock := 0, transactionReceipts := .empty}

    let accounts := applyWithdrawals s.accounts block.withdrawals.array

    pure { s with accounts := accounts }

def preImpliesPost (entry : TestEntry)
  : Except Evm.Exception (Option (PersistentAccountMap))
:= do
    let resultState ← processBlocks entry.pre entry.blocks entry.genesisRLP
    let lastAccountMap :=
      resultState.blocks.findRev? (·.hash == entry.lastblockhash)
      |>.option resultState.accounts ProcessedBlock.accounts
    let result : PersistentAccountMap :=
      lastAccountMap.foldl
        (λ r addr ⟨⟨nonce, balance, storage, code⟩, _, _⟩ ↦ r.insert addr ⟨nonce, balance, storage, code⟩) default
    let persistentAccountMap := resultState.accounts.toPersistentAccountMap
    match entry.postState with
      | .Map post =>
        match almostBEqButNotQuite post result with
          | .error e =>
            dbg_trace e
            pure (.some persistentAccountMap)
          | .ok _ => pure .none
      | .Hash h =>
        if stateTrieRoot persistentAccountMap ≠ h then
          dbg_trace "state hash mismatch"
          pure (.some persistentAccountMap)
        else
          pure .none

instance (priority := high) : Repr (PersistentAccountMap) := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(toHex k.toByteArray) /-|>.takeRight 5-/}]\n"
      result := result ++ s!"balance: {v.balance}\nnonce: {v.nonce}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩
 
def processTest (entry : TestEntry) (isTimed : Option (Nat × TestId) := .none) (verbose := true) : IO TestResult := do
  let tα ← if isTimed.isSome then IO.monoMsNow else pure 0
  let result := preImpliesPost entry
  let tω ← if isTimed.isSome then IO.monoMsNow else pure 0
  if let .some (thread, filepath, testname) := isTimed then
    IO.eprint s!"#{if thread / 10 == 1 then "" else " "}{thread} "
    IO.eprint s!"{testname} FROM {System.FilePath.mk (filepath.components.drop 3 |>.intersperse "/" |>.foldl (·++·) "")} "
    IO.eprintln s!"took: {(tω - tα).toFloat / 1000.0}s"
  pure <|
    match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => errorF <$> result
  where discardError : PersistentAccountMap → String := λ _ ↦ "ERROR."
        verboseError : PersistentAccountMap → String := λ accounts ↦
          match entry.postState with
            | .Map post =>
              let (postSubActual, actualSubPost) := storageDelta post accounts
              s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
            | .Hash h =>
              s!"\npost: {toHex h} \nactual: {toHex <$> stateTrieRoot accounts}"
        errorF := if verbose then verboseError else discardError

/--
Run one already-parsed test from a fixture file. Used by the per-test task
pool — the file is parsed once and shared by all its test tasks.
-/
def processSingleTest (path : System.FilePath) (file : Lean.Json) (testName : String)
    : IO (Array TestId × Array (TestId × TestResult × Nat)) := do
  let testId : TestId := (path, testName)
  let test := Except.mapError Conform.Exception.CannotParse <| file.getObjValAs? TestEntry testName
  match test with
  | .error _ =>
    IO.eprintln s!"Cannot parse: {testId}"
    return (#[testId], #[])
  | .ok test =>
    if test.network.startsWith "Cancun" then
      let t0 ← IO.monoMsNow
      let res ← processTest test
      let t1 ← IO.monoMsNow
      return (#[], #[(testId, res, t1 - t0)])
    else
      return (#[], #[])

end Conform

end Evm
