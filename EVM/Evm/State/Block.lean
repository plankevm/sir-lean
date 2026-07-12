import Mathlib.Data.Finset.Basic

import Evm.State.BlockHeader
import Evm.State.Transaction
import Evm.State.Withdrawal

namespace Evm

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

structure Transactions where
  trieRoot : ByteArray
  array : Array Transaction
deriving BEq, Inhabited, Repr

structure Withdrawals where
  trieRoot : ByteArray
  array : Array Withdrawal
deriving BEq, Inhabited, Repr

structure RawBlock where
  rlp          : ByteArray
  exception    : List String
  /-- Per-transaction `sender` fields from the test fixture, when provided.
      Lets the conform runner skip ECDSA sender recovery. -/
  senders      : Array (Option AccountAddress) := #[]
deriving BEq, Inhabited, Repr

abbrev RawBlocks := Array RawBlock

structure DeserializedBlock where
  hash         : UInt256
  blockHeader  : BlockHeader
  transactions : Transactions
  withdrawals  : Withdrawals
  exception    : List String
  /-- Fixture-provided tx senders, indexed in transaction order (see `RawBlock.senders`). -/
  senders      : Array (Option AccountAddress) := #[]
deriving BEq, Inhabited, Repr

abbrev DeserializedBlocks := Array DeserializedBlock

structure ProcessedBlock where
  hash        : UInt256
  blockHeader : BlockHeader
  accounts    : AccountMap
deriving Inhabited

abbrev ProcessedBlocks := Array ProcessedBlock

def validateUInt256
  (b : ByteArray)
  (e : Exception)
  : Except Exception UInt256
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt256.size then throw e
  pure (.ofNat b)

def validateUInt64
  (b : ByteArray)
  (e : Exception)
  : Except Exception UInt64
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt64.size then throw e
  pure (.ofNat b)

def validateAccountAddress
  (a : ByteArray)
  (e : Exception)
  : Except Exception AccountAddress
:= do
  if a.size ≠ 20 then throw e
  pure (.ofNat (fromByteArrayBigEndian a))

/--
`computeRoots := false` skips the (expensive, evmrs-backed) transaction and
withdrawal trie-root computations; the corresponding `trieRoot` fields are left
`.empty`. Only valid when the caller does not inspect them — the conform runner
checks them only for blocks that expect a block exception.
-/
def deserializeBlock
  (rlp : ByteArray)
  (computeRoots : Bool := true)
  : Except Exception (UInt256 × BlockHeader × Transactions × Withdrawals)
:= do
  let (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws) ←
    Option.toExceptWith (.BlockException .RLP_STRUCTURES_ENCODING) do
      let .inr [headerRLP, transactionsRLP, _, withdrawalsRLP] ← Rlp.decodeOne rlp | none
      let hash : UInt256 := .ofNat <| fromByteArrayBigEndian <| ffi.KEC headerRLP
      let header ← Rlp.decode headerRLP
      let (.inr transactions) ← Rlp.decodeOne transactionsRLP | none
      let getTrieSnd (t : ByteArray) : Option ByteArray := do
        match ← Rlp.decodeOne t with
          | .inl typePlusPayload => typePlusPayload
          | .inr _ => t
      let transactionTrieRoot ←
        if computeRoots then
          Transaction.computeTrieRoot (← transactions.toArray.mapM getTrieSnd)
        else pure .empty
      let ts ← transactions.mapM Rlp.decode
      let (.inr withdrawals) ← Rlp.decodeOne withdrawalsRLP | none
      let withdrawalTrieRoot ←
        if computeRoots then
          Withdrawal.computeTrieRoot withdrawals.toArray
        else pure .empty
      let ws ← withdrawals.mapM Rlp.decode
      pure (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws)
  let header ← parseHeader header
  let transactions ← parseTransactions (.list ts)
  let withdrawals ← parseWithdrawals (.list ws)
  pure (hash, header, ⟨transactionTrieRoot, Array.mk transactions⟩, ⟨withdrawalTrieRoot, Array.mk withdrawals⟩)
 where
  parseWithdrawal : Rlp → Except Exception Withdrawal
    | .list [.bytes globalIndex, .bytes validatorIndex, .bytes recipient, .bytes amount] => do
      pure <|
        .mk
          (← validateUInt64 globalIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateUInt64 validatorIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateAccountAddress recipient (.BlockException .RLP_INVALID_ADDRESS))
          (← validateUInt64 amount (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
    | _ =>
      dbg_trace "RLP error: parseWithdrawal"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseWithdrawals : Rlp → Except Exception (List Withdrawal)
    | .list withdrawals => withdrawals.mapM parseWithdrawal
    | .bytes ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseWithdrawals"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseStorageKey : Rlp → Except Exception UInt256
    | .bytes key => pure <| .ofNat <| fromByteArrayBigEndian key
    | _ =>
      dbg_trace "RLP error: parseStorageKey"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseAccessListEntry : Rlp → Except Exception (AccountAddress × Array UInt256)
    | .list [.bytes accountAddress, .list storageKeys] => do
      let storageKeys ← storageKeys.mapM parseStorageKey
      let accountAddress : AccountAddress := .ofNat <| fromByteArrayBigEndian accountAddress
      pure (accountAddress, Array.mk storageKeys)
    | _ =>
      dbg_trace "RLP error: parseAccessListEntry"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseBlobVersionHash : Rlp → Except Exception ByteArray
    | .bytes hash => pure hash
    | _ =>
      dbg_trace "RLP error: parseBlobVersionHash"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseTransaction : Rlp → Except Exception Transaction
    | .bytes typePlusPayload =>
      match Rlp.decode (typePlusPayload.extract 1 typePlusPayload.size) with
        | some
          (.list
            [ .bytes chainId
            , .bytes nonce
            , .bytes maxPriorityFeePerGas
            , .bytes maxFeePerGas
            , .bytes gasLimit
            , .bytes recipient
            , .bytes value
            , .bytes p
            , .list accessList
            , .bytes maxFeePerBlobGas
            , .list blobVersionedHashes
            , .bytes y
            , .bytes r
            , .bytes s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (← validateUInt64 nonce (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                (← validateUInt64 gasLimit (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas := .ofNat <| fromByteArrayBigEndian maxFeePerGas
            let maxFeePerBlobGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerBlobGas
            let blobVersionedHashes ←
              blobVersionedHashes.mapM parseBlobVersionHash
            let dynamicFeeTransaction : DynamicFeeTransaction :=
              .mk base withAccessList maxFeePerGas maxPriorityFeePerGas
            pure <| .blob <|
              BlobTransaction.mk
                dynamicFeeTransaction
                  maxFeePerBlobGas
                  blobVersionedHashes
        | some
          (.list
            [ .bytes chainId
            , .bytes nonce
            , .bytes maxPriorityFeePerGas
            , .bytes maxFeePerGas
            , .bytes gasLimit
            , .bytes recipient
            , .bytes value
            , .bytes p
            , .list accessList
            , .bytes y
            , .bytes r
            , .bytes s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (← validateUInt64 nonce (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                (← validateUInt64 gasLimit (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerGas
            pure <| .dynamic <|
              DynamicFeeTransaction.mk
                base
                withAccessList
                maxFeePerGas maxPriorityFeePerGas
        | some
          (.list
            [ .bytes chainId
            , .bytes nonce
            , .bytes gasPrice
            , .bytes gasLimit
            , .bytes recipient
            , .bytes value
            , .bytes p
            , .list accessList
            , .bytes y
            , .bytes r
            , .bytes s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (← validateUInt64 nonce (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                (← validateUInt64 gasLimit (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
            pure <| .access <| AccessListTransaction.mk base withAccessList ⟨gasPrice⟩
        | _ =>
          dbg_trace "RLP error: Rlp.decode could not parse non-legacy transaction"
          throw <| .BlockException .RLP_STRUCTURES_ENCODING
    | .list
      [ .bytes nonce
      , .bytes gasPrice
      , .bytes gasLimit
      , .bytes recipient
      , .bytes value
      , .bytes p
      , .bytes w
      , .bytes r
      , .bytes s
      ] => do
        let recipient : Option AccountAddress:=
          if recipient.isEmpty then none
          else some <| .ofNat <| fromByteArrayBigEndian recipient

        let base : Transaction.Base :=
          Transaction.Base.mk
            (← validateUInt64 nonce (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
            (← validateUInt64 gasLimit (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
            recipient
            (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
            r
            s
            p
        let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
        let w := .ofNat <| fromByteArrayBigEndian w
        pure <| .legacy <| LegacyTransaction.mk base ⟨gasPrice⟩ w
    | _ =>
      dbg_trace "RLP error: parseTransaction"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseTransactions : Rlp → Except Exception (List Transaction)
    | .list transactions => transactions.mapM parseTransaction
    | .bytes ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseTransactions"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseHeader : Rlp → Except Exception BlockHeader
    | .list
      [ .bytes parentHash
      , .bytes uncleHash
      , .bytes coinbase
      , .bytes stateRoot
      , .bytes transactionsTrie
      , .bytes receiptTrie
      , .bytes bloom
      , .bytes difficulty
      , .bytes number
      , .bytes gasLimit
      , .bytes gasUsed
      , .bytes timestamp
      , .bytes extraData
      , .bytes mixHash
      , .bytes nonce
      , .bytes baseFeePerGas
      , .bytes withdrawalsRoot
      , .bytes blobGasUsed
      , .bytes excessBlobGas
      , .bytes parentBeaconBlockRoot
      ]
      => pure <|
        BlockHeader.mk
          (.ofNat <| fromByteArrayBigEndian parentHash)
          (.ofNat <| fromByteArrayBigEndian uncleHash)
          (.ofNat <| fromByteArrayBigEndian coinbase)
          (.ofNat <| fromByteArrayBigEndian stateRoot)
          transactionsTrie
          receiptTrie
          bloom
          (fromByteArrayBigEndian difficulty)
          (fromByteArrayBigEndian number)
          (fromByteArrayBigEndian gasLimit)
          (fromByteArrayBigEndian gasUsed)
          (fromByteArrayBigEndian timestamp)
          extraData
          (.ofNat <| fromByteArrayBigEndian nonce)
          (.ofNat <| fromByteArrayBigEndian mixHash)
          (fromByteArrayBigEndian baseFeePerGas)
          parentBeaconBlockRoot
          withdrawalsRoot
          (.ofNat <| fromByteArrayBigEndian blobGasUsed)
          (.ofNat <| fromByteArrayBigEndian excessBlobGas)
    | _ =>
      dbg_trace "Block header has wrong Rlp.encode structure"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

end Evm
