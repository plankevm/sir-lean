import Mathlib.Data.List.AList

import Evm.UInt256
import Evm.Rlp
import Evm.Wheels
import Evm.State.TrieRoot
import Conform.Wheels
import Evm.State.Substate

namespace Evm

open Batteries (RBMap RBSet)

structure Transaction.Base where
  nonce           : UInt64
  gasLimit        : UInt64
  recipient       : Option AccountAddress
  value           : UInt256
  r               : ByteArray
  s               : ByteArray
  data            : ByteArray
deriving BEq, Repr

structure Transaction.WithAccessList where
  chainId : UInt256
  accessList : List (AccountAddress × Array UInt256)
  yParity : UInt256
deriving BEq, Repr

structure Transaction.WithGasPrice where
  gasPrice : UInt256
deriving BEq, Repr

structure LegacyTransaction extends Transaction.Base, Transaction.WithGasPrice where
  w: UInt256
deriving BEq, Repr

structure AccessListTransaction
  extends Transaction.Base, Transaction.WithAccessList, Transaction.WithGasPrice
deriving BEq, Repr

structure DynamicFeeTransaction extends Transaction.Base, Transaction.WithAccessList where
  maxFeePerGas         : UInt256
  maxPriorityFeePerGas : UInt256
deriving BEq, Repr

structure BlobTransaction extends DynamicFeeTransaction where
  maxFeePerBlobGas  : UInt256
  blobVersionedHashes : List ByteArray
deriving BEq, Repr

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  | blob    : BlobTransaction → Transaction
deriving BEq, Repr

def Transaction.base : Transaction → Transaction.Base
  | legacy t => t.toBase
  | access t => t.toBase
  | dynamic t => t.toBase
  | blob t => t.toBase

def Transaction.getAccessList : Transaction → List (AccountAddress × Array UInt256)
  | legacy _ => []
  | access t => t.accessList
  | dynamic t => t.accessList
  | blob t => t.accessList

def Transaction.type : Transaction → UInt8
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2
  | .blob _ => 3

def Transaction.toBlobs (t : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← Rlp.encode (.bytes (BE t.1))
  let rlp := t.2
  pure (toHex rlpᵢ, toHex rlp)

def Transaction.computeTrieRoot (ts : Array ByteArray) : Option ByteArray := do
  match Array.mapM Transaction.toBlobs ((Array.range ts.size).zip ts) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

structure TransactionReceipt where
  type                     : UInt8
  statusCode               : Bool
  cumulativeGasUsedInBlock : ℕ
  bloomFilter              : ByteArray
  logSeries                : LogSeries
deriving BEq, Inhabited, Repr

def TransactionReceipt.toRlp : TransactionReceipt → Rlp
  | ⟨_, statusCode, cumulativeGasUsedInBlock, bloomFilter, logSeries⟩ =>
  .list
    [ if statusCode then .bytes (BE 1) else .bytes (BE 0)
    , .bytes (BE cumulativeGasUsedInBlock)
    , .bytes bloomFilter
    , logSeries.toRlp
    ]

def TransactionReceipt.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← Rlp.encode (.bytes (BE w.1))
  let rlp ← w.2
  pure (toHex rlpᵢ, toHex rlp)

def TransactionReceipt.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM TransactionReceipt.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def TransactionReceipt.toTrieValue (r : TransactionReceipt) : ByteArray :=
  let rlp := Option.get! ∘ Rlp.encode ∘ TransactionReceipt.toRlp <| r
  if r.type = 0 then rlp else ⟨#[r.type]⟩ ++ rlp

end Evm
