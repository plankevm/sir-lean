
import Evm.Rlp
import Evm.Wheels
import Evm.PerformIO
import Evm.Maps.AccountMap
import Conform.Wheels
import Evm.Exception

import Evm.State.TrieRoot

open Evm ByteArray

/--
EIP-4895: Beacon chain push withdrawals as operations.
- `index` - starting from `0`
- `validator_index`
- `address` - a recipient for the withdrawn ether
- `amount` - a nonzero amount of ether given in Gwei
-/
structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : AccountAddress
  amount : UInt64
deriving Repr, BEq

namespace Withdrawal

def toRlp : Withdrawal → Rlp
  | {index, validatorIndex, address, amount} =>
    .list
      [ .bytes (BE index.toFin.val)
      , .bytes (BE validatorIndex.toFin.val)
      , .bytes (address.toByteArray)
      , .bytes (BE amount.toFin.val)
      ]

end Withdrawal

def Withdrawal.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← Rlp.encode (.bytes (BE w.1))
  let rlp ← w.2
  pure (toHex rlpᵢ, toHex rlp)

-- EIP-4895
def Withdrawal.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM Withdrawal.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def applyWithdrawals
  (accounts : AccountMap)
  (ws : Array Withdrawal)
    :
  AccountMap
:=
  ws.foldl applyWithdrawal accounts
 where
  applyWithdrawal (accounts : AccountMap) (w : Withdrawal) : AccountMap :=
    if w.amount <= 0 then accounts else
      match accounts.find? w.address with
        | none =>
          accounts.insert w.address {(default : Account) with balance := .ofNat <| w.amount.toFin.val * 10^9}
        | some ac =>
          accounts.insert w.address {ac with balance := .ofNat <| ac.balance.toNat + w.amount.toFin.val * 10^9}
