/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import Evm.Rlp
import Evm.Wheels

import Evm.Maps.StorageMap

import Evm.State.Account
import Evm.State.AccountOps

namespace Evm

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Batteries.RBMap AccountAddress α compare
abbrev AccountMap := AddrMap (Account)
abbrev PersistentAccountMap := AddrMap (PersistentAccountState)
def AccountMap.toPersistentAccountMap (a : AccountMap) : PersistentAccountMap :=
  a.mapVal (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance (accounts : AccountMap) (addr : AccountAddress) (amount : UInt256)
  : AccountMap
:=
  match accounts.find? addr with
    | none => accounts.insert addr {(default : Account) with balance := amount}
    | some acc => accounts.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.decreaseBalance (accounts : AccountMap) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap)
:=
  match accounts.find? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (accounts.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.transferBalance (accounts : AccountMap) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap)
:=
  match (accounts.decreaseBalance from_addr amount) with
    | .none => .none
    | .some accounts' => accounts'.increaseBalance to_addr amount

def toExecute (accounts : AccountMap) (t : AccountAddress) : ToExecute :=
  if /- t is a precompiled account -/ t ∈ precompileAddresses then
    ToExecute.Precompiled t
  else Id.run do
    -- We use the code directly without an indirection a'la `codeMap[t]`.
    let .some tDirect := accounts.find? t | ToExecute.Code default
    ToExecute.Code tDirect.code

/--
The secured state trie root. The whole computation (per-account storage
roots, account RLP, state trie) happens in a single `evmrs state-root`
invocation — one process per root, not one per contract account.
-/
def stateTrieRoot (accounts : PersistentAccountMap) : Option ByteArray :=
  let payload :=
    accounts.foldl (init := s!"{accounts.size}\n") λ acc addr account ↦
      let storage := account.storage.1.toArray
      let storageLines :=
        storage.foldl (init := s!"{storage.size}\n") λ acc (slot, value) ↦
          acc
            ++ toHex (ffi.KEC slot.toByteArray) ++ "\n"
            ++ toHex ((Rlp.encode (.bytes (BE value.toNat))).get!) ++ "\n"
      acc
        ++ toHex (ffi.KEC addr.toByteArray) ++ "\n"
        ++ toHex (BE account.nonce.toNat) ++ "\n"
        ++ toHex (BE account.balance.toNat) ++ "\n"
        ++ toHex account.codeHash.toByteArray ++ "\n"
        ++ storageLines
  (ByteArray.ofBlob (blobComputeStateRoot payload)).toOption

end RemoveLater

end Evm
