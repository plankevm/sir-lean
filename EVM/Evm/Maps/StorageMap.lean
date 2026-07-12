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
import Mathlib.Data.Multiset.Sort

import Evm.Rlp
import Evm.Wheels
import Evm.State.TrieRoot
import Evm.Crypto.Keccak256

import Evm.FFI.ffi

namespace Evm

section RemoveLater

abbrev Storage : Type := Batteries.RBMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert k v

def Storage.toEvmStorage (self : Storage) : Evm.Storage :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert k v

def toBlobs (pair : UInt256 × UInt256) : Option (String × String) := do
  let kec := ffi.KEC pair.1.toByteArray
  let rlp ← Rlp.encode (.bytes (BE pair.2.toNat))
  pure (toHex kec, toHex rlp)

def computeTrieRoot (storage : Storage) : Option ByteArray :=
  match Array.mapM toBlobs storage.1.toArray with
    | none => .none
    | some pairs => (ByteArray.ofBlob (blobComputeTrieRoot pairs)).toOption

end RemoveLater

end Evm
