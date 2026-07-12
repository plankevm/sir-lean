import Evm.Maps.StorageMap
import Evm.Crypto.Keccak256

import Evm.UInt256
import Evm.Wheels
import Evm.Operations


namespace Evm

def precompileAddresses : Batteries.RBSet AccountAddress compare :=
  Batteries.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare

inductive ToExecute where
  | Code (code : ByteArray)
  | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState where
  nonce    : UInt64
  balance  : UInt256
  storage  : Storage
  code     : ByteArray
  deriving BEq, Inhabited, Repr

structure Account extends PersistentAccountState where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

def Account.codeHash (self : (Account)) : UInt256 :=
  self.toPersistentAccountState.codeHash

end Evm
