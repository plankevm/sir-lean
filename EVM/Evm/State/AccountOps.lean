import Evm.State.Account

import Evm.Maps.StorageMap

import Evm.Pretty

namespace Evm

namespace Account

def lookupStorage (self : Account) (k : UInt256) : UInt256 :=
  self.storage.findD k 0

def updateStorage (self : Account) (k v : UInt256) : Account :=
  if v == default then
    { self with storage := self.storage.erase k }
  else
    { self with storage := self.storage.insert k v }

def lookupTransientStorage (self : Account) (k : UInt256) : UInt256 :=
  self.tstorage.findD k 0

def updateTransientStorage (self : Account) (k v : UInt256) : Account :=
  if v == default then
    { self with tstorage := self.tstorage.erase k }
  else
    { self with tstorage := self.tstorage.insert k v }

def emptyAccount (self : Account) : Bool :=
  self.code.isEmpty ∧ self.nonce = 0 ∧ self.balance = 0

end Account

end Evm
