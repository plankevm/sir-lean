import Evm.State.SubstateOps
import Evm.State.AccountOps

import Evm.Maps.AccountMap

import Evm.State
import Evm.Wheels
import Evm.Semantics.GasConstants

namespace Evm

namespace State

def addAccessedAccount (self : State) (addr : AccountAddress) : State :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey (self : State) (sk : AccountAddress × UInt256) : State :=
  { self with substate := self.substate.addAccessedStorageKey sk }

def dead (accounts : AccountMap) (addr : AccountAddress) : Bool :=
  accounts.find? addr |>.option True Account.emptyAccount

def accountExists (self : State) (addr : AccountAddress) : Bool := self.accounts.find? addr |>.isSome

def lookupAccount (self : State) (addr : AccountAddress) : Option (Account) :=
  self.accounts.find? addr

def updateAccount (addr : AccountAddress) (act : Account) (self : State) : State :=
  { self with accounts := self.accounts.insert addr act }

def setAccount (self : State) (addr : AccountAddress) (acc : Account) : State :=
  { self with accounts := self.accounts.insert addr acc }

def updateAccount! (self : State) (addr : AccountAddress) (f : Account → Account) : State :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def balance (self : State) (k : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accounts.find? addr |>.elim 0 (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State) : State :=
  if self.accountExists addr then self else self.updateAccount addr default

def calldataload (self : State) (currentValue : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.calldata.readBytes currentValue.toNat 32

def setNonce! (self : State) (addr : AccountAddress) (nonce : UInt64) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

section CodeCopy

def extCodeSize (self : State) (a : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option 0 (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State) (currentValue : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 currentValue
  let newState := self.addAccessedAccount addr
  if dead self.accounts addr then (newState, 0) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 currentValue) |>.option 0 Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash (self : State) (blockNumber : UInt256) : UInt256 :=
  let currentValue := self.executionEnv.blockHeader.number
  if currentValue ≤ blockNumber.toNat || blockNumber.toNat + 256 < currentValue then 0
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat 0

def coinBase (self : State) : AccountAddress :=
  self.executionEnv.blockHeader.beneficiary

def timeStamp (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.timestamp

def number (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.number

def difficulty (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.difficulty

def gasLimit (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.gasLimit

def chainId (s : State) : UInt256 := s.executionEnv.chainId

def selfbalance (self : State) : UInt256 :=
  Batteries.RBMap.find? self.accounts self.executionEnv.address |>.elim 0 (·.balance)

end Blocks

section Storage

def setStorage! (self : State) (addr : AccountAddress) (strg : Storage) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def sload (self : State) (spos : UInt256) : State × UInt256 :=
  let selfAddress := self.executionEnv.address
  let currentValue := self.lookupAccount selfAddress |>.option 0 (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (selfAddress, spos)
  (state', currentValue)

def sstore (self : State) (spos sval : UInt256) : State :=
  let selfAddress := self.executionEnv.address
  let { storage := selfStorage, .. } := self.accounts.find! selfAddress
  let originalValue :=
    match self.originalAccounts.find? selfAddress with
      | none => 0
      | some acc => acc.storage.findD spos 0
  let currentValue := selfStorage.findD spos 0
  let newValue := sval

  let r_dirtyclear : ℤ :=
    if originalValue ≠ .ofNat 0 && currentValue = .ofNat 0 then - GasConstants.Rsclear else
    if originalValue ≠ .ofNat 0 && newValue = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if originalValue = newValue && originalValue = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if originalValue = newValue && originalValue ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let refundDelta : ℤ :=
    if currentValue ≠ newValue && originalValue = currentValue && newValue = .ofNat 0 then GasConstants.Rsclear else
    if currentValue ≠ newValue && originalValue ≠ currentValue then r_dirtyclear + r_dirtyreset else
    0

  let refundBalance' : UInt256 :=
    match refundDelta with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - 1
  self.lookupAccount selfAddress |>.option self λ acc ↦
    let self' :=
      self.setAccount selfAddress (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (selfAddress, spos)
    { self' with substate.refundBalance := refundBalance' }

def tload (self : State) (spos : UInt256) : State × UInt256 :=
  let selfAddress := self.executionEnv.address
  let currentValue := self.lookupAccount selfAddress |>.option 0 (Account.lookupTransientStorage (k := spos))
  (self, currentValue)

def tstore (self : State) (spos sval : UInt256) : State :=
  let selfAddress := self.executionEnv.address
  self.lookupAccount selfAddress |>.option self λ acc ↦
    self.updateAccount selfAddress (acc.updateTransientStorage spos sval)

end Storage

end State

end Evm
