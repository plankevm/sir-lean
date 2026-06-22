import Mathlib.Data.Nat.Log

import Evm.State
import Evm.StateOps
import Evm.State.TransactionOps
import Evm.Semantics.GasConstants

namespace Evm

section Gas

open GasConstants

def Cₘ (a : UInt64) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

def sstoreCost (originalValue currentValue newValue : UInt256) (warm : Bool) : ℕ :=
  let loadComponent := if warm then 0 else Gcoldsload
  let storeComponent :=
    if currentValue = newValue || originalValue ≠ currentValue                          then Gwarmaccess else
    if currentValue ≠ newValue && originalValue = currentValue && originalValue = 0 then Gsset else
    Gsreset
  loadComponent + storeComponent

def tstoreCost : ℕ :=
  Gwarmaccess

def accessCost (a : AccountAddress) (substate : Substate) : ℕ :=
  if substate.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

def selfdestructCost (warm createsAccount : Bool) : ℕ :=
  Gselfdestruct + (if warm then 0 else Gcoldaccountaccess) + (if createsAccount then Gnewaccount else 0)

def sloadCost (warm : Bool) : ℕ :=
  if warm then Gwarmaccess else Gcoldsload

def tloadCost : ℕ :=
  Gwarmaccess

def expCost (exponent : UInt256) : ℕ :=
  if exponent == 0 then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 exponent.toNat)

def keccakCost (size : UInt256) : ℕ :=
  Gkeccak256 + Gkeccak256word * ((size.toNat + 31) / 32)

def copyCost (size : UInt256) : ℕ :=
  Gcopy * ((size.toNat + 31) / 32)

def logCost (topicCount : ℕ) (size : UInt256) : ℕ :=
  Glog + Glogdata * size.toNat + topicCount * Glogtopic

def allButOneSixtyFourth (n : ℕ) : ℕ := n - (n / 64)

def newAccountCost (t : AccountAddress) (val : UInt256) (accounts : AccountMap) : ℕ :=
  if Evm.State.dead accounts t && val != 0 then Gnewaccount else 0

def transferCost (val : UInt256) : ℕ :=
  if val != 0 then Gcallvalue else 0

def callExtraCost (t r : AccountAddress) (val : UInt256) (accounts : AccountMap) (substate : Substate) : ℕ :=
  accessCost t substate + transferCost val + newAccountCost r val accounts

def callGasCap (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) :=
  if gasAvailable.toNat >= callExtraCost t r val accounts substate then
    min (allButOneSixtyFourth <| (gasAvailable.toNat - callExtraCost t r val accounts substate)) g.toNat
  else
    g.toNat

def callGas (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) : ℕ :=
  match val with
    | 0 => callGasCap t r val g accounts gasAvailable substate
    | _ => callGasCap t r val g accounts gasAvailable substate + GasConstants.Gcallstipend

def callCost (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) : ℕ :=
  callGasCap t r val g accounts gasAvailable substate + callExtraCost t r val accounts substate

def initCodeCost (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

def createCost (initSize : UInt256) : ℕ :=
  Gcreate + initCodeCost initSize.toNat

def create2Cost (initSize : UInt256) : ℕ :=
  Gcreate + Gkeccak256word * ((initSize.toNat + 31) / 32) + initCodeCost initSize.toNat

def intrinsicGas (T : Transaction) : ℕ :=
  let dataCost :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let createCost : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + initCodeCost (T.base.data.size)
    else 0

  let accessListCost : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  dataCost + createCost + GasConstants.Gtransaction + accessListCost

end Gas

end Evm
