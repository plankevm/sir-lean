import Lean.Data.RBMap
import Lean.Data.Json

-- import Evm.Maps
import Evm.Operations
import Evm.Rlp
import Evm.Wheels
import Evm.State.Withdrawal
import Evm.State.Block

import Evm.Machine.ExecutionState

import Conform.Wheels

namespace Evm

namespace Conform

section Model

open Lean

abbrev Code := ByteArray

abbrev Pre := PersistentAccountMap

abbrev PostEntry := PersistentAccountState

abbrev Post := PersistentAccountMap

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

private local instance : Repr Json := ⟨λ s _ ↦ Json.pretty s⟩

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `ExecutionState`.
-/

inductive PostState where
  | Hash : ByteArray → PostState
  | Map : Post → PostState
  deriving Inhabited

structure TestEntry where
  info               : Json := ""
  blocks             : RawBlocks
  genesisRLP         : ByteArray
  lastblockhash      : UInt256
  network            : String
  postState          : PostState
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev TestMap := Batteries.RBMap String TestEntry compare

abbrev AccessListEntry := AccountAddress × Array UInt256

abbrev AccessList := Array AccessListEntry

def TestResult := Option String
  deriving Repr, Inhabited

namespace TestResult

def isSuccess (self : TestResult) : Bool := self matches none

def mkFailed (reason : String := "") : TestResult := .some reason

def mkSuccess : TestResult := .none

end TestResult

end Model
