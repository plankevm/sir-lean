import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import Evm.State.ExecutionEnv
import Evm.State.Substate
import Evm.State.Account
import Evm.State.Block
import Evm.State.Substate
import Evm.State.Transaction

import Evm.Maps.AccountMap

import Evm.UInt256
import Evm.Wheels

namespace Evm

/-- Global execution state. -/
structure State where
  accounts            : AccountMap
  originalAccounts    : AccountMap
  totalGasUsedInBlock : ℕ
  transactionReceipts : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Batteries.RBSet AccountAddress compare
deriving Inhabited

def State.blockHashes (self : State) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end Evm
