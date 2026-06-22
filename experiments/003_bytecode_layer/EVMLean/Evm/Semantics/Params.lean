import Evm.Maps.AccountMap
import Evm.State
import Evm.State.Substate
import Evm.UInt256

namespace Evm

structure CallParams where
  blobVersionedHashes : List ByteArray
  createdAccounts     : Batteries.RBSet AccountAddress compare
  genesisBlockHeader  : BlockHeader
  blocks              : ProcessedBlocks
  accounts            : AccountMap
  originalAccounts    : AccountMap
  substate            : Substate
  caller              : AccountAddress
  origin              : AccountAddress
  recipient           : AccountAddress
  codeSource          : ToExecute
  gas                 : UInt64
  gasPrice            : UInt256
  value               : UInt256
  apparentValue       : UInt256
  calldata            : ByteArray
  depth               : ℕ
  blockHeader         : BlockHeader
  chainId             : UInt256
  canModifyState      : Bool

structure CallResult where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accounts        : AccountMap
  gasRemaining    : UInt64
  substate        : Substate
  success         : Bool
  output          : ByteArray

/--
Parameters of contract creation. `accounts` is the map the creation executes
against; for CREATE/CREATE2 the caller's nonce bump is already applied. `salt`
distinguishes CREATE2 from CREATE.
-/
structure CreateParams where
  blobVersionedHashes : List ByteArray
  createdAccounts     : Batteries.RBSet AccountAddress compare
  genesisBlockHeader  : BlockHeader
  blocks              : ProcessedBlocks
  accounts            : AccountMap
  originalAccounts    : AccountMap
  substate            : Substate
  caller              : AccountAddress
  origin              : AccountAddress
  gas                 : UInt64
  gasPrice            : UInt256
  value               : UInt256
  initCode            : ByteArray
  depth               : ℕ
  salt                : Option ByteArray
  blockHeader         : BlockHeader
  chainId             : UInt256
  canModifyState      : Bool

structure CreateResult extends CallResult where
  address : AccountAddress

structure TransactionResult where
  accounts : AccountMap
  substate : Substate
  success  : Bool
  gasUsed  : UInt64

end Evm
