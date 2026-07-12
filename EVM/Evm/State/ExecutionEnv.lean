import Evm.Wheels
import Evm.Operations
import Evm.UInt256
import Evm.State.BlockHeader

namespace Evm

structure ExecutionEnv where
  address   : AccountAddress
  origin    : AccountAddress
  caller    : AccountAddress
  value     : UInt256
  calldata : ByteArray
  code      : ByteArray
  gasPrice  : ℕ
  blockHeader : BlockHeader
  depth     : ℕ
  canModifyState : Bool
  blobVersionedHashes : List ByteArray
  chainId   : UInt256 := 1
  deriving BEq, Inhabited, Repr

def prevRandao (e : ExecutionEnv) : UInt256 :=
  e.blockHeader.prevRandao

def basefee (e : ExecutionEnv) : UInt256 :=
  .ofNat e.blockHeader.baseFeePerGas

def ExecutionEnv.getBlobGasprice (e : ExecutionEnv) : UInt256 :=
  .ofNat e.blockHeader.getBlobGasprice

def blobhash (e : ExecutionEnv) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option 0
    (.ofNat ∘ fromByteArrayBigEndian)

end Evm
