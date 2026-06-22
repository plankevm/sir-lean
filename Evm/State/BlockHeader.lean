import Evm.UInt256
import Evm.Wheels

namespace Evm

structure BlockHeader where
  parentHash    : UInt256
  ommersHash    : UInt256
  beneficiary   : AccountAddress
  stateRoot     : UInt256
  transRoot     : ByteArray
  receiptRoot   : ByteArray
  logsBloom     : ByteArray
  -- Officially deprecated, but checked in `wrongDifficulty_Cancun`
  difficulty    : ℕ
  number        : ℕ
  gasLimit      : ℕ
  gasUsed       : ℕ
  timestamp     : ℕ
  extraData     : ByteArray
  nonce         : UInt64
  prevRandao    : UInt256
  baseFeePerGas : ℕ
  parentBeaconBlockRoot : ByteArray
  withdrawalsRoot : ByteArray
  blobGasUsed     : UInt64
  excessBlobGas   : UInt64
deriving DecidableEq, Inhabited, Repr, BEq

def TARGET_BLOB_GAS_PER_BLOCK := 393216

def calcExcessBlobGas (parent : BlockHeader) : Option UInt64 := do
  if parent.excessBlobGas.toNat + parent.blobGasUsed.toNat < TARGET_BLOB_GAS_PER_BLOCK then
    pure 0
  else
    pure <| .ofNat <| parent.excessBlobGas.toNat + parent.blobGasUsed.toNat - TARGET_BLOB_GAS_PER_BLOCK

-- See https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
partial def fakeExponential0 (i output factor numerator denominator : ℕ) : (numeratorAccum : ℕ) → ℕ
  | 0 =>
    output / denominator
  | numeratorAccum =>
    let output := output + numeratorAccum
    let numeratorAccum := (numeratorAccum * numerator) / (denominator * i)
    let i := i + 1
    fakeExponential0 i output factor numerator denominator numeratorAccum

def fakeExponential (factor numerator denominator : ℕ) : ℕ :=
  fakeExponential0 1 0 factor numerator denominator (factor * denominator)

def MIN_BASE_FEE_PER_BLOB_GAS := 1
def BLOB_BASE_FEE_UPDATE_FRACTION := 3338477

def BlockHeader.getBlobGasprice (h : BlockHeader) : ℕ :=
  fakeExponential
    MIN_BASE_FEE_PER_BLOB_GAS
    h.excessBlobGas.toNat
    BLOB_BASE_FEE_UPDATE_FRACTION

end Evm
