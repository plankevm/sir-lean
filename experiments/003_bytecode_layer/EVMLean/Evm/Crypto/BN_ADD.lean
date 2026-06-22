import Evm.Wheels
import Evm.PerformIO
import Evm.Crypto.Evmrs
import Conform.Wheels

def blobBN_ADD (x₀ y₀ x₁ y₁ : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    evmrsCommandOfInput x₀ y₀ x₁ y₁
  where evmrsCommandOfInput (x₀ y₀ x₁ y₁ : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["bn-add", x₀, y₀, x₁, y₁]
  }

def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  match blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁) with
    | "error" => .error "BN_ADD failed"
    | s => ByteArray.ofBlob s
