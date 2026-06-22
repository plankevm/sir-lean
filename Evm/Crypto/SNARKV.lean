import Evm.Wheels
import Evm.PerformIO
import Evm.Crypto.Evmrs
import Conform.Wheels

def blobSNARKV (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    evmrsCommandOfInput data
  where evmrsCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["snarkv", data]
  }

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s
