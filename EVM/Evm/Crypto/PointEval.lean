import Evm.Wheels
import Evm.PerformIO
import Evm.Crypto.Evmrs
import Conform.Wheels

def blobPointEval (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    evmrsCommandOfInput data
  where evmrsCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["point-eval", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s
