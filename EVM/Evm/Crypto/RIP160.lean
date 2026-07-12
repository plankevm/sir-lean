import Evm.PerformIO
import Evm.Crypto.Evmrs
import Evm.Wheels
import Conform.Wheels

def blobRIP160 (d : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    evmrsCommandOfInput d
  where evmrsCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["rip160", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobRIP160 (toHex d)
