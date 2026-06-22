import Evm.Wheels
import Evm.PerformIO
import Evm.Crypto.Evmrs
import Conform.Wheels
import Evm.Crypto.Keccak256

def secp256k1n : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337

def blobECDSARECOVER (e v r s : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    evmrsCommandOfInput e v r s
  where evmrsCommandOfInput (e v r s : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["recover", e, v, r, s]
  }

def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  match blobECDSARECOVER (toHex e) (toHex v) (toHex r) (toHex s) with
    | "error" => .error "ECDSARECOVER failed"
    | s => ByteArray.ofBlob <| padLeft 128 s /- 128 characters means 64 bytes -/

open Batteries
