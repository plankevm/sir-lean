import BytecodeLayer.Exec.Observable
import BytecodeLayer.Exec.Call

namespace BytecodeLayer.Exec

open Evm

def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8), UInt8.ofNat n ]

def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i =>
    UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

end BytecodeLayer.Exec
