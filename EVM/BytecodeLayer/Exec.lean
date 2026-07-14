import BytecodeLayer.Exec.Observable
import BytecodeLayer.Exec.Call
import BytecodeLayer.Exec.Create
import BytecodeLayer.Exec.CallRealises
import BytecodeLayer.Exec.CleanHaltExtract
import BytecodeLayer.Exec.CallPreservesSelf
import BytecodeLayer.Exec.Gas
import BytecodeLayer.Exec.Alignment
import BytecodeLayer.Exec.Results
import BytecodeLayer.Exec.WitnessChecks
import BytecodeLayer.Exec.Modellable
import BytecodeLayer.Exec.Frame
import BytecodeLayer.Exec.Memory
import BytecodeLayer.Exec.Stash

namespace BytecodeLayer.Exec

open Evm

def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8), UInt8.ofNat n ]

def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i =>
    UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

end BytecodeLayer.Exec
