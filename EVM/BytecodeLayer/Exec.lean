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
import BytecodeLayer.Exec.CyclicSim

namespace BytecodeLayer.Exec

open Evm

/-- Big-endian 4-byte encoding of a code offset `n` — the immediate a
`PUSH4`-encoded jump target carries. Consumed by the assembler's PUSH-immediate
encoders (`Asm.lean`), the `Asm/Geometry` layout proofs, and the ByteWindow
round-trip lemmas. Hosted on this aggregator (not in `Exec/ByteWindow.lean`)
because ByteWindow imports the aggregator — moving it there would create an
import cycle. -/
def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8), UInt8.ofNat n ]

/-- Big-endian 32-byte encoding of a `Word` — the immediate of a full-width
`PUSH32`. Companion of `offsetBytesBE`, same consumers and same hosting
rationale. -/
def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i =>
    UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

end BytecodeLayer.Exec
