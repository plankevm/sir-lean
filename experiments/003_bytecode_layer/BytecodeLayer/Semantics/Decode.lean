import Evm
import BytecodeLayer.Programs

/-!
# Program `decode` lemmas (`Decode`)

The per-pc `decode` facts for the example programs (`stopProgram`,
`pushStopProgram`, `sstoreProgram`). Reused by the straight-line program proofs
(`ProgramExamples`, built on `Straightline`) and by the descent / external-call
proofs (`DescentDrops`, `ExternalCall`).
-/

namespace BytecodeLayer.Decode
open Evm

/-! ## STOP -/

theorem decode_stopProgram : decode stopProgram 0 = some (.System .STOP, .none) := by rfl

/-! ## PUSH1 ; STOP -/

theorem decode_pushStop_0 :
    decode pushStopProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_pushStop_2 :
    decode pushStopProgram ((0 : UInt32) + UInt8.toUInt32 2) = some (.System .STOP, .none) := by rfl

/-! ## PUSH1 ; PUSH1 ; SSTORE ; STOP -/

theorem decode_sstore_0 :
    decode sstoreProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_sstore_2 :
    decode sstoreProgram ((0 : UInt32) + UInt8.toUInt32 2)
      = some (.Push .PUSH1, some (7, 1)) := by rfl

theorem decode_sstore_4 :
    decode sstoreProgram (((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
      = some (.Smsf .SSTORE, .none) := by rfl

theorem decode_sstore_5 :
    decode sstoreProgram
      ((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
      = some (.System .STOP, .none) := by rfl

end BytecodeLayer.Decode
