import BytecodeLayer.Exec.Observable
import BytecodeLayer.Hoare.Sequence

namespace BytecodeLayer.Exec

open Evm
open GasConstants
open BytecodeLayer.Hoare

/-- A single-element `subCharges` is one subtraction. -/
theorem subCharges_singleton (g : UInt64) (c : ℕ) :
    subCharges g [c] = g - UInt64.ofNat c := rfl

/-- The final binary opcode subtracts the trailing `Gverylow` charge. -/
theorem charge_binOpPost_gas (fr : Frame) (op : UInt256 → UInt256 → UInt256)
    (a b : Word) (rest : Stack Word) :
    (BytecodeLayer.Dispatch.binOpPost fr.exec op a b rest).gasAvailable
      = subCharges fr.exec.gasAvailable [Gverylow] := by
  rw [subCharges_singleton]
  rfl

end BytecodeLayer.Exec
