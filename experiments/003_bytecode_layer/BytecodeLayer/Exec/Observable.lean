import Evm

/-!
# Generic execution observables and oracle-stream aliases

These aliases are structurally EVM-generic: a storage world, gas observations,
CALL/CREATE result streams, and the frame-free observable reported by a run.
The IR package re-exports them under `Lir` for compatibility.
-/

namespace BytecodeLayer.Exec

open Evm

abbrev Word := UInt256

abbrev World := Word → Word

inductive IRHalt where
  | stopped
  | returned (w : Word)
deriving DecidableEq, Repr

abbrev GasOracle := List Word

-- Compatibility alias; declarations generally use `GasOracle`.
abbrev Trace := GasOracle

abbrev CallStream := List (World × Word)

abbrev CreateStream := List (World × Word)

structure Observable where
  world  : World
  result : IRHalt

end BytecodeLayer.Exec
