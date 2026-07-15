import Evm

/-!
# Generic execution observables and oracle-stream aliases

These aliases cover a storage world, gas observations, CALL/CREATE result streams,
and the frame-free observable reported by a run.
-/

namespace BytecodeLayer.Exec

open Evm

abbrev Word := UInt256

abbrev World := Word → Word

inductive HaltResult where
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
  result : HaltResult

end BytecodeLayer.Exec
