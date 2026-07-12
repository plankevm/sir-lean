import Batteries

import Evm.Maps.ByteMap
import Evm.UInt256
import Batteries.Data.HashMap

namespace Evm

open Batteries

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

/--
Mutable machine state for the current frame.

The RETURN/REVERT payload is delivered directly in the halt signal rather than
stored here.
-/
structure MachineState where
  gasAvailable        : UInt64
  activeWords         : UInt64
  memory              : ByteArray
  returnData          : ByteArray
  deriving Inhabited

end Evm
