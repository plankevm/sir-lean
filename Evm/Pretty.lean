/-
Human-eyeball friendly version of various data used throughout the project.
Mostly used for debugging, possibly for reporting.

The function for pretty printing is always `<Datatype>.pretty (self : Datatype) : String`
modulo parametricity.
-/

import Evm.Operations

import Conform.Wheels

namespace Evm

/--
Strip the existing `repr` a'la:
- Evm.Operation.Push (Evm.Operation.PushOp.PUSH1) → PUSH1

This breaks the moment that `Repr` changes its behaviour; it is fine for the time being.
-/
def Operation.pretty (self : Operation) : String :=
  let reprStr := ToString.toString <| repr self
  let lastComponent := reprStr.splitOn "." |>.getLast!
  lastComponent.take lastComponent.length.pred |>.toString

end Evm
