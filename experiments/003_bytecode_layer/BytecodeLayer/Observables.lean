import Evm

/-!
# Observables at the messageCall boundary

The **exported** surface. `messageCall : CallParams → Except _ CallResult`
returns a `CallResult` whose fields are the message-call's observable effects.
The capstones speak only of the `observe` projection — never of `Frame`, `pc`,
`stack`, fuel, or any lockstep internal.

We project the two observables that are world-map-independent and therefore
state cleanly for a handwritten program: the **success flag** and the
**returned output**. (The account map and substate are also observables, but for
the call-completes-cleanly programs proved here they are returned verbatim from
the call's inputs/snapshot; exposing them would drag the full `AccountMap` into
the statement without adding force. The success/output pair is what 001's
`∃G₀` counterexample turns on — the caller's stored flag and its clean halt.)
-/

namespace BytecodeLayer
open Evm

/-- The world-independent observables of a completed message call. -/
structure Observables where
  success : Bool
  output  : ByteArray

/-- Project a `CallResult` to its world-independent observables. -/
def CallResult.observe (r : CallResult) : Observables :=
  { success := r.success, output := r.output }

/-! ## A persistent-storage observable

The success/output pair is world-independent; the next rung (SSTORE) asserts a
**persistent effect**, so we extend the observed surface with the storage cell a
completed call leaves behind. This reads the cell exactly as the EVM does
(`Account.lookupStorage`, i.e. `findD … 0`) at a chosen `(addr, key)`, off the
call's returned `accounts` map — still at the messageCall boundary, no `Frame`,
pc, stack, or fuel. -/

/-- The persistent storage value a completed call leaves at `(addr, key)`:
the `key` cell of `addr`'s account in the returned `accounts` map, defaulting to
`0` for an absent account or unset cell — exactly the EVM's own `SLOAD` reading. -/
def CallResult.storageAt (r : CallResult) (addr : AccountAddress) (key : UInt256) : UInt256 :=
  r.accounts.find? addr |>.option 0 (fun a => a.lookupStorage key)

end BytecodeLayer
