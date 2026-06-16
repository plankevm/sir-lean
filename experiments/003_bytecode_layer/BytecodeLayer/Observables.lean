import Evm

/-!
# Observables at the messageCall boundary

`messageCall : CallParams → Except _ CallResult` returns a `CallResult` carrying
a call's full effects. To state results without dragging the whole machine into
the statement, we observe only two things:

1. **`Observables`** — the *world-independent* outcome: did the call succeed, and
   what bytes did it return (`success`, `output`).
2. **`storageAt addr key`** — one *persistent* effect: the value left in a single
   storage cell `(addr, key)`, read exactly as the EVM's `SLOAD`.

That is the entire vocabulary the specs in `Spec.lean` use. No `Frame`, `pc`,
`stack`, gas counter, or fuel ever appears.
-/

namespace BytecodeLayer
open Evm

/-- The world-independent outcome of a completed message call: the success flag
and the returned output bytes. -/
structure Observables where
  success : Bool
  output  : ByteArray

/-- `succeeded out`: a successful completion that returned `out`. -/
def Observables.succeeded (out : ByteArray) : Observables := { success := true, output := out }

/-- The common case: completed successfully with **no return data**. Reads in a
spec as "the call succeeded and returned nothing." -/
def Observables.ok : Observables := Observables.succeeded .empty

/-- Project a `CallResult` to its world-independent outcome. -/
def CallResult.observe (r : CallResult) : Observables :=
  { success := r.success, output := r.output }

/-! ## A persistent-storage observable

For results about a contract that writes to storage, we also read one storage
cell the completed call leaves behind — exactly as the EVM's `SLOAD` would
(`Account.lookupStorage`, i.e. default to `0` for an absent account or unset
cell). -/

/-- The persistent storage value a completed call leaves at `(addr, key)`:
the `key` cell of `addr`'s account in the returned `accounts` map, defaulting to
`0` for an absent account or unset cell — exactly the EVM's own `SLOAD` reading. -/
def CallResult.storageAt (r : CallResult) (addr : AccountAddress) (key : UInt256) : UInt256 :=
  r.accounts.find? addr |>.option 0 (fun a => a.lookupStorage key)

/-! ## The named outcome of a message call

`messageCall p : Except ExecutionException CallResult` is the raw result. Reading
it in a spec forces decoding `.ok`/`.error` and the `success` flag (see the
external-call counterexample, where `.ok 0` silently means "completed but the
inner write was rolled back"). `Outcome` names the three things that can happen
at the top-level boundary so a statement reads in words:

* **`completed out σ`** — the top-level run finished and **did not revert**
  (`CallResult.success = true`). It returned the bytes `out`, and `σ` is the
  persistent storage it left behind: `σ a k` is the value at cell `(a, k)`, read
  exactly as `SLOAD` (defaulting to `0`). This is the "succeeds" case higher IRs
  care about — observables *plus* queryable storage.
* **`reverted out`** — the top-level run finished but **reverted**
  (`CallResult.success = false`): its storage effects are rolled back, so only
  the returned bytes `out` are observable, no storage to query.
* **`exception e`** — the run raised a top-level `ExecutionException` `e` (the
  `.error` branch of `messageCall`), e.g. `OutOfGas`. Note `OutOfFuel` is such an
  `e`: an honest `completed` claim must rule it out (a terminating, gas-respecting
  run never reports it). -/
inductive Outcome where
  /-- Finished without reverting: returned `out`, leaving storage `σ` (`σ a k` is
  the `SLOAD` of cell `(a, k)`). -/
  | completed (out : ByteArray) (σ : AccountAddress → UInt256 → UInt256)
  /-- Finished but reverted: only the returned bytes `out` survive. -/
  | reverted (out : ByteArray)
  /-- Raised a top-level execution exception. -/
  | exception (e : ExecutionException)

namespace Outcome

/-- The named outcome of a finished `CallResult`: `completed`/`reverted` chosen by
the `success` flag, with output bytes and (for `completed`) the `storageAt` reader
as the queryable storage. -/
def ofResult (r : CallResult) : Outcome :=
  if r.success then .completed r.output (CallResult.storageAt r) else .reverted r.output

/-- The named outcome of a whole `messageCall`: an `.error` is `exception`, an
`.ok` is decoded by `ofResult`. This is the single decoder every
for-all-programs statement observes through. -/
def ofCall (res : Except ExecutionException CallResult) : Outcome :=
  match res with
  | .error e => .exception e
  | .ok r => ofResult r

/-- `o` completed without reverting, leaving `v` at storage cell `(a, k)`. The
predicate the storage-effect specs land on, reading as a sentence:
"the call completed and cell `(a, k)` holds `v`." -/
def completedWith (o : Outcome) (a : AccountAddress) (k : UInt256) (v : UInt256) : Prop :=
  ∃ out σ, o = .completed out σ ∧ σ a k = v

/-- `o` completed without reverting, returning exactly the bytes `out`. Reads as
"the call succeeded and returned `out`"; the call-free / `RETURN` specs land here. -/
def completedReturning (o : Outcome) (out : ByteArray) : Prop :=
  ∃ σ, o = .completed out σ

end Outcome

end BytecodeLayer
