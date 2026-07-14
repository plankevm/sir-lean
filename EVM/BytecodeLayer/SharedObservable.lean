import BytecodeLayer.Observables

/-!
# A toolchain-neutral shared observable, and the flat `EVMSemantics` instance

This is the **flat** (`«evm»` / exp003) half of the cross-engine observable
bridge. Its mirror image lives on the nested side as
`experiments/004_nested_evmyul/NestedEvmYul/SharedObservable.lean`.

## Why the observable is *plain data*

The two EVM engines do **not** co-compile: exp003 pins
`leanprover/lean4:v4.30.0` and exp004 pins `leanprover/lean4:v4.22.0`, and
`.olean` artifacts are toolchain-version-locked, so no single `lake` target can
import both `«evm»` and `«evmyul»` (the namespace collisions on
`AccountAddress`/`State`/`Operation`/`UInt` are a *second*, milder blocker — see
the experiment report). The only thing that can cross the toolchain boundary is
**serialized plain data**.

So `SharedObservable` below is deliberately built from toolchain-agnostic
primitives only — `Bool`, `String`, `ℕ`, `List` — with **no dependency on any
heavy engine type**. Its definition is duplicated *verbatim* on the nested side
(same field names, same types, same constructors). A value produced by
`observe_flat` and a value produced by `observe_nested` are therefore comparable
purely as data: equal `SharedObservable`s ⇔ same observable behaviour.

## What it captures (width-normalized to ℕ)

* the success / revert / exception **tag** (canonicalized to a `String` so the
  flat `OutOfGas` and nested `OutOfGass` spelling difference does not leak);
* the **output** bytes (as `List ℕ`, each byte's `.toNat`);
* a **storage reader** materialized as the association list of
  `((addr : ℕ) × (key : ℕ)) ↦ (val : ℕ)` it produces — but since a function is
  not comparable as data, we expose `storageAt : ℕ → ℕ → ℕ` *and* a separate
  pure-data `SharedObservable` that omits it; storage equality is stated
  pointwise (see `SharedObservable.storageAgrees`);
* **gas remaining** normalized to `ℕ` (flat `UInt64.toNat`, nested
  `UInt256.toNat`);
* the **log/event** series, each entry `(address, topics, data)` normalized to
  `(ℕ, List ℕ, List ℕ)`.
-/

/-- The three-way halt tag, canonicalized to a `String` so the flat/nested
exception-spelling differences (`OutOfGas` vs `OutOfGass`) do not leak into the
shared comparison. `"ok"`/`"revert"` are the two completed cases. -/
def Evm.ExecutionException.canonTag : Evm.ExecutionException → String
  | .OutOfFuel          => "OutOfFuel"
  | .InvalidInstruction => "InvalidInstruction"
  | .OutOfGas           => "OutOfGas"
  | .BadJumpDestination => "BadJumpDestination"
  | .StackOverflow      => "StackOverflow"
  | .StackUnderflow     => "StackUnderflow"
  | .InvalidMemoryAccess => "InvalidMemoryAccess"
  | .StaticModeViolation => "StaticModeViolation"

namespace BytecodeLayer
open Evm

/-- A normalized log entry: address as `ℕ`, topics and data as `List ℕ` (each
byte / word `.toNat`). Field-identical to the nested mirror. -/
structure SharedLog where
  address : Nat
  topics  : List Nat
  data    : List Nat
deriving BEq, Repr, DecidableEq

/-- The toolchain-neutral, width-normalized observable. Pure data except the
storage reader, which is materialized as a function `addr → key → val` over `ℕ`
(storage is compared pointwise, not by `=` on the function). Everything else is
`Bool`/`String`/`ℕ`/`List`, identical to the nested mirror. -/
structure SharedObservable where
  /-- `"ok"` (completed, no revert), `"revert"` (completed but reverted), or an
  exception's `canonTag`. -/
  tag       : String
  /-- the returned bytes, each `.toNat`. -/
  output    : List Nat
  /-- gas remaining, normalized to `ℕ`. `none` on the exception branch (no
  result to read gas from). -/
  gas       : Option Nat
  /-- the emitted logs, in order. -/
  logs      : List SharedLog
  /-- the persistent storage left behind: `storageAt addr key` reads cell
  `(addr, key)` exactly as `SLOAD` (default `0`). Not part of the data
  comparison; related pointwise via `storageAgrees`. -/
  storageAt : Nat → Nat → Nat

/-- The pure-data part of two observables agree (everything but storage). -/
def SharedObservable.dataAgrees (a b : SharedObservable) : Prop :=
  a.tag = b.tag ∧ a.output = b.output ∧ a.gas = b.gas ∧ a.logs = b.logs

/-- The two storage readers agree on every cell. -/
def SharedObservable.storageAgrees (a b : SharedObservable) : Prop :=
  ∀ addr key, a.storageAt addr key = b.storageAt addr key

/-- Full observational agreement: pure data plus pointwise storage. -/
def SharedObservable.agrees (a b : SharedObservable) : Prop :=
  a.dataAgrees b ∧ a.storageAgrees b

namespace SharedObservable

/-- Normalize a `ByteArray` to `List ℕ`. -/
def ofBytes (b : ByteArray) : List Nat := b.toList.map (·.toNat)

/-- Normalize a flat `LogEntry` to a `SharedLog`. -/
def ofFlatLog (l : Evm.LogEntry) : SharedLog :=
  { address := l.address.val
    topics  := l.topics.toList.map (·.toNat)
    data    := ofBytes l.data }

end SharedObservable

/-- **`observe_flat`** — project a flat `messageCall` result into the shared
observable. `.error e` ↦ exception tag (no gas, no logs, empty storage);
`.ok r` ↦ `"ok"`/`"revert"` by `r.success`, with output, gas
(`gasRemaining.toNat`), logs, and the `storageAt` lens already shipped in
`Observables.lean`. -/
def observe_flat (res : Except ExecutionException CallResult) : SharedObservable :=
  match res with
  | .error e =>
      { tag := e.canonTag, output := [], gas := none, logs := []
        storageAt := fun _ _ => 0 }
  | .ok r =>
      { tag := if r.success then "ok" else "revert"
        output := SharedObservable.ofBytes r.output
        gas := some r.gasRemaining.toNat
        logs := r.substate.logSeries.toList.map SharedObservable.ofFlatLog
        storageAt := fun addr key =>
          -- read via the shared `lookupStorage` lens, addressed by ℕ
          match r.accounts.toList.find? (fun p => p.1.val = addr) with
          | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
          | none   => 0 }

/-!
## The state-polymorphic `EVMSemantics` interface (convergence report §3.1)

Observable-level only (per §3.4): `World`, `Result`, `run`, `observe`. The
never-OutOfFuel obligation is left as a separate per-engine theorem
(`messageCall_never_outOfFuel` flat / `Θ_never_outOfFuel` nested) rather than a
field, so the interface stays decidable plain data and does not drag the fuel
envelope into the structure. The nested side declares the *same* structure
(verbatim) and instantiates it with `run := Θ`-wrapper / `observe := observe_nested`.
-/

/-- A state-polymorphic, observable-level EVM semantics: an engine is a boundary
entry `run : World → Except E Result` together with an `observe` projection into
the toolchain-neutral `SharedObservable`. `E` is the engine's own exception type
(distinct Lean types across the two packages — hence polymorphic). -/
structure EVMSemantics where
  World   : Type
  Result  : Type
  E       : Type
  run     : World → Except E Result
  observe : Except E Result → SharedObservable

/-- The flat (`«evm»`) instance: `run := messageCall`, `observe := observe_flat`. -/
def flatSem : EVMSemantics where
  World   := CallParams
  Result  := CallResult
  E       := ExecutionException
  run     := Evm.messageCall
  observe := observe_flat

end BytecodeLayer
