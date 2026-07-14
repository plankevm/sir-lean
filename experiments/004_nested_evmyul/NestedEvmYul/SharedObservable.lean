import EvmYul.EVM.Semantics
import NestedEvmYul.NeverOutOfFuel

/-!
# A toolchain-neutral shared observable, and the nested `EVMSemantics` instance

This is the **nested** (`«evmyul»` / exp004) half of the cross-engine observable
bridge. Its mirror image lives on the flat side as
`EVM/BytecodeLayer/SharedObservable.lean`.

## Why the observable is *plain data*

The two EVM engines do **not** co-compile: exp003 pins
`leanprover/lean4:v4.30.0` and exp004 pins `leanprover/lean4:v4.22.0`, and
`.olean` artifacts are toolchain-version-locked, so no single `lake` target can
import both `«evm»` and `«evmyul»`. The only thing that crosses the toolchain
boundary is **serialized plain data**.

So `SharedObservable` below is built from toolchain-agnostic primitives only —
`Bool`, `String`, `ℕ`, `List` — with **no dependency on any heavy engine type**.
Its definition is duplicated *verbatim* on the flat side (same field names, same
types, same constructors). A value produced by `observe_nested` here and a value
produced by `observe_flat` there are therefore comparable purely as data.

This file is the exp004 deliverable the convergence report
(`docs/flat-vs-nested-convergence.md` §5, step 1–3) flagged as MISSING: an
`observe` projection above `Θ` plus the `EVMSemantics` instance. The nested side
previously had nothing above `Θ` (only `Θ_never_outOfFuel`).
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-- The three-way halt tag, canonicalized to a `String` so the flat/nested
exception-spelling differences (`OutOfGas` vs `OutOfGass`) do not leak into the
shared comparison. `"ok"`/`"revert"` are the two completed cases. Mirror of the
flat `Evm.ExecutionException.canonTag` (note: the nested constructor is spelled
`OutOfGass`, canonicalized here to the flat `"OutOfGas"`). -/
def canonTag : EVM.ExecutionException → String
  | .OutOfFuel          => "OutOfFuel"
  | .InvalidInstruction => "InvalidInstruction"
  | .OutOfGass          => "OutOfGas"
  | .BadJumpDestination => "BadJumpDestination"
  | .StackOverflow      => "StackOverflow"
  | .StackUnderflow     => "StackUnderflow"
  | .InvalidMemoryAccess => "InvalidMemoryAccess"
  | .StaticModeViolation => "StaticModeViolation"

/-- A normalized log entry. **Verbatim mirror** of the flat `SharedLog`. -/
structure SharedLog where
  address : Nat
  topics  : List Nat
  data    : List Nat
deriving BEq, Repr, DecidableEq

/-- The toolchain-neutral, width-normalized observable. **Verbatim mirror** of
the flat `BytecodeLayer.SharedObservable` (same fields, same types). -/
structure SharedObservable where
  tag       : String
  output    : List Nat
  gas       : Option Nat
  logs      : List SharedLog
  storageAt : Nat → Nat → Nat

/-- Pure-data agreement (everything but storage). Mirror of the flat version. -/
def SharedObservable.dataAgrees (a b : SharedObservable) : Prop :=
  a.tag = b.tag ∧ a.output = b.output ∧ a.gas = b.gas ∧ a.logs = b.logs

/-- Pointwise storage agreement. Mirror of the flat version. -/
def SharedObservable.storageAgrees (a b : SharedObservable) : Prop :=
  ∀ addr key, a.storageAt addr key = b.storageAt addr key

/-- Full observational agreement. Mirror of the flat version. -/
def SharedObservable.agrees (a b : SharedObservable) : Prop :=
  a.dataAgrees b ∧ a.storageAgrees b

namespace SharedObservable

/-- Normalize a `ByteArray` to `List ℕ`. Mirror of the flat version. -/
def ofBytes (b : ByteArray) : List Nat := b.toList.map (·.toNat)

/-- Normalize a nested `LogEntry` to a `SharedLog`. The nested `LogEntry` is
field-identical to the flat one (`address`/`topics`/`data`), shared lineage. -/
def ofNestedLog (l : EvmYul.LogEntry) : SharedLog :=
  { address := l.address.val
    topics  := l.topics.toList.map (·.toNat)
    data    := ofBytes l.data }

end SharedObservable

/-- The exact `Except` output type of `Θ`: `createdAccounts × σ' × g' × A' × z × o`. -/
abbrev ThetaResult :=
  Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool × ByteArray

/-- **`observe_nested`** — project a nested `Θ` result into the shared
observable. Mirrors `observe_flat`: `.error e` ↦ exception tag (no gas, no logs,
empty storage); `.ok (_, σ', g', A', z, o)` ↦ `"ok"`/`"revert"` by `z`, with
output `o`, gas `g'.toNat`, logs from `A'.logSeries`, and storage read through
the **shared** `Account.lookupStorage` lens (identical definition to flat). -/
def observe_nested (res : Except EVM.ExecutionException ThetaResult) : SharedObservable :=
  match res with
  | .error e =>
      { tag := canonTag e, output := [], gas := none, logs := []
        storageAt := fun _ _ => 0 }
  | .ok (_, σ', g', A', z, o) =>
      { tag := if z then "ok" else "revert"
        output := SharedObservable.ofBytes o
        gas := some g'.toNat
        logs := A'.logSeries.toList.map SharedObservable.ofNestedLog
        storageAt := fun addr key =>
          match σ'.toList.find? (fun p => p.1.val = addr) with
          | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
          | none   => 0 }

/-!
## The state-polymorphic `EVMSemantics` interface (convergence report §3.1)

**Verbatim mirror** of the flat `BytecodeLayer.EVMSemantics`. Observable-level
only: `World`, `Result`, `run`, `observe`. The never-OOF obligation stays a
separate per-engine theorem (`Θ_never_outOfFuel`), not a field.

The nested `run` must be **fuel-free** to match flat's `messageCall`, so it wraps
`Θ` with a `seedFuel`-analogue derived from the proven `fuelBound` envelope
(report §5 step 2). The `World` bundles the 19 positional `Θ` arguments plus the
top-level `gas`/`depth` so the seeding is internal.
-/

/-- A state-polymorphic, observable-level EVM semantics. Verbatim mirror of the
flat `BytecodeLayer.EVMSemantics`. -/
structure EVMSemantics where
  World   : Type
  Result  : Type
  E       : Type
  run     : World → Except E Result
  observe : Except E Result → SharedObservable

/-- The 19 positional arguments of `Θ`, bundled into a record so the nested
`run` is a single-argument function like flat's `messageCall`. The seeding fuel
is derived internally from `g`/`e`, so callers never pass `fuel`. -/
structure NestedWorld where
  blobVersionedHashes : List ByteArray
  createdAccounts     : Batteries.RBSet AccountAddress compare
  genesisBlockHeader  : BlockHeader
  blocks              : ProcessedBlocks
  σ  : AccountMap
  σ₀ : AccountMap
  A  : Substate
  s  : AccountAddress
  o  : AccountAddress
  r  : AccountAddress
  c  : ToExecute
  g  : UInt256
  p  : UInt256
  v  : UInt256
  v' : UInt256
  d  : ByteArray
  e  : Nat
  H  : BlockHeader
  w  : Bool

/-- The `seedFuel`-analogue: the proven never-OOF envelope plus its `+3` offset,
exactly the seeding under which `Θ_never_outOfFuel` discharges (report §5 step 2,
`NestedEvmYul.NeverOutOfFuel.fuelBound`). -/
def seedFuel (w : NestedWorld) : Nat :=
  EvmYul.EVM.NeverOutOfFuel.fuelBound w.g.toNat w.e + 3

/-- Run `Θ` fuel-free: seed the fuel from the world, then unpack the 19 args. -/
def runΘ (w : NestedWorld) : Except EVM.ExecutionException ThetaResult :=
  Θ (seedFuel w) w.blobVersionedHashes w.createdAccounts w.genesisBlockHeader
    w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v w.v' w.d w.e w.H w.w

/-- The nested (`«evmyul»`) instance: `run := runΘ`, `observe := observe_nested`. -/
def nestedSem : EVMSemantics where
  World   := NestedWorld
  Result  := ThetaResult
  E       := EVM.ExecutionException
  run     := runΘ
  observe := observe_nested

/-- The nested side's never-OutOfFuel discharge re-expressed against the
fuel-free `runΘ`: under the proven envelope (`e ≤ 1024`), the seeded run never
reports `OutOfFuel`. This is `Θ_never_outOfFuel` applied at `seedFuel`. -/
theorem runΘ_never_outOfFuel (w : NestedWorld) (he : w.e ≤ 1024) :
    runΘ w ≠ .error .OutOfFuel := by
  unfold runΘ seedFuel
  exact EvmYul.EVM.NeverOutOfFuel.Θ_never_outOfFuel
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he (Nat.le_refl _)

end NestedEvmYul
