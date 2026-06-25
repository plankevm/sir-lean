import LirLean.IR
import Evm
import BytecodeLayer.Semantics.Dispatch

/-!
# LirLean — the abstract gas oracle (`docs/ir-design.md` §3)

The IR's gas accounting is **gas-agnostic**: every cost the small-step semantics
charges is read from an abstract `GasOracle`, not from hardcoded EVM constants.
The IR keeps its `GAS` opcode (`Expr.gas`) — its *counter* semantics (remaining =
initial − consumed) are oracle-independent — but the *cost* assigned to each IR
construct is a field of the oracle.

This mirrors how other EVM formalizations parameterize gas, and makes the
"gas consumed is monotonically non-decreasing" property hold for free (each
charge subtracts a `Nat` cost; see `IRState.charge` and `consumed_mono` in
`LirLean/SmallStep.lean`).

The concrete EVM gas schedule is **one** instantiation, `evmOracle`, whose fields
reduce by `rfl` to the existing `GasConstants.*` / `Evm.sloadCost` /
`sstoreChargeOf`. The lowering / `Match` layer instantiates the oracle to
`evmOracle`, at which point the IR's `Expr.gas` value is *reflexively equal* to
the lowered `GAS` opcode's pushed value (`Lir.gas_reflects_lowered` in
`LirLean/Match.lean`).
-/

namespace Lir

open Evm
open BytecodeLayer.Dispatch

/-- An abstract **gas oracle**: the per-construct `Nat` cost data the IR's
small-step semantics charges. The concrete EVM schedule (`evmOracle`) is one
instantiation; the field types are chosen so that instantiation is
*definitional* (each field reduces by `rfl` to the existing EVM cost).

* `verylow` — the cost of an `add` / `lt` / operand materialisation (EVM
  `Gverylow`, charged by `binOpPost` and each materialising PUSH);
* `base` — the cost of the `GAS` opcode (EVM `Gbase`, charged by `gasPost`);
* `mid` — the cost of an unconditional `JUMP` (EVM `Gmid`);
* `high` — the cost of a conditional `JUMPI` (EVM `Ghigh`);
* `sload warm` — the cost of an `SLOAD`, a function of the warm/cold access bit;
* `sstore exec key newValue` — the cost of an `SSTORE`, a function of the world
  it observes (original/current cell value, warm bit) — exactly the data
  `sstoreChargeOf` reads. -/
structure GasOracle where
  /-- Cost of `add` / `lt` / one operand push (EVM `Gverylow`). -/
  verylow : Nat
  /-- Cost of the `GAS` opcode (EVM `Gbase`). -/
  base    : Nat
  /-- Cost of an unconditional `JUMP` (EVM `Gmid`). -/
  mid     : Nat
  /-- Cost of a conditional `JUMPI` (EVM `Ghigh`). -/
  high    : Nat
  /-- Cost of an `SLOAD`, as a function of the warm/cold access bit. -/
  sload   : Bool → Nat
  /-- Cost of an `SSTORE`, as a function of the observed world (the data
  `sstoreChargeOf` reads): the execution state, the key, the new value. -/
  sstore  : ExecutionState → Word → Word → Nat

/-- **The concrete EVM gas schedule** — one instantiation of `GasOracle`. Every
field reduces by `rfl` to the EVM cost the lowered opcode charges, so the IR's
gas accounting at `evmOracle` is *definitionally* the lowered bytecode's: the
`sim_*` lemmas and `Match`'s `M4` go through unchanged (defeq) — see
`LirLean/Match.lean`. -/
def evmOracle : GasOracle where
  verylow := GasConstants.Gverylow
  base    := GasConstants.Gbase
  mid     := GasConstants.Gmid
  high    := GasConstants.Ghigh
  sload   := Evm.sloadCost
  sstore  := fun exec key newValue => sstoreChargeOf exec key newValue

end Lir
