import LirLean.IR
import LirLean.Gas
import Evm
import BytecodeLayer.Semantics.UInt64

/-!
# LirLean — small-step, gas-aware IR semantics (C3)

This module fixes the IR's operational semantics (`docs/ir-design.md` §3), the
primary relation the lowering-preservation proof simulates. The choice is
**small-step with an explicit gas counter** so each IR step lines up with one
exp003 `Runs` segment over the lowered bytecode.

The gas charges and storage effects deliberately **mirror exp003's post-frame
transformers** (`binOpPost`, `sloadPost`, `gasPost`, `sstorePost`, the jump
posts) so the `Match` invariant's gas clause (`M4`) and storage clause (`M3`) are
preserved step-by-step by `rfl`-clean arithmetic — see `LirLean/Match.lean`.

## Design notes

* `IRState.gas` is a `UInt64` (not `ℕ`) so it equals `fr.exec.gasAvailable`
  *exactly* — `M4` becomes a plain equality of `UInt64`s, and each construct's IR
  charge is the same `UInt64.ofNat <cost>` subtraction the EVM post-frame
  performs. The *cost* itself comes from an abstract `GasOracle` (`LirLean/Gas.lean`);
  the EVM schedule is the `evmOracle` instantiation, defeq to the old constants.
* `IRState.storage : Word → Word` mirrors the self account's storage *through the
  observable lens* (`find?/lookupStorage`) that `M3` and exp003's
  `sstoreFrame_storage_self` / `sloadFrame_storage_self` use.
* Expression evaluation `evalExpr` is total (`Option`) and recompute-friendly: it
  reads `locals` for `tmp`, the storage map for `sload`, and the gas counter for
  `gas`. The arithmetic functions are exp003's `UInt256.add` / `UInt256.lt`, so
  the value the IR computes is *definitionally* the value the lowered opcode pushes.
-/

namespace Lir

open Evm

/-! ## Gas charges (read from the abstract `GasOracle`)

Every IR cost is a field of the `GasOracle` parameter (`LirLean/Gas.lean`) rather
than a hardcoded EVM constant: the IR's gas accounting is **gas-agnostic**. The
EVM schedule is the `evmOracle` instantiation, at which each reader below reduces
by `rfl` to the constant the lowered opcode charges (e.g. `gVerylow evmOracle =
GasConstants.Gverylow` by `rfl`). -/

/-- Gas charged by `add`/`lt`/(operand) materialisation per arithmetic op — the
oracle's `verylow`. At `evmOracle` this is `Gverylow = 3` (mirrors `binOpPost`). -/
def gVerylow (oracle : GasOracle) : Nat := oracle.verylow

/-- Gas charged by `GAS` — the oracle's `base`. At `evmOracle` this is `Gbase = 2`
(mirrors `gasPost`). -/
def gBase (oracle : GasOracle) : Nat := oracle.base

/-- Gas charged by `JUMP` — the oracle's `mid`. At `evmOracle` this is `Gmid = 8`. -/
def gMid (oracle : GasOracle) : Nat := oracle.mid

/-- Gas charged by `JUMPI` — the oracle's `high`. At `evmOracle` this is `Ghigh = 10`. -/
def gHigh (oracle : GasOracle) : Nat := oracle.high

/-! ## The IR machine state -/

/-- The IR register/storage/gas state. `storage` is the self account's storage
read through the observable lens; `gas` is a `UInt64` so it equals
`fr.exec.gasAvailable` exactly (the `M4` clause of `Match`).

`callResult` is the **call-result slot** — the home of the one value that is *not*
recomputable from a pure `Expr`: the most recent external CALL's 0/1 success word
(`docs/ir-design.md` §4, §5). Recompute-on-use materialises every `tmp` from its
defining `Expr` at each use, but the success flag is dynamic (it depends on the
child run), so it has no `Expr`. We therefore make it first-class IR state: a CALL
writes it (`IRState.applyCall`), and the `resultTmp` binding reads it *once at the
call* into `locals` (`IRState.bindCallResult`) — so a later use of `resultTmp` is a
normal `locals`/`Expr.tmp` read, never a recomputation. This keeps `Match`'s
`M5 stack_nil` intact (the slot is pure IR state; the lowered CALL's physical
flag-on-stack is bridged by the `successWord` reflexivity, not by `Match`). -/
structure IRState where
  /-- Register file: each temporary's bound value (if assigned). -/
  locals  : Tmp → Option Word
  /-- The self account's storage (observable lens). -/
  storage : Word → Word
  /-- Remaining gas — a `UInt64`, equal to `gasAvailable` under `Match`. -/
  gas     : UInt64
  /-- The most recent external CALL's 0/1 success word, if a CALL has run. The one
  value not recomputable from an `Expr`; written by `IRState.applyCall`, read once
  into `locals` by `IRState.bindCallResult` at the call's `resultTmp`. -/
  callResult : Option Word := none

/-- An IR halt result (the terminator outcomes). -/
inductive IRHalt where
  /-- `STOP` — success, no output word. -/
  | stopped
  /-- `RETURN t` — success returning the word `t` evaluated to. -/
  | returned (w : Word)
deriving DecidableEq, Repr

/-- An IR machine configuration: either running inside a block at a statement
cursor, or halted with a result. -/
inductive IRConf where
  /-- Inside block `L`, about to execute statement index `pc` (or, when `pc`
  reaches the block length, its terminator) of `L`. -/
  | running (L : Label) (pc : Nat) (st : IRState)
  /-- Halted with `h`. -/
  | halted  (h : IRHalt)

/-! ## Expression evaluation

`evalExpr st e` is the IR value of `e` in state `st`. It is total via `Option`
(an undefined `tmp` yields `none`). The arithmetic mirrors exp003 exactly:
`add → UInt256.add`, `lt → UInt256.lt`, `sload → storage lens`, `gas → ofUInt64
gas`. This makes the IR value definitionally equal to the word the lowered opcode
leaves on the stack. -/

/-- Evaluate an expression to a word (total via `Option`; `none` = undefined tmp). -/
def evalExpr (st : IRState) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.storage key)
  | .gas     => some (UInt256.ofUInt64 st.gas)

/-! ## Helpers on `IRState` -/

/-- Bind a temporary to a value. -/
def IRState.setLocal (st : IRState) (t : Tmp) (w : Word) : IRState :=
  { st with locals := fun t' => if t' = t then some w else st.locals t' }

/-- **Bind the call-result slot into `locals` at a `resultTmp`.** The dynamic CALL
success word lives in `callResult` (the one non-recomputable value); this binds it
*once* to the call's `resultTmp` — after which it is an ordinary `locals` value that
recompute-on-use materialises via `Expr.tmp`. When the spec binds no result
(`resultTmp = none`) or no CALL has run (`callResult = none`), `locals` is
unchanged. This is the read path for `CallSpec.resultTmp`. -/
def IRState.bindCallResult (st : IRState) : Option Tmp → IRState
  | none   => st
  | some t => match st.callResult with
              | none   => st
              | some w => st.setLocal t w

/-- Write a storage cell. -/
def IRState.setStorage (st : IRState) (k v : Word) : IRState :=
  { st with storage := fun k' => if k' = k then v else st.storage k' }

/-- Charge `c` gas (as `UInt64.ofNat`), mirroring the EVM post-frames'
`gasAvailable - UInt64.ofNat c`. -/
def IRState.charge (st : IRState) (c : Nat) : IRState :=
  { st with gas := st.gas - UInt64.ofNat c }

/-! ## Monotone consumed-gas (the "gas only ever goes up" property)

`consumed init st : ℕ` is how much gas has been spent getting from `init` to `st`
(initial − remaining, in `ℕ`). The point of charging a `Nat` cost is that, under
the per-step gas-sufficiency precondition the `sim_*` lemmas already carry (the
`hgas` hypotheses, which prevent `UInt64` underflow), **consumed gas is
monotonically non-decreasing**: each charge adds exactly its cost. This is the
"monotonically increasing numbers" property made explicit (`consumed_charge`,
`consumed_mono`) instead of left implicit in the per-construct arithmetic. -/

/-- Gas consumed going from `init.gas` to `st.gas`, in `ℕ`. -/
def consumed (init st : IRState) : Nat := init.gas.toNat - st.gas.toNat

/-- **Remaining gas drops by exactly the cost.** Under the gas-sufficiency
precondition (`c ≤ st.gas.toNat`, the same `hgas` the `sim_*` lemmas carry; with
`c` in `UInt64` range), the post-charge counter is `st.gas.toNat - c` — no
`UInt64` underflow. The `≤ st.gas.toNat` guard is exactly what rules it out. -/
theorem charge_gas_toNat (st : IRState) (c : Nat)
    (hc : c ≤ st.gas.toNat) (hlt : c < 2 ^ 64) :
    (st.charge c).gas.toNat = st.gas.toNat - c := by
  unfold IRState.charge
  exact BytecodeLayer.UInt64.toNat_sub_ofNat st.gas c hc hlt

/-- **Charging exactly accounts for the cost.** Under the gas-sufficiency
precondition and `st` being downstream of `init` (`st.gas.toNat ≤ init.gas.toNat`,
the standing `Match`/M4 invariant — gas only falls), consumed gas after charging
`c` is the prior consumed plus `c`. -/
theorem consumed_charge (init st : IRState) (c : Nat)
    (hdown : st.gas.toNat ≤ init.gas.toNat)
    (hc : c ≤ st.gas.toNat) (hlt : c < 2 ^ 64) :
    consumed init (st.charge c) = consumed init st + c := by
  unfold consumed
  rw [charge_gas_toNat st c hc hlt]
  omega

/-- **Consumed gas is monotone along a charge.** Under the gas-sufficiency
precondition, charging never decreases consumed gas — the "gas only goes up"
property the IR enforces for free, made explicit. (No `init`-ordering needed: the
counter falls, so consumed = `init − remaining` rises.) -/
theorem consumed_mono (init st : IRState) (c : Nat)
    (hc : c ≤ st.gas.toNat) (hlt : c < 2 ^ 64) :
    consumed init st ≤ consumed init (st.charge c) := by
  unfold consumed
  rw [charge_gas_toNat st c hc hlt]
  omega

/-! ## Block / program accessors -/

/-- The block at label `L`, if present. -/
def Program.blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

/-- The statement at cursor `(L, pc)`, if present. -/
def Program.stmtAt (prog : Program) (L : Label) (pc : Nat) : Option Stmt := do
  let b ← prog.blockAt L
  b.stmts[pc]?

/-! ## The single-statement / terminator gas costs

Each construct's IR charge is the **sum** of the EVM charges of the opcodes it
lowers to (operand materialisation pushes charge `Gverylow` each, the effecting
opcode its own constant). The `Match` proof in `LirLean/Match.lean` checks these
against the per-opcode `Runs` rules step by step, so we keep them as named sums
rather than precomputed numbers. -/

/-- Gas charged for materialising an expression onto the stack (the oracle's
`verylow` per push/arith op the lowered byte-stream emits, the `sload`/`base`
costs for `SLOAD`/`GAS`). Recurses through `tmp` like `materialiseExpr`. `fuel`
bounds the recursion (well-formed SSA terminates). At `evmOracle` it reduces to the
old concrete sum. -/
def matCost (oracle : GasOracle) (defs : Tmp → Option Expr) : Nat → Expr → Nat
  | _,     .imm _   => gVerylow oracle                -- one PUSH32
  | 0,     _        => 0
  | f + 1, .tmp t   => match defs t with
                       | some e => matCost oracle defs f e
                       | none   => gVerylow oracle
  | f + 1, .add a b => matCost oracle defs f (.tmp b) + matCost oracle defs f (.tmp a) + gVerylow oracle
  | f + 1, .lt  a b => matCost oracle defs f (.tmp b) + matCost oracle defs f (.tmp a) + gVerylow oracle
  | f + 1, .sload k => matCost oracle defs f (.tmp k) + oracle.sload true   -- warm self-cell
  | _ + 1, .gas     => gBase oracle

end Lir
