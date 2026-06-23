import LirLean.IR
import Evm

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
  charge is the same `UInt64.ofNat <constant>` subtraction the EVM post-frame
  performs.
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

/-! ## Gas charges (the same constants the lowered opcodes charge) -/

/-- Gas charged by `add`/`lt`/(operand) materialisation per arithmetic op — the
EVM `Gverylow = 3`. Mirrors `binOpPost`'s charge. -/
def gVerylow : Nat := GasConstants.Gverylow

/-- Gas charged by `GAS` — the EVM `Gbase = 2`. Mirrors `gasPost`'s charge. -/
def gBase : Nat := GasConstants.Gbase

/-- Gas charged by `JUMP` — the EVM `Gmid = 8`. Mirrors `jumpPost`'s charge. -/
def gMid : Nat := GasConstants.Gmid

/-- Gas charged by `JUMPI` — the EVM `Ghigh = 10`. Mirrors the jump posts. -/
def gHigh : Nat := GasConstants.Ghigh

/-! ## The IR machine state -/

/-- The IR register/storage/gas state. `storage` is the self account's storage
read through the observable lens; `gas` is a `UInt64` so it equals
`fr.exec.gasAvailable` exactly (the `M4` clause of `Match`). -/
structure IRState where
  /-- Register file: each temporary's bound value (if assigned). -/
  locals  : Tmp → Option Word
  /-- The self account's storage (observable lens). -/
  storage : Word → Word
  /-- Remaining gas — a `UInt64`, equal to `gasAvailable` under `Match`. -/
  gas     : UInt64

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

/-- Write a storage cell. -/
def IRState.setStorage (st : IRState) (k v : Word) : IRState :=
  { st with storage := fun k' => if k' = k then v else st.storage k' }

/-- Charge `c` gas (as `UInt64.ofNat`), mirroring the EVM post-frames'
`gasAvailable - UInt64.ofNat c`. -/
def IRState.charge (st : IRState) (c : Nat) : IRState :=
  { st with gas := st.gas - UInt64.ofNat c }

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

/-- Gas charged for materialising an expression onto the stack (the `Gverylow`
per push/arith op the lowered byte-stream emits). Recurses through `tmp` like
`materialiseExpr`. `fuel` bounds the recursion (well-formed SSA terminates). -/
def matCost (defs : Tmp → Option Expr) : Nat → Expr → Nat
  | _,     .imm _   => gVerylow                       -- one PUSH32
  | 0,     _        => 0
  | f + 1, .tmp t   => match defs t with
                       | some e => matCost defs f e
                       | none   => gVerylow
  | f + 1, .add a b => matCost defs f (.tmp b) + matCost defs f (.tmp a) + gVerylow
  | f + 1, .lt  a b => matCost defs f (.tmp b) + matCost defs f (.tmp a) + gVerylow
  | f + 1, .sload k => matCost defs f (.tmp k) + Evm.sloadCost true   -- warm self-cell
  | _ + 1, .gas     => gBase

end Lir
