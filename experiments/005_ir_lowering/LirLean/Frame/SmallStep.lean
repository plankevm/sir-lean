import LirLean.Spec.IR
import Evm

/-!
# LirLean — small-step IR semantics (C3)

This module fixes the IR's operational state (`docs/ir-design.md` §3), the primary
relation the lowering-preservation proof simulates. The choice is **small-step** so
each IR step lines up with one exp003 `Runs` segment over the lowered bytecode.

The storage effects deliberately **mirror exp003's post-frame transformers**
(`sloadPost`, `sstorePost`) so the `Match` invariant's storage clause (`M3`) is
preserved step-by-step by `rfl`-clean arithmetic — see `Frame/Match.lean`.

There is **no gas counter / cost accounting**: the IR does not model opcode cost.
(The gas-free observable line lives in `LirLean/V2/*`, where `Expr.gas` is a value
*supplied by an external gas stream*, never computed from a counter.)

## Design notes

* `IRState.storage : Word → Word` mirrors the self account's storage *through the
  observable lens* (`find?/lookupStorage`) that `M3` and exp003's
  `sstoreFrame_storage_self` / `sloadFrame_storage_self` use.
* Expression evaluation `evalExpr` is total (`Option`) and recompute-friendly: it
  reads `locals` for `tmp` and the storage map for `sload`. The arithmetic
  functions are exp003's `UInt256.add` / `UInt256.lt`, so the value the IR computes
  is *definitionally* the value the lowered opcode pushes.
-/

namespace Lir

open Evm

/-! ## The IR machine state -/

/-- The IR register/storage state. `storage` is the self account's storage read
through the observable lens.

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
  /-- The most recent external CALL's 0/1 success word, if a CALL has run. The one
  value not recomputable from an `Expr`; written by `IRState.applyCall`, read once
  into `locals` by `IRState.bindCallResult` at the call's `resultTmp`. -/
  callResult : Option Word := none
  /-- The most recent external CREATE/CREATE2's deployed-address-or-`0` word, if a
  CREATE has run. The `callResult`-analogue slot for the CREATE line: like the CALL
  success word it is dynamic (depends on the child run), hence not recomputable from
  an `Expr`; written by `IRState.applyCreate` (`Frame/Create.lean`), read once into
  `locals` by `IRState.bindCreateResult` at the create's `resultTmp`. -/
  createResult : Option Word := none

/-- An IR halt result (the terminator outcomes). -/
inductive IRHalt where
  /-- `STOP` — success, no output word. -/
  | stopped
  /-- `RETURN t` — success returning the word `t` evaluated to. -/
  | returned (w : Word)
deriving DecidableEq, Repr

/-! ## Expression evaluation

`evalExpr st e` is the IR value of `e` in state `st`. It is total via `Option`
(an undefined `tmp` yields `none`). The arithmetic mirrors exp003 exactly:
`add → UInt256.add`, `lt → UInt256.lt`, `sload → storage lens`. This makes the IR
value definitionally equal to the word the lowered opcode leaves on the stack.

`Expr.gas` has **no** value here: the gas-free v1 state carries no counter to read
it from. Gas introspection is the v2 line's concern (`LirLean/V2/*`), where the
`GAS` value is *supplied by an external gas stream*, not computed. -/

/-- Evaluate an expression to a word (total via `Option`; `none` = undefined tmp or
`Expr.gas`, which has no counter to read in the gas-free v1 state). -/
def evalExpr (st : IRState) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.storage key)
  | .gas     => none
  | .slot _ => none

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

/-- **Bind the create-result slot into `locals` at a `resultTmp`.** The CREATE twin
of `bindCallResult`: the dynamic deployed-address-or-`0` word lives in `createResult`
(the one non-recomputable value the CREATE pushes); this binds it *once* to the
create's `resultTmp` — after which it is an ordinary `locals` value that
recompute-on-use materialises via `Expr.tmp`. When the spec binds no result
(`resultTmp = none`) or no CREATE has run (`createResult = none`), `locals` is
unchanged. This is the read path for `CreateSpec.resultTmp`. -/
def IRState.bindCreateResult (st : IRState) : Option Tmp → IRState
  | none   => st
  | some t => match st.createResult with
              | none   => st
              | some w => st.setLocal t w

/-- Write a storage cell. -/
def IRState.setStorage (st : IRState) (k v : Word) : IRState :=
  { st with storage := fun k' => if k' = k then v else st.storage k' }

/-! ## Block / program accessors -/

/-- The block at label `L`, if present. -/
def Program.blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

end Lir
