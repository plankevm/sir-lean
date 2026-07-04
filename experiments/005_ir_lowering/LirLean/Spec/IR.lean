import Evm

/-!
# LirLean — the high-level IR (datatypes)

The fresh "Lowered IR" of experiment 005. See `docs/ir-design.md` §1 for why this
is a fresh IR rather than an extension of exp002's `SirLean` (word size, EVM-state
coupling, no CALL, no gas, SSA scaffolding) and §2 for the grammar.

Values are EVM words (`Evm.UInt256`), so the IR and exp003's bytecode layer speak
the same word type. The IR is a register (temporary) machine over named locals,
organised as a CFG of basic blocks — each a straight-line statement list ending in
a branch/return terminator. Branching (`Term.branch`) is what makes
gas-introspection reasoning (`Expr.gas`) meaningful.

This file is **datatypes only** (the C1 deliverable). The small-step semantics
(`IRStep`) and the lowering live in their own modules.
-/

namespace Lir

open Evm

/-- A 256-bit EVM word — the single value type of the IR. -/
abbrev Word := UInt256

/-- A local / temporary (an SSA-ish register name). -/
structure Tmp where
  id : Nat
deriving DecidableEq, Repr

/-- A basic-block label (index into a program's block array). -/
structure Label where
  idx : Nat
deriving DecidableEq, Repr

/-- The external-CALL payload. C1 models exp003's value-free, calldata-free call
(the `callerProg` shape its boundary bridge already supports): a callee address
and a gas-to-forward temporary (which may be `Expr.gas`-derived — that is the
gas-introspection coupling), plus an optional temporary to receive CALL's 0/1
success flag. Value, arg-window and ret-window are fixed to zero for C1; the
richer shape is future work (see `docs/ir-design.md` §2). -/
structure CallSpec where
  /-- Temporary holding the callee address (as a word). -/
  callee : Tmp
  /-- Temporary holding the gas to forward to the callee. -/
  gasFwd : Tmp
  /-- Where to bind the CALL success flag (`1`/`0`), if anywhere. -/
  resultTmp : Option Tmp
deriving DecidableEq, Repr

/-- The external-CREATE / CREATE2 payload — the twin of `CallSpec`. C1 models
exp003's empty-init-code create (`beginCreate`, `Create.lean:31`): the value to
endow, and the init-code memory window (`initOffset`/`initSize`) are carried as
temporaries but fixed to zero for the first cut, so the richer (nonzero init-code)
shape needs no re-shape later. `salt` distinguishes CREATE (`none`) from CREATE2
(`some`) **from day one** — the single field that makes CREATE2 a lowering delta,
not a rebuild. `resultTmp` receives the deployed-address-or-`0` word CREATE pushes
(`createAddrOrZero`, `Frame/Create.lean:75`). -/
structure CreateSpec where
  /-- Temporary holding the value (wei) to endow the new contract with. -/
  value : Tmp
  /-- Temporary holding the init-code memory offset. -/
  initOffset : Tmp
  /-- Temporary holding the init-code memory size. -/
  initSize : Tmp
  /-- The CREATE2 salt, if this is a CREATE2 (`none` = CREATE). -/
  salt : Option Tmp
  /-- Where to bind the pushed deployed-address-or-`0` word, if anywhere. -/
  resultTmp : Option Tmp
deriving DecidableEq, Repr

/-- A pure expression. `gas` is first-class — the IR can observe remaining gas and
later branch on it (`docs/ir-design.md` §2 "Why `gas` belongs in the IR"). -/
inductive Expr where
  /-- A literal 256-bit constant (lowers to `PUSH32 w`). -/
  | imm   (w : Word)
  /-- Read a local. -/
  | tmp   (t : Tmp)
  /-- `a + b` (lowers to `ADD`). -/
  | add   (a b : Tmp)
  /-- `a < b → 0/1` (lowers to `LT`). -/
  | lt    (a b : Tmp)
  /-- `storage[key]` (lowers to `SLOAD`). -/
  | sload (key : Tmp)
  /-- Remaining gas (lowers to `GAS`) — gas introspection. -/
  | gas
  /-- Lowering-only marker: "this tmp lives in EVM memory at `slot`; MLOAD it" — a
  generic spill-load (the `.slot` half of the remat/spill policy). Today produced by
  `allocate`/`defsOf` only for call results (Route B, the call-result value channel);
  in later phases any spilled value (gas, sload) reuses it. Never produced by a source
  program and never evaluated by the IR (`V2.evalExpr (.slot _) = none`). See
  `docs/uniform-spill-alloc-plan.md` and `docs/calls-value-channel-plan.md`. -/
  | slot (slot : Nat)
deriving DecidableEq, Repr

/-- A statement: a sequenced effect within a basic block. -/
inductive Stmt where
  /-- `t := e`. -/
  | assign (t : Tmp) (e : Expr)
  /-- `storage[key] := value` (lowers to `SSTORE`). -/
  | sstore (key value : Tmp)
  /-- An external CALL (see `CallSpec`). The C4 multi-call question lives here:
  exp003's `messageCall_call_runs` supports only **one** of these between two
  call-free `Runs` segments — see `docs/ir-design.md` §5. -/
  | call   (cs : CallSpec)
  /-- An external CREATE / CREATE2 (see `CreateSpec`). The twin of `Stmt.call`;
  the reference layer (`beginCreate`/`resumeAfterCreate`) already unifies both
  kinds — see `docs/create/BUILD-PLAN.md`. -/
  | create (cs : CreateSpec)
deriving DecidableEq, Repr

/-- A block terminator: the control-flow edge(s) leaving a block. -/
inductive Term where
  /-- RETURN the word in `t` (the block's exit word / code). -/
  | ret    (t : Tmp)
  /-- STOP. -/
  | stop
  /-- Unconditional branch to `dst` (lowers to `PUSH4 off; JUMP`). -/
  | jump   (dst : Label)
  /-- `if t ≠ 0 then thenL else elseL` (lowers to `PUSH4 off; JUMPI; …`). The
  conditional branch — gas introspection becomes meaningful when `t` is computed
  from `Expr.gas`. -/
  | branch (cond : Tmp) (thenL elseL : Label)
deriving DecidableEq, Repr

/-- A basic block: a straight-line statement list ending in a terminator. -/
structure Block where
  stmts : List Stmt
  term  : Term
deriving Repr

/-- A program: a finite array of basic blocks plus an entry label. -/
structure Program where
  blocks : Array Block
  entry  : Label
deriving Repr

end Lir
