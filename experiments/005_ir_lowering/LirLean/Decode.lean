import LirLean.Lowering
import LirLean.DecodeLower
import LirLean.Match

/-!
# LirLean — decode round-trip checks (C2 acceptance bar)

This module is the **executable, build-enforced** evidence that `lower` produces
`Evm.decode`-compatible bytecode for the full single-call IR surface. It defines a
worked single-call program `workedCall` exercising every C2 construct —

* storage arithmetic: `sload`, `sstore`, `add`, `lt`;
* exactly one external `Stmt.call` (value-free, calldata-free — the `callerProg`
  shape);
* `Term.branch` (and `Term.ret` / `Term.stop`);

— and then asserts, with `example … := by rfl`, that `Evm.decode (lower workedCall)
pc = expected` at **every** emitted instruction pc. Because these are `example`s
(not `#eval`s), a regression in `lower` that breaks decode-compatibility breaks the
build. No `sorry`, no `axiom`.

See `docs/ir-design.md` §4 ("Decode-compatibility — the acceptance bar").
-/

namespace Lir.Decode

open Evm Lir

-- `lower` is a deep computation (PUSH32 literals are 33 bytes each); the kernel
-- reduction in the `by rfl` decode checks below needs a higher recursion limit.
set_option maxRecDepth 100000

/-! ## A worked single-call program -/

private def t (n : Nat) : Tmp := ⟨n⟩
private def L (n : Nat) : Label := ⟨n⟩

/-- A worked program covering the full single-call C2 surface in one shot:
storage write/read, `add`, `lt`, one external `CALL`, a `branch` on the `lt`
result, and `ret` / `stop` terminators.

Block 0: `slot7 := 5; x := sload slot7; s := x + 9; c := s < 100;`
`call(callee = 0xCA11EE, gasFwd = 0xFFFFFFFF); branch c then=1 else=2`.
Block 1: `ret c`. Block 2: `stop`. -/
def workedCall : Program :=
  { entry := L 0
    blocks := #[
      { stmts := [
          .assign (t 0) (.imm 5),
          .assign (t 1) (.imm 7),
          .sstore (t 1) (t 0),
          .assign (t 2) (.sload (t 1)),
          .assign (t 3) (.imm 9),
          .assign (t 4) (.add (t 2) (t 3)),
          .assign (t 5) (.imm 100),
          .assign (t 6) (.lt (t 4) (t 5)),
          .assign (t 7) (.imm 0xCA11EE),
          .assign (t 8) (.imm 0xFFFFFFFF),
          .call { callee := t 7, gasFwd := t 8, resultTmp := none } ],
        term := .branch (t 6) (L 1) (L 2) },
      { stmts := [], term := .ret (t 6) },
      { stmts := [], term := .stop } ] }

/-- The lowered bytecode, named so the checks below all `decode` the same array. -/
def code : ByteArray := lower workedCall

/-! ## Block JUMPDEST offsets (the offset table is a concrete prefix sum)

Block 0 starts at 0, block 1 at 414, block 2 at 518. These are exactly the
immediates the `branch`/`jump` destination pushes must carry, checked below. -/

example : offsetTable (defsOf workedCall) (recomputeFuel workedCall) workedCall.blocks 0 = 0 := by rfl
example : offsetTable (defsOf workedCall) (recomputeFuel workedCall) workedCall.blocks 1 = 414 := by rfl
example : offsetTable (defsOf workedCall) (recomputeFuel workedCall) workedCall.blocks 2 = 518 := by rfl
example : code.size = 520 := by rfl

/-! ## Decode round-trip at every emitted pc

Each `example` pins one instruction. The constructors `decode` returns confirm the
exp003 form: `ADD = .ArithLogic .ADD`, `LT = .ArithLogic .LT`, `SLOAD/SSTORE/GAS/
JUMP/JUMPI/JUMPDEST = .Smsf …`, `STOP/RETURN/CALL = .System …`, pushes carry the
big-endian immediate and width. -/

/-! ### Block 0 — JUMPDEST, the storage-arith + CALL operand pushes, CALL -/

example : decode code 0   = some (.Smsf .JUMPDEST, none)             := by rfl
example : decode code 1   = some (.Push .PUSH32, some (5, 32))       := by rfl   -- value 5 (for sstore)
example : decode code 34  = some (.Push .PUSH32, some (7, 32))       := by rfl   -- key 7 (for sstore)
example : decode code 67  = some (.Smsf .SSTORE, none)               := by rfl
example : decode code 68  = some (.Push .PUSH32, some (0, 32))       := by rfl   -- CALL arg out_size
example : decode code 101 = some (.Push .PUSH32, some (0, 32))       := by rfl   -- CALL arg out_off
example : decode code 134 = some (.Push .PUSH32, some (0, 32))       := by rfl   -- CALL arg in_size
example : decode code 167 = some (.Push .PUSH32, some (0, 32))       := by rfl   -- CALL arg in_off
example : decode code 200 = some (.Push .PUSH32, some (0, 32))       := by rfl   -- CALL arg value
example : decode code 233 = some (.Push .PUSH32, some (0xCA11EE, 32)) := by rfl  -- CALL arg callee
example : decode code 266 = some (.Push .PUSH32, some (0xFFFFFFFF, 32)) := by rfl -- CALL arg gasFwd
example : decode code 299 = some (.System .CALL, none)               := by rfl

/-! ### Block 0 — the `branch` condition recompute, then JUMPI/JUMP

`branch (t 6) …` re-materialises `t 6 = (sload 7 + 9) < 100`. Materialisation is
operands-then-op with the second operand pushed first, so the literal order is:
PUSH32 100 (the `lt`'s right operand `t5`), then PUSH32 9 (`add`'s right operand
`t3`), then PUSH32 7 (`sload`'s key `t1`), then SLOAD, ADD, LT — then
`PUSH4 thenOff; JUMPI; PUSH4 elseOff; JUMP`. -/

example : decode code 300 = some (.Push .PUSH32, some (100, 32))     := by rfl   -- lt operand (t5)
example : decode code 333 = some (.Push .PUSH32, some (9, 32))       := by rfl   -- add operand (t3)
example : decode code 366 = some (.Push .PUSH32, some (7, 32))       := by rfl   -- sload key (t1)
example : decode code 399 = some (.Smsf .SLOAD, none)                := by rfl
example : decode code 400 = some (.ArithLogic .ADD, none)            := by rfl
example : decode code 401 = some (.ArithLogic .LT, none)             := by rfl
example : decode code 402 = some (.Push .PUSH4, some (414, 4))       := by rfl   -- then-block offset
example : decode code 407 = some (.Smsf .JUMPI, none)                := by rfl
example : decode code 408 = some (.Push .PUSH4, some (518, 4))       := by rfl   -- else-block offset
example : decode code 413 = some (.Smsf .JUMP, none)                 := by rfl

/-! ### Block 1 — JUMPDEST, the `ret` condition recompute, RETURN -/

example : decode code 414 = some (.Smsf .JUMPDEST, none)             := by rfl
example : decode code 415 = some (.Push .PUSH32, some (100, 32))     := by rfl  -- lt operand (t5)
example : decode code 448 = some (.Push .PUSH32, some (9, 32))       := by rfl  -- add operand (t3)
example : decode code 481 = some (.Push .PUSH32, some (7, 32))       := by rfl  -- sload key (t1)
example : decode code 514 = some (.Smsf .SLOAD, none)                := by rfl
example : decode code 515 = some (.ArithLogic .ADD, none)            := by rfl
example : decode code 516 = some (.ArithLogic .LT, none)             := by rfl
example : decode code 517 = some (.System .RETURN, none)             := by rfl

/-! ### Block 2 — JUMPDEST, STOP -/

example : decode code 518 = some (.Smsf .JUMPDEST, none)             := by rfl
example : decode code 519 = some (.System .STOP, none)               := by rfl

/-! ## The branch destinations are legal jump targets

The two branch-destination immediates (414, 518) decode to `JUMPDEST` — proven
axiom-cleanly by the `decode code 402 = PUSH4 414`, `decode code 408 = PUSH4 518`
checks above together with `decode code 414 = JUMPDEST` and
`decode code 518 = JUMPDEST`. So the lowered `JUMPI`/`JUMP` land on real
`JUMPDEST`s — a prerequisite for exp003's jump steps. (We do not assert
`validJumpDests` directly: it is a `partial def`, so the only way to evaluate it in
a proof is `native_decide`, which would pull in a native-reduction axiom and break
the axiom-clean bar. The four `rfl` decode checks give the same guarantee for the
two destinations this program actually uses.) -/

/-! ## The generic `decode_lower` lemmas subsume the per-pc `rfl`s

`LirLean/DecodeLower.lean` factors the whole-array `rfl` checks above into two
program-independent lemmas (`decode_lower_nonpush` / `decode_lower_push`): a decode
fact follows from a *list-local* statement about `flatBytes workedCall` — the byte
at the pc (`flatBytes …[n]? = some opByte`) and, for a PUSH, the
`uInt256OfByteArray` of the immediate sublist — each itself a small `rfl`/`decide`.
These two examples re-derive a non-push and a push instruction *through* the generic
lemmas (rather than by a single whole-array kernel reduction), confirming the
infrastructure connects end-to-end on the worked program. -/

/-- JUMPDEST at pc 0, via the generic non-push lemma. -/
example : decode (lower workedCall) (UInt32.ofNat 0) = some (.Smsf .JUMPDEST, .none) :=
  decode_lower_nonpush workedCall 0 0x5b (by norm_num) rfl rfl

/-- `PUSH32 5` at pc 1 (the `sstore` value), via the generic push lemma. -/
example : decode (lower workedCall) (UInt32.ofNat 1) = some (.Push .PUSH32, some (5, 32)) :=
  decode_lower_push workedCall 1 0x7f 32 5 (by norm_num) rfl rfl (by decide) (by rfl)

/-! ## `M1` at a *symbolic* `pcOf` cursor — the offset-table discharge

The decode facts above pin a *literal* pc (`0`, `1`). The simulation engine needs
decode at the *symbolic* offset-table address `pcOf prog L pc`. This example
discharges that for the `sstore` cursor (statement `2` of block `0`) of `workedCall`
**through the offset-table arithmetic** — `pcOf` → `flatBytes_at_pcOf`
(`Layout.stmt_byte_anchor`, the prefix-sum decomposition) → `decode_lower_push`. No
whole-array `rfl` and no literal pc: the byte at `pcOf workedCall ⟨0⟩ 2` is shown to
be the head of `emitStmt (.sstore …)` (a `PUSH32`) by the generic byte-layout lemmas,
then decoded. This is the program-global `M1` brick the engine consumes at each
statement step. -/
example :
    decode (lower workedCall) (UInt32.ofNat (pcOf workedCall ⟨0⟩ 2))
      = some (.Push .PUSH32, some (5, 32)) := by
  have hbyte : (flatBytes workedCall)[pcOf workedCall ⟨0⟩ 2]? = some 0x7f := by
    rw [flatBytes_at_pcOf workedCall ⟨0⟩ _ 2 (.sstore ⟨1⟩ ⟨0⟩) rfl rfl (by decide)]; rfl
  exact decode_lower_push workedCall _ 0x7f 32 5 (by decide) hbyte rfl (by decide) (by rfl)

end Lir.Decode
