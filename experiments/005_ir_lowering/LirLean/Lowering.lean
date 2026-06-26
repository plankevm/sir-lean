import LirLean.IR
import Evm

/-!
# LirLean — lowering IR → EVM bytecode (C2: decode-compatible single-call lowering)

`lower : Program → ByteArray` emits opcode bytes that exp003's `Evm.decode`
(`EVMLean/Evm/Semantics/Decode.lean`) reads back as the intended opcode stream.
See `docs/ir-design.md` §4 for the layout (per-block `JUMPDEST`, two-pass offset
table, uniform `PUSH4` destination width) and the per-op opcode templates.

## C2 scope (this milestone)

The lowering now **materialises operands onto the stack** (recompute-on-use,
mirroring exp003's worked programs which push each literal immediately before the
consuming opcode — `seqProgram`, `callerProg`). So the emitted byte stream is a
real, runnable EVM sequence, not just a sequence of consuming opcodes. The full
single-call IR surface lowers:

* storage arithmetic — `sload` / `sstore` / `add` / `lt`;
* exactly **one** external `Stmt.call` (the value-free, calldata-free `callerProg`
  shape exp003's `messageCall_call_runs` already supports);
* `Term.branch` (lowered structurally — `PUSH4 thenOff; JUMPI; PUSH4 elseOff; JUMP`).

Decode-compatibility is **build-enforced** by the `example`/`#eval` round-trip
checks in `LirLean/Decode.lean`: `Evm.decode (lower worked) pc = expected` for a
worked single-call program, asserted `by decide`/`by rfl` over every emitted pc.

No theorem about the *semantics* (the simulation / preservation statement) is
proved here — that is C3. Nothing in this file is `sorry`- or `axiom`-backed; it
is executable byte emission only.

Opcode bytes (confirmed against `EVMLean/Evm/Instr.lean`):
`STOP 0x00`, `ADD 0x01`, `LT 0x10`, `SLOAD 0x54`, `SSTORE 0x55`, `JUMP 0x56`,
`JUMPI 0x57`, `GAS 0x5a`, `JUMPDEST 0x5b`, `PUSH1 0x60`, `PUSH4 0x63`,
`PUSH32 0x7f`, `CALL 0xf1`, `RETURN 0xf3`.
-/

namespace Lir

open Evm

/-! ## Opcode bytes (a thin local table, kept in sync with `Evm.Instr`) -/

namespace Byte
def stop     : UInt8 := 0x00
def add      : UInt8 := 0x01
def lt       : UInt8 := 0x10
def pop      : UInt8 := 0x50
def mload    : UInt8 := 0x51
def mstore   : UInt8 := 0x52
def sload    : UInt8 := 0x54
def sstore   : UInt8 := 0x55
def jump     : UInt8 := 0x56
def jumpi    : UInt8 := 0x57
def gas      : UInt8 := 0x5a
def jumpdest : UInt8 := 0x5b
def push4    : UInt8 := 0x63
def push32   : UInt8 := 0x7f
def call     : UInt8 := 0xf1
def ret      : UInt8 := 0xf3
end Byte

/-- Big-endian 4-byte encoding of a `Nat` jump destination (low 32 bits). Read
back by `decode` via `uInt256OfByteArray` (which is big-endian), so the immediate
round-trips to `UInt256.ofNat (n % 2^32)`. -/
def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8),  UInt8.ofNat n ]

/-- 32-byte big-endian encoding of a word (for `PUSH32 imm`). -/
def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

/-! ## Operand materialisation (recompute-on-use)

The IR is a register machine; lowering materialises each operand onto the EVM
stack by re-emitting the push-sequence of its defining expression. We thread a
`defs : Tmp → Option Expr` environment recording each `assign`'s right-hand side,
and `materialise` walks it. This is the "recompute-on-use" scheme of
`docs/ir-design.md` §4: an `assign` itself emits **no** bytes; the work happens at
the consuming opcode, exactly as exp003's programs push a literal immediately
before consuming it.

`fuel` bounds the recursion structurally (an IR with cyclic tmp definitions is
ill-formed; well-formed SSA-ish programs terminate). It is a lowering convenience,
never surfaced in a theorem. -/

/-- Emit a literal push (`PUSH32 w`). -/
def emitImm (w : Word) : List UInt8 := Byte.push32 :: wordBytesBE w

/-- Private memory slot for a call-result tmp. Unique per tmp id; SSA single-binding
⇒ write-once. Base offset keeps slots clear of the (zero-size) CALL windows. -/
def slotOf (t : Tmp) : Nat := t.id * 32

/-- Emit a destination push (`PUSH4 off`). -/
def emitDest (off : Nat) : List UInt8 := Byte.push4 :: offsetBytesBE off

/-- Materialise the value of expression `e` onto the stack: emit the push-sequence
that leaves `e`'s value on top. Operands of binary ops are pushed in reverse so
the first operand ends up on top (`a` on top of `b`). -/
def materialiseExpr (defs : Tmp → Option Expr) : Nat → Expr → List UInt8
  | _,      .imm w  => emitImm w
  | _,      .callResult slot => emitImm (UInt256.ofNat slot) ++ [Byte.mload]
  | 0,      _       => []                       -- fuel exhausted (ill-formed IR)
  | f + 1,  .tmp t  =>
      match defs t with
      | some e => materialiseExpr defs f e
      | none   => emitImm (0 : Word)            -- undefined tmp → conservative 0
  | f + 1,  .add a b =>
      materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
  | f + 1,  .lt a b =>
      materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
  | f + 1,  .sload k =>
      materialiseExpr defs f (.tmp k) ++ [Byte.sload]
  | _ + 1,  .gas    => [Byte.gas]

/-- Materialise a temporary onto the stack. -/
def materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) : List UInt8 :=
  materialiseExpr defs fuel (.tmp t)

/-- A generous recompute-fuel bound: the number of `assign`s seen so far bounds the
definition-chain depth of any tmp. We pass the program's total statement count. -/
def recomputeFuel (prog : Program) : Nat :=
  (prog.blocks.toList.map (fun b => b.stmts.length)).sum + 1

/-! ## Per-construct emission -/

/-- Emit the opcode bytes for one statement, given the `defs` environment and
recompute fuel. `assign` emits nothing (recompute-on-use); effectful statements
materialise their operands then emit the consuming opcode.

* `sstore key value` → materialise `value`, materialise `key`, `SSTORE`
  (leaving `key :: value :: rest` — the stack shape exp003's `runs_sstore`
  expects).
* `call cs` → push the seven CALL args (value-free, zero-memory window:
  `out_size, out_off, in_size, in_off, value`, then `callee`, then `gasFwd` on
  top — the `callerProg` order), then `CALL`. The 0/1 success flag CALL pushes is
  left on the stack for a following `assign`/use of `resultTmp`. -/
def emitStmt (defs : Tmp → Option Expr) (fuel : Nat) : Stmt → List UInt8
  | .assign _ _ => []                            -- recompute-on-use: no bytes here
  | .sstore key value =>
      materialise defs fuel value ++ materialise defs fuel key ++ [Byte.sstore]
  | .call cs =>
      -- seven args, bottom-to-top: out_size, out_off, in_size, in_off, value,
      -- callee, gasFwd. Zero-memory + value-free ⇒ the first five are 0.
      emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ materialise defs fuel cs.callee
      ++ materialise defs fuel cs.gasFwd
      ++ [Byte.call]
      ++ (match cs.resultTmp with
          | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]   -- PUSH slot; MSTORE
          | none   => [Byte.pop])                                          -- discard flag

/-- Emit the opcode bytes for a terminator, given the `defs` environment, fuel, and
the resolved offset table `labelOff` (label index → byte offset of its
`JUMPDEST`).

`ret t` materialises `t`, then pushes the two zero `RETURN`-window operands
(`offset = 0`, `size = 0`) so the `RETURN` is well-formed: `RETURN` pops **two** words,
but `materialise t` leaves only one — without the two `PUSH32 0` the stack would
underflow. `RETURN(0,0)` returns the empty output and halts; the returned scalar is out
of the world-channel scope (only the storage delta is observed), so the residual
materialised value below the window is discarded with the frame. -/
def emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat) : Term → List UInt8
  | .ret t              => materialise defs fuel t ++ emitImm 0 ++ emitImm 0 ++ [Byte.ret]
  | .stop               => [Byte.stop]
  | .jump dst           => emitDest (labelOff dst.idx) ++ [Byte.jump]
  | .branch cond thenL elseL =>
      materialise defs fuel cond
      ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
      ++ emitDest (labelOff elseL.idx) ++ [Byte.jump]

/-! ## Definition environment

Recompute-on-use needs each tmp's defining expression. We build it from a
*program-global* scan of all `assign`s (SSA-ish: each tmp assigned once). For C2's
single-block / single-path worked programs this is exact; richer scoping is a C3
refinement. -/

/-- The program-global `Tmp → Option Expr` map: the last `assign` to each tmp. -/
def defsOf (prog : Program) : Tmp → Option Expr :=
  let pairs : List (Tmp × Expr) :=
    prog.blocks.toList.flatMap (fun b =>
      b.stmts.filterMap (fun
        | .assign t e          => some (t, e)
        | .call ⟨_, _, some t⟩ => some (t, Expr.callResult (slotOf t))
        | _                    => none))
  fun t => (pairs.find? (fun p => p.1 == t)).map (·.2)

/-! ## Block layout (two-pass offset table) -/

/-- Bytes of one block, *excluding* the leading `JUMPDEST`, given the `defs`
environment, fuel, and offset table. Pass 1 measures lengths with a zero offset
table; pass 2 emits with the real table. Both pass through the same function, and
`emitDest` always emits a fixed-width `PUSH4 <off>` (5 bytes) regardless of the
offset value, so the two passes agree on lengths. -/
def emitBlockBody (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) : List UInt8 :=
  (b.stmts.flatMap (emitStmt defs fuel)) ++ emitTerm defs fuel labelOff b.term

/-- Length of a lowered block (leading `JUMPDEST` + body). Independent of the
offset table because destination pushes have fixed width. -/
def blockLen (defs : Tmp → Option Expr) (fuel : Nat) (b : Block) : Nat :=
  1 + (emitBlockBody defs fuel (fun _ => 0) b).length

/-- The offset table: byte offset of block `i`'s `JUMPDEST`, as a prefix sum of
block lengths over `blocks[0..i)`. -/
def offsetTable (defs : Tmp → Option Expr) (fuel : Nat) (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map (blockLen defs fuel)).sum

/-- **The lowering.** `lower prog` is the concatenation, in block order, of each
block lowered as `JUMPDEST :: emitBlockBody`. Branch destinations are resolved via
`offsetTable`. The result is a `ByteArray` that `Evm.decode` reads back as the
intended opcode stream (verified executably in `LirLean/Decode.lean`). -/
def lower (prog : Program) : ByteArray :=
  let defs := defsOf prog
  let fuel := recomputeFuel prog
  let labelOff := offsetTable defs fuel prog.blocks
  let bytes : List UInt8 :=
    prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody defs fuel labelOff b)
  ⟨bytes.toArray⟩

end Lir
