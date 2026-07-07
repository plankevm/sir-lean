import LirLean.Spec.IR
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

Decode-compatibility is established by the decode-anchor theorems (A1/A2/A3) in
`Decode/DecodeAnchors.lean`: `Evm.decode (lower prog) pc = expected` at every
statement head, intra-statement cursor, and terminator offset.

No theorem about the *semantics* (the simulation / preservation statement) is
proved here — that is C3. Nothing in this file is `sorry`- or `axiom`-backed; it
is executable byte emission only.

Opcode bytes (confirmed against `EVMLean/Evm/Instr.lean`):
`STOP 0x00`, `ADD 0x01`, `LT 0x10`, `SLOAD 0x54`, `SSTORE 0x55`, `JUMP 0x56`,
`JUMPI 0x57`, `GAS 0x5a`, `JUMPDEST 0x5b`, `PUSH1 0x60`, `PUSH4 0x63`,
`PUSH32 0x7f`, `CREATE 0xf0`, `CALL 0xf1`, `CREATE2 0xf5`, `RETURN 0xf3`.
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
def create   : UInt8 := 0xf0
def call     : UInt8 := 0xf1
def create2  : UInt8 := 0xf5
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

/-! ## Allocation policy — where each tmp lives (`Loc` / `Alloc`)

The lowering's per-value decision is a single *policy* choice — **rematerialise or
spill** (`docs/uniform-spill-alloc-plan.md` §2.1). `Loc` names the two answers; an
`Alloc` is the per-tmp policy. Today the policy reproduces the recompute-on-use
behaviour exactly (pure exprs ⇒ `remat`, call results ⇒ `slot`); later phases route
gas/sload to `slot` too. The mechanism (`emit`) is uniform and consults only the
`Alloc`.

`Alloc` is `Tmp → Option Loc` (partial) rather than the total `Tmp → Loc` of the
design sketch: a tmp with **no** definition (used but never assigned — impossible in
a `WellFormed` program) has *no* location, mirroring `defsOf`'s `none`. This keeps
`allocate` a faithful re-presentation of `defsOf` (`allocate_toDefs`). A later phase
can switch to the total shape once undefined tmps are ruled out by `WellFormed`. -/

/-- Where a tmp's value lives: rematerialise its defining expression on each use, or
spill it to a fixed memory slot and `MLOAD` on use. -/
inductive Loc where
  /-- Recompute the defining expression `e` at each use (pure, cheap, stable values). -/
  | remat (e : Expr)
  /-- The value lives in EVM memory at `slot n`; load it (`PUSH n; MLOAD`) on use. -/
  | slot  (n : Nat)
deriving DecidableEq, Repr

/-- A per-tmp allocation policy. Partial (`Option`): a tmp with no definition has no
location (the `defsOf … = none` case). -/
abbrev Alloc := Tmp → Option Loc

/-- The defining-expression a `Loc` materialises as: `remat e` recomputes `e`; a
`slot n` is the generic spill-load `Expr.slot n` (`PUSH n; MLOAD`). -/
def Loc.toDef : Loc → Expr
  | .remat e => e
  | .slot  n => .slot n

/-- View an `Alloc` as the `defs : Tmp → Option Expr` environment the byte mechanism
consumes: each located tmp materialises its `Loc.toDef`. -/
def Alloc.toDefs (a : Alloc) : Tmp → Option Expr := fun t => (a t).map Loc.toDef

/-! ## Operand materialisation (recompute-on-use)

The IR is a register machine; lowering materialises each operand onto the EVM
stack by re-emitting the push-sequence of its defining expression. We thread a
`defs : Tmp → Option Expr` environment recording each tmp's location (an `Alloc`,
read through `Alloc.toDefs`), and `materialise` walks it. This is the
"recompute-on-use" scheme of `docs/ir-design.md` §4: an `assign` itself emits **no**
bytes; the work happens at the consuming opcode, exactly as exp003's programs push a
literal immediately before consuming it.

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
  | _,      .slot slot => emitImm (UInt256.ofNat slot) ++ [Byte.mload]
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
  | .assign t e =>
      -- **Alloc-native def-site.** A tmp the allocation spills (`defs t = some (.slot n)`:
      -- gas, in Phase B) is computed **once** here and stashed to its memory slot
      -- (`materialise(e) ++ PUSH n ++ MSTORE`); for gas, `materialise .gas = [GAS]`, so the
      -- stash is `[GAS] ++ PUSH n ++ MSTORE`. A rematerialised tmp emits **no** bytes — its
      -- value is recomputed at each use.
      match defs t with
      | some (.slot n) =>
          materialiseExpr defs fuel e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
      | _ => []
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
  | .create cs =>
      -- CREATE / CREATE2 (empty-init first cut: value/initOffset/initSize = 0 via `emitImm 0`).
      -- Push the three create args, then — if `cs.salt = some s` — materialise the salt and emit
      -- `CREATE2` (0xf5); else emit `CREATE` (0xf0). The pushed deployed-address-or-0 word is
      -- stashed to `slotOf t` (byte-identical to the CALL result stash) if `resultTmp = some t`,
      -- else discarded (`POP`). See `docs/create/BUILD-PLAN.md` §2 Step 4.
      emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ (match cs.salt with
          | some s => materialise defs fuel s ++ [Byte.create2]
          | none   => [Byte.create])
      ++ (match cs.resultTmp with
          | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]   -- PUSH slot; MSTORE
          | none   => [Byte.pop])                                          -- discard address

/-- Emit the opcode bytes for a terminator, given the `defs` environment, fuel, and
the resolved offset table `labelOff` (label index → byte offset of its
`JUMPDEST`).

`ret t` materialises `t` (leaving the returned word `vw` on top), stashes it to
memory at offset `0` (`PUSH32 0; MSTORE` — stack `0 :: vw`, `MSTORE` pops `addr = 0`,
`val = vw`), then returns that 32-byte window (`PUSH32 32; PUSH32 0; RETURN` — stack
`0 :: 32`, `RETURN` pops `offset = 0`, `size = 32`). So `RETURN(0, 32)` returns exactly
`vw`'s big-endian bytes — the returned value is now the observed halt result (`observe`
reads it back as `returned vw`), not discarded. The tail after `materialise t` is
`PUSH32 0 ++ MSTORE ++ PUSH32 32 ++ PUSH32 0 ++ RETURN`, i.e. `33 + 1 + 33 + 33 + 1 = 101`
bytes. -/
def emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat) : Term → List UInt8
  | .ret t              => materialise defs fuel t
                             ++ emitImm 0 ++ [Byte.mstore]
                             ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]
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

/-- The program-global `Tmp → Option Expr` map: the last `assign` to each tmp, with the
three **non-recomputable** defining expressions routed to the spill-load `Expr.slot`:

* a **gas** assign `assign t .gas` registers `t` as `Expr.slot (slotOf t)` — the gas value
  is read **once** at the def-site stash (`emitStmt .assign`) and reused from memory on each
  use, never re-emitting `GAS` (Phase B; `docs/uniform-spill-alloc-plan.md` §6);
* an **sload** assign `assign t (.sload k)` registers `t` as `Expr.slot (slotOf t)` — the
  SLOAD value (and its cold/warm warmth charge) is read **once** at the def-site stash
  (`materialise k ++ [SLOAD] ++ PUSH slot ++ MSTORE`) and reused from memory (`MLOAD`) on
  each use, never re-emitting `SLOAD` (Phase C; `docs/uniform-spill-alloc-plan.md` §6). This
  retires the `SloadRealises` warmth universal: the warmth cost is the single def-site read;
* a **call result** `call ⟨_, _, some t⟩` registers `t` as `Expr.slot (slotOf t)` (Route B,
  stashed by `emitStmt .call`).

Every other (pure) assign keeps its expression for rematerialisation. -/
def defsOf (prog : Program) : Tmp → Option Expr :=
  let pairs : List (Tmp × Expr) :=
    prog.blocks.toList.flatMap (fun b =>
      b.stmts.filterMap (fun
        | .assign t .gas       => some (t, Expr.slot (slotOf t))
        | .assign t (.sload _) => some (t, Expr.slot (slotOf t))
        | .assign t e          => some (t, e)
        | .call ⟨_, _, some t⟩ => some (t, Expr.slot (slotOf t))
        | .create ⟨_, _, _, _, some t⟩ => some (t, Expr.slot (slotOf t))
        | _                    => none))
  fun t => (pairs.find? (fun p => p.1 == t)).map (·.2)

/-! ## Allocation: the default policy

`allocate prog` is the **policy** half of `lower = encode ∘ emit (allocate prog)`.
The Phase-A default reproduces `defsOf` exactly: a call result (recorded by `defsOf`
as the spill-load `Expr.slot (slotOf t)`) becomes a `Loc.slot`; every other defined
tmp (`imm`/`add`/`lt`/`sload`/`gas`) becomes a `Loc.remat` of its defining
expression. Future phases route gas/sload to `slot` as well (the `SoundAlloc` floor;
`docs/uniform-spill-alloc-plan.md` §3). -/

/-- Classify a defining expression into a `Loc`: an `Expr.slot` (the generic
spill-load) is already a `Loc.slot`; everything else rematerialises. -/
def locOfExpr : Expr → Loc
  | .slot n => .slot n
  | e       => .remat e

/-- The default allocation: classify each tmp's `defsOf` definition into a `Loc`.
Undefined tmps get no location (`none`). -/
def allocate (prog : Program) : Alloc := fun t => (defsOf prog t).map locOfExpr

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

/-! ## The composition: `lower = encode ∘ emit (allocate prog)`

The lowering factors into a **mechanism** (`emit`, alloc-driven byte assembly) and a
**backend** (`encode`, the offset-table-resolved byte concatenation + `ByteArray`
wrap). `emit a prog` consumes the allocation through `Alloc.toDefs`, so the existing
`materialise`/`emitStmt`/`emitTerm`/`emitBlockBody`/`offsetTable` machinery is reused
verbatim. With `a := allocate prog` (whose `toDefs = defsOf prog`, `allocate_toDefs`)
the emitted bytes are exactly the old `lower`'s (`lower_eq_flatBytes`, no longer
`rfl` but a one-line bridge). -/

/-- **Mechanism.** The flat byte list of a program under allocation `a`: each block
lowered as `JUMPDEST :: emitBlockBody`, with branch destinations resolved via
`offsetTable`. Reads the allocation through `Alloc.toDefs`. -/
def emit (a : Alloc) (prog : Program) : List UInt8 :=
  let defs := a.toDefs
  let fuel := recomputeFuel prog
  let labelOff := offsetTable defs fuel prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody defs fuel labelOff b)

/-- **Backend.** Wrap an emitted byte list as the `ByteArray` `Evm.decode` reads. -/
def encode (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- **The lowering.** `lower = encode ∘ emit (allocate prog)`: allocate (policy),
emit (mechanism), encode (backend). The result is a `ByteArray` that `Evm.decode`
reads back as the intended opcode stream (established by the decode-anchor theorems in
`Decode/DecodeAnchors.lean`). -/
def lower (prog : Program) : ByteArray := encode (emit (allocate prog) prog)

end Lir
