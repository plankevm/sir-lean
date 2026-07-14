import LirLean.Decode.Layout
import LirLean.Decode.DecodeLower

/-!
# LirLean — decode-at-cursor anchor lemmas (Layer A of the `lower_conforms` grind)

`docs/lower-conforms-plan.md` factors the general `lower_conforms` proof into a DAG
whose **Layer A** turns an offset-table address `pcOf prog L pc` (or a byte cursor
*inside* a statement's emitted push-sequence, or a terminator offset) into a concrete
`Evm.decode (lower prog) …` fact. This module proves those anchors, all over the fold
emission (`matCache prog` cache + `defsOf prog` allocation; no fuel anywhere):

* **A1 `decode_at_stmt_head`** — at `pcOf prog L pc` the decode yields the head opcode
  of the statement at that cursor (`(emitStmt … s)[0]`). Two corollaries cover the two
  possible head shapes (non-push / push), each a composition of `flatBytes_at_pcOf`
  (`Layout.lean`, the prefix-sum byte anchor) with `decode_lower_{nonpush,push}`
  (`DecodeLower.lean`).
* **A2 `decode_at_offset`** — decode at an arbitrary cursor `pcOf prog L pc + k`
  *inside* a statement's emitted bytes (the byte being `(emitStmt … s)[k]`). This is
  the engine stepping through each PUSH in a materialised operand sequence. Built on
  `stmt_byte_anchor_k`, the `k`-generalisation of `Layout.stmt_byte_anchor` (which is
  the `k = 0` instance) via `Layout.mid_index`.
* **A3 `decode_at_term`** — decode at the terminator's bytes, after the block's
  statements. Built on `term_byte_anchor` (the terminator analogue of
  `stmt_byte_anchor`, from `Layout.flatBytes_block_split`), with `termOf` giving the
  terminator's byte offset.

These compose with the per-opcode decode bricks `sim_*` in `Match.lean`; nothing here
touches `Spec/Semantics.lean` or `Law.lean` (the frame-free spine).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-! ## A2 layout brick — the `k`-generalised statement-cursor byte anchor

`Layout.stmt_byte_anchor` reads off the *head* byte (`k = 0`) of `emitStmt … s` at
the offset-table address of cursor `(L, pc)`. The assembly engine, stepping through
the PUSH-sequence a statement emits, needs the byte at an *arbitrary* offset `k` into
that statement's emitted bytes. This is the same prefix-sum decomposition, but the
final `mid_index` lands at `k` rather than `0`. -/

/-- **The `k`-generalised statement-cursor byte anchor.** For a real statement `s` at
cursor `(L, pc)` and any byte offset `k < (emitStmt … s).length`, the byte
`flatBytes prog` holds at `offsetTable … L.idx + 1 + (Σ emitted-stmt-lengths over the
first `pc` statements) + k` is `(emitStmt … s)[k]`. The `k = 0` case (with the
`emitStmt … s ≠ []` hypothesis) is `Layout.stmt_byte_anchor`. -/
theorem stmt_byte_anchor_k (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (k : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length) :
    (flatBytes prog)[offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
        + ((b.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog))).length + k]?
      = (emitStmt (matCache prog) (defsOf prog) s)[k]? := by
  rw [flatBytes_block_split prog L b hb]
  set cache := matCache prog with hcache
  set alloc := defsOf prog with halloc
  set lo := offsetTable cache alloc prog.blocks with hlo
  set pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hpre
  set suf := (prog.blocks.toList.drop (L.idx + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hsuf
  have hprelen : pre.length = lo L.idx := flatBytes_block_offset prog L
  set sp := ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length with hsp
  have hsplit : b.stmts.flatMap (emitStmt cache alloc)
      = (b.stmts.take pc).flatMap (emitStmt cache alloc)
        ++ emitStmt cache alloc s
        ++ (b.stmts.drop (pc + 1)).flatMap (emitStmt cache alloc) :=
    flatMap_split b.stmts pc s hs _
  have hbody : emitBlockBody cache alloc lo b
      = (b.stmts.take pc).flatMap (emitStmt cache alloc)
        ++ (emitStmt cache alloc s
            ++ ((b.stmts.drop (pc + 1)).flatMap (emitStmt cache alloc)
                ++ emitTerm cache lo b.term)) := by
    unfold emitBlockBody
    rw [hsplit]; simp [List.append_assoc]
  rw [show lo L.idx + 1 + sp + k = pre.length + (1 + (sp + k)) from by rw [hprelen]; omega]
  have hmidlen : 1 + (sp + k) < (Byte.jumpdest :: emitBlockBody cache alloc lo b).length := by
    rw [hbody]; simp only [List.length_cons, List.length_append, hsp]; omega
  rw [mid_index pre _ suf (1 + (sp + k)) hmidlen]
  rw [show (1 + (sp + k)) = (sp + k) + 1 from by omega, List.getElem?_cons_succ, hbody]
  rw [List.getElem?_append_right (by rw [← hsp]; omega),
      show sp + k - ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length = k from by
        rw [hsp]; omega]
  rw [List.getElem?_append_left (by omega)]

/-! ## A3 layout brick — the terminator byte anchor

The terminator's bytes sit after *all* the block's statements (the
`b.stmts.flatMap (emitStmt …)` segment) inside the block body
(`emitBlockBody = stmts-flatMap ++ emitTerm`, `Lowering.emitBlockBody`). This anchors
the byte at offset `k` into `emitTerm … b.term` — the terminator analogue of
`stmt_byte_anchor_k`, from the same `flatBytes_block_split` decomposition. -/

/-- **The terminator-cursor byte anchor.** For block `L = b` and any byte offset
`k < (emitTerm … b.term).length`, the byte `flatBytes prog` holds at
`offsetTable … L.idx + 1 + (the full stmts byte length) + k` is
`(emitTerm … b.term)[k]` — the terminator's `k`-th emitted byte. -/
theorem term_byte_anchor (prog : Program) (L : Label) (b : Block) (k : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hk : k < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length) :
    (flatBytes prog)[offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
        + (b.stmts.flatMap (emitStmt (matCache prog) (defsOf prog))).length + k]?
      = (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[k]? := by
  rw [flatBytes_block_split prog L b hb]
  set cache := matCache prog with hcache
  set alloc := defsOf prog with halloc
  set lo := offsetTable cache alloc prog.blocks with hlo
  set pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hpre
  set suf := (prog.blocks.toList.drop (L.idx + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hsuf
  have hprelen : pre.length = lo L.idx := flatBytes_block_offset prog L
  set sp := (b.stmts.flatMap (emitStmt cache alloc)).length with hsp
  have hbody : emitBlockBody cache alloc lo b
      = b.stmts.flatMap (emitStmt cache alloc) ++ emitTerm cache lo b.term := rfl
  rw [show lo L.idx + 1 + sp + k = pre.length + (1 + (sp + k)) from by rw [hprelen]; omega]
  have hmidlen : 1 + (sp + k) < (Byte.jumpdest :: emitBlockBody cache alloc lo b).length := by
    rw [hbody]; simp only [List.length_cons, List.length_append, hsp]; omega
  rw [mid_index pre _ suf (1 + (sp + k)) hmidlen]
  rw [show (1 + (sp + k)) = (sp + k) + 1 from by omega, List.getElem?_cons_succ, hbody]
  rw [List.getElem?_append_right (by rw [← hsp]; omega),
      show sp + k - (b.stmts.flatMap (emitStmt cache alloc)).length = k from by rw [hsp]; omega]

/-! ## `pcOf`-level byte facts (the `Layout.flatBytes_at_pcOf` family)

`Layout.pcOf prog L pc` is the offset-table address of a *statement* cursor. We lift
the two layout bricks above to it: the byte at `pcOf prog L pc + k` is
`(emitStmt … s)[k]` (A2's byte half), and — defining `termOf` for the terminator
offset — the byte at `termOf prog L + k` is `(emitTerm … b.term)[k]` (A3's byte
half). These specialise `Layout.flatBytes_at_pcOf` (the `k = 0` statement instance)
to arbitrary cursors. -/

/-- The byte at the statement cursor `pcOf prog L pc` plus offset `k` is the `k`-th
byte of `emitStmt … s` — the `pcOf`-level form of `stmt_byte_anchor_k`. The `k = 0`
case is `Layout.flatBytes_at_pcOf`. -/
theorem flatBytes_at_pcOf_offset (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (k : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length) :
    (flatBytes prog)[pcOf prog L pc + k]?
      = (emitStmt (matCache prog) (defsOf prog) s)[k]? := by
  rw [pcOf_eq_anchor prog L b pc hb]
  exact stmt_byte_anchor_k prog L b pc s k hb hs hk

/-- The byte offset of block `L = b`'s terminator in `flatBytes prog`: after the
block's `JUMPDEST` (`offsetTable … L.idx + 1`) and *all* its emitted statements. The
`Layout.pcOf` analogue for the block's `Term`. -/
def termOf (prog : Program) (L : Label) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b => (b.stmts.flatMap (emitStmt cache alloc)).length)).getD 0)

/-- `termOf prog L` unfolds to the offset-table terminator anchor index when block
`L = b` is present (the `getD 0` collapses to the block's full stmts byte length). -/
theorem termOf_eq_anchor (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    termOf prog L
      = offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
        + (b.stmts.flatMap (emitStmt (matCache prog) (defsOf prog))).length := by
  unfold termOf; rw [blockAt_of_toList prog L b hb]; rfl

/-- The byte at the terminator cursor `termOf prog L` plus offset `k` is the `k`-th
byte of `emitTerm … b.term` — the `termOf`-level form of `term_byte_anchor`. -/
theorem flatBytes_at_termOf (prog : Program) (L : Label) (b : Block) (k : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hk : k < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length) :
    (flatBytes prog)[termOf prog L + k]?
      = (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[k]? := by
  rw [termOf_eq_anchor prog L b hb]
  exact term_byte_anchor prog L b k hb hk

/-! ## A1 — `decode_at_stmt_head`

At the statement cursor `pcOf prog L pc`, `decode (lower prog)` yields the head opcode
of the statement's lowering. A statement's head byte is either a zero-width opcode (a
`SLOAD`/`SSTORE`/… should the lowering ever lead with one) or — for the materialised
operand pushes that begin `sstore`/`call` — a `PUSH`. We provide both shapes; the
caller picks by computing the concrete head byte (a `decide`/`rfl`). -/

/-- **A1, non-push head.** If the statement at cursor `(L, pc)` leads with a
zero-width opcode `byte` (`(emitStmt … s)[0] = byte`, `pushArgWidth (parseInstr byte)
= 0`), then `decode (lower prog)` at `pcOf prog L pc` is that opcode. -/
theorem decode_at_stmt_head_nonpush (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (byte : UInt8)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hhead : (emitStmt (matCache prog) (defsOf prog) s)[0]? = some byte)
    (hbound : pcOf prog L pc < 2 ^ 32)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat (pcOf prog L pc))
      = some (Evm.parseInstr byte, .none) := by
  have hne : emitStmt (matCache prog) (defsOf prog) s ≠ [] := by
    intro h; rw [h] at hhead; simp at hhead
  have hbyte : (flatBytes prog)[pcOf prog L pc]? = some byte := by
    rw [flatBytes_at_pcOf prog L b pc s hb hs hne]; exact hhead
  exact decode_lower_nonpush prog (pcOf prog L pc) byte hbound hbyte hnp

/-- **A1, push head.** If the statement at cursor `(L, pc)` leads with a `PUSH` of
width `w > 0` carrying immediate `imm` (`(emitStmt … s)[0] = byte`,
`pushArgWidth (parseInstr byte) = w`, the `w` immediate bytes
`uInt256OfByteArray` to `imm`), then `decode (lower prog)` at `pcOf prog L pc` is that
push. Covers the `PUSH32` operand a `sstore`/`call` leads with. -/
theorem decode_at_stmt_head_push (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (byte w : UInt8) (imm : UInt256)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hhead : (emitStmt (matCache prog) (defsOf prog) s)[0]? = some byte)
    (hbound : pcOf prog L pc < 2 ^ 32)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytes prog).toArray).extract
                  (pcOf prog L pc + 1) (pcOf prog L pc + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat (pcOf prog L pc))
      = some (Evm.parseInstr byte, some (imm, w)) := by
  have hne : emitStmt (matCache prog) (defsOf prog) s ≠ [] := by
    intro h; rw [h] at hhead; simp at hhead
  have hbyte : (flatBytes prog)[pcOf prog L pc]? = some byte := by
    rw [flatBytes_at_pcOf prog L b pc s hb hs hne]; exact hhead
  exact decode_lower_push prog (pcOf prog L pc) byte w imm hbound hbyte hp hw himm

/-! ## A2 — `decode_at_offset`

Decode at an arbitrary byte cursor `pcOf prog L pc + k` *inside* the statement's
emitted bytes. The engine, having pushed the first `k` bytes of a materialised
operand sequence, steps the opcode at `(emitStmt … s)[k]`. Same two head shapes. -/

/-- **A2, non-push.** Decode at the cursor `pcOf prog L pc + k` (inside statement
`s`'s emitted bytes) when `(emitStmt … s)[k]` is a zero-width opcode. -/
theorem decode_at_offset_nonpush (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (k : Nat) (byte : UInt8)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length)
    (hbyte0 : (emitStmt (matCache prog) (defsOf prog) s)[k]? = some byte)
    (hbound : pcOf prog L pc + k < 2 ^ 32)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat (pcOf prog L pc + k))
      = some (Evm.parseInstr byte, .none) := by
  have hbyte : (flatBytes prog)[pcOf prog L pc + k]? = some byte := by
    rw [flatBytes_at_pcOf_offset prog L b pc s k hb hs hk]; exact hbyte0
  exact decode_lower_nonpush prog (pcOf prog L pc + k) byte hbound hbyte hnp

/-- **A2, push.** Decode at the cursor `pcOf prog L pc + k` (inside statement `s`'s
emitted bytes) when `(emitStmt … s)[k]` is a `PUSH` of width `w > 0` carrying `imm`. -/
theorem decode_at_offset_push (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (k : Nat) (byte w : UInt8) (imm : UInt256)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length)
    (hbyte0 : (emitStmt (matCache prog) (defsOf prog) s)[k]? = some byte)
    (hbound : pcOf prog L pc + k < 2 ^ 32)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytes prog).toArray).extract
                  (pcOf prog L pc + k + 1) (pcOf prog L pc + k + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat (pcOf prog L pc + k))
      = some (Evm.parseInstr byte, some (imm, w)) := by
  have hbyte : (flatBytes prog)[pcOf prog L pc + k]? = some byte := by
    rw [flatBytes_at_pcOf_offset prog L b pc s k hb hs hk]; exact hbyte0
  exact decode_lower_push prog (pcOf prog L pc + k) byte w imm hbound hbyte hp hw himm

/-! ## A3 — `decode_at_term`

Decode at a byte cursor `termOf prog L + k` inside the block's terminator bytes
(`emitTerm … b.term`). The terminators (`ret`/`stop`/`jump`/`branch`) decode to
`RETURN`/`STOP`/`JUMP`/`JUMPI` (non-push) and the `PUSH4`/`PUSH32` destination /
condition operands (push). Same two head shapes, anchored at `termOf`. -/

/-- **A3, non-push.** Decode at the terminator cursor `termOf prog L + k` when
`(emitTerm … b.term)[k]` is a zero-width opcode (`RETURN`/`STOP`/`JUMP`/`JUMPI`). -/
theorem decode_at_term_nonpush (prog : Program) (L : Label) (b : Block) (k : Nat) (byte : UInt8)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hk : k < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length)
    (hbyte0 : (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[k]? = some byte)
    (hbound : termOf prog L + k < 2 ^ 32)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat (termOf prog L + k))
      = some (Evm.parseInstr byte, .none) := by
  have hbyte : (flatBytes prog)[termOf prog L + k]? = some byte := by
    rw [flatBytes_at_termOf prog L b k hb hk]; exact hbyte0
  exact decode_lower_nonpush prog (termOf prog L + k) byte hbound hbyte hnp

/-- **A3, push.** Decode at the terminator cursor `termOf prog L + k` when
`(emitTerm … b.term)[k]` is a `PUSH` of width `w > 0` carrying `imm` (the `PUSH4`
destination of a `jump`/`branch`, or the `PUSH32` of a `ret`/`branch` operand). -/
theorem decode_at_term_push (prog : Program) (L : Label) (b : Block) (k : Nat)
    (byte w : UInt8) (imm : UInt256)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hk : k < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length)
    (hbyte0 : (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[k]? = some byte)
    (hbound : termOf prog L + k < 2 ^ 32)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytes prog).toArray).extract
                  (termOf prog L + k + 1) (termOf prog L + k + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat (termOf prog L + k))
      = some (Evm.parseInstr byte, some (imm, w)) := by
  have hbyte : (flatBytes prog)[termOf prog L + k]? = some byte := by
    rw [flatBytes_at_termOf prog L b k hb hk]; exact hbyte0
  exact decode_lower_push prog (termOf prog L + k) byte w imm hbound hbyte hp hw himm

end Lir
