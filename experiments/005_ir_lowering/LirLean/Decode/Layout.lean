import LirLean.Decode.DecodeLower

/-!
# LirLean — byte-layout arithmetic of `lower` (the offset-table prefix sum, C3)

`LirLean/DecodeLower.lean` reduces a decode obligation about `lower prog` to a
*list-local* fact: which byte (and immediate window) `lowerBytes prog` holds at the
pc. This module proves the **byte-layout arithmetic** that produces such facts at the
offset-table address `pcOf prog L pc` — over an *arbitrary* program, by prefix-sum
decomposition rather than per-program kernel `rfl`. All emission is the fold pipeline
(`matCache prog` cache + `defsOf prog` allocation; no fuel anywhere):

* `emitBlockBody`/`emitTerm` lengths are independent of the resolved offset table
  (`emitDest` is a fixed-width `PUSH4`), so the two lowering passes agree — the fact
  that makes the offset table well-defined (`emitBlockBody_length_labelOff`,
  `emitTerm_length_labelOff`);
* the assembler geometry's `flatMap_split` decomposes a `List.flatMap` around the
  element at a known index;
* `blockPrefix_length`: the bytes of the first `i` lowered blocks total exactly
  `offsetTable cache alloc blocks i` (the table is a prefix sum of `blockLen`);
* `lowerBytes_block_split`: `lowerBytes prog` decomposes around block `L` into
  `(blockPrefix) ++ (JUMPDEST :: emitBlockBody … b_L) ++ (blockSuffix)`, the prefix's
  length being `offsetTable … L.idx` — so byte `pcOf prog L pc` lies inside block
  `L`'s lowered bytes.

These are the bricks that turn a `pcOf` address into the `(lowerBytes prog)[n]?` fact
`decode_lower_{nonpush,push}` consume. The per-statement decode anchors built on top
live in `Decode/DecodeAnchors.lean`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-! ## Length invariance under the resolved offset table

The offset table is well-defined precisely because destination pushes are
fixed-width (`emitDest off = PUSH4 :: 4 bytes`, 5 bytes for any `off`): the measuring
pass (`labelOff = fun _ => 0`) and the emitting pass (the real `offsetTable`) produce
byte streams of the *same length*. -/

/-- `emitTerm`'s byte length does not depend on the offset table: `emitDest` is a
fixed-width `PUSH4` regardless of the destination value. -/
theorem emitTerm_length_labelOff (cache : Tmp → List UInt8)
    (lo1 lo2 : Nat → Nat) (t : Term) :
    (emitTerm cache lo1 t).length = (emitTerm cache lo2 t).length := by
  cases t <;> simp [emitTerm, emitDest, BytecodeLayer.Exec.offsetBytesBE]

/-- `emitBlockBody`'s byte length does not depend on the offset table (only its
terminator's destination pushes use it, and those are fixed-width). -/
theorem emitBlockBody_length_labelOff (cache : Tmp → List UInt8) (alloc : Alloc)
    (lo1 lo2 : Nat → Nat) (b : Block) :
    (emitBlockBody cache alloc lo1 b).length = (emitBlockBody cache alloc lo2 b).length := by
  unfold emitBlockBody
  simp only [List.length_append]
  rw [emitTerm_length_labelOff cache lo1 lo2]

/-- The lowered-block length (`blockLen`, measured with the zero table) equals the
length of the block lowered with **any** offset table — the prefix-sum table is the
genuine byte layout. -/
theorem blockLen_eq_length (cache : Tmp → List UInt8) (alloc : Alloc) (lo : Nat → Nat)
    (b : Block) :
    blockLen cache alloc b = (Byte.jumpdest :: emitBlockBody cache alloc lo b).length := by
  unfold blockLen
  simp only [List.length_cons]
  rw [emitBlockBody_length_labelOff cache alloc (fun _ => 0) lo]
  omega

/-! ## The block-prefix byte count = the offset table -/

/-- The bytes of the first `i` lowered blocks total `offsetTable cache alloc blocks i`.
`offsetTable` is `((blocks.take i).map blockLen).sum`; each lowered block
`JUMPDEST :: emitBlockBody … lo b` has length `blockLen … b` (`blockLen_eq_length`),
independent of the offset table `lo`. -/
theorem blockPrefix_length (cache : Tmp → List UInt8) (alloc : Alloc) (lo : Nat → Nat)
    (blocks : Array Block) (i : Nat) :
    ((blocks.toList.take i).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b)).length
      = offsetTable cache alloc blocks i := by
  unfold offsetTable
  rw [List.length_flatMap]
  rw [show (List.map (fun b => (Byte.jumpdest :: emitBlockBody cache alloc lo b).length)
            (blocks.toList.take i)).sum
        = (List.map (blockLen cache alloc) (blocks.toList.take i)).sum from ?_]
  · congr 1
    apply List.map_congr_left
    intro b _
    exact (blockLen_eq_length cache alloc lo b).symm

/-! ## `lowerBytes prog` decomposes around a block -/

/-- The flat byte list of `lower prog` decomposed around block `L`: the bytes of the
blocks before `L` (total length `offsetTable … L.idx`), then block `L`'s
`JUMPDEST :: emitBlockBody`, then the rest — provided `L` is a real block index. The
byte at `pcOf prog L pc = offsetTable … L.idx + 1 + …` therefore lies inside block
`L`'s lowered bytes. -/
theorem lowerBytes_block_split (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    lowerBytes prog
      = ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
                        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))
        ++ (Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
              (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)
        ++ ((prog.blocks.toList.drop (L.idx + 1)).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
                        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)) := by
  rw [lowerBytes_eq_blockBytes]
  exact flatMap_split prog.blocks.toList L.idx b hb _

/-- The byte-offset of block `L`'s leading `JUMPDEST` in `lowerBytes prog` is
`offsetTable … L.idx`: the prefix decomposition's first component has exactly that
length. This is the `M1` anchor for a block entry (`pcOf prog L 0 = offsetTable …
L.idx + 1`, the byte right after this `JUMPDEST`). -/
theorem lowerBytes_block_offset (prog : Program) (L : Label) :
    ((prog.blocks.toList.take L.idx).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
                    (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length
      = offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx :=
  blockPrefix_length (matCache prog) (defsOf prog) _ prog.blocks L.idx

/-! ## The statement-cursor byte anchor

The payoff: over an **arbitrary** program, the byte `lowerBytes prog` holds at the
offset-table address of a statement cursor `(L, pc)` is the *head byte* of that
statement's emitted opcodes — `(emitStmt … s)[0]?`. Composed with `decode_lower`
(`DecodeLower.lean`), this turns a `pcOf`-addressed decode obligation into a fact
about the construct's lowering, generically, replacing the per-program whole-array
`rfl`. -/

/-- **The statement-cursor byte anchor.** For a real statement `s` at cursor
`(L, pc)` whose lowering emits at least one byte, the byte `lowerBytes prog` holds at
the offset-table address `offsetTable … L.idx + 1 + (Σ emitted-stmt-lengths over the
first `pc` statements)` — i.e. `pcOf prog L pc` (definitionally this expression when
`prog.blockAt L = some b`) — is the head byte of `emitStmt … s`. The
prefix-sum/offset-table arithmetic, discharged once, generically. -/
theorem stmt_byte_anchor (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hne : emitStmt (matCache prog) (defsOf prog) s ≠ []) :
    (lowerBytes prog)[offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
        + ((b.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog))).length]?
      = (emitStmt (matCache prog) (defsOf prog) s)[0]? := by
  rw [lowerBytes_block_split prog L b hb]
  set cache := matCache prog with hcache
  set alloc := defsOf prog with halloc
  set lo := offsetTable cache alloc prog.blocks with hlo
  set pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hpre
  set suf := (prog.blocks.toList.drop (L.idx + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b) with hsuf
  have hprelen : pre.length = lo L.idx := lowerBytes_block_offset prog L
  have hslen : (emitStmt cache alloc s).length ≥ 1 := by
    cases h : emitStmt cache alloc s with
    | nil => exact absurd h hne
    | cons _ _ => simp
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
  rw [show lo L.idx + 1 + sp = pre.length + (1 + sp) from by rw [hprelen]; omega]
  have hmidlen : 1 + sp < (Byte.jumpdest :: emitBlockBody cache alloc lo b).length := by
    rw [hbody]; simp only [List.length_cons, List.length_append, hsp]; omega
  rw [mid_index pre _ suf (1 + sp) hmidlen]
  rw [show (1 + sp) = sp + 1 from by omega, List.getElem?_cons_succ, hbody]
  rw [List.getElem?_append_right (by rw [← hsp]),
      show sp - ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length = 0 from by
        rw [hsp]; omega]
  rw [List.getElem?_append_left (by omega)]

/-! ## The offset-table statement cursor `pcOf` and its byte anchor (generic `M1`)

`pcOf prog L pc` is the byte offset the resolved offset table assigns to cursor
`(L, pc)`: the block's `JUMPDEST` (`offsetTable … L.idx`), skip the `JUMPDEST` (`+1`),
then the byte length of the emitted statements `0 .. pc` of block `L`. It lives here
(pure byte-offset geometry over `lower prog`) rather than inside the simulation relation;
`Corr.pc_eq` pins `fr.exec.pc` to it. These lemmas wire the offset-table arithmetic into a
decode fact at the *symbolic* `pcOf` address, over an arbitrary program — the
program-global `M1` discharge the simulation engine needs at each statement step. -/

/-- `prog.blockAt L = some b` from the `toList` index witness (the form `Layout`'s
lemmas take). -/
theorem blockAt_of_toList (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) : prog.blockAt L = some b := by
  unfold Program.blockAt; rw [← Array.getElem?_toList]; exact hb

/-- The byte offset the offset table assigns to cursor `(L, pc)` of `prog`: the
block's `JUMPDEST` (`offsetTable … L.idx`), skip the `JUMPDEST` (`+1`), then the
byte length of the emitted statements `0 .. pc` of block `L`. A prefix sum, so it
is computable; `Corr.pc_eq` pins `fr.exec.pc` to this. -/
def pcOf (prog : Program) (L : Label) (pc : Nat) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b =>
          ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length)).getD 0)

/-- `pcOf prog L pc` unfolds to the offset-table anchor index (the `Layout` form)
when block `L` is present — the `getD 0` collapses to the block's stmt-prefix length. -/
theorem pcOf_eq_anchor (prog : Program) (L : Label) (b : Block) (pc : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    pcOf prog L pc
      = offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
        + ((b.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog))).length := by
  unfold pcOf; rw [blockAt_of_toList prog L b hb]; rfl

/-- **The statement-cursor byte (generic `M1`).** The byte `lowerBytes prog` holds at
`pcOf prog L pc` is the head byte of the statement at that cursor — `(emitStmt … s)[0]`.
The composition of `pcOf_eq_anchor` (pc = offset-table anchor) and
`stmt_byte_anchor` (anchor byte = `emitStmt` head). The `decode_lower_*` lemmas
turn this into a decode fact for the construct. -/
theorem lowerBytes_at_pcOf (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hne : emitStmt (matCache prog) (defsOf prog) s ≠ []) :
    (lowerBytes prog)[pcOf prog L pc]?
      = (emitStmt (matCache prog) (defsOf prog) s)[0]? := by
  rw [pcOf_eq_anchor prog L b pc hb]
  exact stmt_byte_anchor prog L b pc s hb hs hne

end Lir
