import LirLean.DecodeLower
import LirLean.SmallStep

/-!
# LirLean — byte-layout arithmetic of `lower` (the offset-table prefix sum, C3)

`LirLean/DecodeLower.lean` reduces a decode obligation about `lower prog` to a
*list-local* fact: which byte (and immediate window) `flatBytes prog` holds at the
pc. This module proves the **byte-layout arithmetic** that produces such facts at the
offset-table address `pcOf prog L pc` — over an *arbitrary* program, by prefix-sum
decomposition rather than per-program kernel `rfl`:

* `emitBlockBody`/`emitTerm` lengths are independent of the resolved offset table
  (`emitDest` is a fixed-width `PUSH4`), so the two lowering passes agree — the fact
  that makes the offset table well-defined (`emitBlockBody_length_labelOff`,
  `emitTerm_length_labelOff`);
* `flatMap_split`: a `List.flatMap` decomposes around the element at a known index
  into `prefix ++ f b ++ suffix`;
* `blockPrefix_length`: the bytes of the first `i` lowered blocks total exactly
  `offsetTable defs fuel blocks i` (the table is a prefix sum of `blockLen`);
* `flatBytes_block_split`: `flatBytes prog` decomposes around block `L` into
  `(blockPrefix) ++ (JUMPDEST :: emitBlockBody … b_L) ++ (blockSuffix)`, the prefix's
  length being `offsetTable … L.idx` — so byte `pcOf prog L pc` lies inside block
  `L`'s lowered bytes.

These are the bricks that turn a `pcOf` address into the `(flatBytes prog)[n]?` fact
`decode_lower_{nonpush,push}` consume. The per-statement index within a block body
(the `Σ emitStmt-length` part of `pcOf`) is the next layer; see `PLAN.md`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## Length invariance under the resolved offset table

The offset table is well-defined precisely because destination pushes are
fixed-width (`emitDest off = PUSH4 :: 4 bytes`, 5 bytes for any `off`): the measuring
pass (`labelOff = fun _ => 0`) and the emitting pass (the real `offsetTable`) produce
byte streams of the *same length*. -/

/-- `emitTerm`'s byte length does not depend on the offset table: `emitDest` is a
fixed-width `PUSH4` regardless of the destination value. -/
theorem emitTerm_length_labelOff (defs : Tmp → Option Expr) (fuel : Nat)
    (lo1 lo2 : Nat → Nat) (t : Term) :
    (emitTerm defs fuel lo1 t).length = (emitTerm defs fuel lo2 t).length := by
  cases t <;> simp [emitTerm, emitDest, offsetBytesBE]

/-- `emitBlockBody`'s byte length does not depend on the offset table (only its
terminator's destination pushes use it, and those are fixed-width). -/
theorem emitBlockBody_length_labelOff (defs : Tmp → Option Expr) (fuel : Nat)
    (lo1 lo2 : Nat → Nat) (b : Block) :
    (emitBlockBody defs fuel lo1 b).length = (emitBlockBody defs fuel lo2 b).length := by
  unfold emitBlockBody
  simp only [List.length_append]
  rw [emitTerm_length_labelOff defs fuel lo1 lo2]

/-- The lowered-block length (`blockLen`, measured with the zero table) equals the
length of the block lowered with **any** offset table — the prefix-sum table is the
genuine byte layout. -/
theorem blockLen_eq_length (defs : Tmp → Option Expr) (fuel : Nat) (lo : Nat → Nat) (b : Block) :
    blockLen defs fuel b = (Byte.jumpdest :: emitBlockBody defs fuel lo b).length := by
  unfold blockLen
  simp only [List.length_cons]
  rw [emitBlockBody_length_labelOff defs fuel (fun _ => 0) lo]
  omega

/-! ## `flatMap` index decomposition -/

/-- Decompose a `List.flatMap` around the element at a known index: `blocks.flatMap f
= (take i).flatMap f ++ f b ++ (drop (i+1)).flatMap f` when `blocks[i] = b`. -/
theorem flatMap_split {α β : Type _} (xs : List α) (i : Nat) (a : α) (hi : xs[i]? = some a)
    (f : α → List β) :
    xs.flatMap f = (xs.take i).flatMap f ++ f a ++ (xs.drop (i + 1)).flatMap f := by
  have hlt : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hi; exact absurd hi (by simp)
  have hget : xs[i] = a := by
    have h2 := List.getElem?_eq_getElem hlt; rw [h2] at hi; exact Option.some.inj hi
  conv_lhs => rw [← List.take_append_drop i xs]
  rw [List.flatMap_append, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hlt, hget, List.flatMap_cons]

/-! ## The block-prefix byte count = the offset table -/

/-- The bytes of the first `i` lowered blocks total `offsetTable defs fuel blocks i`.
`offsetTable` is `((blocks.take i).map blockLen).sum`; each lowered block
`JUMPDEST :: emitBlockBody … lo b` has length `blockLen … b` (`blockLen_eq_length`),
independent of the offset table `lo`. -/
theorem blockPrefix_length (defs : Tmp → Option Expr) (fuel : Nat) (lo : Nat → Nat)
    (blocks : Array Block) (i : Nat) :
    ((blocks.toList.take i).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody defs fuel lo b)).length
      = offsetTable defs fuel blocks i := by
  unfold offsetTable
  rw [List.length_flatMap]
  rw [show (List.map (fun b => (Byte.jumpdest :: emitBlockBody defs fuel lo b).length)
            (blocks.toList.take i)).sum
        = (List.map (blockLen defs fuel) (blocks.toList.take i)).sum from ?_]
  · congr 1
    apply List.map_congr_left
    intro b _
    exact (blockLen_eq_length defs fuel lo b).symm

/-! ## `flatBytes prog` decomposes around a block -/

/-- The flat byte list of `lower prog` decomposed around block `L`: the bytes of the
blocks before `L` (total length `offsetTable … L.idx`), then block `L`'s
`JUMPDEST :: emitBlockBody`, then the rest — provided `L` is a real block index. The
byte at `pcOf prog L pc = offsetTable … L.idx + 1 + …` therefore lies inside block
`L`'s lowered bytes. -/
theorem flatBytes_block_split (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    flatBytes prog
      = ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
                        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b))
        ++ (Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
              (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)
        ++ ((prog.blocks.toList.drop (L.idx + 1)).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
                        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)) := by
  unfold flatBytes
  exact flatMap_split prog.blocks.toList L.idx b hb _

/-- The byte-offset of block `L`'s leading `JUMPDEST` in `flatBytes prog` is
`offsetTable … L.idx`: the prefix decomposition's first component has exactly that
length. This is the `M1` anchor for a block entry (`pcOf prog L 0 = offsetTable …
L.idx + 1`, the byte right after this `JUMPDEST`). -/
theorem flatBytes_block_offset (prog : Program) (L : Label) :
    ((prog.blocks.toList.take L.idx).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
                    (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)).length
      = offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx :=
  blockPrefix_length (defsOf prog) (recomputeFuel prog) _ prog.blocks L.idx

/-! ## The statement-cursor byte anchor

The payoff: over an **arbitrary** program, the byte `flatBytes prog` holds at the
offset-table address of a statement cursor `(L, pc)` is the *head byte* of that
statement's emitted opcodes — `(emitStmt … s)[0]?`. Composed with `decode_lower`
(`DecodeLower.lean`), this turns a `pcOf`-addressed decode obligation into a fact
about the construct's lowering, generically, replacing the per-program whole-array
`rfl`. -/

/-- Index into the middle of a three-way append: `(pre ++ mid ++ suf)[pre.length + k]
= mid[k]` for `k < mid.length`. -/
theorem mid_index (pre mid suf : List UInt8) (k : Nat) (h : k < mid.length) :
    (pre ++ mid ++ suf)[pre.length + k]? = mid[k]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left h]

/-- **The statement-cursor byte anchor.** For a real statement `s` at cursor
`(L, pc)` whose lowering emits at least one byte, the byte `flatBytes prog` holds at
the offset-table address `offsetTable … L.idx + 1 + (Σ emitted-stmt-lengths over the
first `pc` statements)` — i.e. `pcOf prog L pc` (`Match.pcOf`, definitionally this
expression when `prog.blockAt L = some b`) — is the head byte of `emitStmt … s`. The
prefix-sum/offset-table arithmetic, discharged once, generically. -/
theorem stmt_byte_anchor (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hne : emitStmt (defsOf prog) (recomputeFuel prog) s ≠ []) :
    (flatBytes prog)[offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx + 1
        + ((b.stmts.take pc).flatMap (emitStmt (defsOf prog) (recomputeFuel prog))).length]?
      = (emitStmt (defsOf prog) (recomputeFuel prog) s)[0]? := by
  rw [flatBytes_block_split prog L b hb]
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set lo := offsetTable defs fuel prog.blocks with hlo
  set pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody defs fuel lo b) with hpre
  set suf := (prog.blocks.toList.drop (L.idx + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody defs fuel lo b) with hsuf
  have hprelen : pre.length = lo L.idx := flatBytes_block_offset prog L
  have hslen : (emitStmt defs fuel s).length ≥ 1 := by
    cases h : emitStmt defs fuel s with
    | nil => exact absurd h hne
    | cons _ _ => simp
  set sp := ((b.stmts.take pc).flatMap (emitStmt defs fuel)).length with hsp
  have hsplit : b.stmts.flatMap (emitStmt defs fuel)
      = (b.stmts.take pc).flatMap (emitStmt defs fuel)
        ++ emitStmt defs fuel s
        ++ (b.stmts.drop (pc + 1)).flatMap (emitStmt defs fuel) :=
    flatMap_split b.stmts pc s hs _
  have hbody : emitBlockBody defs fuel lo b
      = (b.stmts.take pc).flatMap (emitStmt defs fuel)
        ++ (emitStmt defs fuel s
            ++ ((b.stmts.drop (pc + 1)).flatMap (emitStmt defs fuel)
                ++ emitTerm defs fuel lo b.term)) := by
    unfold emitBlockBody
    rw [hsplit]; simp [List.append_assoc]
  rw [show lo L.idx + 1 + sp = pre.length + (1 + sp) from by rw [hprelen]; omega]
  have hmidlen : 1 + sp < (Byte.jumpdest :: emitBlockBody defs fuel lo b).length := by
    rw [hbody]; simp only [List.length_cons, List.length_append, hsp]; omega
  rw [mid_index pre _ suf (1 + sp) hmidlen]
  rw [show (1 + sp) = sp + 1 from by omega, List.getElem?_cons_succ, hbody]
  rw [List.getElem?_append_right (by rw [← hsp]),
      show sp - ((b.stmts.take pc).flatMap (emitStmt defs fuel)).length = 0 from by rw [hsp]; omega]
  rw [List.getElem?_append_left (by omega)]

end Lir
