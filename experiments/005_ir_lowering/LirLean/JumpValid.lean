import LirLean.Layout
import LirLean.DecodeLower
import LirLean.DecodeAnchors
import LirLean.Match
import Evm

/-!
# LirLean — block jump-destination validity (Layer E3 of the `lower_conforms` grind)

`docs/lower-conforms-plan.md` node **E3**: every block's offset is a valid JUMP
destination of the lowered bytecode,

```lean
theorem block_offset_validJump (prog : Program) (L : Label) (hL : L.idx < prog.blocks.size) :
    (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx))
      ∈ validJumpDests (lower prog) 0
```

This generalises the concrete `nineteen_mem_validJumps` / `wc_reaches_415` walks (which
step the lowered byte stream instruction-by-instruction via `by decide`) from a fixed
program to an **arbitrary** `lower prog`.

## The crux (per the brief)

`validJumpDests` (`EVMLean/Evm/Semantics/Decode.lean`) walks the bytecode marking
`JUMPDEST` bytes valid, **skipping PUSH immediates** (`nextInstrPosNat` advances by
`1 + pushArgWidth`). `lower prog` emits `PUSH32` (33-byte) and `PUSH4` (5-byte)
sequences, so the reachability walk over arbitrary-width pushes is the subtle part.

The byte AT each block offset IS `Byte.jumpdest` (`flatBytes_block_split`); the work is
proving the walk REACHES it correctly past all preceding blocks' PUSH-laden bytes.

## The architecture

* **`SegAligned`** — a *list-level* notion: a byte list is a concatenation of complete
  instructions (each opcode byte followed by exactly `pushArgWidth` immediate bytes).
  This abstracts "the boundary walk over these bytes lands exactly at their end".
* **`reaches_of_segAligned`** — the transport: if the bytecode `c` matches an aligned
  segment `seg` over `[base, base + seg.length)`, the boundary walk reaches
  `base + seg.length` from `base`. Pure induction on `SegAligned`, no concrete bytes.
* **lowering-emits-aligned lemmas** — `emitImm`/`emitDest`/`materialiseExpr`/`emitStmt`/
  `emitTerm`/`emitBlockBody` all produce `SegAligned` byte lists (the immediate widths
  match `pushArgWidth` by construction). The push-skipping is discharged once, here.
* **`reaches_block_offset`** — the boundary walk reaches block `i`'s offset, by induction
  on `i`: each lowered block `JUMPDEST :: emitBlockBody` is aligned, so the walk steps
  exactly `blockLen` bytes per block, matching `offsetTable`'s prefix sum.
* **`block_offset_validJump`** — the headline: the byte at the offset is `JUMPDEST`
  (`flatBytes_block_split`), reachable (`reaches_block_offset`), so `validJumpDests`
  records it (`mem_validJumpDests_of_reachable_jumpdest`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## `ReachesBoundary` transitivity

The boundary walk composes: reaching `m` from `a` and `n` from `m` gives `n` from `a`.
Induction on the first walk. -/

theorem ReachesBoundary.trans {c : ByteArray} {a m n : Nat}
    (h1 : ReachesBoundary c a m) (h2 : ReachesBoundary c m n) :
    ReachesBoundary c a n := by
  induction h1 with
  | refl _ => exact h2
  | step hget _ ih => exact .step hget (ih h2)

/-! ## List-level instruction alignment

`SegAligned seg`: the byte list `seg` is a concatenation of complete EVM instructions —
each opcode byte `b` is immediately followed by exactly `(pushArgWidth (parseInstr b)).toNat`
immediate bytes (zero for non-pushes). This is precisely the property the boundary walk
needs to consume the segment exactly: at each opcode byte it advances `1 + pushArgWidth`,
landing on the next instruction's first byte. -/

inductive SegAligned : List UInt8 → Prop where
  | nil : SegAligned []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hrest : SegAligned rest) :
      SegAligned (byte :: (imm ++ rest))

/-! ## `SegAligned` composition

Aligned segments concatenate: an instruction stream is aligned iff each of its pieces
is. These are the bricks the lowering-emits-aligned lemmas glue with. -/

/-- Appending two aligned segments yields an aligned segment. Induction on the first. -/
theorem SegAligned.append {a b : List UInt8} (ha : SegAligned a) (hb : SegAligned b) :
    SegAligned (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | cons byte imm rest himm _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons byte imm (rest ++ b) himm ih

/-- A single zero-width (non-push) opcode is an aligned one-instruction segment. -/
theorem SegAligned.nonpush (byte : UInt8) (h : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    SegAligned [byte] := by
  have := SegAligned.cons byte [] [] (by simp [h]) .nil
  simpa using this

/-- A push opcode followed by exactly `pushArgWidth` immediate bytes is an aligned
one-instruction segment. -/
theorem SegAligned.push (byte : UInt8) (imm : List UInt8)
    (h : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat) :
    SegAligned (byte :: imm) := by
  have := SegAligned.cons byte imm [] h .nil
  simpa using this

/-! ## The transport: an aligned segment is walked to its end

If `c`'s bytes over `[base, base + seg.length)` are exactly `seg`, and `seg` is
instruction-aligned, then the boundary walk reaches `base + seg.length` from `base`.
Induction on `SegAligned seg`. The matching hypothesis is phrased pointwise on `get?`
so it threads through `ByteArray` cleanly. -/

theorem reaches_of_segAligned (c : ByteArray) (seg : List UInt8) (hseg : SegAligned seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ReachesBoundary c base (base + seg.length) := by
  induction hseg with
  | nil =>
    intro base _
    simpa using ReachesBoundary.refl (c := c) base
  | cons byte imm rest himm hrest ih =>
    intro base hmatch
    -- head byte at `base`
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp)
      simpa using this
    -- the walk's next boundary after the opcode + its immediates
    have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
      unfold nextInstrPosNat; rw [himm]
    -- length of the whole segment
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    -- the matching hypothesis restricted to `rest`, at the shifted base
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
        rw [hseglen]; omega
      have := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at this
      rw [this]
      -- (byte :: (imm ++ rest))[1 + imm.length + j]? = rest[j]?
      rw [show (1 + imm.length + j) = (imm.length + j) + 1 from by omega,
          List.getElem?_cons_succ, List.getElem?_append_right (by omega),
          show imm.length + j - imm.length = j from by omega]
    -- IH gives the walk from the shifted base to the segment end
    have hih := ih (base + 1 + imm.length) hmatch'
    refine .step (byte := byte) hhead ?_
    rw [hnext]
    rw [show base + (byte :: (imm ++ rest)).length = (base + 1 + imm.length) + rest.length from by
          rw [hseglen]; omega]
    exact hih

/-! ## The lowering emits aligned byte streams

Every emission helper produces an instruction-aligned segment: literal/destination
pushes carry exactly their immediate width, effecting opcodes are zero-width, and the
recursive `materialiseExpr`/`emitStmt`/`emitTerm`/`emitBlockBody` glue these with
`SegAligned.append`. This discharges the PUSH-immediate-skipping once and for all. -/

/-- `emitImm w = PUSH32 :: wordBytesBE w` is an aligned single PUSH32 instruction:
`wordBytesBE w` has 32 bytes, matching `pushArgWidth (PUSH32) = 32`. -/
theorem segAligned_emitImm (w : Word) : SegAligned (emitImm w) := by
  refine SegAligned.push Byte.push32 (wordBytesBE w) ?_
  show (wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [wordBytesBE, Evm.pushArgWidth]

/-- `emitDest off = PUSH4 :: offsetBytesBE off` is an aligned single PUSH4 instruction:
`offsetBytesBE off` has 4 bytes, matching `pushArgWidth (PUSH4) = 4`. -/
theorem segAligned_emitDest (off : Nat) : SegAligned (emitDest off) := by
  refine SegAligned.push Byte.push4 (offsetBytesBE off) ?_
  show (offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [offsetBytesBE, Evm.pushArgWidth]

/-- The call-result rematerialisation `emitImm slot ++ [MLOAD]` is aligned: an aligned
PUSH32 immediate followed by the zero-width `MLOAD` opcode. -/
theorem segAligned_slot (slot : Nat) :
    SegAligned (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAligned_emitImm (UInt256.ofNat slot)).append
    (SegAligned.nonpush Byte.mload (by decide))

/-- `materialiseExpr defs fuel e` is aligned: literal leaves are `emitImm`, the `.gas`
leaf is the zero-width `GAS` opcode, and the binary/sload recursions append aligned
sub-sequences then a single zero-width opcode. Induction on the `materialiseExpr`
recursion (`fuel` then the expression). -/
theorem segAligned_materialiseExpr (defs : Tmp → Option Expr) :
    ∀ (fuel : Nat) (e : Expr), SegAligned (materialiseExpr defs fuel e)
  | 0,      .imm w  => segAligned_emitImm w
  | f + 1,  .imm w  => segAligned_emitImm w
  | 0,      .tmp _  => .nil
  | 0,      .add _ _ => .nil
  | 0,      .lt _ _ => .nil
  | 0,      .sload _ => .nil
  | 0,      .gas    => .nil
  | 0,      .slot slot => segAligned_slot slot
  | f + 1,  .slot slot => segAligned_slot slot
  | f + 1,  .tmp t  => by
      rw [show materialiseExpr defs (f+1) (.tmp t)
            = (match defs t with
               | some e => materialiseExpr defs f e
               | none   => emitImm (0 : Word)) from rfl]
      cases defs t with
      | some e => exact segAligned_materialiseExpr defs f e
      | none   => exact segAligned_emitImm 0
  | f + 1,  .add a b => by
      rw [show materialiseExpr defs (f+1) (.add a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
            from rfl]
      exact ((segAligned_materialiseExpr defs f (.tmp b)).append
              (segAligned_materialiseExpr defs f (.tmp a))).append
            (SegAligned.nonpush Byte.add (by decide))
  | f + 1,  .lt a b => by
      rw [show materialiseExpr defs (f+1) (.lt a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
            from rfl]
      exact ((segAligned_materialiseExpr defs f (.tmp b)).append
              (segAligned_materialiseExpr defs f (.tmp a))).append
            (SegAligned.nonpush Byte.lt (by decide))
  | f + 1,  .sload k => by
      rw [show materialiseExpr defs (f+1) (.sload k)
            = materialiseExpr defs f (.tmp k) ++ [Byte.sload] from rfl]
      exact (segAligned_materialiseExpr defs f (.tmp k)).append
            (SegAligned.nonpush Byte.sload (by decide))
  | f + 1,  .gas    => by
      rw [show materialiseExpr defs (f+1) .gas = [Byte.gas] from rfl]
      exact SegAligned.nonpush Byte.gas (by decide)

/-- `materialise` is aligned (it is `materialiseExpr` on a `.tmp`). -/
theorem segAligned_materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) :
    SegAligned (materialise defs fuel t) :=
  segAligned_materialiseExpr defs fuel (.tmp t)

/-- `emitStmt` is aligned: `assign` emits nothing, `sstore` is two materialised operands
then `SSTORE`, `call` is five `emitImm 0`, two materialised operands, then `CALL`. -/
theorem segAligned_emitStmt (defs : Tmp → Option Expr) (fuel : Nat) (s : Stmt) :
    SegAligned (emitStmt defs fuel s) := by
  cases s with
  | assign t e =>
      -- alloc-native: a spilled (`.slot n`) tmp stashes `materialise e ++ PUSH n ++ MSTORE`;
      -- a rematerialised tmp emits nothing.
      rw [show emitStmt defs fuel (.assign t e)
            = (match defs t with
               | some (.slot n) =>
                   materialiseExpr defs fuel e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
               | _ => []) from rfl]
      cases defs t with
      | none => exact .nil
      | some loc =>
          cases loc with
          | imm => exact .nil
          | tmp => exact .nil
          | add => exact .nil
          | lt => exact .nil
          | sload => exact .nil
          | gas => exact .nil
          | slot n =>
              exact ((segAligned_materialiseExpr defs fuel e).append
                      (segAligned_emitImm (UInt256.ofNat n))).append
                    (SegAligned.nonpush Byte.mstore (by decide))
  | sstore key value =>
      rw [show emitStmt defs fuel (.sstore key value)
            = materialise defs fuel value ++ materialise defs fuel key ++ [Byte.sstore] from rfl]
      exact ((segAligned_materialise defs fuel value).append
              (segAligned_materialise defs fuel key)).append
            (SegAligned.nonpush Byte.sstore (by decide))
  | call cs =>
      rw [show emitStmt defs fuel (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ materialise defs fuel cs.callee
              ++ materialise defs fuel cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAligned_emitImm (0 : Word)).append (segAligned_emitImm 0)
      have h := h.append (segAligned_emitImm 0)
      have h := h.append (segAligned_emitImm 0)
      have h := h.append (segAligned_emitImm 0)
      have h := h.append (segAligned_materialise defs fuel cs.callee)
      have h := h.append (segAligned_materialise defs fuel cs.gasFwd)
      have h := h.append (SegAligned.nonpush Byte.call (by decide))
      -- The result-tail (MSTORE for `some`, POP for `none`) is aligned in both cases.
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAligned.nonpush Byte.pop (by decide)
      | some t =>
          exact (segAligned_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAligned.nonpush Byte.mstore (by decide))

/-- `emitTerm` is aligned: `ret` is a materialised operand then the two `PUSH32 0`
window operands then `RETURN`, `stop` is `STOP`, `jump` is `PUSH4 dest; JUMP`,
`branch` is materialised cond then `PUSH4 thenOff; JUMPI; PUSH4 elseOff; JUMP`. -/
theorem segAligned_emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (t : Term) : SegAligned (emitTerm defs fuel labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm defs fuel labelOff (.ret tt)
            = materialise defs fuel tt ++ emitImm 0 ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((segAligned_materialise defs fuel tt).append
              (segAligned_emitImm 0)).append (segAligned_emitImm 0)).append
            (SegAligned.nonpush Byte.ret (by decide))
  | stop =>
      rw [show emitTerm defs fuel labelOff .stop = [Byte.stop] from rfl]
      exact SegAligned.nonpush Byte.stop (by decide)
  | jump dst =>
      rw [show emitTerm defs fuel labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAligned_emitDest _).append (SegAligned.nonpush Byte.jump (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm defs fuel labelOff (.branch cond thenL elseL)
            = materialise defs fuel cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((segAligned_materialise defs fuel cond).append
              (segAligned_emitDest _)).append (SegAligned.nonpush Byte.jumpi (by decide))).append
              (segAligned_emitDest _)).append (SegAligned.nonpush Byte.jump (by decide))

/-- `emitBlockBody` is aligned: the block's statements' emissions appended with the
terminator's. -/
theorem segAligned_emitBlockBody (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (b : Block) : SegAligned (emitBlockBody defs fuel labelOff b) := by
  unfold emitBlockBody
  refine SegAligned.append ?_ (segAligned_emitTerm defs fuel labelOff b.term)
  -- the flatMap of `emitStmt` over the statement list is aligned: induction on the list
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAligned_emitStmt defs fuel s).append ih

/-- A lowered block `JUMPDEST :: emitBlockBody` is aligned: the leading `JUMPDEST` is a
zero-width opcode, the body is aligned (`segAligned_emitBlockBody`). -/
theorem segAligned_loweredBlock (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (b : Block) : SegAligned (Byte.jumpdest :: emitBlockBody defs fuel labelOff b) := by
  have hjd : SegAligned [Byte.jumpdest] := SegAligned.nonpush Byte.jumpdest (by decide)
  have := hjd.append (segAligned_emitBlockBody defs fuel labelOff b)
  simpa using this

/-! ## The boundary walk reaches every block offset

The bytes of `lower prog` over `[offsetTable i, offsetTable (i+1))` are exactly block
`i`'s lowered `JUMPDEST :: emitBlockBody` (`flatBytes_block_split`), which is
`SegAligned` (`segAligned_loweredBlock`). Each block therefore steps the walk exactly
`blockLen` bytes, so by induction on `i` the walk reaches `offsetTable i`. -/

/-- `(lower prog).get? n` is the `n`-th byte of `flatBytes prog` — the byte the
boundary walk reads at index `n` (via `bget` and `lower_eq_flatBytes`). -/
theorem lower_get?_eq (prog : Program) (n : Nat) :
    (lower prog).get? n = (flatBytes prog)[n]? := by
  rw [lower_eq_flatBytes]; exact bget (flatBytes prog) n

/-- `offsetTable` increments by the lowered length of block `i` (`blockLen`): the table
is the prefix sum of block lengths. Needs block `i` present. -/
theorem offsetTable_succ (defs : Tmp → Option Expr) (fuel : Nat) (blocks : Array Block)
    (i : Nat) (b : Block) (hb : blocks.toList[i]? = some b) :
    offsetTable defs fuel blocks (i + 1)
      = offsetTable defs fuel blocks i + blockLen defs fuel b := by
  have hlt : i < blocks.toList.length := by
    rcases Nat.lt_or_ge i blocks.toList.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hb; exact absurd hb (by simp)
  have hget : blocks.toList[i] = b := by
    have h2 := List.getElem?_eq_getElem hlt; rw [h2] at hb; exact Option.some.inj hb
  unfold offsetTable
  rw [List.take_add_one, List.map_append, List.sum_append]
  congr 1
  rw [List.getElem?_eq_getElem hlt, hget]
  simp

/-- The matching hypothesis the segment transport needs at block `i`: the byte
`lower prog` holds at `offsetTable i + j` is block `i`'s lowered byte `j`, for `j`
within the lowered block. From `flatBytes_block_split` + `mid_index`. -/
theorem lower_match_block (prog : Program) (i : Nat) (b : Block)
    (hb : prog.blocks.toList[i]? = some b) :
    ∀ j, j < (Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
                (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b).length →
      (lower prog).get? (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks i + j)
        = (Byte.jumpdest :: emitBlockBody (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)[j]? := by
  intro j hj
  rw [lower_get?_eq]
  -- decompose flatBytes around block i (L.idx = i)
  rw [flatBytes_block_split prog ⟨i⟩ b hb]
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set lo := offsetTable defs fuel prog.blocks with hlo
  set pre := (prog.blocks.toList.take i).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody defs fuel lo b) with hpre
  set mid := Byte.jumpdest :: emitBlockBody defs fuel lo b with hmid
  set suf := (prog.blocks.toList.drop (i + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody defs fuel lo b) with hsuf
  have hprelen : pre.length = lo i := by
    have := flatBytes_block_offset prog ⟨i⟩
    simpa [hpre, hlo] using this
  rw [show lo i + j = pre.length + j from by rw [hprelen]]
  exact mid_index pre mid suf j hj

/-- **The boundary walk reaches block `i`'s offset.** For every `i ≤ prog.blocks.size`,
`ReachesBoundary (lower prog) 0 (offsetTable … i)`. Induction on `i`: block `i`'s
lowered bytes are aligned (`segAligned_loweredBlock`) and match `lower prog` at
`offsetTable i` (`lower_match_block`), so the segment transport walks the whole block,
landing at `offsetTable (i+1)`. -/
theorem reaches_block_offset (prog : Program) :
    ∀ i, i ≤ prog.blocks.size →
      ReachesBoundary (lower prog) 0
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [show offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks 0 = 0 from by
          simp [offsetTable]]
    exact .refl 0
  | succ n ih =>
    intro hn
    have hnlt : n < prog.blocks.size := by omega
    -- block n exists
    have hblist : n < prog.blocks.toList.length := by simpa using hnlt
    set b := prog.blocks.toList[n] with hbdef
    have hb : prog.blocks.toList[n]? = some b := by rw [List.getElem?_eq_getElem hblist]
    -- walk to offsetTable n by IH
    have h1 := ih (by omega)
    -- walk block n's bytes from offsetTable n
    set defs := defsOf prog with hdefs
    set fuel := recomputeFuel prog with hfuel
    set lo := offsetTable defs fuel prog.blocks with hlo
    have hseg : SegAligned (Byte.jumpdest :: emitBlockBody defs fuel lo b) :=
      segAligned_loweredBlock defs fuel lo b
    have hmatch := lower_match_block prog n b hb
    have hwalk := reaches_of_segAligned (lower prog)
      (Byte.jumpdest :: emitBlockBody defs fuel lo b) hseg (lo n) hmatch
    -- the segment length is blockLen b, so the walk lands at offsetTable (n+1)
    have hlen : (Byte.jumpdest :: emitBlockBody defs fuel lo b).length = blockLen defs fuel b :=
      (blockLen_eq_length defs fuel lo b).symm
    have hsucc : lo (n + 1) = lo n + blockLen defs fuel b :=
      offsetTable_succ defs fuel prog.blocks n b hb
    rw [hsucc]
    rw [show lo n + blockLen defs fuel b
          = lo n + (Byte.jumpdest :: emitBlockBody defs fuel lo b).length from by rw [hlen]]
    exact ReachesBoundary.trans h1 hwalk

/-! ## The headline (E3)

The byte at block `L`'s offset is `JUMPDEST` (`flatBytes_block_split` leads each block
with `Byte.jumpdest`, and `parseInstr Byte.jumpdest = .JUMPDEST`), and the offset is
reachable (`reaches_block_offset`), so `validJumpDests` records it. -/

/-- The byte `lower prog` holds at block `L`'s offset is `Byte.jumpdest`. -/
theorem lower_byte_at_offset (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    (lower prog).get? (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx)
      = some Byte.jumpdest := by
  have hmatch := lower_match_block prog L.idx b hb
  have := hmatch 0 (by simp)
  simpa using this

/-- **E3 — block jump-destination validity.** Every block's offset is a valid JUMP
destination of the lowered bytecode: the byte there is `JUMPDEST` and the offset is
reachable from the program start (skipping every preceding PUSH immediate). Needed by
every `jump`/`branch` (Layer E2). -/
theorem block_offset_validJump (prog : Program) (L : Label) (hL : L.idx < prog.blocks.size) :
    (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx))
      ∈ validJumpDests (lower prog) 0 := by
  -- block L exists
  have hblist : L.idx < prog.blocks.toList.length := by simpa using hL
  set b := prog.blocks.toList[L.idx] with hbdef
  have hb : prog.blocks.toList[L.idx]? = some b := by rw [List.getElem?_eq_getElem hblist]
  -- the offset is reachable
  have hreach : ReachesBoundary (lower prog) 0
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx) :=
    reaches_block_offset prog L.idx (by omega)
  -- the byte there is JUMPDEST
  have hget : (lower prog).get?
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx) = some Byte.jumpdest :=
    lower_byte_at_offset prog L b hb
  -- route through the characterization lemma
  have hmem := mem_validJumpDests_of_reachable_jumpdest (lower prog)
    (i := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx)
    hreach (byte := Byte.jumpdest) hget (by decide)
  -- (offsetTable …).toUInt32 = UInt32.ofNat (offsetTable …)
  simpa [UInt32.ofNat] using hmem

/-- **Decode of a block's leading `JUMPDEST`.** At the block offset `offsetTable … L.idx`
(the byte `lower_byte_at_offset` pins to `Byte.jumpdest`), `decode (lower prog)` is the
zero-width `JUMPDEST`. The byte a `jump`/`branch` lands on (the `corr_at_jumpdest_landing`
step), and the entry block's leading `JUMPDEST` the top-level frame's entry `Corr` steps. -/
theorem decode_at_block_offset_jumpdest (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx < 2 ^ 32) :
    Evm.decode (lower prog)
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx))
      = some (.Smsf .JUMPDEST, .none) := by
  have hbyte : (flatBytes prog)[offsetTable (defsOf prog) (recomputeFuel prog)
      prog.blocks L.idx]? = some Byte.jumpdest := by
    have h := lower_byte_at_offset prog L b hb
    rw [lower_eq_flatBytes] at h
    rwa [bget] at h
  have := decode_lower_nonpush prog
    (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx) Byte.jumpdest
    hbound hbyte (by decide)
  simpa using this

-- Build-enforced axiom-cleanliness guard: E3 depends only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms block_offset_validJump

end Lir
