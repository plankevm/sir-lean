import LirLean.Decode.SegAligned
import LirLean.Decode.Layout
import LirLean.Decode.DecodeLower
import LirLean.Decode.DecodeAnchors
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
  This abstracts "the boundary walk over these bytes lands exactly at their end". It is the
  predicate-free instance of the parameterized `SegAlignedP` (`Decode/SegAligned.lean`),
  which also carries the composition bricks, both transports and the emit-ladder — all proven
  once and shared with the `SegAlignedLowering` tower.
* **`reaches_of_segAligned`** — the transport: if the bytecode `c` matches an aligned
  segment `seg` over `[base, base + seg.length)`, the boundary walk reaches
  `base + seg.length` from `base`. The predicate-free `reaches_end_of_segAlignedP`.
* **`segAligned_loweredBlock`** — each lowered block `JUMPDEST :: emitBlockBody` is aligned:
  the shared `IsLoweringOp` emit-ladder (`Decode/SegAligned.lean`) weakened by
  `SegAlignedP.mono`. The push-skipping is discharged once, there.
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

/-! ## List-level instruction alignment (the base tower)

`SegAligned` is the predicate-free instance of the parameterized `SegAlignedP`
(`Decode/SegAligned.lean`): a byte list that is a concatenation of complete EVM
instructions — each opcode byte `b` followed by exactly `(pushArgWidth (parseInstr b)).toNat`
immediate bytes — with **no** constraint on the head opcodes (`P = fun _ => True`). The
strengthened `SegAlignedLowering` tower (in `BoundaryReach`) is the other instance; both share
the one emit-ladder + transports proven once in `Decode/SegAligned.lean`. -/

/-- The base instruction-alignment notion: `SegAlignedP` with the trivial head predicate. -/
abbrev SegAligned : List UInt8 → Prop := SegAlignedP (fun _ => True)

/-- The transport: if `c`'s bytes over `[base, base + seg.length)` are exactly `seg` and `seg`
is aligned, the boundary walk reaches `base + seg.length` from `base`. The predicate-free
`reaches_end_of_segAlignedP` at `SegAligned`. -/
theorem reaches_of_segAligned (c : ByteArray) (seg : List UInt8) (hseg : SegAligned seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ReachesBoundary c base (base + seg.length) :=
  reaches_end_of_segAlignedP c seg hseg

/-- A lowered block `JUMPDEST :: emitBlockBody` is aligned: the `IsLoweringOp` witness
(`segAlignedP_loweredBlock`) weakened to `True` by `SegAlignedP.mono`. -/
theorem segAligned_loweredBlock (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (b : Block) : SegAligned (Byte.jumpdest :: emitBlockBody defs fuel labelOff b) :=
  (segAlignedP_loweredBlock defs fuel labelOff b).mono (fun _ _ => trivial)

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

/-! ## Fold jump-validity twins (Phase 2A P4)

Fold twins of the E3 tower, over `lowerF`/`flatBytesF`/`emitBlockBodyF`/`offsetTableF`. The
per-block alignment comes from `segAligned_loweredBlockF` (cache aligned by `segAlignedP_matCache`,
UNCONDITIONALLY); the boundary walk, offset-table prefix sum and `validJumpDests` characterisation
are reused verbatim. -/

/-- Fold twin of `segAligned_loweredBlock`. -/
theorem segAligned_loweredBlockF (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc) (labelOff : Nat → Nat)
    (b : Block) : SegAligned (Byte.jumpdest :: emitBlockBodyF cache alloc labelOff b) :=
  (segAlignedP_loweredBlockF cache hcache alloc labelOff b).mono (fun _ _ => trivial)

/-- Fold twin of `lower_get?_eq`. -/
theorem lowerF_get?_eq (prog : Program) (n : Nat) :
    (lowerF prog).get? n = (flatBytesF prog)[n]? := by
  rw [lowerF_eq_flatBytesF]; exact bget (flatBytesF prog) n

/-- Fold twin of `offsetTable_succ`. -/
theorem offsetTableF_succ (cache : Tmp → List UInt8) (alloc : Alloc) (blocks : Array Block)
    (i : Nat) (b : Block) (hb : blocks.toList[i]? = some b) :
    offsetTableF cache alloc blocks (i + 1)
      = offsetTableF cache alloc blocks i + blockLenF cache alloc b := by
  have hlt : i < blocks.toList.length := by
    rcases Nat.lt_or_ge i blocks.toList.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hb; exact absurd hb (by simp)
  have hget : blocks.toList[i] = b := by
    have h2 := List.getElem?_eq_getElem hlt; rw [h2] at hb; exact Option.some.inj hb
  unfold offsetTableF
  rw [List.take_add_one, List.map_append, List.sum_append]
  congr 1
  rw [List.getElem?_eq_getElem hlt, hget]
  simp

/-- Fold twin of `lower_match_block`. -/
theorem lowerF_match_block (prog : Program) (i : Nat) (b : Block)
    (hb : prog.blocks.toList[i]? = some b) :
    ∀ j, j < (Byte.jumpdest :: emitBlockBodyF (matCache prog) (allocate prog)
                (offsetTableF (matCache prog) (allocate prog) prog.blocks) b).length →
      (lowerF prog).get? (offsetTableF (matCache prog) (allocate prog) prog.blocks i + j)
        = (Byte.jumpdest :: emitBlockBodyF (matCache prog) (allocate prog)
            (offsetTableF (matCache prog) (allocate prog) prog.blocks) b)[j]? := by
  intro j hj
  rw [lowerF_get?_eq]
  rw [flatBytesF_block_split prog ⟨i⟩ b hb]
  set cache := matCache prog with hcache
  set alloc := allocate prog with halloc
  set lo := offsetTableF cache alloc prog.blocks with hlo
  set pre := (prog.blocks.toList.take i).flatMap
    (fun b => Byte.jumpdest :: emitBlockBodyF cache alloc lo b) with hpre
  set mid := Byte.jumpdest :: emitBlockBodyF cache alloc lo b with hmid
  set suf := (prog.blocks.toList.drop (i + 1)).flatMap
    (fun b => Byte.jumpdest :: emitBlockBodyF cache alloc lo b) with hsuf
  have hprelen : pre.length = lo i := by
    have := flatBytesF_block_offset prog ⟨i⟩
    simpa [hpre, hlo] using this
  rw [show lo i + j = pre.length + j from by rw [hprelen]]
  exact mid_index pre mid suf j hj

/-- Fold twin of `reaches_block_offset`. -/
theorem reaches_block_offsetF (prog : Program) :
    ∀ i, i ≤ prog.blocks.size →
      ReachesBoundary (lowerF prog) 0
        (offsetTableF (matCache prog) (allocate prog) prog.blocks i) := by
  have hca : ∀ t, SegAlignedP IsLoweringOp (matCache prog t) := segAlignedP_matCache prog
  intro i
  induction i with
  | zero =>
    intro _
    rw [show offsetTableF (matCache prog) (allocate prog) prog.blocks 0 = 0 from by
          simp [offsetTableF]]
    exact .refl 0
  | succ n ih =>
    intro hn
    have hnlt : n < prog.blocks.size := by omega
    have hblist : n < prog.blocks.toList.length := by simpa using hnlt
    set b := prog.blocks.toList[n] with hbdef
    have hb : prog.blocks.toList[n]? = some b := by rw [List.getElem?_eq_getElem hblist]
    have h1 := ih (by omega)
    set cache := matCache prog with hcache
    set alloc := allocate prog with halloc
    set lo := offsetTableF cache alloc prog.blocks with hlo
    have hseg : SegAligned (Byte.jumpdest :: emitBlockBodyF cache alloc lo b) :=
      segAligned_loweredBlockF cache hca alloc lo b
    have hmatch := lowerF_match_block prog n b hb
    have hwalk := reaches_of_segAligned (lowerF prog)
      (Byte.jumpdest :: emitBlockBodyF cache alloc lo b) hseg (lo n) hmatch
    have hlen : (Byte.jumpdest :: emitBlockBodyF cache alloc lo b).length
        = blockLenF cache alloc b := (blockLenF_eq_length cache alloc lo b).symm
    have hsucc : lo (n + 1) = lo n + blockLenF cache alloc b :=
      offsetTableF_succ cache alloc prog.blocks n b hb
    rw [hsucc]
    rw [show lo n + blockLenF cache alloc b
          = lo n + (Byte.jumpdest :: emitBlockBodyF cache alloc lo b).length from by rw [hlen]]
    exact ReachesBoundary.trans h1 hwalk

/-- Fold twin of `lower_byte_at_offset`. -/
theorem lowerF_byte_at_offset (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    (lowerF prog).get? (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx)
      = some Byte.jumpdest := by
  have hmatch := lowerF_match_block prog L.idx b hb
  have := hmatch 0 (by simp)
  simpa using this

/-- Fold twin of `block_offset_validJump` (E3). -/
theorem block_offset_validJumpF (prog : Program) (L : Label) (hL : L.idx < prog.blocks.size) :
    (UInt32.ofNat (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx))
      ∈ validJumpDests (lowerF prog) 0 := by
  have hblist : L.idx < prog.blocks.toList.length := by simpa using hL
  set b := prog.blocks.toList[L.idx] with hbdef
  have hb : prog.blocks.toList[L.idx]? = some b := by rw [List.getElem?_eq_getElem hblist]
  have hreach : ReachesBoundary (lowerF prog) 0
      (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx) :=
    reaches_block_offsetF prog L.idx (by omega)
  have hget : (lowerF prog).get?
      (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx) = some Byte.jumpdest :=
    lowerF_byte_at_offset prog L b hb
  have hmem := mem_validJumpDests_of_reachable_jumpdest (lowerF prog)
    (i := offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx)
    hreach (byte := Byte.jumpdest) hget (by decide)
  simpa [UInt32.ofNat] using hmem

/-- Fold twin of `decode_at_block_offset_jumpdest`. -/
theorem decode_at_block_offset_jumpdestF (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbound : offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx < 2 ^ 32) :
    Evm.decode (lowerF prog)
        (UInt32.ofNat (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx))
      = some (.Smsf .JUMPDEST, .none) := by
  have hbyte : (flatBytesF prog)[offsetTableF (matCache prog) (allocate prog)
      prog.blocks L.idx]? = some Byte.jumpdest := by
    have h := lowerF_byte_at_offset prog L b hb
    rw [lowerF_eq_flatBytesF] at h
    rwa [bget] at h
  have := decode_lowerF_nonpush prog
    (offsetTableF (matCache prog) (allocate prog) prog.blocks L.idx) Byte.jumpdest
    hbound hbyte (by decide)
  simpa using this

-- Build-enforced axiom-cleanliness guard: E3 depends only on
-- `[propext, Classical.choice, Quot.sound]`.

end Lir
