import LirLean.JumpValid

/-!
# LirLean — the lowering emits no CREATE/CREATE2 opcode at any instruction boundary

This module discharges the **structural** half of the `NotCreate` modellability clause
(`V2/Modellable.lean`): no matter which instruction boundary of `lower prog` the engine
reaches, the opcode there is never `CREATE` (`0xf0`) nor `CREATE2` (`0xf5`). The IR has no
create constructor and `emitStmt`/`emitTerm`/`materialiseExpr` emit only the 16 opcodes
`{STOP, ADD, LT, POP, MLOAD, MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4,
PUSH32, CALL, RETURN}` — none of which is CREATE/CREATE2.

The subtlety is that a PUSH **immediate** byte may itself be `0xf0`/`0xf5` (push immediates
are arbitrary data), so "every emitted byte ≠ 0xf0" is *false*. The correct structural fact
is opcode-positional: every byte that the boundary walk *reads as an opcode* (i.e. the head
of an emitted instruction) is non-CREATE. We capture that with `SegAlignedSafe` — the
instruction-aligned `SegAligned` of `JumpValid.lean` strengthened so each instruction head
parses to a non-CREATE op — and transport it along the boundary walk.

## Architecture (paralleling `JumpValid.lean`)

* **`SegAlignedSafe`** — a `SegAligned` whose every instruction *head* byte satisfies
  `parseInstr byte ∉ {CREATE, CREATE2}`. The strengthened alignment notion.
* **`reaches_safe_of_segAlignedSafe`** — the transport: if `c`'s bytes over
  `[base, base + seg.length)` are `seg` and `seg` is `SegAlignedSafe`, then any boundary
  `n` the walk reaches from `base` *strictly inside* the segment reads a non-CREATE opcode.
  Pure induction on `SegAlignedSafe`, no concrete bytes.
* **lowering-emits-safe lemmas** — `emitImm`/`emitDest`/`materialiseExpr`/`emitStmt`/
  `emitTerm`/`emitBlockBody`/`loweredBlock` all produce `SegAlignedSafe` byte lists (every
  emitted opcode is a concrete non-CREATE byte, discharged by `decide`).
* **`reachable_boundary_notCreate`** — the headline: at every boundary `n` reachable from
  `0` in `lower prog` (and strictly before the program end), `decode (lower prog) n` reads a
  non-CREATE op. Composes `reaches_block_offset` (the per-block walk of `JumpValid.lean`)
  with `reaches_safe_of_segAlignedSafe`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §1 — `SegAlignedSafe`: alignment with non-CREATE instruction heads

`SegAlignedSafe seg` is `SegAligned seg` (each opcode byte followed by exactly
`pushArgWidth` immediate bytes) plus: every opcode *head* byte `b` satisfies
`parseInstr b ∉ {CREATE, CREATE2}`. The immediate bytes are unconstrained (they are data,
never read as opcodes by the aligned boundary walk). -/

inductive SegAlignedSafe : List UInt8 → Prop where
  | nil : SegAlignedSafe []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hsafe : Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2)
      (hrest : SegAlignedSafe rest) :
      SegAlignedSafe (byte :: (imm ++ rest))

/-- A `SegAlignedSafe` segment is in particular `SegAligned` (forget the head-safety). -/
theorem SegAlignedSafe.toSegAligned {seg : List UInt8} (h : SegAlignedSafe seg) :
    SegAligned seg := by
  induction h with
  | nil => exact .nil
  | cons byte imm rest himm _ _ ih => exact .cons byte imm rest himm ih

/-! ### §1.1 — `SegAlignedSafe` composition (mirrors `SegAligned`)

The bricks the lowering-emits-safe lemmas glue with: append, a single non-CREATE
zero-width opcode, a non-CREATE push with its immediate. -/

/-- Appending two safe-aligned segments yields a safe-aligned segment. Induction on the
first. -/
theorem SegAlignedSafe.append {a b : List UInt8} (ha : SegAlignedSafe a) (hb : SegAlignedSafe b) :
    SegAlignedSafe (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | cons byte imm rest himm hsafe _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons byte imm (rest ++ b) himm hsafe ih

/-- A single zero-width (non-push) **non-CREATE** opcode is a safe-aligned one-instruction
segment. -/
theorem SegAlignedSafe.nonpush (byte : UInt8) (h : Evm.pushArgWidth (Evm.parseInstr byte) = 0)
    (hsafe : Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2) :
    SegAlignedSafe [byte] := by
  have := SegAlignedSafe.cons byte [] [] (by simp [h]) hsafe .nil
  simpa using this

/-- A **non-CREATE** push opcode followed by exactly `pushArgWidth` immediate bytes is a
safe-aligned one-instruction segment. -/
theorem SegAlignedSafe.push (byte : UInt8) (imm : List UInt8)
    (h : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
    (hsafe : Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2) :
    SegAlignedSafe (byte :: imm) := by
  have := SegAlignedSafe.cons byte imm [] h hsafe .nil
  simpa using this

/-! ## §2 — the transport: a boundary reached inside a safe segment reads a non-CREATE op

If `c` matches a `SegAlignedSafe` segment `seg` over `[base, base + seg.length)`, then any
instruction boundary `n` the walk reaches from `base` that is **strictly inside** the segment
(`n < base + seg.length`) reads a byte parsing to a non-CREATE op. Induction on
`SegAlignedSafe seg`, mirroring `reaches_of_segAligned`: the head boundary `base` reads the
(safe) head byte; a deeper boundary is reached past the head, landing in the aligned `rest`,
where the IH applies. -/

/-- The boundary walk never decreases the position: a reachable boundary is `≥` the start. -/
theorem reachesBoundary_le {c : ByteArray} {a n : Nat} (h : ReachesBoundary c a n) : a ≤ n := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step _ _ ih => exact Nat.le_trans (Nat.le_of_lt (nextInstrPosNat_gt _ _)) ih

theorem reaches_safe_of_segAlignedSafe (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedSafe seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte
          ∧ Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2 := by
  induction hseg with
  | nil =>
    -- empty segment: no boundary is strictly inside (the walk never decreases the position).
    intro base _ n hreach hlt
    simp only [List.length_nil, Nat.add_zero] at hlt
    exact absurd (reachesBoundary_le hreach) (by omega)
  | cons byte imm rest himm hsafe hrest ih =>
    intro base hmatch n hreach hlt
    -- the head byte sits at `base`.
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp); simpa using this
    -- length of the whole segment.
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    -- the matching hypothesis restricted to `rest`, at the shifted base (as in
    -- `reaches_of_segAligned`).
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by rw [hseglen]; omega
      have := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at this
      rw [this]
      rw [show (1 + imm.length + j) = (imm.length + j) + 1 from by omega,
          List.getElem?_cons_succ, List.getElem?_append_right (by omega),
          show imm.length + j - imm.length = j from by omega]
    -- case on the walk: either `n = base` (the head boundary) or it steps past the head.
    cases hreach with
    | refl _ =>
      -- `n = base`: read the safe head byte.
      exact ⟨byte, hhead, hsafe.1, hsafe.2⟩
    | step hget rest' =>
      -- the walk steps from `base` past the head + its immediates: the byte read is `byte`
      -- (so `nextInstrPosNat base (parseInstr byte) = base + 1 + imm.length`), and the rest of
      -- the walk reaches `n` from the shifted base, strictly inside `rest`.
      rw [hhead] at hget
      cases hget
      have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
        unfold nextInstrPosNat; rw [himm]
      rw [hnext] at rest'
      have hlt' : n < (base + 1 + imm.length) + rest.length := by
        have : base + (byte :: (imm ++ rest)).length = (base + 1 + imm.length) + rest.length := by
          rw [hseglen]; omega
        omega
      exact ih (base + 1 + imm.length) hmatch' n rest' hlt'

/-! ## §3 — the lowering emits safe-aligned byte streams

Every emission helper produces a `SegAlignedSafe` segment: each emitted opcode is a concrete
non-CREATE byte (`decide` discharges `parseInstr byte ∉ {CREATE, CREATE2}` for each of the 16),
and the immediate widths match `pushArgWidth` exactly (already proven for `SegAligned`). These
mirror the `segAligned_*` family of `JumpValid.lean` one-for-one. -/

/-- `emitImm w = PUSH32 :: wordBytesBE w` is safe-aligned: `PUSH32` is not CREATE. -/
theorem segAlignedSafe_emitImm (w : Word) : SegAlignedSafe (emitImm w) := by
  refine SegAlignedSafe.push Byte.push32 (wordBytesBE w) ?_ (by decide)
  show (wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [wordBytesBE, Evm.pushArgWidth]

/-- `emitDest off = PUSH4 :: offsetBytesBE off` is safe-aligned: `PUSH4` is not CREATE. -/
theorem segAlignedSafe_emitDest (off : Nat) : SegAlignedSafe (emitDest off) := by
  refine SegAlignedSafe.push Byte.push4 (offsetBytesBE off) ?_ (by decide)
  show (offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [offsetBytesBE, Evm.pushArgWidth]

/-- The call-result rematerialisation `emitImm slot ++ [MLOAD]` is safe-aligned. -/
theorem segAlignedSafe_slot (slot : Nat) :
    SegAlignedSafe (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedSafe_emitImm (UInt256.ofNat slot)).append
    (SegAlignedSafe.nonpush Byte.mload (by decide) (by decide))

/-- `materialiseExpr defs fuel e` is safe-aligned. Mirrors `segAligned_materialiseExpr`:
literal leaves are `emitImm`, the `.gas` leaf is the non-CREATE `GAS` opcode, the binary/sload
recursions append safe sub-sequences then a single non-CREATE zero-width opcode. -/
theorem segAlignedSafe_materialiseExpr (defs : Tmp → Option Expr) :
    ∀ (fuel : Nat) (e : Expr), SegAlignedSafe (materialiseExpr defs fuel e)
  | 0,      .imm w  => segAlignedSafe_emitImm w
  | f + 1,  .imm w  => segAlignedSafe_emitImm w
  | 0,      .tmp _  => .nil
  | 0,      .add _ _ => .nil
  | 0,      .lt _ _ => .nil
  | 0,      .sload _ => .nil
  | 0,      .gas    => .nil
  | 0,      .slot slot => segAlignedSafe_slot slot
  | f + 1,  .slot slot => segAlignedSafe_slot slot
  | f + 1,  .tmp t  => by
      rw [show materialiseExpr defs (f+1) (.tmp t)
            = (match defs t with
               | some e => materialiseExpr defs f e
               | none   => emitImm (0 : Word)) from rfl]
      cases defs t with
      | some e => exact segAlignedSafe_materialiseExpr defs f e
      | none   => exact segAlignedSafe_emitImm 0
  | f + 1,  .add a b => by
      rw [show materialiseExpr defs (f+1) (.add a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
            from rfl]
      exact ((segAlignedSafe_materialiseExpr defs f (.tmp b)).append
              (segAlignedSafe_materialiseExpr defs f (.tmp a))).append
            (SegAlignedSafe.nonpush Byte.add (by decide) (by decide))
  | f + 1,  .lt a b => by
      rw [show materialiseExpr defs (f+1) (.lt a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
            from rfl]
      exact ((segAlignedSafe_materialiseExpr defs f (.tmp b)).append
              (segAlignedSafe_materialiseExpr defs f (.tmp a))).append
            (SegAlignedSafe.nonpush Byte.lt (by decide) (by decide))
  | f + 1,  .sload k => by
      rw [show materialiseExpr defs (f+1) (.sload k)
            = materialiseExpr defs f (.tmp k) ++ [Byte.sload] from rfl]
      exact (segAlignedSafe_materialiseExpr defs f (.tmp k)).append
            (SegAlignedSafe.nonpush Byte.sload (by decide) (by decide))
  | f + 1,  .gas    => by
      rw [show materialiseExpr defs (f+1) .gas = [Byte.gas] from rfl]
      exact SegAlignedSafe.nonpush Byte.gas (by decide) (by decide)

/-- `materialise` is safe-aligned (it is `materialiseExpr` on a `.tmp`). -/
theorem segAlignedSafe_materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) :
    SegAlignedSafe (materialise defs fuel t) :=
  segAlignedSafe_materialiseExpr defs fuel (.tmp t)

/-- `emitStmt` is safe-aligned (mirrors `segAligned_emitStmt`): every emitted opcode
(`MSTORE`/`SSTORE`/`CALL`/`POP`/`MLOAD`/`PUSH*`) is non-CREATE. -/
theorem segAlignedSafe_emitStmt (defs : Tmp → Option Expr) (fuel : Nat) (s : Stmt) :
    SegAlignedSafe (emitStmt defs fuel s) := by
  cases s with
  | assign t e =>
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
              exact ((segAlignedSafe_materialiseExpr defs fuel e).append
                      (segAlignedSafe_emitImm (UInt256.ofNat n))).append
                    (SegAlignedSafe.nonpush Byte.mstore (by decide) (by decide))
  | sstore key value =>
      rw [show emitStmt defs fuel (.sstore key value)
            = materialise defs fuel value ++ materialise defs fuel key ++ [Byte.sstore] from rfl]
      exact ((segAlignedSafe_materialise defs fuel value).append
              (segAlignedSafe_materialise defs fuel key)).append
            (SegAlignedSafe.nonpush Byte.sstore (by decide) (by decide))
  | call cs =>
      rw [show emitStmt defs fuel (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ materialise defs fuel cs.callee
              ++ materialise defs fuel cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedSafe_emitImm (0 : Word)).append (segAlignedSafe_emitImm 0)
      have h := h.append (segAlignedSafe_emitImm 0)
      have h := h.append (segAlignedSafe_emitImm 0)
      have h := h.append (segAlignedSafe_emitImm 0)
      have h := h.append (segAlignedSafe_materialise defs fuel cs.callee)
      have h := h.append (segAlignedSafe_materialise defs fuel cs.gasFwd)
      have h := h.append (SegAlignedSafe.nonpush Byte.call (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedSafe.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedSafe_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedSafe.nonpush Byte.mstore (by decide) (by decide))

/-- `emitTerm` is safe-aligned (mirrors `segAligned_emitTerm`): `RETURN`/`STOP`/`JUMP`/`JUMPI`
and the `PUSH4`/`PUSH32` operands are all non-CREATE. -/
theorem segAlignedSafe_emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (t : Term) : SegAlignedSafe (emitTerm defs fuel labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm defs fuel labelOff (.ret tt)
            = materialise defs fuel tt ++ emitImm 0 ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((segAlignedSafe_materialise defs fuel tt).append
              (segAlignedSafe_emitImm 0)).append (segAlignedSafe_emitImm 0)).append
            (SegAlignedSafe.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm defs fuel labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedSafe.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm defs fuel labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedSafe_emitDest _).append
        (SegAlignedSafe.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm defs fuel labelOff (.branch cond thenL elseL)
            = materialise defs fuel cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((segAlignedSafe_materialise defs fuel cond).append
              (segAlignedSafe_emitDest _)).append
              (SegAlignedSafe.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedSafe_emitDest _)).append
            (SegAlignedSafe.nonpush Byte.jump (by decide) (by decide))

/-- `emitBlockBody` is safe-aligned: the block's statements' emissions appended with the
terminator's. -/
theorem segAlignedSafe_emitBlockBody (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedSafe (emitBlockBody defs fuel labelOff b) := by
  unfold emitBlockBody
  refine SegAlignedSafe.append ?_ (segAlignedSafe_emitTerm defs fuel labelOff b.term)
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedSafe_emitStmt defs fuel s).append ih

/-- A lowered block `JUMPDEST :: emitBlockBody` is safe-aligned: the leading `JUMPDEST` is a
non-CREATE zero-width opcode, the body is safe-aligned. -/
theorem segAlignedSafe_loweredBlock (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (b : Block) : SegAlignedSafe (Byte.jumpdest :: emitBlockBody defs fuel labelOff b) := by
  have hjd : SegAlignedSafe [Byte.jumpdest] :=
    SegAlignedSafe.nonpush Byte.jumpdest (by decide) (by decide)
  have := hjd.append (segAlignedSafe_emitBlockBody defs fuel labelOff b)
  simpa using this

/-- The whole flat byte stream `flatBytes prog` is safe-aligned: it is the `flatMap` of the
per-block `JUMPDEST :: emitBlockBody` over all blocks, each safe-aligned
(`segAlignedSafe_loweredBlock`), glued by `SegAlignedSafe.append`. Induction on the block list. -/
theorem segAlignedSafe_flatBytes (prog : Program) : SegAlignedSafe (flatBytes prog) := by
  unfold flatBytes
  set defs := defsOf prog
  set fuel := recomputeFuel prog
  set lo := offsetTable defs fuel prog.blocks
  induction prog.blocks.toList with
  | nil => exact .nil
  | cons b rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedSafe_loweredBlock defs fuel lo b).append ih

/-! ## §4 — the headline: no CREATE/CREATE2 at any reachable boundary of `lower prog`

Composing the whole-program safe alignment (`segAlignedSafe_flatBytes`) with the boundary-walk
transport (`reaches_safe_of_segAlignedSafe`): every boundary reachable from `0` and strictly
inside `flatBytes prog` reads a non-CREATE opcode. This is the **structural** content of the
`NotCreate` modellability clause — it holds for *every* `lower prog`, no program hypothesis. -/

/-- **The structural no-CREATE fact.** At every instruction boundary `n` reachable from `0` in
`lower prog` that lies strictly before the program end, the byte `lower prog` holds parses to a
non-CREATE (and non-CREATE2) opcode. The lowering emits only the 16 non-CREATE opcodes at any
instruction head; this transports that along the boundary walk. -/
theorem reachable_boundary_notCreate (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length) :
    ∃ byte, (lower prog).get? n = some byte
      ∧ Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2 := by
  have hmatch : ∀ j, j < (flatBytes prog).length →
      (lower prog).get? (0 + j) = (flatBytes prog)[j]? := by
    intro j _; rw [Nat.zero_add]; exact lower_get?_eq prog j
  have := reaches_safe_of_segAlignedSafe (lower prog) (flatBytes prog)
    (segAlignedSafe_flatBytes prog) 0 hmatch n hreach (by rwa [Nat.zero_add])
  exact this

/-- **The structural no-CREATE fact, at the `decode` level.** At every instruction boundary `n`
reachable from `0` in `lower prog` (strictly before the program end, and within the `UInt32`
address space), `decode (lower prog) n` reads an opcode that is neither `CREATE` nor `CREATE2`.
This is the form the `currentOp`-level `NotCreate` clause consumes: a reached boundary decodes
its (non-push *or* push) head opcode, and that opcode is never CREATE-family. -/
theorem decode_reachable_boundary_some (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∃ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg)
      ∧ op ≠ .System .CREATE ∧ op ≠ .System .CREATE2 := by
  obtain ⟨byte, hget, hsafe1, hsafe2⟩ := reachable_boundary_notCreate prog n hreach hn
  -- the byte at a reachable boundary is `flatBytes prog`'s byte (`lower_get?_eq`), and `decode`
  -- at that boundary reads `parseInstr byte` as the opcode (non-push or push, by `decode_lower_*`).
  have hbyte : (flatBytes prog)[n]? = some byte := by rw [← lower_get?_eq]; exact hget
  -- split on whether the head byte is a push: either way `decode`'s op component is `parseInstr byte`.
  by_cases hw : Evm.pushArgWidth (Evm.parseInstr byte) = 0
  · exact ⟨Evm.parseInstr byte, .none,
      decode_lower_nonpush prog n byte hbound hbyte hw, hsafe1, hsafe2⟩
  · have hwpos : Evm.pushArgWidth (Evm.parseInstr byte) > 0 := UInt8.pos_iff_ne_zero.mpr hw
    exact ⟨Evm.parseInstr byte, _,
      decode_lower_push prog n byte (Evm.pushArgWidth (Evm.parseInstr byte)) _
        hbound hbyte rfl hwpos rfl, hsafe1, hsafe2⟩

/-- **The structural no-CREATE fact, at the `decode` level.** At every instruction boundary `n`
reachable from `0` in `lower prog` (strictly before the program end, and within the `UInt32`
address space), whatever opcode `decode (lower prog) n` reads is neither `CREATE` nor `CREATE2`.
The `currentOp`-level form of `decode_reachable_boundary_some`. -/
theorem decode_reachable_boundary_notCreate (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∀ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg) →
      op ≠ .System .CREATE ∧ op ≠ .System .CREATE2 := by
  obtain ⟨op', arg', hdec', hsafe1, hsafe2⟩ :=
    decode_reachable_boundary_some prog n hreach hn hbound
  intro op arg hdec
  rw [hdec'] at hdec
  obtain ⟨hop, _⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hdec)
  subst hop; exact ⟨hsafe1, hsafe2⟩

end Lir

-- Build-enforced axiom-cleanliness guards: the structural no-CREATE chain — the safe-alignment
-- transport (`reaches_safe_of_segAlignedSafe`), the whole-program safe alignment
-- (`segAlignedSafe_flatBytes`) and the two headline forms (`reachable_boundary_notCreate`,
-- `decode_reachable_boundary_notCreate`) all depend only on `[propext, Classical.choice,
-- Quot.sound]`.
#print axioms Lir.reaches_safe_of_segAlignedSafe
#print axioms Lir.segAlignedSafe_flatBytes
#print axioms Lir.reachable_boundary_notCreate
#print axioms Lir.decode_reachable_boundary_some
#print axioms Lir.decode_reachable_boundary_notCreate
