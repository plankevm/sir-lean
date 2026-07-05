import LirLean.Decode.DecodeLower
import Evm

/-!
# LirLean — the predicate-parameterized instruction-alignment tower

`JumpValid.lean`, `NoCreateBytes.lean` and `BoundaryReach.lean` each once carried a private
copy of the *same* inductive — an instruction-aligned byte list (each opcode byte followed by
exactly `pushArgWidth` immediate bytes) — differing **only** by a per-head predicate `P` on the
decoded opcode:

* `SegAligned`         (`JumpValid`)      — `P = fun _ => True`;
* `SegAlignedSafe`     (`NoCreateBytes`)  — `P op = op ≠ CREATE ∧ op ≠ CREATE2`;
* `SegAlignedLowering` (`BoundaryReach`)  — `P = IsLoweringOp` (the 16 emitted opcodes).

The entire supporting ladder (composition + the two boundary-walk transports + the
lowering-emits-aligned lemmas + the whole-program lift) was re-proven three times, line-for-line
identical modulo the predicate argument. This module collapses that triplication:

* **`SegAlignedP P`** — the one parameterized inductive.
* **`SegAlignedP.mono`** — weaken the predicate pointwise (`P → Q` gives
  `SegAlignedP P → SegAlignedP Q`); the lever that derives the two weaker towers from the strongest.
* **`SegAlignedP.append/nonpush/push`** — composition, generic in `P`.
* **`reaches_end_of_segAlignedP`** — the predicate-free "walk reaches the segment end" transport
  (the old `reaches_of_segAligned`). `P` is ignored; alignment alone drives it.
* **`reaches_P_of_segAlignedP`** — the interior transport: any boundary reached *strictly inside* a
  matched segment reads a head byte satisfying `P` (the merged
  `reaches_safe_of_segAlignedSafe` / `reaches_loweringOp_of_segAlignedLowering`).
* **`IsLoweringOp`** (+ `Decidable`) and the **emit-ladder proven ONCE** at `P := IsLoweringOp`
  (the tightest predicate; each concrete opcode discharged by `decide`), culminating in
  `segAlignedP_flatBytes : SegAlignedP IsLoweringOp (flatBytes prog)`.

The three named towers are then thin `abbrev`s of `SegAlignedP _`, and their whole-program /
transport facts are one-line `.mono` corollaries — see `JumpValid`/`NoCreateBytes`/`BoundaryReach`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §0 — generic `ReachesBoundary` helpers shared by the transports -/

/-- The boundary walk never decreases the position: a reachable boundary is `≥` the start. -/
theorem reachesBoundary_le {c : ByteArray} {a n : Nat} (h : ReachesBoundary c a n) : a ≤ n := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step _ _ ih => exact Nat.le_trans (Nat.le_of_lt (nextInstrPosNat_gt _ _)) ih

/-! ## §1 — the parameterized inductive

`SegAlignedP P seg`: the byte list `seg` is a concatenation of complete EVM instructions — each
opcode byte `b` immediately followed by exactly `(pushArgWidth (parseInstr b)).toNat` immediate
bytes — with, additionally, every opcode *head* byte satisfying `P (parseInstr b)`. Instantiating
`P` recovers the three concrete towers. -/

inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hP : P (Evm.parseInstr byte))
      (hrest : SegAlignedP P rest) :
      SegAlignedP P (byte :: (imm ++ rest))

/-- **Predicate monotonicity.** If `P` implies `Q` pointwise, a `P`-aligned segment is `Q`-aligned.
The lever deriving `SegAligned` (`True`) and `SegAlignedSafe` (`notCreate`) from the strongest
`SegAlignedLowering` (`IsLoweringOp`). Induction on the alignment derivation. -/
theorem SegAlignedP.mono {P Q : Operation → Prop} (h : ∀ op, P op → Q op) :
    ∀ {seg : List UInt8}, SegAlignedP P seg → SegAlignedP Q seg := by
  intro seg hseg
  induction hseg with
  | nil => exact .nil
  | cons byte imm rest himm hP _ ih => exact .cons byte imm rest himm (h _ hP) ih

/-! ### §1.1 — composition -/

/-- Appending two aligned segments yields an aligned segment. Induction on the first. -/
theorem SegAlignedP.append {P : Operation → Prop} {a b : List UInt8}
    (ha : SegAlignedP P a) (hb : SegAlignedP P b) : SegAlignedP P (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | cons byte imm rest himm hP _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons byte imm (rest ++ b) himm hP ih

/-- A single zero-width (non-push) opcode satisfying `P` is an aligned one-instruction segment. -/
theorem SegAlignedP.nonpush {P : Operation → Prop} (byte : UInt8)
    (h : Evm.pushArgWidth (Evm.parseInstr byte) = 0) (hP : P (Evm.parseInstr byte)) :
    SegAlignedP P [byte] := by
  have := SegAlignedP.cons (P := P) byte [] [] (by simp [h]) hP .nil
  simpa using this

/-- A push opcode satisfying `P`, followed by exactly `pushArgWidth` immediate bytes, is an
aligned one-instruction segment. -/
theorem SegAlignedP.push {P : Operation → Prop} (byte : UInt8) (imm : List UInt8)
    (h : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
    (hP : P (Evm.parseInstr byte)) : SegAlignedP P (byte :: imm) := by
  have := SegAlignedP.cons (P := P) byte imm [] h hP .nil
  simpa using this

/-! ## §2 — the reach-END transport (predicate-free)

If `c`'s bytes over `[base, base + seg.length)` are exactly `seg`, and `seg` is instruction-aligned,
the boundary walk reaches `base + seg.length` from `base`. `P` is not consulted — alignment alone
drives the walk. Induction on the alignment derivation. -/

theorem reaches_end_of_segAlignedP {P : Operation → Prop} (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ReachesBoundary c base (base + seg.length) := by
  induction hseg with
  | nil =>
    intro base _
    simpa using ReachesBoundary.refl (c := c) base
  | cons byte imm rest himm _ hrest ih =>
    intro base hmatch
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp)
      simpa using this
    have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
      unfold nextInstrPosNat; rw [himm]
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
        rw [hseglen]; omega
      have := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at this
      rw [this]
      rw [show (1 + imm.length + j) = (imm.length + j) + 1 from by omega,
          List.getElem?_cons_succ, List.getElem?_append_right (by omega),
          show imm.length + j - imm.length = j from by omega]
    have hih := ih (base + 1 + imm.length) hmatch'
    refine .step (byte := byte) hhead ?_
    rw [hnext]
    rw [show base + (byte :: (imm ++ rest)).length = (base + 1 + imm.length) + rest.length from by
          rw [hseglen]; omega]
    exact hih

/-! ## §3 — the interior transport (predicate-carrying)

If `c` matches a `SegAlignedP P` segment `seg` over `[base, base + seg.length)`, then any boundary
`n` the walk reaches from `base` **strictly inside** the segment (`n < base + seg.length`) reads a
head byte satisfying `P`. Induction on the alignment derivation; the head boundary reads the
`P`-satisfying head, a deeper boundary lands in the aligned `rest` where the IH applies. -/

theorem reaches_P_of_segAlignedP {P : Operation → Prop} (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte ∧ P (Evm.parseInstr byte) := by
  induction hseg with
  | nil =>
    intro base _ n hreach hlt
    simp only [List.length_nil, Nat.add_zero] at hlt
    exact absurd (reachesBoundary_le hreach) (by omega)
  | cons byte imm rest himm hP hrest ih =>
    intro base hmatch n hreach hlt
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp); simpa using this
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
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
    cases hreach with
    | refl _ =>
      exact ⟨byte, hhead, hP⟩
    | step hget rest' =>
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

/-! ## §4 — the tightest predicate: `IsLoweringOp`

The lowering emits exactly these 16 opcodes at any instruction head. It is the strongest of the
three per-head predicates (every one of the 16 is non-CREATE, and anything implies `True`), so the
emit-ladder is proven ONCE here and the weaker towers follow by `SegAlignedP.mono`. -/

/-- The 18 opcodes the lowering ever emits at an instruction head (`STOP, ADD, LT, POP, MLOAD,
MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4, PUSH32, CALL, RETURN`, plus `CREATE`
/`CREATE2` now that `emitStmt .create` emits them). -/
def IsLoweringOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD
    ∨ op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP
    ∨ op = .JUMPI ∨ op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4
    ∨ op = .PUSH32 ∨ op = .CALL ∨ op = .RETURN
    ∨ op = .System .CREATE ∨ op = .System .CREATE2

instance (op : Operation) : Decidable (IsLoweringOp op) := by unfold IsLoweringOp; infer_instance

/-! ## §5 — the lowering emits `IsLoweringOp`-aligned byte streams (the ladder, proven ONCE)

Every emission helper produces a `SegAlignedP IsLoweringOp` segment: each emitted opcode is a
concrete lowering byte (`decide` discharges `IsLoweringOp (parseInstr byte)` for each of the 16),
and the immediate widths match `pushArgWidth` by construction. -/

theorem segAlignedP_emitImm (w : Word) : SegAlignedP IsLoweringOp (emitImm w) := by
  refine SegAlignedP.push Byte.push32 (wordBytesBE w) ?_ (by decide)
  show (wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [wordBytesBE, Evm.pushArgWidth]

theorem segAlignedP_emitDest (off : Nat) : SegAlignedP IsLoweringOp (emitDest off) := by
  refine SegAlignedP.push Byte.push4 (offsetBytesBE off) ?_ (by decide)
  show (offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [offsetBytesBE, Evm.pushArgWidth]

theorem segAlignedP_slot (slot : Nat) :
    SegAlignedP IsLoweringOp (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedP_emitImm (UInt256.ofNat slot)).append
    (SegAlignedP.nonpush Byte.mload (by decide) (by decide))

theorem segAlignedP_materialiseExpr (defs : Tmp → Option Expr) :
    ∀ (fuel : Nat) (e : Expr), SegAlignedP IsLoweringOp (materialiseExpr defs fuel e)
  | 0,      .imm w  => segAlignedP_emitImm w
  | f + 1,  .imm w  => segAlignedP_emitImm w
  | 0,      .tmp _  => .nil
  | 0,      .add _ _ => .nil
  | 0,      .lt _ _ => .nil
  | 0,      .sload _ => .nil
  | 0,      .gas    => .nil
  | 0,      .slot slot => segAlignedP_slot slot
  | f + 1,  .slot slot => segAlignedP_slot slot
  | f + 1,  .tmp t  => by
      rw [show materialiseExpr defs (f+1) (.tmp t)
            = (match defs t with
               | some e => materialiseExpr defs f e
               | none   => emitImm (0 : Word)) from rfl]
      cases defs t with
      | some e => exact segAlignedP_materialiseExpr defs f e
      | none   => exact segAlignedP_emitImm 0
  | f + 1,  .add a b => by
      rw [show materialiseExpr defs (f+1) (.add a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
            from rfl]
      exact ((segAlignedP_materialiseExpr defs f (.tmp b)).append
              (segAlignedP_materialiseExpr defs f (.tmp a))).append
            (SegAlignedP.nonpush Byte.add (by decide) (by decide))
  | f + 1,  .lt a b => by
      rw [show materialiseExpr defs (f+1) (.lt a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
            from rfl]
      exact ((segAlignedP_materialiseExpr defs f (.tmp b)).append
              (segAlignedP_materialiseExpr defs f (.tmp a))).append
            (SegAlignedP.nonpush Byte.lt (by decide) (by decide))
  | f + 1,  .sload k => by
      rw [show materialiseExpr defs (f+1) (.sload k)
            = materialiseExpr defs f (.tmp k) ++ [Byte.sload] from rfl]
      exact (segAlignedP_materialiseExpr defs f (.tmp k)).append
            (SegAlignedP.nonpush Byte.sload (by decide) (by decide))
  | f + 1,  .gas    => by
      rw [show materialiseExpr defs (f+1) .gas = [Byte.gas] from rfl]
      exact SegAlignedP.nonpush Byte.gas (by decide) (by decide)

theorem segAlignedP_materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) :
    SegAlignedP IsLoweringOp (materialise defs fuel t) :=
  segAlignedP_materialiseExpr defs fuel (.tmp t)

theorem segAlignedP_emitStmt (defs : Tmp → Option Expr) (fuel : Nat) (s : Stmt) :
    SegAlignedP IsLoweringOp (emitStmt defs fuel s) := by
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
              exact ((segAlignedP_materialiseExpr defs fuel e).append
                      (segAlignedP_emitImm (UInt256.ofNat n))).append
                    (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | sstore key value =>
      rw [show emitStmt defs fuel (.sstore key value)
            = materialise defs fuel value ++ materialise defs fuel key ++ [Byte.sstore] from rfl]
      exact ((segAlignedP_materialise defs fuel value).append
              (segAlignedP_materialise defs fuel key)).append
            (SegAlignedP.nonpush Byte.sstore (by decide) (by decide))
  | call cs =>
      rw [show emitStmt defs fuel (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ materialise defs fuel cs.callee
              ++ materialise defs fuel cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedP_emitImm (0 : Word)).append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_materialise defs fuel cs.callee)
      have h := h.append (segAlignedP_materialise defs fuel cs.gasFwd)
      have h := h.append (SegAlignedP.nonpush Byte.call (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | create cs =>
      rw [show emitStmt defs fuel (.create cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ (match cs.salt with
                  | some s => materialise defs fuel s ++ [Byte.create2]
                  | none   => [Byte.create])
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have hmid : SegAlignedP IsLoweringOp
          (match cs.salt with
            | some s => materialise defs fuel s ++ [Byte.create2]
            | none   => [Byte.create]) := by
        cases cs.salt with
        | none => exact SegAlignedP.nonpush Byte.create (by decide) (by decide)
        | some s =>
            exact (segAlignedP_materialise defs fuel s).append
              (SegAlignedP.nonpush Byte.create2 (by decide) (by decide))
      have h := (segAlignedP_emitImm (0 : Word)).append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append hmid
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))

theorem segAlignedP_emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (t : Term) : SegAlignedP IsLoweringOp (emitTerm defs fuel labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm defs fuel labelOff (.ret tt)
            = materialise defs fuel tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((segAlignedP_materialise defs fuel tt).append
              (segAlignedP_emitImm 0)).append
              (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))).append
              (segAlignedP_emitImm 32)).append (segAlignedP_emitImm 0)).append
            (SegAlignedP.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm defs fuel labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedP.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm defs fuel labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedP_emitDest _).append
        (SegAlignedP.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm defs fuel labelOff (.branch cond thenL elseL)
            = materialise defs fuel cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((segAlignedP_materialise defs fuel cond).append
              (segAlignedP_emitDest _)).append
              (SegAlignedP.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedP_emitDest _)).append
            (SegAlignedP.nonpush Byte.jump (by decide) (by decide))

theorem segAlignedP_emitBlockBody (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (emitBlockBody defs fuel labelOff b) := by
  unfold emitBlockBody
  refine SegAlignedP.append ?_ (segAlignedP_emitTerm defs fuel labelOff b.term)
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedP_emitStmt defs fuel s).append ih

/-- A lowered block `JUMPDEST :: emitBlockBody` is `IsLoweringOp`-aligned: the leading `JUMPDEST`
is a zero-width lowering opcode, the body is aligned. -/
theorem segAlignedP_loweredBlock (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (Byte.jumpdest :: emitBlockBody defs fuel labelOff b) := by
  have hjd : SegAlignedP IsLoweringOp [Byte.jumpdest] :=
    SegAlignedP.nonpush Byte.jumpdest (by decide) (by decide)
  have := hjd.append (segAlignedP_emitBlockBody defs fuel labelOff b)
  simpa using this

/-- The whole flat byte stream `flatBytes prog` is `IsLoweringOp`-aligned: the `flatMap` of the
per-block `JUMPDEST :: emitBlockBody` over all blocks, each aligned, glued by `SegAlignedP.append`.
Induction on the block list. -/
theorem segAlignedP_flatBytes (prog : Program) :
    SegAlignedP IsLoweringOp (flatBytes prog) := by
  unfold flatBytes
  set defs := defsOf prog
  set fuel := recomputeFuel prog
  set lo := offsetTable defs fuel prog.blocks
  induction prog.blocks.toList with
  | nil => exact .nil
  | cons b rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedP_loweredBlock defs fuel lo b).append ih

end Lir
