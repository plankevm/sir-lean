import LirLean.Decode.DecodeLower
import Evm

/-!
# LirLean — the predicate-parameterized instruction-alignment tower

`JumpValid.lean` and `BoundaryReach.lean` each once carried a private
copy of the *same* inductive — an instruction-aligned byte list (each opcode byte followed by
exactly `pushArgWidth` immediate bytes) — differing **only** by a per-head predicate `P` on the
decoded opcode:

* `SegAligned`         (`JumpValid`)      — `P = fun _ => True`;
* `SegAlignedLowering` (`BoundaryReach`)  — `P = IsLoweringOp` (the 18 emitted opcodes).

(A third `SegAlignedSafe` / `NoCreateBytes` tower — `P op = op ≠ CREATE ∧ op ≠ CREATE2` — was
DELETED once `emitStmt .create` made CREATE/CREATE2 emitted opcodes: "the lowered code contains
no CREATE bytes" is no longer true.)

The entire supporting ladder (composition + the two boundary-walk transports + the
lowering-emits-aligned lemmas + the whole-program lift) was re-proven per tower, line-for-line
identical modulo the predicate argument. This module collapses that duplication:

* **`SegAlignedP P`** — the one parameterized inductive.
* **`SegAlignedP.mono`** — weaken the predicate pointwise (`P → Q` gives
  `SegAlignedP P → SegAlignedP Q`); the lever that derives the weaker `SegAligned` (`True`) tower
  from the strongest.
* **`SegAlignedP.append/nonpush/push`** — composition, generic in `P`.
* **`reaches_end_of_segAlignedP`** — the predicate-free "walk reaches the segment end" transport
  (the old `reaches_of_segAligned`). `P` is ignored; alignment alone drives it.
* **`reaches_P_of_segAlignedP`** — the interior transport: any boundary reached *strictly inside* a
  matched segment reads a head byte satisfying `P` (generalising
  `reaches_loweringOp_of_segAlignedLowering`).
* **`IsLoweringOp`** (+ `Decidable`) and the **emit-ladder proven ONCE** at `P := IsLoweringOp`
  (the tightest predicate; each concrete opcode discharged by `decide`), culminating in
  `segAlignedP_flatBytes : SegAlignedP IsLoweringOp (flatBytes prog)` — UNCONDITIONAL, over
  the total fold cache `matCache prog` (no fuel, no well-formedness hypothesis).

The two named towers are then thin `abbrev`s of `SegAlignedP _`, and their whole-program /
transport facts are one-line `.mono` corollaries — see `JumpValid`/`BoundaryReach`.

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
The lever deriving `SegAligned` (`True`) from the strongest `SegAlignedLowering` (`IsLoweringOp`).
Induction on the alignment derivation. -/
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

The lowering emits exactly these 18 opcodes at any instruction head. It is the strongest of the
per-head predicates (anything implies `True`), so the emit-ladder is proven ONCE here and the
weaker `SegAligned` tower follows by `SegAlignedP.mono`. -/

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

/-! ## §5 — the emission bricks are `IsLoweringOp`-aligned

Every emission helper produces a `SegAlignedP IsLoweringOp` segment: each emitted opcode is a
concrete lowering byte (`decide` discharges `IsLoweringOp (parseInstr byte)` for each of the 18),
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

/-! ### Legacy fuel-materialisation alignment (unconsumed; P9 deletes with `materialiseExpr`) -/

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

/-! ## §6 — the fold cache is `IsLoweringOp`-aligned pointwise (UNCONDITIONAL)

Proven DIRECTLY over `matCache`/`matExpr`/`matStep` by structural induction — NO fuel. The
engine is `segAlignedP_matExpr` (operand lookups discharged by the pointwise-alignment
hypothesis on the cache) plus `matFold_aligned` (list induction: `matStep` preserves
pointwise-alignment), giving `segAlignedP_matCache` UNCONDITIONALLY (the initial cache
`emitImm 0` is aligned). The `emitStmt`/`emitTerm`/`emitBlockBody`/`flatBytes` ladder then
reuses `SegAlignedP.append` over the per-construct opcode shape. -/

/-- **The fold value channel is aligned pointwise.** If every operand's cached bytes are
`IsLoweringOp`-aligned, then `matExpr cache e` is aligned for every expression `e`. Case analysis
on `e`; operand lookups discharged by `hcache`, composites glued by `SegAlignedP.append`. -/
theorem segAlignedP_matExpr (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ e, SegAlignedP IsLoweringOp (matExpr cache e) := by
  intro e
  cases e with
  | imm w => exact segAlignedP_emitImm w
  | tmp t => exact hcache t
  | add a b =>
      rw [matExpr_add]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.add (by decide) (by decide))
  | lt a b =>
      rw [matExpr_lt]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.lt (by decide) (by decide))
  | sload k =>
      rw [matExpr_sload]
      exact (hcache k).append (SegAlignedP.nonpush Byte.sload (by decide) (by decide))
  | gas =>
      rw [matExpr_gas]
      exact SegAlignedP.nonpush Byte.gas (by decide) (by decide)
  | slot n =>
      rw [matExpr_slot]
      exact segAlignedP_slot n

/-- A `Loc`'s materialised bytes under an aligned cache are aligned. -/
theorem segAlignedP_matLoc (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ loc, SegAlignedP IsLoweringOp (matLoc cache loc)
  | .remat e => segAlignedP_matExpr cache hcache e
  | .slot n  => segAlignedP_slot n

/-- **`matStep` preserves pointwise-alignment.** Extending an aligned cache by binding one tmp to
its `Loc`'s (aligned) bytes keeps the cache pointwise-aligned — the update is aligned at the bound
key (`segAlignedP_matLoc`) and unchanged elsewhere. -/
theorem matStep_aligned (c : Tmp → List UInt8)
    (hc : ∀ t, SegAlignedP IsLoweringOp (c t)) (p : Tmp × Loc) :
    ∀ t, SegAlignedP IsLoweringOp (matStep c p t) := by
  intro t
  simp only [matStep, Function.update_apply]
  by_cases h : t = p.1
  · rw [if_pos h]; exact segAlignedP_matLoc c hc p.2
  · rw [if_neg h]; exact hc t

/-- **The fold preserves pointwise-alignment.** From an aligned initial cache, the whole `matFold`
over any def-env is pointwise-aligned. List induction, `matStep_aligned` at each step. -/
theorem matFold_aligned (init : Tmp → List UInt8)
    (hinit : ∀ t, SegAlignedP IsLoweringOp (init t)) (l : List (Tmp × Loc)) :
    ∀ t, SegAlignedP IsLoweringOp (matFold init l t) := by
  induction l generalizing init with
  | nil => simpa [matFold] using hinit
  | cons p rest ih =>
      rw [matFold_cons]
      exact ih (matStep init p) (matStep_aligned init hinit p)

/-- **`matCache prog` is pointwise `IsLoweringOp`-aligned, UNCONDITIONALLY.** The initial cache
`fun _ => emitImm 0` is aligned, and the fold preserves alignment. No well-formedness hypothesis. -/
theorem segAlignedP_matCache (prog : Program) :
    ∀ t, SegAlignedP IsLoweringOp (matCache prog t) := by
  unfold matCache
  exact matFold_aligned _ (fun _ => segAlignedP_emitImm 0) (defEnv prog)

/-- A statement's emitted bytes are aligned under an aligned cache. Operand lookups discharged
by `hcache`; the `assign` def-site uses `segAlignedP_matExpr`. -/
theorem segAlignedP_emitStmt (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc) (s : Stmt) :
    SegAlignedP IsLoweringOp (emitStmt cache alloc s) := by
  cases s with
  | assign t e =>
      rw [show emitStmt cache alloc (.assign t e)
            = (match alloc t with
               | some (.slot n) => matExpr cache e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
               | _ => []) from rfl]
      cases alloc t with
      | none => exact .nil
      | some loc =>
          cases loc with
          | remat => exact .nil
          | slot n =>
              exact ((segAlignedP_matExpr cache hcache e).append
                      (segAlignedP_emitImm (UInt256.ofNat n))).append
                    (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | sstore key value =>
      rw [show emitStmt cache alloc (.sstore key value)
            = cache value ++ cache key ++ [Byte.sstore] from rfl]
      exact ((hcache value).append (hcache key)).append
            (SegAlignedP.nonpush Byte.sstore (by decide) (by decide))
  | call cs =>
      rw [show emitStmt cache alloc (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ cache cs.callee
              ++ cache cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedP_emitImm (0 : Word)).append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (hcache cs.callee)
      have h := h.append (hcache cs.gasFwd)
      have h := h.append (SegAlignedP.nonpush Byte.call (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | create cs =>
      rw [show emitStmt cache alloc (.create cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ (match cs.salt with
                  | some s => cache s ++ [Byte.create2]
                  | none   => [Byte.create])
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have hmid : SegAlignedP IsLoweringOp
          (match cs.salt with
            | some s => cache s ++ [Byte.create2]
            | none   => [Byte.create]) := by
        cases cs.salt with
        | none => exact SegAlignedP.nonpush Byte.create (by decide) (by decide)
        | some s =>
            exact (hcache s).append (SegAlignedP.nonpush Byte.create2 (by decide) (by decide))
      have h := (segAlignedP_emitImm (0 : Word)).append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append hmid
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))

/-- A terminator's emitted bytes are aligned under an aligned cache. -/
theorem segAlignedP_emitTerm (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (labelOff : Nat → Nat) (t : Term) :
    SegAlignedP IsLoweringOp (emitTerm cache labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm cache labelOff (.ret tt)
            = cache tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((hcache tt).append
              (segAlignedP_emitImm 0)).append
              (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))).append
              (segAlignedP_emitImm 32)).append (segAlignedP_emitImm 0)).append
            (SegAlignedP.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm cache labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedP.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm cache labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedP_emitDest _).append
        (SegAlignedP.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm cache labelOff (.branch cond thenL elseL)
            = cache cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((hcache cond).append
              (segAlignedP_emitDest _)).append
              (SegAlignedP.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedP_emitDest _)).append
            (SegAlignedP.nonpush Byte.jump (by decide) (by decide))

/-- A block body's emitted bytes are aligned under an aligned cache. -/
theorem segAlignedP_emitBlockBody (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (emitBlockBody cache alloc labelOff b) := by
  unfold emitBlockBody
  refine SegAlignedP.append ?_ (segAlignedP_emitTerm cache hcache labelOff b.term)
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedP_emitStmt cache hcache alloc s).append ih

/-- A lowered block `JUMPDEST :: emitBlockBody` is `IsLoweringOp`-aligned: the leading
`JUMPDEST` is a zero-width lowering opcode, the body is aligned. -/
theorem segAlignedP_loweredBlock (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (Byte.jumpdest :: emitBlockBody cache alloc labelOff b) := by
  have hjd : SegAlignedP IsLoweringOp [Byte.jumpdest] :=
    SegAlignedP.nonpush Byte.jumpdest (by decide) (by decide)
  have := hjd.append (segAlignedP_emitBlockBody cache hcache alloc labelOff b)
  simpa using this

/-- **The whole flat byte stream `flatBytes prog` is `IsLoweringOp`-aligned, UNCONDITIONALLY.**
The `flatMap` of per-block `JUMPDEST :: emitBlockBody`, each aligned
(`segAlignedP_loweredBlock`, cache aligned by `segAlignedP_matCache`), glued by
`SegAlignedP.append`. No well-formedness hypothesis. -/
theorem segAlignedP_flatBytes (prog : Program) :
    SegAlignedP IsLoweringOp (flatBytes prog) := by
  have hcache : ∀ t, SegAlignedP IsLoweringOp (matCache prog t) := segAlignedP_matCache prog
  unfold flatBytes
  set cache := matCache prog
  set alloc := defsOf prog
  set lo := offsetTable cache alloc prog.blocks
  induction prog.blocks.toList with
  | nil => exact .nil
  | cons b rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedP_loweredBlock cache hcache alloc lo b).append ih

end Lir
