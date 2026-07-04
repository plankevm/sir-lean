import LirLean.NoCreateBytes

/-!
# LirLean — boundary-reachability bricks for the whole-run `AtReachableBoundary` invariant

The whole-run boundary invariant the modellability producer needs is
`∀ fr', Runs (codeFrame params (lower prog)) fr' → AtReachableBoundary prog fr'`
(`hrb` of `BytecodeLayer.Interpreter.lower_modellable`, `V2/Modellable.lean`):
every `Runs`-reachable frame sits at an instruction boundary reachable from `0` and in range.
Proving it is a `Runs`-induction whose `step`/`call` cases need three reachability facts beyond
`JumpValid.lean` / `NoCreateBytes.lean`; this module supplies all three:

* **`reachesBoundary_of_mem_validJumpDests`** — the *converse* of
  `mem_validJumpDests_of_reachable_jumpdest`: every recorded jump destination
  `x ∈ validJumpDests c 0` is itself a `ReachesBoundary c 0` boundary (it was pushed at a boundary
  the scan reached). Turns a taken `JUMP`/`JUMPI` (`new_pc ∈ fr.validJumps`) back into a
  `ReachesBoundary` witness.
* **`reachesBoundary_nextInstr`** — the *sequential* (fall-through) advance: a reached boundary
  whose byte decodes extends to the next instruction's boundary `nextInstrPosNat n (parseInstr
  byte)`. Turns a non-jump `stepFrame` advance back into a `ReachesBoundary` witness.
* **`decode_reachable_boundary_loweringOp`** — at any reachable in-range boundary the decoded op
  is one of the 16 lowering opcodes (`IsLoweringOp`). The `SegAlignedLowering` allow-list transport
  (mirrors `NoCreateBytes`); it *scopes* the per-step pc-advance case analysis to the emitted set.

REMAINING (the `Runs`-induction itself, not yet landed): the per-step pc inversion
`stepFrame fr = .next e → e.pc.toNat` is either `nextInstrPosNat n (decoded op)` (sequential) or a
`fr.validJumps` member (taken JUMP/JUMPI), case-analysed over the 16 `IsLoweringOp` arms (the
`stepFrame_next_accMono` dispatch-walk template of `Engine/StepWalk.lean`, mirrored for the
pc component); plus the in-range `e.pc.toNat < (flatBytes prog).length` preservation. With those,
the base case (`codeFrame` pc = 0, `ReachesBoundary.refl`) and the `call` case
(`resumeAfterCall` pc = call-site pc + 1, the byte after CALL) close the induction via the three
bricks above.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §1 — the converse: a recorded jump destination is a reachable boundary

`validJumpDestsAuxNat c start acc` only ever pushes `i.toUInt32` for boundaries `i` it
reaches from `start` (at which a `JUMPDEST` sits). So any member of the result is either
already in `acc` or such a reached, in-bounds `JUMPDEST` boundary. Induction on the scan's
recursion (well-founded on `c.size - start`). -/

/-- **The scan's membership inversion.** Every `x ∈ validJumpDestsAuxNat c start acc` is
either already in the accumulator `acc`, or it is `j.toUInt32` for some instruction boundary
`j` the walk reaches from `start`, lying in bounds and carrying a `JUMPDEST`. -/
theorem mem_validJumpDestsAuxNat_inv (c : ByteArray) (start : Nat) (acc : Array UInt32)
    {x : UInt32} (hx : x ∈ validJumpDestsAuxNat c start acc) :
    x ∈ acc ∨ ∃ j byte, ReachesBoundary c start j ∧ x = j.toUInt32 ∧ j < c.size
        ∧ c.get? j = some byte ∧ Evm.parseInstr byte = .JUMPDEST := by
  rw [validJumpDestsAuxNat_eq] at hx
  cases hget : c.get? start with
  | none => rw [hget] at hx; exact Or.inl hx
  | some byte =>
    rw [hget] at hx
    simp only at hx
    -- the boundary `start` is in bounds (its byte decoded).
    have hstartlt : start < c.size := lt_size_of_get?_isSome (by rw [hget]; exact Option.isSome_some)
    by_cases hj : Evm.parseInstr byte = .JUMPDEST
    · -- a JUMPDEST at `start`: the recursion ran with `acc.push start.toUInt32`.
      rw [if_pos hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c (nextInstrPosNat start (Evm.parseInstr byte))
        (acc.push start.toUInt32) hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · -- `x` is in `acc.push start.toUInt32`: either in `acc`, or it is `start.toUInt32`.
        rcases Array.mem_push.mp hmem with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨start, byte, ReachesBoundary.refl start, heq, hstartlt, hget, hj⟩
      · -- `x = j.toUInt32` reached from the next boundary: prepend the step at `start`.
        exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach, hxj, hjlt, hjget, hjjd⟩
    · rw [if_neg hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c (nextInstrPosNat start (Evm.parseInstr byte)) acc hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · exact Or.inl hmem
      · exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach, hxj, hjlt, hjget, hjjd⟩
  termination_by c.size - start
  decreasing_by
    all_goals
      simp only [nextInstrPosNat]
      omega

/-- **The converse of `mem_validJumpDests_of_reachable_jumpdest`.** A member `x` of
`validJumpDests c 0` is itself a boundary reachable from `0`: it was pushed at some boundary
`j` the scan reached from `0`, with `x = j.toUInt32` and `j` in bounds. The taken-jump
direction the boundary invariant needs. -/
theorem reachesBoundary_of_mem_validJumpDests (c : ByteArray) {x : UInt32}
    (hx : x ∈ validJumpDests c 0) :
    ∃ j, ReachesBoundary c 0 j ∧ x = j.toUInt32 ∧ j < c.size := by
  rw [validJumpDests] at hx
  simp only [show (0 : UInt32).toNat = 0 from rfl] at hx
  rcases mem_validJumpDestsAuxNat_inv c 0 #[] hx with hmem | ⟨j, _, hreach, hxj, hjlt, _, _⟩
  · exact absurd hmem (by simp)
  · exact ⟨j, hreach, hxj, hjlt⟩

/-! ## §2 — extending a reached boundary by one sequential instruction

A reached boundary whose byte decodes extends to the next instruction's boundary: the walk
appends one `ReachesBoundary.step`. This is the *sequential* (fall-through / non-jump) advance
of the whole-run boundary invariant — it needs no alignment hypothesis, only that the current
boundary's byte is present (which a successful `stepFrame` decode supplies). -/

/-- **The boundary walk extends by one instruction.** If `n` is reachable from `start` and the
byte at `n` decodes, the next instruction boundary `nextInstrPosNat n (parseInstr byte)` is also
reachable. Pure `ReachesBoundary.trans` with a single trailing step. -/
theorem reachesBoundary_nextInstr {c : ByteArray} {start n : Nat} {byte : UInt8}
    (hreach : ReachesBoundary c start n) (hget : c.get? n = some byte) :
    ReachesBoundary c start (nextInstrPosNat n (Evm.parseInstr byte)) :=
  ReachesBoundary.trans hreach (ReachesBoundary.step hget (ReachesBoundary.refl _))

/-! ## §3 — every reachable-boundary head is one of the 16 lowering opcodes

The lowering emits exactly the 16 opcodes
`{STOP, ADD, LT, POP, MLOAD, MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4,
PUSH32, CALL, RETURN}` at any instruction head. We capture that as `IsLoweringOp` and transport
it along the boundary walk (mirroring `NoCreateBytes.lean`'s no-CREATE-head transport). This
*scopes* the per-step pc-advance analysis: at any reachable boundary the decoded op is one of
these 16, so the whole-run boundary invariant's step case only needs those arms. -/

/-- The 16 opcodes the lowering ever emits at an instruction head (`STOP, ADD, LT, POP, MLOAD,
MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4, PUSH32, CALL, RETURN`). -/
def IsLoweringOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD
    ∨ op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP
    ∨ op = .JUMPI ∨ op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4
    ∨ op = .PUSH32 ∨ op = .CALL ∨ op = .RETURN

instance (op : Operation) : Decidable (IsLoweringOp op) := by unfold IsLoweringOp; infer_instance

/-- A `SegAligned` whose every instruction *head* byte parses to one of the 16 lowering
opcodes. The allow-list strengthening of `SegAligned` (mirrors `SegAlignedSafe`). -/
inductive SegAlignedLowering : List UInt8 → Prop where
  | nil : SegAlignedLowering []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hop : IsLoweringOp (Evm.parseInstr byte))
      (hrest : SegAlignedLowering rest) :
      SegAlignedLowering (byte :: (imm ++ rest))

/-- A `SegAlignedLowering` segment is in particular `SegAligned`. -/
theorem SegAlignedLowering.toSegAligned {seg : List UInt8} (h : SegAlignedLowering seg) :
    SegAligned seg := by
  induction h with
  | nil => exact .nil
  | cons byte imm rest himm _ _ ih => exact .cons byte imm rest himm ih

/-- Appending two allow-listed segments yields an allow-listed segment. -/
theorem SegAlignedLowering.append {a b : List UInt8}
    (ha : SegAlignedLowering a) (hb : SegAlignedLowering b) : SegAlignedLowering (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | cons byte imm rest himm hop _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons byte imm (rest ++ b) himm hop ih

/-- A single zero-width lowering opcode is an allow-listed one-instruction segment. -/
theorem SegAlignedLowering.nonpush (byte : UInt8)
    (h : Evm.pushArgWidth (Evm.parseInstr byte) = 0) (hop : IsLoweringOp (Evm.parseInstr byte)) :
    SegAlignedLowering [byte] := by
  have := SegAlignedLowering.cons byte [] [] (by simp [h]) hop .nil
  simpa using this

/-- A lowering push opcode followed by its immediate is an allow-listed one-instruction segment. -/
theorem SegAlignedLowering.push (byte : UInt8) (imm : List UInt8)
    (h : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
    (hop : IsLoweringOp (Evm.parseInstr byte)) :
    SegAlignedLowering (byte :: imm) := by
  have := SegAlignedLowering.cons byte imm [] h hop .nil
  simpa using this

/-- **The transport.** A boundary `n` reached from `base` and strictly inside a
`SegAlignedLowering` segment matching `c` reads a byte whose op is one of the 16 lowering
opcodes. Induction on `SegAlignedLowering` (mirrors `reaches_safe_of_segAlignedSafe`). -/
theorem reaches_loweringOp_of_segAlignedLowering (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedLowering seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte ∧ IsLoweringOp (Evm.parseInstr byte) := by
  induction hseg with
  | nil =>
    intro base _ n hreach hlt
    simp only [List.length_nil, Nat.add_zero] at hlt
    exact absurd (reachesBoundary_le hreach) (by omega)
  | cons byte imm rest himm hop hrest ih =>
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
    | refl _ => exact ⟨byte, hhead, hop⟩
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

/-! ### §3.1 — the lowering emits allow-listed byte streams (mirrors `segAlignedSafe_*`) -/

theorem segAlignedLowering_emitImm (w : Word) : SegAlignedLowering (emitImm w) := by
  refine SegAlignedLowering.push Byte.push32 (wordBytesBE w) ?_ (by decide)
  show (wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [wordBytesBE, Evm.pushArgWidth]

theorem segAlignedLowering_emitDest (off : Nat) : SegAlignedLowering (emitDest off) := by
  refine SegAlignedLowering.push Byte.push4 (offsetBytesBE off) ?_ (by decide)
  show (offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [offsetBytesBE, Evm.pushArgWidth]

theorem segAlignedLowering_slot (slot : Nat) :
    SegAlignedLowering (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedLowering_emitImm (UInt256.ofNat slot)).append
    (SegAlignedLowering.nonpush Byte.mload (by decide) (by decide))

theorem segAlignedLowering_materialiseExpr (defs : Tmp → Option Expr) :
    ∀ (fuel : Nat) (e : Expr), SegAlignedLowering (materialiseExpr defs fuel e)
  | 0,      .imm w  => segAlignedLowering_emitImm w
  | f + 1,  .imm w  => segAlignedLowering_emitImm w
  | 0,      .tmp _  => .nil
  | 0,      .add _ _ => .nil
  | 0,      .lt _ _ => .nil
  | 0,      .sload _ => .nil
  | 0,      .gas    => .nil
  | 0,      .slot slot => segAlignedLowering_slot slot
  | f + 1,  .slot slot => segAlignedLowering_slot slot
  | f + 1,  .tmp t  => by
      rw [show materialiseExpr defs (f+1) (.tmp t)
            = (match defs t with
               | some e => materialiseExpr defs f e
               | none   => emitImm (0 : Word)) from rfl]
      cases defs t with
      | some e => exact segAlignedLowering_materialiseExpr defs f e
      | none   => exact segAlignedLowering_emitImm 0
  | f + 1,  .add a b => by
      rw [show materialiseExpr defs (f+1) (.add a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
            from rfl]
      exact ((segAlignedLowering_materialiseExpr defs f (.tmp b)).append
              (segAlignedLowering_materialiseExpr defs f (.tmp a))).append
            (SegAlignedLowering.nonpush Byte.add (by decide) (by decide))
  | f + 1,  .lt a b => by
      rw [show materialiseExpr defs (f+1) (.lt a b)
            = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
            from rfl]
      exact ((segAlignedLowering_materialiseExpr defs f (.tmp b)).append
              (segAlignedLowering_materialiseExpr defs f (.tmp a))).append
            (SegAlignedLowering.nonpush Byte.lt (by decide) (by decide))
  | f + 1,  .sload k => by
      rw [show materialiseExpr defs (f+1) (.sload k)
            = materialiseExpr defs f (.tmp k) ++ [Byte.sload] from rfl]
      exact (segAlignedLowering_materialiseExpr defs f (.tmp k)).append
            (SegAlignedLowering.nonpush Byte.sload (by decide) (by decide))
  | f + 1,  .gas    => by
      rw [show materialiseExpr defs (f+1) .gas = [Byte.gas] from rfl]
      exact SegAlignedLowering.nonpush Byte.gas (by decide) (by decide)

theorem segAlignedLowering_materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) :
    SegAlignedLowering (materialise defs fuel t) :=
  segAlignedLowering_materialiseExpr defs fuel (.tmp t)

theorem segAlignedLowering_emitStmt (defs : Tmp → Option Expr) (fuel : Nat) (s : Stmt) :
    SegAlignedLowering (emitStmt defs fuel s) := by
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
              exact ((segAlignedLowering_materialiseExpr defs fuel e).append
                      (segAlignedLowering_emitImm (UInt256.ofNat n))).append
                    (SegAlignedLowering.nonpush Byte.mstore (by decide) (by decide))
  | sstore key value =>
      rw [show emitStmt defs fuel (.sstore key value)
            = materialise defs fuel value ++ materialise defs fuel key ++ [Byte.sstore] from rfl]
      exact ((segAlignedLowering_materialise defs fuel value).append
              (segAlignedLowering_materialise defs fuel key)).append
            (SegAlignedLowering.nonpush Byte.sstore (by decide) (by decide))
  | call cs =>
      rw [show emitStmt defs fuel (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ materialise defs fuel cs.callee
              ++ materialise defs fuel cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedLowering_emitImm (0 : Word)).append (segAlignedLowering_emitImm 0)
      have h := h.append (segAlignedLowering_emitImm 0)
      have h := h.append (segAlignedLowering_emitImm 0)
      have h := h.append (segAlignedLowering_emitImm 0)
      have h := h.append (segAlignedLowering_materialise defs fuel cs.callee)
      have h := h.append (segAlignedLowering_materialise defs fuel cs.gasFwd)
      have h := h.append (SegAlignedLowering.nonpush Byte.call (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedLowering.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedLowering_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedLowering.nonpush Byte.mstore (by decide) (by decide))

theorem segAlignedLowering_emitTerm (defs : Tmp → Option Expr) (fuel : Nat) (labelOff : Nat → Nat)
    (t : Term) : SegAlignedLowering (emitTerm defs fuel labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm defs fuel labelOff (.ret tt)
            = materialise defs fuel tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((segAlignedLowering_materialise defs fuel tt).append
              (segAlignedLowering_emitImm 0)).append
              (SegAlignedLowering.nonpush Byte.mstore (by decide) (by decide))).append
              (segAlignedLowering_emitImm 32)).append (segAlignedLowering_emitImm 0)).append
            (SegAlignedLowering.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm defs fuel labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedLowering.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm defs fuel labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedLowering_emitDest _).append
        (SegAlignedLowering.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm defs fuel labelOff (.branch cond thenL elseL)
            = materialise defs fuel cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((segAlignedLowering_materialise defs fuel cond).append
              (segAlignedLowering_emitDest _)).append
              (SegAlignedLowering.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedLowering_emitDest _)).append
            (SegAlignedLowering.nonpush Byte.jump (by decide) (by decide))

theorem segAlignedLowering_emitBlockBody (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedLowering (emitBlockBody defs fuel labelOff b) := by
  unfold emitBlockBody
  refine SegAlignedLowering.append ?_ (segAlignedLowering_emitTerm defs fuel labelOff b.term)
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedLowering_emitStmt defs fuel s).append ih

theorem segAlignedLowering_loweredBlock (defs : Tmp → Option Expr) (fuel : Nat)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedLowering (Byte.jumpdest :: emitBlockBody defs fuel labelOff b) := by
  have hjd : SegAlignedLowering [Byte.jumpdest] :=
    SegAlignedLowering.nonpush Byte.jumpdest (by decide) (by decide)
  have := hjd.append (segAlignedLowering_emitBlockBody defs fuel labelOff b)
  simpa using this

/-- The whole flat byte stream is allow-listed: the `flatMap` of per-block
`JUMPDEST :: emitBlockBody`, each allow-listed. Induction on the block list. -/
theorem segAlignedLowering_flatBytes (prog : Program) : SegAlignedLowering (flatBytes prog) := by
  unfold flatBytes
  set defs := defsOf prog
  set fuel := recomputeFuel prog
  set lo := offsetTable defs fuel prog.blocks
  induction prog.blocks.toList with
  | nil => exact .nil
  | cons b rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedLowering_loweredBlock defs fuel lo b).append ih

/-! ## §4 — the headline: a reachable in-range boundary decodes to a lowering opcode -/

/-- **A reachable in-range boundary's byte parses to a lowering opcode.** Composes the
whole-program allow-list (`segAlignedLowering_flatBytes`) with the transport
(`reaches_loweringOp_of_segAlignedLowering`). -/
theorem reachable_boundary_loweringByte (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length) :
    ∃ byte, (lower prog).get? n = some byte ∧ IsLoweringOp (Evm.parseInstr byte) := by
  have hmatch : ∀ j, j < (flatBytes prog).length →
      (lower prog).get? (0 + j) = (flatBytes prog)[j]? := by
    intro j _; rw [Nat.zero_add]; exact lower_get?_eq prog j
  exact reaches_loweringOp_of_segAlignedLowering (lower prog) (flatBytes prog)
    (segAlignedLowering_flatBytes prog) 0 hmatch n hreach (by rwa [Nat.zero_add])

/-- **A reachable in-range boundary decodes to a lowering opcode.** The `decode`-level form:
at every boundary `n` reachable from `0` (strictly before the program end, within `UInt32`),
`decode (lower prog) n` reads an op satisfying `IsLoweringOp`. This *scopes* the whole-run
boundary invariant's per-step pc analysis to the 16 emitted opcodes. -/
theorem decode_reachable_boundary_loweringOp (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∃ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg) ∧ IsLoweringOp op := by
  obtain ⟨byte, hget, hop⟩ := reachable_boundary_loweringByte prog n hreach hn
  have hbyte : (flatBytes prog)[n]? = some byte := by rw [← lower_get?_eq]; exact hget
  by_cases hw : Evm.pushArgWidth (Evm.parseInstr byte) = 0
  · exact ⟨Evm.parseInstr byte, .none,
      decode_lower_nonpush prog n byte hbound hbyte hw, hop⟩
  · have hwpos : Evm.pushArgWidth (Evm.parseInstr byte) > 0 := UInt8.pos_iff_ne_zero.mpr hw
    exact ⟨Evm.parseInstr byte, _,
      decode_lower_push prog n byte (Evm.pushArgWidth (Evm.parseInstr byte)) _
        hbound hbyte rfl hwpos rfl, hop⟩

end Lir

-- Build-enforced axiom-cleanliness guards: the boundary-reachability bricks depend only on
-- `[propext, Classical.choice, Quot.sound]`.
