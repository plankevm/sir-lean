import LirLean.Decode.JumpValid
import LirLean.Engine.Descent

/-!
# LirLean — boundary-reachability bricks for the whole-run `AtReachableBoundary` invariant

The whole-run boundary invariant the modellability producer needs is
`∀ fr', Runs (codeFrame params (lower prog)) fr' → AtReachableBoundary prog fr'`
(`hrb` of `BytecodeLayer.Interpreter.lower_modellable`, `V2/Modellable.lean`):
every `Runs`-reachable frame sits at an instruction boundary reachable from `0` and in range.
Proving it is a `Runs`-induction whose `step`/`call` cases need three reachability facts beyond
`JumpValid.lean`; this module supplies all three:

* **`reachesBoundary_of_mem_validJumpDests`** — the *converse* of
  `mem_validJumpDests_of_reachable_jumpdest`: every recorded jump destination
  `x ∈ validJumpDests c 0` is itself a `ReachesBoundary c 0` boundary (it was pushed at a boundary
  the scan reached). Turns a taken `JUMP`/`JUMPI` (`new_pc ∈ fr.validJumps`) back into a
  `ReachesBoundary` witness.
* **`reachesBoundary_nextInstr`** — the *sequential* (fall-through) advance: a reached boundary
  whose byte decodes extends to the next instruction's boundary `nextInstrPosNat n (parseInstr
  byte)`. Turns a non-jump `stepFrame` advance back into a `ReachesBoundary` witness.
* **`decode_reachable_boundary_loweringOp`** — at any reachable in-range boundary the decoded op
  is one of the 18 lowering opcodes (`IsLoweringOp`). The `SegAlignedLowering` allow-list transport;
  `SegAlignedLowering`, `IsLoweringOp` and the whole-program alignment
  (`segAlignedP_flatBytes`) are the strongest instance of the shared `SegAlignedP` tower
  (`Decode/SegAligned.lean`). It *scopes* the per-step pc-advance case analysis to the emitted set.

REMAINING (the `Runs`-induction itself, not yet landed): the per-step pc inversion
`stepFrame fr = .next e → e.pc.toNat` is either `nextInstrPosNat n (decoded op)` (sequential) or a
`fr.validJumps` member (taken JUMP/JUMPI), case-analysed over the 18 `IsLoweringOp` arms (the
`stepFrame_next_accMono` dispatch-walk template of `Engine/StepWalk.lean`, mirrored for the
pc component); plus the in-range `e.pc.toNat < (flatBytes prog).length` preservation. With those,
the base case (`codeFrame` pc = 0, `ReachesBoundary.refl`) and the `call` case
(`resumeAfterCall` pc = call-site pc + 1, the byte after CALL) close the induction via the three
bricks above.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §0 — materialised operands have no CALL/CREATE instruction heads -/

def NoCallCreateOp (op : Operation) : Prop :=
  op ≠ .CALL ∧ op ≠ .System .CREATE ∧ op ≠ .System .CREATE2

instance (op : Operation) : Decidable (NoCallCreateOp op) := by
  unfold NoCallCreateOp
  infer_instance

theorem noCallCreate_of_byte (byte : UInt8) (h : NoCallCreateOp (Evm.parseInstr byte)) :
    Evm.parseInstr byte ≠ .CALL
      ∧ Evm.parseInstr byte ≠ .System .CREATE
      ∧ Evm.parseInstr byte ≠ .System .CREATE2 := h

theorem segAlignedNoCall_emitImm (w : Word) : SegAlignedP NoCallCreateOp (emitImm w) := by
  refine SegAlignedP.push Byte.push32 (wordBytesBE w) ?_ (by decide)
  show (wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [wordBytesBE, Evm.pushArgWidth]

theorem segAlignedNoCall_emitDest (off : Nat) : SegAlignedP NoCallCreateOp (emitDest off) := by
  refine SegAlignedP.push Byte.push4 (offsetBytesBE off) ?_ (by decide)
  show (offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [offsetBytesBE, Evm.pushArgWidth]

theorem segAlignedNoCall_slot (slot : Nat) :
    SegAlignedP NoCallCreateOp (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedNoCall_emitImm (UInt256.ofNat slot)).append
    (SegAlignedP.nonpush Byte.mload (by decide) (by decide))

theorem segAlignedNoCall_matExpr (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP NoCallCreateOp (cache t)) :
    ∀ e, SegAlignedP NoCallCreateOp (matExpr cache e) := by
  intro e
  cases e with
  | imm w => exact segAlignedNoCall_emitImm w
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

theorem segAlignedNoCall_matLoc (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP NoCallCreateOp (cache t)) :
    ∀ loc, SegAlignedP NoCallCreateOp (matLoc cache loc)
  | .remat e => segAlignedNoCall_matExpr cache hcache e
  | .slot n  => segAlignedNoCall_slot n

theorem matStep_noCall_aligned (c : Tmp → List UInt8)
    (hc : ∀ t, SegAlignedP NoCallCreateOp (c t)) (p : Tmp × Loc) :
    ∀ t, SegAlignedP NoCallCreateOp (matStep c p t) := by
  intro t
  simp only [matStep, Function.update_apply]
  by_cases h : t = p.1
  · rw [if_pos h]
    exact segAlignedNoCall_matLoc c hc p.2
  · rw [if_neg h]
    exact hc t

theorem matFold_noCall_aligned (init : Tmp → List UInt8)
    (hinit : ∀ t, SegAlignedP NoCallCreateOp (init t)) (l : List (Tmp × Loc)) :
    ∀ t, SegAlignedP NoCallCreateOp (matFold init l t) := by
  induction l generalizing init with
  | nil => simpa [matFold] using hinit
  | cons p rest ih =>
      rw [matFold_cons]
      exact ih (matStep init p) (matStep_noCall_aligned init hinit p)

theorem segAlignedNoCall_matCache (prog : Program) :
    ∀ t, SegAlignedP NoCallCreateOp (matCache prog t) := by
  unfold matCache
  exact matFold_noCall_aligned _ (fun _ => segAlignedNoCall_emitImm 0) (defEnv prog)

theorem segAlignedNoCall_matExpr_matCache (prog : Program) :
    ∀ e, SegAlignedP NoCallCreateOp (matExpr (matCache prog) e) :=
  segAlignedNoCall_matExpr (matCache prog) (segAlignedNoCall_matCache prog)

theorem segAlignedNoCall_matLoc_matCache (prog : Program) :
    ∀ loc, SegAlignedP NoCallCreateOp (matLoc (matCache prog) loc) :=
  segAlignedNoCall_matLoc (matCache prog) (segAlignedNoCall_matCache prog)

theorem segAlignedNoCall_emitTerm (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP NoCallCreateOp (cache t)) (labelOff : Nat → Nat) (t : Term) :
    SegAlignedP NoCallCreateOp (emitTerm cache labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm cache labelOff (.ret tt)
            = cache tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((hcache tt).append
              (segAlignedNoCall_emitImm 0)).append
              (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))).append
              (segAlignedNoCall_emitImm 32)).append (segAlignedNoCall_emitImm 0)).append
            (SegAlignedP.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm cache labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedP.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm cache labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedNoCall_emitDest _).append
        (SegAlignedP.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm cache labelOff (.branch cond thenL elseL)
            = cache cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((hcache cond).append
              (segAlignedNoCall_emitDest _)).append
              (SegAlignedP.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedNoCall_emitDest _)).append
            (SegAlignedP.nonpush Byte.jump (by decide) (by decide))

theorem segAlignedNoCall_emitTerm_matCache (prog : Program) (t : Term) :
    SegAlignedP NoCallCreateOp
      (emitTerm (matCache prog) (offsetTable (matCache prog) (defsOf prog) prog.blocks) t) :=
  segAlignedNoCall_emitTerm (matCache prog) (segAlignedNoCall_matCache prog)
    (offsetTable (matCache prog) (defsOf prog) prog.blocks) t

theorem reachesBoundary_drop_segAlignedP {P : Operation → Prop} (c : ByteArray)
    (seg : List UInt8) (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → base + seg.length ≤ n →
        ReachesBoundary c (base + seg.length) n := by
  induction hseg with
  | nil =>
      intro base _ n hreach _
      simpa using hreach
  | cons byte imm rest himm _hP hrest ih =>
      intro base hmatch n hreach hle
      have hhead : c.get? base = some byte := by
        have := hmatch 0 (by simp)
        simpa using this
      have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
        simp [List.length_append]
        omega
      have hmatch' : ∀ j, j < rest.length →
          c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
        intro j hj
        have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
          rw [hseglen]; omega
        have := hmatch (1 + imm.length + j) hj'
        rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at this
        rw [this]
        rw [show 1 + imm.length + j = (imm.length + j) + 1 from by omega,
            List.getElem?_cons_succ, List.getElem?_append_right (by omega),
            show imm.length + j - imm.length = j from by omega]
      cases hreach with
      | refl _ =>
          rw [hseglen] at hle
          omega
      | step hget restReach =>
          rw [hhead] at hget
          cases hget
          have hnext : Evm.nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
            unfold Evm.nextInstrPosNat
            rw [himm]
          rw [hnext] at restReach
          have hle' : (base + 1 + imm.length) + rest.length ≤ n := by
            rw [hseglen] at hle
            omega
          have := ih (base + 1 + imm.length) hmatch' n restReach hle'
          simpa [hseglen, Nat.add_assoc] using this

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

/-! ## §3 — every reachable-boundary head is one of the 18 lowering opcodes

The lowering emits exactly the 18 opcodes
`{STOP, ADD, LT, POP, MLOAD, MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4,
PUSH32, CALL, RETURN, CREATE, CREATE2}` at any instruction head. That allow-list (`IsLoweringOp`)
is the tightest per-head predicate, so `Decode/SegAligned.lean` proves the whole-program alignment
and interior transport there once; here we only instantiate them. This *scopes* the per-step
pc-advance analysis: at any reachable boundary the decoded op is one of these 18, so the whole-run
boundary invariant's step case only needs those arms. -/

/-- Alignment with `IsLoweringOp` instruction heads — the strongest instance of the shared
parameterized tower (`SegAlignedP`, `Decode/SegAligned.lean`). -/
abbrev SegAlignedLowering : List UInt8 → Prop := SegAlignedP IsLoweringOp

/-- **The transport.** A boundary `n` reached from `base` and strictly inside a
`SegAlignedLowering` segment matching `c` reads a byte whose op is one of the 18 lowering
opcodes. The interior transport (`reaches_P_of_segAlignedP`) at `IsLoweringOp`. -/
theorem reaches_loweringOp_of_segAlignedLowering (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedLowering seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte ∧ IsLoweringOp (Evm.parseInstr byte) :=
  reaches_P_of_segAlignedP c seg hseg

/-- The whole flat byte stream is allow-listed: `segAlignedP_flatBytes` at `IsLoweringOp`
(`Decode/SegAligned.lean`). -/
theorem segAlignedLowering_flatBytes (prog : Program) : SegAlignedLowering (flatBytes prog) :=
  segAlignedP_flatBytes prog

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
boundary invariant's per-step pc analysis to the 18 emitted opcodes. -/
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

theorem decode_of_loweringByte {prog : Program} {b : Nat} {byte : UInt8}
    (hbnd : b < 2 ^ 32) (hget : (lower prog).get? b = some byte) :
    ∃ arg, Evm.decode (lower prog) (UInt32.ofNat b) = some (Evm.parseInstr byte, arg) := by
  have hbyte : (flatBytes prog)[b]? = some byte := by rw [← lower_get?_eq]; exact hget
  by_cases hw : Evm.pushArgWidth (Evm.parseInstr byte) = 0
  · exact ⟨.none, decode_lower_nonpush prog b byte hbnd hbyte hw⟩
  · have hwpos : Evm.pushArgWidth (Evm.parseInstr byte) > 0 := UInt8.pos_iff_ne_zero.mpr hw
    exact ⟨_,
      decode_lower_push prog b byte (Evm.pushArgWidth (Evm.parseInstr byte)) _
        hbnd hbyte rfl hwpos rfl⟩

theorem loweringOp_call_family_eq_call {op : Evm.Operation} (hop : IsLoweringOp op)
    (h :
      op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL) :
    op = .CALL := by
  rcases h with h | h | h | h
  · exact h
  · subst h; unfold IsLoweringOp at hop; simp at hop
  · subst h; unfold IsLoweringOp at hop; simp at hop
  · subst h; unfold IsLoweringOp at hop; simp at hop

theorem stepFrame_needsCall_lowering_site_inv {prog : Program} {fr : Evm.Frame}
    {cp : Evm.CallParams} {pd : Evm.PendingCall} {b : Nat} {byte : UInt8}
    (hcode : fr.exec.executionEnv.code = lower prog) (hpc : fr.exec.pc = UInt32.ofNat b)
    (hbnd : b < 2 ^ 32) (hget : (lower prog).get? b = some byte)
    (hop : IsLoweringOp (Evm.parseInstr byte))
    (hstep : Evm.stepFrame fr = .needsCall cp pd) :
    Evm.parseInstr byte = .CALL ∧ pd.frame.exec.pc = fr.exec.pc
      ∧ pd.frame.validJumps = fr.validJumps := by
  obtain ⟨arg, hdec⟩ := decode_of_loweringByte (prog := prog) hbnd hget
  obtain ⟨hopFam, hppc, hpvj, _⟩ := Evm.stepFrame_needsCall_site_inv hstep
  have hgetD :
      (Evm.decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none)).1
        = Evm.parseInstr byte := by
    simp [hcode, hpc, hdec]
  have hfam :
      Evm.parseInstr byte = .CALL ∨ Evm.parseInstr byte = .CALLCODE
        ∨ Evm.parseInstr byte = .DELEGATECALL ∨ Evm.parseInstr byte = .STATICCALL := by
    simpa [hgetD] using hopFam
  exact ⟨loweringOp_call_family_eq_call hop hfam, hppc, hpvj⟩

theorem stepFrame_needsCreate_lowering_site_inv {prog : Program} {fr : Evm.Frame}
    {cp : Evm.CreateParams} {pd : Evm.PendingCreate} {b : Nat} {byte : UInt8}
    (hcode : fr.exec.executionEnv.code = lower prog) (hpc : fr.exec.pc = UInt32.ofNat b)
    (hbnd : b < 2 ^ 32) (hget : (lower prog).get? b = some byte)
    (_hop : IsLoweringOp (Evm.parseInstr byte))
    (hstep : Evm.stepFrame fr = .needsCreate cp pd) :
    (Evm.parseInstr byte = .System .CREATE ∨ Evm.parseInstr byte = .System .CREATE2)
      ∧ pd.frame.exec.pc = fr.exec.pc ∧ pd.frame.validJumps = fr.validJumps := by
  obtain ⟨arg, hdec⟩ := decode_of_loweringByte (prog := prog) hbnd hget
  obtain ⟨hopCreate, hppc, hpvj, _⟩ := Evm.stepFrame_needsCreate_site_inv hstep
  have hgetD :
      (Evm.decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none)).1
        = Evm.parseInstr byte := by
    simp [hcode, hpc, hdec]
  have hcreate :
      Evm.parseInstr byte = .System .CREATE ∨ Evm.parseInstr byte = .System .CREATE2 := by
    simpa [hgetD] using hopCreate
  exact ⟨hcreate, hppc, hpvj⟩


end Lir

-- Build-enforced axiom-cleanliness guards: the boundary-reachability bricks depend only on
-- `[propext, Classical.choice, Quot.sound]`.
