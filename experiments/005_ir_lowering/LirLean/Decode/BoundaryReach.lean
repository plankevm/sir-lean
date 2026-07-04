import LirLean.Decode.NoCreateBytes

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
  is one of the 16 lowering opcodes (`IsLoweringOp`). The `SegAlignedLowering` allow-list transport;
  `SegAlignedLowering`, `IsLoweringOp` and the whole-program alignment
  (`segAlignedP_flatBytes`) are the strongest instance of the shared `SegAlignedP` tower
  (`LirLean/SegAligned.lean`). It *scopes* the per-step pc-advance case analysis to the emitted set.

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
PUSH32, CALL, RETURN}` at any instruction head. That allow-list (`IsLoweringOp`) is the tightest
of the three per-head predicates, so `LirLean/SegAligned.lean` proves the whole-program alignment
and interior transport there once; here we only instantiate them. This *scopes* the per-step
pc-advance analysis: at any reachable boundary the decoded op is one of these 16, so the whole-run
boundary invariant's step case only needs those arms. -/

/-- Alignment with `IsLoweringOp` instruction heads — the strongest instance of the shared
parameterized tower (`SegAlignedP`, `LirLean/SegAligned.lean`). -/
abbrev SegAlignedLowering : List UInt8 → Prop := SegAlignedP IsLoweringOp

/-- **The transport.** A boundary `n` reached from `base` and strictly inside a
`SegAlignedLowering` segment matching `c` reads a byte whose op is one of the 16 lowering
opcodes. The interior transport (`reaches_P_of_segAlignedP`) at `IsLoweringOp`. -/
theorem reaches_loweringOp_of_segAlignedLowering (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedLowering seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte ∧ IsLoweringOp (Evm.parseInstr byte) :=
  reaches_P_of_segAlignedP c seg hseg

/-- The whole flat byte stream is allow-listed: `segAlignedP_flatBytes` at `IsLoweringOp`
(`LirLean/SegAligned.lean`). -/
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
