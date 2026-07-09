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

The per-step pc inversion
`stepFrame fr = .next e → e.pc` is either `nextInstrPosNat n (decoded op)` (sequential) or a
`fr.validJumps` member (taken JUMP/JUMPI), case-analysed over the 18 `IsLoweringOp` arms below.

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

theorem segAlignedP_flatMap {α : Type _} {P : Evm.Operation → Prop}
    {xs : List α} {f : α → List UInt8}
    (h : ∀ x ∈ xs, SegAlignedP P (f x)) :
    SegAlignedP P (xs.flatMap f) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      rw [List.flatMap_cons]
      exact (h x (by simp)).append (ih (by
        intro y hy
        exact h y (by simp [hy])))

theorem lower_get?_blockPrefix {prog : Program} {i j : Nat}
    (hj : j < ((prog.blocks.toList.take i).flatMap
      (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length) :
    (lower prog).get? j =
      (((prog.blocks.toList.take i).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))[j]?) := by
  rw [lower_get?_eq]
  unfold flatBytes
  change (prog.blocks.toList.flatMap
      (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))[j]? =
      ((prog.blocks.toList.take i).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))[j]?
  conv_lhs =>
    rw [← List.take_append_drop i prog.blocks.toList, List.flatMap_append]
  rw [List.getElem?_append_left hj]

theorem reachesBoundary_drop_to_blockEntry {prog : Program} {L : Label} {blk : Block} {n : Nat}
    (_hb : prog.blocks.toList[L.idx]? = some blk)
    (hreach : Evm.ReachesBoundary (lower prog) 0 n)
    (hle : offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx ≤ n) :
    Evm.ReachesBoundary (lower prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx) n := by
  let pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)
  have hprelen : pre.length =
      offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx := by
    simpa [pre] using flatBytes_block_offset prog L
  have hseg : SegAlignedP IsLoweringOp pre := by
    unfold pre
    apply segAlignedP_flatMap
    intro b _
    exact segAlignedP_loweredBlock (matCache prog) (segAlignedP_matCache prog) (defsOf prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks) b
  have hmatch : ∀ j, j < pre.length → (lower prog).get? (0 + j) = pre[j]? := by
    intro j hj
    rw [Nat.zero_add]
    exact lower_get?_blockPrefix (prog := prog) (i := L.idx) (j := j) (by simpa [pre] using hj)
  have hd := reachesBoundary_drop_segAlignedP (lower prog) pre hseg 0 hmatch n hreach (by
    rw [hprelen]; simpa using hle)
  simpa [hprelen] using hd

theorem reachesBoundary_drop_jumpdest {prog : Program} {L : Label} {blk : Block} {n : Nat}
    (hb : prog.blocks.toList[L.idx]? = some blk)
    (hreach : Evm.ReachesBoundary (lower prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx) n)
    (hle : offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1 ≤ n) :
    Evm.ReachesBoundary (lower prog) (pcOf prog L 0) n := by
  let base := offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx
  have hseg : SegAlignedP IsLoweringOp [Byte.jumpdest] :=
    SegAlignedP.nonpush Byte.jumpdest (by decide) (by decide)
  have hmatch : ∀ j, j < [Byte.jumpdest].length →
      (lower prog).get? (base + j) = [Byte.jumpdest][j]? := by
    intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst j
    rw [Nat.add_zero, lower_get?_eq]
    have hsplit := flatBytes_block_split prog L blk hb
    have hprelen := flatBytes_block_offset prog L
    rw [hsplit]
    rw [show base = ((prog.blocks.toList.take L.idx).flatMap
        (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length from by
        simpa [base] using hprelen.symm]
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
    simp
  have hd := reachesBoundary_drop_segAlignedP (lower prog) [Byte.jumpdest] hseg base hmatch n
    hreach (by simpa [base] using hle)
  have hpc : pcOf prog L 0 = base + 1 := by
    rw [pcOf_eq_anchor prog L blk 0 hb]
    simp [base]
  rwa [hpc]

private theorem lower_match_stmt_prefix {prog : Program} {L : Label} {blk : Block} {pc : Nat} :
    prog.blocks.toList[L.idx]? = some blk →
    ∀ j, j < ((blk.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog))).length →
      (lower prog).get? (pcOf prog L 0 + j)
        = (((blk.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog)))[j]?) := by
  intro hb j hj
  rw [lower_get?_eq]
  rw [pcOf_eq_anchor prog L blk 0 hb]
  simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
  rw [flatBytes_block_split prog L blk hb]
  set cache := matCache prog
  set alloc := defsOf prog
  set lo := offsetTable cache alloc prog.blocks
  set pre := (prog.blocks.toList.take L.idx).flatMap
    (fun b => Byte.jumpdest :: emitBlockBody cache alloc lo b)
  have hprelen : pre.length = lo L.idx := flatBytes_block_offset prog L
  have hbody : emitBlockBody cache alloc lo blk =
      (blk.stmts.take pc).flatMap (emitStmt cache alloc)
        ++ ((blk.stmts.drop pc).flatMap (emitStmt cache alloc)
          ++ emitTerm cache lo blk.term) := by
    unfold emitBlockBody
    have hstmts : blk.stmts.flatMap (emitStmt cache alloc) =
        (blk.stmts.take pc).flatMap (emitStmt cache alloc)
          ++ (blk.stmts.drop pc).flatMap (emitStmt cache alloc) := by
      rw [← List.flatMap_append, List.take_append_drop]
    rw [hstmts]
    simp [List.append_assoc]
  rw [show offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1 + j
      = pre.length + (1 + j) from by subst cache; subst alloc; subst lo; rw [hprelen]; omega]
  have hmidlen : 1 + j < (Byte.jumpdest :: emitBlockBody cache alloc lo blk).length := by
    rw [hbody]
    simp only [List.length_cons, List.length_append]
    omega
  rw [mid_index pre _ _ (1 + j) hmidlen]
  rw [show 1 + j = j + 1 from by omega, List.getElem?_cons_succ, hbody]
  rw [List.getElem?_append_left hj]

theorem reachesBoundary_drop_stmtPrefix {prog : Program} {L : Label} {blk : Block} {pc n : Nat}
    (hb : prog.blocks.toList[L.idx]? = some blk)
    (hreach : Evm.ReachesBoundary (lower prog) (pcOf prog L 0) n)
    (hle : pcOf prog L pc ≤ n) :
    Evm.ReachesBoundary (lower prog) (pcOf prog L pc) n := by
  let pre := (blk.stmts.take pc).flatMap (emitStmt (matCache prog) (defsOf prog))
  have hseg : SegAlignedP IsLoweringOp pre := by
    unfold pre
    apply segAlignedP_flatMap
    intro s _
    exact segAlignedP_emitStmt (matCache prog) (segAlignedP_matCache prog) (defsOf prog) s
  have hmatch : ∀ j, j < pre.length →
      (lower prog).get? (pcOf prog L 0 + j) = pre[j]? := by
    intro j hj
    exact lower_match_stmt_prefix (prog := prog) (L := L) (blk := blk) (pc := pc) hb j
      (by simpa [pre] using hj)
  have hpc : pcOf prog L pc = pcOf prog L 0 + pre.length := by
    rw [pcOf_eq_anchor prog L blk pc hb, pcOf_eq_anchor prog L blk 0 hb]
    simp [pre]
  have hd := reachesBoundary_drop_segAlignedP (lower prog) pre hseg (pcOf prog L 0) hmatch n
    hreach (by rw [← hpc]; exact hle)
  simpa [hpc] using hd

theorem reachesBoundary_local_stmt {prog : Program} {L : Label} {blk : Block}
    {pc k : Nat} {s : Stmt}
    (hb : prog.blocks.toList[L.idx]? = some blk)
    (_hs : blk.stmts[pc]? = some s)
    (_hk : k < (emitStmt (matCache prog) (defsOf prog) s).length)
    (hreach : Evm.ReachesBoundary (lower prog) 0 (pcOf prog L pc + k)) :
    Evm.ReachesBoundary (lower prog) (pcOf prog L pc) (pcOf prog L pc + k) := by
  have hblock := reachesBoundary_drop_to_blockEntry (prog := prog) (L := L) (blk := blk) hb
    hreach (by
      rw [pcOf_eq_anchor prog L blk pc hb]
      omega)
  have hjd := reachesBoundary_drop_jumpdest (prog := prog) (L := L) (blk := blk) hb hblock (by
    rw [pcOf_eq_anchor prog L blk pc hb]
    omega)
  exact reachesBoundary_drop_stmtPrefix (prog := prog) (L := L) (blk := blk) (pc := pc) hb hjd
    (by omega)

theorem reachesBoundary_local_term {prog : Program} {L : Label} {blk : Block} {k : Nat}
    (hb : prog.blocks.toList[L.idx]? = some blk)
    (_hk : k < (emitTerm (matCache prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk.term).length)
    (hreach : Evm.ReachesBoundary (lower prog) 0 (termOf prog L + k)) :
    Evm.ReachesBoundary (lower prog) (termOf prog L) (termOf prog L + k) := by
  have hblock := reachesBoundary_drop_to_blockEntry (prog := prog) (L := L) (blk := blk) hb
    hreach (by
      rw [termOf_eq_anchor prog L blk hb]
      omega)
  have hjd := reachesBoundary_drop_jumpdest (prog := prog) (L := L) (blk := blk) hb hblock (by
    rw [termOf_eq_anchor prog L blk hb]
    omega)
  have hterm : termOf prog L = pcOf prog L blk.stmts.length := by
    rw [termOf_eq_anchor prog L blk hb, pcOf_eq_anchor prog L blk blk.stmts.length hb]
    rw [List.take_length]
  have hjd' : Evm.ReachesBoundary (lower prog) (pcOf prog L 0)
      (pcOf prog L blk.stmts.length + k) := by
    rwa [← hterm]
  exact (by
    rw [hterm]
    exact reachesBoundary_drop_stmtPrefix (prog := prog) (L := L) (blk := blk)
      (pc := blk.stmts.length) hb hjd' (by rw [← hterm]; omega))

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

/-- A lowered `.next` step either advances from a non-terminal instruction to its sequential
successor or takes a `JUMP`/`JUMPI` target recorded in the frame's valid-jump table. -/
theorem stepFrame_next_lowering_pc_or_validJump {prog : Program} {fr mid : Evm.Frame}
    {b : Nat} {byte : UInt8}
    (hcode : fr.exec.executionEnv.code = lower prog) (hpc : fr.exec.pc = UInt32.ofNat b)
    (hbnd : b < 2 ^ 32) (hget : (lower prog).get? b = some byte)
    (hop : IsLoweringOp (Evm.parseInstr byte))
    (hstep : Evm.stepFrame fr = .next mid.exec) :
    (mid.exec.pc = UInt32.ofNat (Evm.nextInstrPosNat b (Evm.parseInstr byte))
      ∧ Evm.parseInstr byte ≠ .STOP ∧ Evm.parseInstr byte ≠ .RETURN
      ∧ Evm.parseInstr byte ≠ .JUMP)
      ∨ mid.exec.pc ∈ fr.validJumps := by
  have hbyte : (flatBytes prog)[b]? = some byte := by
    rw [← lower_get?_eq]; exact hget
  obtain ⟨arg, hdec0⟩ := decode_of_loweringByte (prog := prog) hbnd hget
  have hdec : Evm.decode fr.exec.executionEnv.code fr.exec.pc =
      some (Evm.parseInstr byte, arg) := by
    simpa [hcode, hpc] using hdec0
  have hdecNone (hw : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
      Evm.decode fr.exec.executionEnv.code fr.exec.pc =
        some (Evm.parseInstr byte, .none) := by
    simpa [hcode, hpc] using decode_lower_nonpush prog b byte hbnd hbyte hw
  unfold IsLoweringOp at hop
  rcases hop with hstop | hadd | hlt | hpop | hmload | hmstore | hsload | hsstore | hjump
    | hjumpi | hgas | hjumpdest | hpush4 | hpush32 | hcall | hreturn | hcreate | hcreate2
  · rw [hstop] at hdec ⊢
    have hdecN := hdecNone (by simp [hstop, Evm.pushArgWidth])
    rw [hstop] at hdecN
    rw [Evm.stepFrame] at hstep
    rw [hdecN] at hstep
    simp only [Option.getD_some] at hstep
    split at hstep
    · exact absurd hstep (by simp)
    · simp only [Evm.dispatch, Evm.systemOp] at hstep
      cases hh : Evm.haltOp .STOP fr.exec with
      | error e =>
          rw [hh] at hstep
          split at hstep <;> simp at hstep
      | ok signal =>
          rw [hh] at hstep
          cases signal with
          | next e => exact absurd hh (BytecodeLayer.System.haltOp_not_next' (by tauto))
          | halted h | needsCall p pc | needsCreate p pc =>
              split at hstep <;> simp at hstep
  · rw [hadd] at hdec ⊢
    have hdecN := hdecNone (by simp [hadd, Evm.pushArgWidth])
    rw [hadd] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_add_pc hpc hdecN hstep, by simp⟩
  · rw [hlt] at hdec ⊢
    have hdecN := hdecNone (by simp [hlt, Evm.pushArgWidth])
    rw [hlt] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_lt_pc hpc hdecN hstep, by simp⟩
  · rw [hpop] at hdec ⊢
    have hdecN := hdecNone (by simp [hpop, Evm.pushArgWidth])
    rw [hpop] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_pop_pc hpc hdecN hstep, by simp⟩
  · rw [hmload] at hdec ⊢
    have hdecN := hdecNone (by simp [hmload, Evm.pushArgWidth])
    rw [hmload] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_mload_pc hpc hdecN hstep, by simp⟩
  · rw [hmstore] at hdec ⊢
    have hdecN := hdecNone (by simp [hmstore, Evm.pushArgWidth])
    rw [hmstore] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_mstore_pc hpc hdecN hstep, by simp⟩
  · rw [hsload] at hdec ⊢
    have hdecN := hdecNone (by simp [hsload, Evm.pushArgWidth])
    rw [hsload] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_sload_pc hpc hdecN hstep, by simp⟩
  · rw [hsstore] at hdec ⊢
    have hdecN := hdecNone (by simp [hsstore, Evm.pushArgWidth])
    rw [hsstore] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_sstore_pc hpc hdecN hstep, by simp⟩
  · rw [hjump] at hdec ⊢
    have hdecN := hdecNone (by simp [hjump, Evm.pushArgWidth])
    rw [hjump] at hdecN
    exact Or.inr (Evm.stepFrame_next_jump_pc hdecN hstep)
  · rw [hjumpi] at hdec ⊢
    have hdecN := hdecNone (by simp [hjumpi, Evm.pushArgWidth])
    rw [hjumpi] at hdecN
    rcases Evm.stepFrame_next_jumpi_pc hpc hdecN hstep with hseq | hjmp
    · exact Or.inl ⟨hseq, by simp⟩
    · exact Or.inr hjmp
  · rw [hgas] at hdec ⊢
    have hdecN := hdecNone (by simp [hgas, Evm.pushArgWidth])
    rw [hgas] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_gas_pc hpc hdecN hstep, by simp⟩
  · rw [hjumpdest] at hdec ⊢
    have hdecN := hdecNone (by simp [hjumpdest, Evm.pushArgWidth])
    rw [hjumpdest] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_jumpdest_pc hpc hdecN hstep, by simp⟩
  · rw [hpush4] at hdec ⊢
    let imm := Evm.uInt256OfByteArray
      ⟨((flatBytes prog).toArray).extract (b + 1) (b + 1 + (4 : UInt8).toNat)⟩
    have hdecP : Evm.decode fr.exec.executionEnv.code fr.exec.pc =
        some (Operation.PUSH4, some (imm, 4)) := by
      simpa [hcode, hpc, hpush4, imm] using
        decode_lower_push prog b byte 4 imm hbnd hbyte (by simp [hpush4, Evm.pushArgWidth])
          (by decide) rfl
    exact Or.inl ⟨Evm.stepFrame_next_push4_pc hpc hdecP hstep, by simp⟩
  · rw [hpush32] at hdec ⊢
    let imm := Evm.uInt256OfByteArray
      ⟨((flatBytes prog).toArray).extract (b + 1) (b + 1 + (32 : UInt8).toNat)⟩
    have hdecP : Evm.decode fr.exec.executionEnv.code fr.exec.pc =
        some (Operation.PUSH32, some (imm, 32)) := by
      simpa [hcode, hpc, hpush32, imm] using
        decode_lower_push prog b byte 32 imm hbnd hbyte (by simp [hpush32, Evm.pushArgWidth])
          (by decide) rfl
    exact Or.inl ⟨Evm.stepFrame_next_push32_pc hpc hdecP hstep, by simp⟩
  · rw [hcall] at hdec ⊢
    have hdecN := hdecNone (by simp [hcall, Evm.pushArgWidth])
    rw [hcall] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_call_pc hpc hdecN hstep, by simp⟩
  · rw [hreturn] at hdec ⊢
    have hdecN := hdecNone (by simp [hreturn, Evm.pushArgWidth])
    rw [hreturn] at hdecN
    rw [Evm.stepFrame] at hstep
    rw [hdecN] at hstep
    simp only [Option.getD_some] at hstep
    split at hstep
    · exact absurd hstep (by simp)
    · simp only [Evm.dispatch, Evm.systemOp] at hstep
      cases hh : Evm.haltOp .RETURN fr.exec with
      | error e =>
          rw [hh] at hstep
          split at hstep <;> simp at hstep
      | ok signal =>
          rw [hh] at hstep
          cases signal with
          | next e => exact absurd hh (BytecodeLayer.System.haltOp_not_next' (by tauto))
          | halted h | needsCall p pc | needsCreate p pc =>
              split at hstep <;> simp at hstep
  · rw [hcreate] at hdec ⊢
    have hdecN := hdecNone (by simp [hcreate, Evm.pushArgWidth])
    rw [hcreate] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_create_pc hpc hdecN hstep, by simp⟩
  · rw [hcreate2] at hdec ⊢
    have hdecN := hdecNone (by simp [hcreate2, Evm.pushArgWidth])
    rw [hcreate2] at hdecN
    exact Or.inl ⟨Evm.stepFrame_next_create2_pc hpc hdecN hstep, by simp⟩


end Lir

-- Build-enforced axiom-cleanliness guards: the boundary-reachability bricks depend only on
-- `[propext, Classical.choice, Quot.sound]`.
