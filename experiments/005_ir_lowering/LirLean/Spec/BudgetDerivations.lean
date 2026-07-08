import LirLean.Spec.WellFormed
import LirLean.Assembly.LowerConforms
import LirLean.Frame.Match
import LirLean.Decode.DecodeAnchors
import LirLean.Decode.Layout
import LirLean.Sim.SimStmt

/-!
# LirLean — the §1B budget-derivation lemmas (1B-lemmas)

The two scalar budgets (`codeFits`/`stackFits`, `Spec/WellFormed.lean`) are the honest
distillation of the ~15 per-cursor quantified bounds the `WellFormedLowered` / `ClosedCFG` /
`WellLowered` families carry. This module PROVES the derivation lemma families that turn the
scalars back into the per-cursor bounds (plan §1B, B1a/B1b), all over the fold emission
(`matCache` byte-cache lengths, `pcOf`/`termOf`/`offsetTable` fold cursors) and sorry-free:

* **B1a `pcBounds_of_codeFits`** — from `codeFits prog` (`(flatBytes prog).length < 2^32`)
  derive every pc/offset bound of the current families: `bound_sstore`/`_sload`/`_ret`/`_stop`/
  `_jump`/`_branch` (`Assembly/LowerConforms.lean`), the `offsetTable … < 2^32` halves of
  `ClosedCFG` (`Surface.lean`), and `gasBound`/`retEpilogueBound` (`Surface.lean`). Each target
  is a CONTIGUOUS SUB-RANGE of `flatBytes prog`, so it is `≤ (flatBytes prog).length < 2^32`.
  The two spilled-stash bounds (`bound_sload`, `gasBound`) additionally consume `DefsConsistent`
  (the cursor's target is registered to a `.slot`, so its emit is the stash whose byte length
  the bound measures). Root geometry: `flatBytes_block_split`/`flatBytes_block_offset`
  (`Decode/Layout.lean`), `pcOf_eq_anchor`/`termOf_eq_anchor`.

* **B1b `stackBounds_of_stackFits`** — from `stackFits prog` (`maxChargeDepth prog ≤ 1024`)
  derive `StackRoomOK prog` (all four folds). The `chargeCache`-LENGTH is independent of the
  runtime `sloadChg` values (`chargeCache_length_sloadChg_eq`, P5a — each `.sload` contributes
  one entry whatever the charge), so each fold's length is `chargeDepth prog ·` (the length at
  `sloadChg := fun _ => 0`), which `maxChargeDepth` maxes over every cursor.

* **`slots_slot_of_noSlotSource`** — the `WellFormedLowered.slots_slot` field derived from the
  `NoSlotSource` well-formedness field: `defsOf` only ever registers the canonical
  `Loc.slot (slotOf t)` unless a source assign carries the lowering-only `.slot` marker.

(There is no fuel-sufficiency family anymore: the fold emission always fully expands —
structural termination on the ordered def-env — so the former B1c `matFueled_*` derivation
vanished with the fuel `WellFormedLowered` fields.)

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir.V2

open Evm

/-! ## Byte-geometry core: every cursor's emit fits inside `flatBytes prog` -/

/-- `(flatBytes prog).length` is the total lowered-block length — the sum of `blockLen` over
every block. Each lowered block `JUMPDEST :: emitBlockBody` has length `blockLen` independent
of the resolved offset table (`blockLen_eq_length`). -/
theorem flatBytes_length_eq (prog : Program) :
    (flatBytes prog).length
      = (prog.blocks.toList.map (Lir.blockLen (matCache prog) (defsOf prog))).sum := by
  rw [show flatBytes prog
        = prog.blocks.toList.flatMap (fun b => Byte.jumpdest ::
            Lir.emitBlockBody (matCache prog) (defsOf prog)
              (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b) from rfl]
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact (Lir.blockLen_eq_length (matCache prog) (defsOf prog) _ b).symm

/-- Every offset-table entry is a prefix of the whole lowered program, hence
`≤ (flatBytes prog).length`. True for ALL `i` (a prefix sum of nonneg block lengths). -/
theorem offsetTable_le_flatBytes (prog : Program) (i : Nat) :
    Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks i ≤ (flatBytes prog).length := by
  rw [flatBytes_length_eq]
  unfold Lir.offsetTable
  rw [show prog.blocks.toList.map (Lir.blockLen (matCache prog) (defsOf prog))
        = (prog.blocks.toList.take i).map (Lir.blockLen (matCache prog) (defsOf prog))
          ++ (prog.blocks.toList.drop i).map (Lir.blockLen (matCache prog) (defsOf prog))
        from by rw [← List.map_append, List.take_append_drop]]
  rw [List.sum_append]
  exact Nat.le_add_right _ _

/-- The byte just past block `L`'s terminator sits within `flatBytes prog`: block `L`'s
`JUMPDEST + statements + terminator` bytes are a contiguous sub-range (`flatBytes_block_split`),
whose end offset is `offsetTable … L.idx + 1 + |stmts| + |term|`. -/
theorem block_end_le_flatBytes (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx + 1
      + (b.stmts.flatMap (Lir.emitStmt (matCache prog) (defsOf prog))).length
      + (Lir.emitTerm (matCache prog)
          (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length
      ≤ (flatBytes prog).length := by
  have hsplit := Lir.flatBytes_block_split prog L b hb
  have hoff := Lir.flatBytes_block_offset prog L
  have hlen : (flatBytes prog).length
      = ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: Lir.emitBlockBody (matCache prog) (defsOf prog)
                        (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length
        + (Byte.jumpdest :: Lir.emitBlockBody (matCache prog) (defsOf prog)
              (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b).length
        + ((prog.blocks.toList.drop (L.idx + 1)).flatMap
            (fun b => Byte.jumpdest :: Lir.emitBlockBody (matCache prog) (defsOf prog)
                        (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length := by
    conv_lhs => rw [hsplit]
    rw [List.length_append, List.length_append]
  have hmid : (Byte.jumpdest :: Lir.emitBlockBody (matCache prog) (defsOf prog)
              (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b).length
      = 1 + ((b.stmts.flatMap (Lir.emitStmt (matCache prog) (defsOf prog))).length
        + (Lir.emitTerm (matCache prog)
            (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length) := by
    rw [List.length_cons]
    unfold Lir.emitBlockBody
    rw [List.length_append]
    omega
  rw [hlen, hmid, hoff]
  omega

/-- A statement cursor's emit ends within `flatBytes prog`:
`pcOf prog L pc + |emitStmt … s| ≤ (flatBytes prog).length`. -/
theorem pcOf_emit_le (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b) (hs : b.stmts[pc]? = some s) :
    Lir.pcOf prog L pc + (Lir.emitStmt (matCache prog) (defsOf prog) s).length
      ≤ (flatBytes prog).length := by
  have hend := block_end_le_flatBytes prog L b hb
  rw [Lir.pcOf_eq_anchor prog L b pc hb]
  have hsb := Lir.flatMap_split b.stmts pc s hs (Lir.emitStmt (matCache prog) (defsOf prog))
  have hsblen : (b.stmts.flatMap (Lir.emitStmt (matCache prog) (defsOf prog))).length
      = ((b.stmts.take pc).flatMap (Lir.emitStmt (matCache prog) (defsOf prog))).length
        + (Lir.emitStmt (matCache prog) (defsOf prog) s).length
        + ((b.stmts.drop (pc + 1)).flatMap (Lir.emitStmt (matCache prog) (defsOf prog))).length := by
    conv_lhs => rw [hsb]
    rw [List.length_append, List.length_append]
  omega

/-- A terminator cursor's emit ends within `flatBytes prog`:
`termOf prog L + |emitTerm … b.term| ≤ (flatBytes prog).length`. -/
theorem termOf_emit_le (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    Lir.termOf prog L + (Lir.emitTerm (matCache prog)
          (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length
      ≤ (flatBytes prog).length := by
  have hend := block_end_le_flatBytes prog L b hb
  rw [Lir.termOf_eq_anchor prog L b hb]
  omega

/-! ## B1a — the pc/offset bound family from `codeFits` -/

/-- **Every offset-table entry fits a 32-bit pc** — the `offsetTable … < 2^32` half of every
`ClosedCFG` field (entry / jump / branch). Uses `codeFits` only. -/
theorem offsetTable_lt_of_codeFits (prog : Program) (hcode : codeFits prog) (i : Nat) :
    Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks i < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (offsetTable_le_flatBytes prog i) hcode

/-- **`bound_sstore`** — the `sstore` operand bytes fit a 32-bit pc. -/
theorem bound_sstore_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    Lir.pcOf prog L pc
      + ((matCache prog value).length + (matCache prog key).length) < 2 ^ 32 := by
  intro L b pc key value hb hs
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hle := pcOf_emit_le prog L b pc (.sstore key value) hb hs
  have hemit : (Lir.emitStmt (matCache prog) (defsOf prog) (.sstore key value)).length
      = (matCache prog value).length + (matCache prog key).length + 1 := by
    rw [Lir.emitStmt_sstore]
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hemit] at hle
  omega

/-- **`bound_sload`** — the whole spilled-`sload` stash (key byte cache + the 35-byte
`SLOAD; PUSH32; MSTORE` tail) fits a 32-bit pc. Needs `DefsConsistent`: the target is
registered to a `.slot`, so the cursor emits the stash. -/
theorem bound_sload_of_codeFits (prog : Program) (hcode : codeFits prog) (hdc : DefsConsistent prog) :
    ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    Lir.pcOf prog L pc + ((matCache prog k).length + 35) < 2 ^ 32 := by
  intro L b pc t k hb hs
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hba : blockAt prog L = some b := by
    show prog.blocks[L.idx]? = some b
    rw [← Array.getElem?_toList]; exact hb
  have hdef : defsOf prog t = some (.slot (slotOf t)) := (hdc L b pc hba).1 t (.sload k) hs
  have hle := pcOf_emit_le prog L b pc (.assign t (.sload k)) hb hs
  have hemit : (Lir.emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k))).length
      = (matCache prog k).length + 35 := by
    rw [Lir.emitStmt_assign_slot (matCache prog) (defsOf prog) t (.sload k) hdef]
    show (matCache prog k ++ [Byte.sload] ++ Lir.emitImm (UInt256.ofNat (slotOf t))
        ++ [Byte.mstore]).length = _
    simp only [List.length_append, Lir.emitImm_length, List.length_cons, List.length_nil]
  rw [hemit] at hle
  omega

/-- **`bound_ret`** — the RETURN-value operand bytes fit a 32-bit pc (`≤ 2^32`). -/
theorem bound_ret_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    Lir.termOf prog L + (matCache prog t).length ≤ 2 ^ 32 := by
  intro L b t hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.emitImm_length, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **`bound_stop`** — the `stop` terminator cursor fits a 32-bit pc. -/
theorem bound_stop_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block),
    prog.blocks.toList[L.idx]? = some b → b.term = .stop →
    Lir.termOf prog L < 2 ^ 32 := by
  intro L b hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, List.length_cons, List.length_nil] at hle
  omega

/-- **`bound_jump`** — the `PUSH4; JUMP` bytes and the destination offset fit a 32-bit pc. -/
theorem bound_jump_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (dst : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
    Lir.termOf prog L + 5 < 2 ^ 32
    ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks dst.idx < 2 ^ 32 := by
  intro L b dst hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  refine ⟨?_, offsetTable_lt_of_codeFits prog hcode dst.idx⟩
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.emitDest, Lir.offsetBytesBE, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **`bound_branch`** — the cond byte cache + two `PUSH4; J…` bytes and both successor
offsets fit a 32-bit pc. -/
theorem bound_branch_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    Lir.termOf prog L + (matCache prog cond).length + 11 < 2 ^ 32
    ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks elseL.idx < 2 ^ 32 := by
  intro L b cond thenL elseL hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  refine ⟨?_, offsetTable_lt_of_codeFits prog hcode thenL.idx,
    offsetTable_lt_of_codeFits prog hcode elseL.idx⟩
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.emitDest, Lir.offsetBytesBE, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **`gasBound`** (the `WellLowered` gas-stash field) — the `[GAS]; PUSH32; MSTORE` stash's pc
range fits a 32-bit pc. Needs `DefsConsistent`: a spilled-`.gas` target is registered to a
`.slot`. -/
theorem gasBound_of_codeFits (prog : Program) (hcode : codeFits prog) (hdc : DefsConsistent prog) :
    ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t .gas) →
    Lir.pcOf prog L pc + 34 < 2 ^ 32 := by
  intro L b pc t hb hs
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  have hdef : defsOf prog t = some (.slot (slotOf t)) := (hdc L b pc hb).1 t .gas hs
  have hle := pcOf_emit_le prog L b pc (.assign t .gas) hbt hs
  have hemit : (Lir.emitStmt (matCache prog) (defsOf prog) (.assign t .gas)).length = 35 := by
    rw [Lir.emitStmt_assign_slot (matCache prog) (defsOf prog) t .gas hdef]
    show ([Byte.gas] ++ Lir.emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]).length = _
    simp only [List.length_append, Lir.emitImm_length, List.length_cons, List.length_nil]
  rw [hemit] at hle
  omega

/-- **`retEpilogueBound`** (the `WellLowered` ret-epilogue field) — the 101-byte full-observable
RETURN epilogue after the return-value bytes fits a 32-bit pc. -/
theorem retEpilogueBound_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    Lir.termOf prog L + (matCache prog t).length + 100 < 2 ^ 32 := by
  intro L b t hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  have hle := termOf_emit_le prog L b hbt
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.emitImm_length, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **B1a — the pc/offset bound family.** From `codeFits` (+ `DefsConsistent` for the two spilled
stashes) all pc/offset bounds of the `WellFormedLowered` / `ClosedCFG` / `WellLowered` families
follow. Packaged as the conjunction the 1B-reshape (`wellFormedLowered_of_IRWellFormed`) consumes;
the individual `*_of_codeFits` lemmas above expose each conjunct on its own. -/
theorem pcBounds_of_codeFits (prog : Program) (hcode : codeFits prog) (hdc : DefsConsistent prog) :
    (∀ i, Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks i < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
        Lir.pcOf prog L pc
          + ((matCache prog value).length + (matCache prog key).length) < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
        Lir.pcOf prog L pc + ((matCache prog k).length + 35) < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (t : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
        Lir.termOf prog L + (matCache prog t).length ≤ 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block),
        prog.blocks.toList[L.idx]? = some b → b.term = .stop → Lir.termOf prog L < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (dst : Label),
        prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
        Lir.termOf prog L + 5 < 2 ^ 32
        ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks dst.idx < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
        prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
        Lir.termOf prog L + (matCache prog cond).length + 11 < 2 ^ 32
        ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks thenL.idx < 2 ^ 32
        ∧ Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks elseL.idx < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
        blockAt prog L = some b → b.stmts[pc]? = some (.assign t .gas) →
        Lir.pcOf prog L pc + 34 < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (t : Tmp),
        blockAt prog L = some b → b.term = .ret t →
        Lir.termOf prog L + (matCache prog t).length + 100 < 2 ^ 32) :=
  ⟨offsetTable_lt_of_codeFits prog hcode,
   bound_sstore_of_codeFits prog hcode,
   bound_sload_of_codeFits prog hcode hdc,
   bound_ret_of_codeFits prog hcode,
   bound_stop_of_codeFits prog hcode,
   bound_jump_of_codeFits prog hcode,
   bound_branch_of_codeFits prog hcode,
   gasBound_of_codeFits prog hcode hdc,
   retEpilogueBound_of_codeFits prog hcode⟩

/-! ## B1b — the `StackRoomOK` folds from `stackFits` -/

/-- `foldl`-with-`max` only grows: the accumulator is `≤` the result. -/
theorem foldl_max_init_le {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl (fun a y => max a (f y)) init := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons y ys ih =>
    intro init
    rw [List.foldl_cons]
    exact le_trans (le_max_left init (f y)) (ih (max init (f y)))

/-- Every element's `f`-value is `≤` the `foldl`-with-`max` result. -/
theorem le_foldl_max_of_mem {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (init : Nat) {x : α}, x ∈ l →
      f x ≤ l.foldl (fun a y => max a (f y)) init := by
  intro l
  induction l with
  | nil => intro init x hx; simp at hx
  | cons y ys ih =>
    intro init x hx
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact le_trans (le_max_right _ _) (foldl_max_init_le f ys _)
    · exact ih (max init (f y)) hxs

/-- A block's terminator operand-depth is `≤ maxChargeDepth`. -/
theorem termChargeDepth_le_max (prog : Program) (b : Block) (hb : b ∈ prog.blocks.toList) :
    termChargeDepth prog b.term ≤ maxChargeDepth prog := by
  unfold maxChargeDepth
  rw [← Array.foldl_toList]
  refine le_trans ?_ (le_foldl_max_of_mem
    (fun b => max (termChargeDepth prog b.term)
      (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0)) prog.blocks.toList 0 hb)
  exact le_max_left _ _

/-- A block's statement operand-depth is `≤ maxChargeDepth`. -/
theorem stmtChargeDepth_le_max (prog : Program) (b : Block) (s : Stmt)
    (hb : b ∈ prog.blocks.toList) (hs : s ∈ b.stmts) :
    stmtChargeDepth prog s ≤ maxChargeDepth prog := by
  unfold maxChargeDepth
  rw [← Array.foldl_toList]
  refine le_trans ?_ (le_foldl_max_of_mem
    (fun b => max (termChargeDepth prog b.term)
      (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0)) prog.blocks.toList 0 hb)
  refine le_trans ?_ (le_max_right _ _)
  exact le_foldl_max_of_mem (fun s => stmtChargeDepth prog s) b.stmts 0 hs

/-- **B1b — the static stack-room bounds.** From `stackFits prog` (`maxChargeDepth ≤ 1024`)
every `StackRoomOK` fold holds: each fold's `chargeCache`-length is `sloadChg`-independent
(`chargeCache_length_sloadChg_eq`), so it reads `chargeDepth` (= the length at
`sloadChg := fun _ => 0`), which `maxChargeDepth` maxes over the cursor. -/
theorem stackBounds_of_stackFits (prog : Program) (h : stackFits prog) : StackRoomOK prog where
  branch := by
    intro sloadChg L b cond thenL elseL hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := termChargeDepth_le_max prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [termChargeDepth, chargeDepth] at hst
    omega
  sloadKey := by
    intro sloadChg L b pc t k hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.assign t (.sload k)) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := stmtChargeDepth_le_max prog b (.assign t (.sload k)) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [stmtChargeDepth, chargeDepth] at hst
    omega
  sstore := by
    intro sloadChg L b pc key value hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.sstore key value) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) value,
        chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) key]
    have hst := stmtChargeDepth_le_max prog b (.sstore key value) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [stmtChargeDepth, chargeDepth] at hst
    omega
  ret := by
    intro sloadChg L b t hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := termChargeDepth_le_max prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [termChargeDepth, chargeDepth] at hst
    omega

/-! ## `slots_slot` from `NoSlotSource` -/

/-- **`slots_slot` from `NoSlotSource`.** Every tmp that `defsOf` registers as a
`.slot slot'` carries its canonical `slotOf`. `defsOf` (the first-find view of `defEnv`) only
ever emits `Loc.slot (slotOf t)` (the gas/sload spill routes and the call/create result
routes), with ONE exception: it routes a source `.assign t (.slot n)` through
`locOfExpr (.slot n) = Loc.slot n` — which `NoSlotSource` excludes. So under `NoSlotSource`
the registration is canonical: the `WellFormedLowered.slots_slot` field, DERIVED (from a
`WellFormed`-level field) rather than supplied. -/
theorem slots_slot_of_noSlotSource (prog : Program) (hns : NoSlotSource prog) :
    ∀ (tw : Tmp) (slot' : Nat), defsOf prog tw = some (.slot slot') → slot' = slotOf tw := by
  intro tw slot' hd
  simp only [defsOf] at hd
  obtain ⟨pr, hf, hpr⟩ := Option.map_eq_some_iff.mp hd
  have hkey := List.find?_some hf
  rw [beq_iff_eq] at hkey
  have hmem := List.mem_of_find?_eq_some hf
  obtain ⟨b, hbmem, hbmap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, hsmem, hsmap⟩ := List.mem_filterMap.mp hbmap
  -- `pr` is the filterMap output for `s`; `pr.2 = .slot slot'`, `pr.1 = tw`.
  -- The canonical (slot-emitting) arms all yield `pr = (t', .slot (slotOf t'))`.
  have canon : ∀ t' : Tmp, pr = (t', Loc.slot (slotOf t')) → slot' = slotOf tw := by
    intro t' hpair
    rw [hpair] at hpr hkey
    have hkey2 : t' = tw := hkey
    have hpr2 : Loc.slot (slotOf t') = Loc.slot slot' := hpr
    subst hkey2
    injection hpr2 with hpr3
    exact hpr3.symm
  cases s with
  | assign t' e' =>
      cases e' with
      | gas =>
          apply canon t'; simp only [Option.some.injEq] at hsmap; exact hsmap.symm
      | sload k' =>
          apply canon t'; simp only [Option.some.injEq] at hsmap; exact hsmap.symm
      | slot n =>
          -- the only non-canonical route: a source `.assign t' (.slot n)` (registered through
          -- `locOfExpr (.slot n) = .slot n`), excluded by `NoSlotSource`.
          exfalso
          obtain ⟨i, hi, hbget⟩ := List.mem_iff_getElem.mp hbmem
          obtain ⟨j, hj, hsget⟩ := List.mem_iff_getElem.mp hsmem
          exact hns ⟨i⟩ b j t' n
            (by show prog.blocks[i]? = some b
                rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hbget])
            (by rw [List.getElem?_eq_getElem hj, hsget])
      | imm w =>
          simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
          exact absurd hpr (by simp [locOfExpr])
      | tmp t'' =>
          simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
          exact absurd hpr (by simp [locOfExpr])
      | add a b =>
          simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
          exact absurd hpr (by simp [locOfExpr])
      | lt a b =>
          simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
          exact absurd hpr (by simp [locOfExpr])
  | sstore _ _ => simp at hsmap
  | call cs =>
      obtain ⟨callee, gasFwd, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          apply canon t''; simp only [Option.some.injEq] at hsmap; exact hsmap.symm
  | create cs =>
      obtain ⟨value, initOffset, initSize, salt, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          apply canon t''; simp only [Option.some.injEq] at hsmap; exact hsmap.symm

end Lir.V2
