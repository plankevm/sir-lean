import LirLean.Spec.WellFormed
import LirLean.Assembly.LowerConforms
import LirLean.Frame.Match
import LirLean.Decode.DecodeAnchors
import LirLean.Decode.Layout
import LirLean.Sim.SimStmt
import LirLean.Materialise.MaterialiseRuns

/-!
# LirLean — the §1B budget-derivation lemmas (1B-lemmas)

The two scalar budgets (`codeFits`/`stackFits`, `Spec/WellFormed.lean`) plus acyclicity are
the honest distillation of the ~15 per-cursor quantified bounds the `WellFormedLowered` /
`ClosedCFG` / `WellLowered` families carry. This module PROVES the three derivation lemma
families that turn the scalars back into the per-cursor bounds (plan §1B, B1a/B1b/B1c), all
ADDITIVE and sorry-free:

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
  derive `StackRoomOK prog` (all four folds). The `chargeOf`-LENGTH is independent of the
  runtime `sloadChg` values (`chargeOf_length_sloadChg_eq`, each `.sload` contributes one entry
  whatever the charge — the `StackRoomOK` docstring's `∀ sloadChg`-uniform fact), so each fold's
  length is `chargeDepth prog … (.tmp ·)`, which `maxChargeDepth` maxes over every cursor.

* **B1c `matFueled_of_acyclic`** — from `Acyclic (defsOf prog) rank` with `rank`-fits-fuel
  (`∀ t, rank t + 1 < recomputeFuel prog`) derive the `matFueled_*` field family. This is the
  fuel-sufficiency direction of `matFueled_tmp_of_acyclic` (`Assembly/Acyclic.lean`), packaged
  as the field shapes. NOTE (partial vs the plan's `defRank`-only ask): the rank-fits-fuel
  side-condition is NOT derivable from `Acyclic (defsOf prog) (defRank prog)` alone —
  `defRank t = t.id` is not bounded by `recomputeFuel = #stmts + 1` (a program may read a
  high-id tmp whose def-chain is nonetheless shallow, so `MatFueled` holds while `t.id < fuel`
  fails). A tight derivation needs the chain-depth rank, not the SSA-id rank; that is deferred.
  The lemma below is the honest, directly-usable core (mirroring `AcyclicWellFormed`'s two
  fields).

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
      = (prog.blocks.toList.map (Lir.blockLen (defsOf prog) (recomputeFuel prog))).sum := by
  rw [show flatBytes prog
        = prog.blocks.toList.flatMap (fun b => Byte.jumpdest ::
            Lir.emitBlockBody (defsOf prog) (recomputeFuel prog)
              (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b) from rfl]
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact (Lir.blockLen_eq_length (defsOf prog) (recomputeFuel prog) _ b).symm

/-- Every offset-table entry is a prefix of the whole lowered program, hence
`≤ (flatBytes prog).length`. True for ALL `i` (a prefix sum of nonneg block lengths). -/
theorem offsetTable_le_flatBytes (prog : Program) (i : Nat) :
    Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks i ≤ (flatBytes prog).length := by
  rw [flatBytes_length_eq]
  unfold Lir.offsetTable
  rw [show prog.blocks.toList.map (Lir.blockLen (defsOf prog) (recomputeFuel prog))
        = (prog.blocks.toList.take i).map (Lir.blockLen (defsOf prog) (recomputeFuel prog))
          ++ (prog.blocks.toList.drop i).map (Lir.blockLen (defsOf prog) (recomputeFuel prog))
        from by rw [← List.map_append, List.take_append_drop]]
  rw [List.sum_append]
  exact Nat.le_add_right _ _

/-- The byte just past block `L`'s terminator sits within `flatBytes prog`: block `L`'s
`JUMPDEST + statements + terminator` bytes are a contiguous sub-range (`flatBytes_block_split`),
whose end offset is `offsetTable … L.idx + 1 + |stmts| + |term|`. -/
theorem block_end_le_flatBytes (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx + 1
      + (b.stmts.flatMap (Lir.emitStmt (defsOf prog) (recomputeFuel prog))).length
      + (Lir.emitTerm (defsOf prog) (recomputeFuel prog)
          (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length
      ≤ (flatBytes prog).length := by
  have hsplit := Lir.flatBytes_block_split prog L b hb
  have hoff := Lir.flatBytes_block_offset prog L
  have hlen : (flatBytes prog).length
      = ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: Lir.emitBlockBody (defsOf prog) (recomputeFuel prog)
                        (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)).length
        + (Byte.jumpdest :: Lir.emitBlockBody (defsOf prog) (recomputeFuel prog)
              (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b).length
        + ((prog.blocks.toList.drop (L.idx + 1)).flatMap
            (fun b => Byte.jumpdest :: Lir.emitBlockBody (defsOf prog) (recomputeFuel prog)
                        (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b)).length := by
    conv_lhs => rw [hsplit]
    rw [List.length_append, List.length_append]
  have hmid : (Byte.jumpdest :: Lir.emitBlockBody (defsOf prog) (recomputeFuel prog)
              (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b).length
      = 1 + ((b.stmts.flatMap (Lir.emitStmt (defsOf prog) (recomputeFuel prog))).length
        + (Lir.emitTerm (defsOf prog) (recomputeFuel prog)
            (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length) := by
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
    Lir.pcOf prog L pc + (Lir.emitStmt (defsOf prog) (recomputeFuel prog) s).length
      ≤ (flatBytes prog).length := by
  have hend := block_end_le_flatBytes prog L b hb
  rw [Lir.pcOf_eq_anchor prog L b pc hb]
  have hsb := Lir.flatMap_split b.stmts pc s hs (Lir.emitStmt (defsOf prog) (recomputeFuel prog))
  have hsblen : (b.stmts.flatMap (Lir.emitStmt (defsOf prog) (recomputeFuel prog))).length
      = ((b.stmts.take pc).flatMap (Lir.emitStmt (defsOf prog) (recomputeFuel prog))).length
        + (Lir.emitStmt (defsOf prog) (recomputeFuel prog) s).length
        + ((b.stmts.drop (pc + 1)).flatMap (Lir.emitStmt (defsOf prog) (recomputeFuel prog))).length := by
    conv_lhs => rw [hsb]
    rw [List.length_append, List.length_append]
  omega

/-- A terminator cursor's emit ends within `flatBytes prog`:
`termOf prog L + |emitTerm … b.term| ≤ (flatBytes prog).length`. -/
theorem termOf_emit_le (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    Lir.termOf prog L + (Lir.emitTerm (defsOf prog) (recomputeFuel prog)
          (Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length
      ≤ (flatBytes prog).length := by
  have hend := block_end_le_flatBytes prog L b hb
  rw [Lir.termOf_eq_anchor prog L b hb]
  omega

/-! ## B1a — the pc/offset bound family from `codeFits` -/

/-- **Every offset-table entry fits a 32-bit pc** — the `offsetTable … < 2^32` half of every
`ClosedCFG` field (entry / jump / branch). Uses `codeFits` only. -/
theorem offsetTable_lt_of_codeFits (prog : Program) (hcode : codeFits prog) (i : Nat) :
    Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks i < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (offsetTable_le_flatBytes prog i) hcode

/-- **`bound_sstore`** — the `sstore` operand bytes fit a 32-bit pc. -/
theorem bound_sstore_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    Lir.pcOf prog L pc
      + ((Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32 := by
  intro L b pc key value hb hs
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hle := pcOf_emit_le prog L b pc (.sstore key value) hb hs
  have hemit : (Lir.emitStmt (defsOf prog) (recomputeFuel prog) (.sstore key value)).length
      = (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length + 1 := by
    rw [Lir.emitStmt_sstore]
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hemit] at hle
  omega

/-- **`bound_sload`** — the whole spilled-`sload` stash (reduced-fuel key materialise + the
35-byte `SLOAD; PUSH32; MSTORE` tail) fits a 32-bit pc. Needs `DefsConsistent`: the target is
registered to a `.slot`, so the cursor emits the stash. -/
theorem bound_sload_of_codeFits (prog : Program) (hcode : codeFits prog) (hdc : DefsConsistent prog) :
    ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    Lir.pcOf prog L pc
      + ((Lir.materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 35) < 2 ^ 32 := by
  intro L b pc t k hb hs
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hba : blockAt prog L = some b := by
    show prog.blocks[L.idx]? = some b
    rw [← Array.getElem?_toList]; exact hb
  have hdef : defsOf prog t = some (.slot (slotOf t)) := (hdc L b pc hba).1 t (.sload k) hs
  have hms : (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.sload k)).length
      = (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 1 := by
    have hfe : recomputeFuel prog = recomputeFuel prog - 1 + 1 := by
      have h1 : 1 ≤ recomputeFuel prog := by unfold recomputeFuel; omega
      omega
    conv_lhs => rw [hfe, Lir.materialiseExpr_sload]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hle := pcOf_emit_le prog L b pc (.assign t (.sload k)) hb hs
  have hemit : (Lir.emitStmt (defsOf prog) (recomputeFuel prog) (.assign t (.sload k))).length
      = (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 35 := by
    rw [Lir.emitStmt_assign_slot (defsOf prog) (recomputeFuel prog) t (.sload k) hdef]
    simp only [List.length_append, Lir.emitImm_length, List.length_cons, List.length_nil, hms]
  rw [hemit] at hle
  omega

/-- **`bound_ret`** — the RETURN-value operand bytes fit a 32-bit pc (`≤ 2^32`). -/
theorem bound_ret_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    Lir.termOf prog L
      + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2 ^ 32 := by
  intro L b t hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.materialise, Lir.emitImm_length, List.length_append,
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
    ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32 := by
  intro L b dst hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  refine ⟨?_, offsetTable_lt_of_codeFits prog hcode dst.idx⟩
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.emitDest, Lir.offsetBytesBE, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **`bound_branch`** — the cond-materialise + two `PUSH4; J…` bytes and both successor
offsets fit a 32-bit pc. -/
theorem bound_branch_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    Lir.termOf prog L
        + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length + 11 < 2 ^ 32
    ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32 := by
  intro L b cond thenL elseL hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  refine ⟨?_, offsetTable_lt_of_codeFits prog hcode thenL.idx,
    offsetTable_lt_of_codeFits prog hcode elseL.idx⟩
  have hle := termOf_emit_le prog L b hb
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.materialise, Lir.emitDest, Lir.offsetBytesBE, List.length_append,
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
  have hmg : (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) Expr.gas).length = 1 := by
    have hfe : recomputeFuel prog = recomputeFuel prog - 1 + 1 := by
      have h1 : 1 ≤ recomputeFuel prog := by unfold recomputeFuel; omega
      omega
    conv_lhs => rw [hfe]
    rfl
  have hle := pcOf_emit_le prog L b pc (.assign t .gas) hbt hs
  have hemit : (Lir.emitStmt (defsOf prog) (recomputeFuel prog) (.assign t .gas)).length = 35 := by
    rw [Lir.emitStmt_assign_slot (defsOf prog) (recomputeFuel prog) t .gas hdef]
    simp only [List.length_append, Lir.emitImm_length, List.length_cons, List.length_nil, hmg]
  rw [hemit] at hle
  omega

/-- **`retEpilogueBound`** (the `WellLowered` ret-epilogue field) — the 101-byte full-observable
RETURN epilogue after the return-value materialise fits a 32-bit pc. -/
theorem retEpilogueBound_of_codeFits (prog : Program) (hcode : codeFits prog) :
    ∀ (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    Lir.termOf prog L + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length + 100
      < 2 ^ 32 := by
  intro L b t hb hterm
  have hc : (flatBytes prog).length < 2 ^ 32 := hcode
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  have hle := termOf_emit_le prog L b hbt
  rw [hterm] at hle
  simp only [Lir.emitTerm, Lir.materialise, Lir.emitImm_length, List.length_append,
    List.length_cons, List.length_nil] at hle
  omega

/-- **B1a — the pc/offset bound family.** From `codeFits` (+ `DefsConsistent` for the two spilled
stashes) all pc/offset bounds of the `WellFormedLowered` / `ClosedCFG` / `WellLowered` families
follow. Packaged as the conjunction the 1B-reshape (`wellFormedLowered_of_wellFormed`) consumes;
the individual `*_of_codeFits` lemmas above expose each conjunct on its own. -/
theorem pcBounds_of_codeFits (prog : Program) (hcode : codeFits prog) (hdc : DefsConsistent prog) :
    (∀ i, Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks i < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
        Lir.pcOf prog L pc
          + ((Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
            + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
        Lir.pcOf prog L pc
          + ((Lir.materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 35) < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (t : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
        Lir.termOf prog L
          + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block),
        prog.blocks.toList[L.idx]? = some b → b.term = .stop → Lir.termOf prog L < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (dst : Label),
        prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
        Lir.termOf prog L + 5 < 2 ^ 32
        ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
        prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
        Lir.termOf prog L
            + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length + 11 < 2 ^ 32
        ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32
        ∧ Lir.offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
        blockAt prog L = some b → b.stmts[pc]? = some (.assign t .gas) →
        Lir.pcOf prog L pc + 34 < 2 ^ 32)
    ∧ (∀ (L : Label) (b : Block) (t : Tmp),
        blockAt prog L = some b → b.term = .ret t →
        Lir.termOf prog L + (Lir.materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length
          + 100 < 2 ^ 32) :=
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

/-- `chargeOf`'s LENGTH is independent of the runtime `sloadChg` values: each `.sload`
contributes exactly one entry (`chargeOf_sload`) whatever the charge. -/
theorem chargeOf_length_sloadChg_eq (defs : Tmp → Option Expr) (c1 c2 : Tmp → ℕ) :
    ∀ (fuel : Nat) (e : Expr),
      (Lir.chargeOf defs c1 fuel e).length = (Lir.chargeOf defs c2 fuel e).length := by
  intro fuel
  induction fuel with
  | zero => intro e; cases e <;> rfl
  | succ f ih =>
    intro e
    cases e with
    | imm w => rfl
    | slot n => rfl
    | gas => rfl
    | tmp t =>
      cases h : defs t with
      | none => rw [Lir.chargeOf_tmp_none defs c1 f t h, Lir.chargeOf_tmp_none defs c2 f t h]
      | some e' =>
        rw [Lir.chargeOf_tmp_some defs c1 f t e' h, Lir.chargeOf_tmp_some defs c2 f t e' h]
        exact ih e'
    | add a b =>
      rw [Lir.chargeOf_add defs c1 f a b, Lir.chargeOf_add defs c2 f a b]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih (.tmp b), ih (.tmp a)]
    | lt a b =>
      rw [Lir.chargeOf_lt defs c1 f a b, Lir.chargeOf_lt defs c2 f a b]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih (.tmp b), ih (.tmp a)]
    | sload k =>
      rw [Lir.chargeOf_sload defs c1 f k, Lir.chargeOf_sload defs c2 f k]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih (.tmp k)]

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

/-- **B1b — the static stack-room bounds.** From `stackFits prog` (`maxChargeDepth ≤ 1024`) every
`StackRoomOK` fold holds: each fold's `chargeOf`-length is `chargeDepth` (length-independent of
`sloadChg`), which `maxChargeDepth` maxes over the cursor. -/
theorem stackBounds_of_stackFits (prog : Program) (h : stackFits prog) : StackRoomOK prog where
  branch := by
    intro sloadChg L b cond thenL elseL hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeOf_length_sloadChg_eq (defsOf prog) sloadChg (fun _ => 0)]
    have hst := termChargeDepth_le_max prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    show chargeDepth prog (recomputeFuel prog) (.tmp cond) ≤ 1024
    simp only [termChargeDepth] at hst
    omega
  sloadKey := by
    intro sloadChg L b pc t k hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.assign t (.sload k)) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeOf_length_sloadChg_eq (defsOf prog) sloadChg (fun _ => 0)]
    have hst := stmtChargeDepth_le_max prog b (.assign t (.sload k)) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    show chargeDepth prog (recomputeFuel prog - 1) (.tmp k) ≤ 1024
    simp only [stmtChargeDepth] at hst
    omega
  sstore := by
    intro sloadChg L b pc key value hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.sstore key value) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeOf_length_sloadChg_eq (defsOf prog) sloadChg (fun _ => 0) (recomputeFuel prog) (.tmp value),
        chargeOf_length_sloadChg_eq (defsOf prog) sloadChg (fun _ => 0) (recomputeFuel prog) (.tmp key)]
    have hst := stmtChargeDepth_le_max prog b (.sstore key value) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    show chargeDepth prog (recomputeFuel prog) (.tmp value)
        + chargeDepth prog (recomputeFuel prog) (.tmp key) + 1 ≤ 1024
    simp only [stmtChargeDepth] at hst
    omega
  ret := by
    intro sloadChg L b t hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeOf_length_sloadChg_eq (defsOf prog) sloadChg (fun _ => 0)]
    have hst := termChargeDepth_le_max prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    show chargeDepth prog (recomputeFuel prog) (.tmp t) ≤ 1024
    simp only [termChargeDepth] at hst
    omega

/-! ## B1b twin (Phase 2A P5d) — the fuel-free `StackRoomOKF` folds from `stackFitsF`

The fuel-free twin of B1b: from `stackFitsF prog` (`maxChargeDepthF prog ≤ 1024`) every
`StackRoomOKF` fold holds. Reuses the generic `foldl`-max helpers above; each fold's
`chargeCache`-length is `sloadChg`-independent (`chargeCache_length_sloadChg_eq`, P5a), so it reads
`chargeDepthF` (= the length at `sloadChg := fun _ => 0`), which `maxChargeDepthF` maxes over the
cursor. Proved ALONGSIDE `stackBounds_of_stackFits`; the fuel version is dropped at P8. -/

/-- Fuel-free twin of `termChargeDepth_le_max`. -/
theorem termChargeDepthF_le_maxF (prog : Program) (b : Block) (hb : b ∈ prog.blocks.toList) :
    termChargeDepthF prog b.term ≤ maxChargeDepthF prog := by
  unfold maxChargeDepthF
  rw [← Array.foldl_toList]
  refine le_trans ?_ (le_foldl_max_of_mem
    (fun b => max (termChargeDepthF prog b.term)
      (b.stmts.foldl (fun a s => max a (stmtChargeDepthF prog s)) 0)) prog.blocks.toList 0 hb)
  exact le_max_left _ _

/-- Fuel-free twin of `stmtChargeDepth_le_max`. -/
theorem stmtChargeDepthF_le_maxF (prog : Program) (b : Block) (s : Stmt)
    (hb : b ∈ prog.blocks.toList) (hs : s ∈ b.stmts) :
    stmtChargeDepthF prog s ≤ maxChargeDepthF prog := by
  unfold maxChargeDepthF
  rw [← Array.foldl_toList]
  refine le_trans ?_ (le_foldl_max_of_mem
    (fun b => max (termChargeDepthF prog b.term)
      (b.stmts.foldl (fun a s => max a (stmtChargeDepthF prog s)) 0)) prog.blocks.toList 0 hb)
  refine le_trans ?_ (le_max_right _ _)
  exact le_foldl_max_of_mem (fun s => stmtChargeDepthF prog s) b.stmts 0 hs

/-- **B1b twin — the fuel-free static stack-room bounds.** From `stackFitsF prog` every
`StackRoomOKF` fold holds. The twin of `stackBounds_of_stackFits`. -/
theorem stackBoundsF_of_stackFitsF (prog : Program) (h : stackFitsF prog) : StackRoomOKF prog where
  branch := by
    intro sloadChg L b cond thenL elseL hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := termChargeDepthF_le_maxF prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepthF prog ≤ 1024 := h
    simp only [termChargeDepthF, chargeDepthF] at hst
    omega
  sloadKey := by
    intro sloadChg L b pc t k hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.assign t (.sload k)) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := stmtChargeDepthF_le_maxF prog b (.assign t (.sload k)) hmem hsmem
    have hb1024 : maxChargeDepthF prog ≤ 1024 := h
    simp only [stmtChargeDepthF, chargeDepthF] at hst
    omega
  sstore := by
    intro sloadChg L b pc key value hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.sstore key value) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) value,
        chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) key]
    have hst := stmtChargeDepthF_le_maxF prog b (.sstore key value) hmem hsmem
    have hb1024 : maxChargeDepthF prog ≤ 1024 := h
    simp only [stmtChargeDepthF, chargeDepthF] at hst
    omega
  ret := by
    intro sloadChg L b t hb hterm
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := termChargeDepthF_le_maxF prog b hmem
    rw [hterm] at hst
    have hb1024 : maxChargeDepthF prog ≤ 1024 := h
    simp only [termChargeDepthF, chargeDepthF] at hst
    omega

/-! ## B1c — the `matFueled_*` family from acyclicity -/

/-- **B1c — recompute-fuel sufficiency from acyclicity.** Given an `Acyclic (defsOf prog) rank`
witness whose ranks all sit one below `recomputeFuel prog`, every materialised operand
(`sstore` key/value, spilled-`sload` key at reduced fuel, `ret`/`branch` operand) is
`MatFueled` — the `WellFormedLowered.matFueled_*` field family. The core is
`matFueled_tmp_of_acyclic` (`Assembly/Acyclic.lean`).

The rank-fits-fuel premise is genuinely needed (and is NOT derivable from
`Acyclic (defsOf prog) (defRank prog)` alone: `defRank t = t.id` is unbounded by
`recomputeFuel = #stmts + 1`). It is the `AcyclicWellFormed.rank_lt_fuel` obligation. -/
theorem matFueled_of_acyclic (prog : Program) {rank : Tmp → ℕ}
    (hac : Lir.Acyclic (defsOf prog) rank) (hfuel : ∀ t, rank t + 1 < recomputeFuel prog) :
    (∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
        Lir.MatFueled (defsOf prog) (recomputeFuel prog) (.tmp value)
        ∧ Lir.MatFueled (defsOf prog) (recomputeFuel prog) (.tmp key))
    ∧ (∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
        1 ≤ recomputeFuel prog
        ∧ Lir.MatFueled (defsOf prog) (recomputeFuel prog - 1) (.tmp k))
    ∧ (∀ (L : Label) (b : Block) (t : Tmp),
        prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
        Lir.MatFueled (defsOf prog) (recomputeFuel prog) (.tmp t))
    ∧ (∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
        prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
        Lir.MatFueled (defsOf prog) (recomputeFuel prog) (.tmp cond)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ key value _ _
    exact ⟨Lir.matFueled_tmp_of_acyclic hac (by have := hfuel value; omega),
           Lir.matFueled_tmp_of_acyclic hac (by have := hfuel key; omega)⟩
  · intro _ _ _ _ k _ _
    exact ⟨by have := hfuel k; omega,
           Lir.matFueled_tmp_of_acyclic hac (by have := hfuel k; omega)⟩
  · intro _ _ t _ _
    exact Lir.matFueled_tmp_of_acyclic hac (by have := hfuel t; omega)
  · intro _ _ cond _ _ _ _
    exact Lir.matFueled_tmp_of_acyclic hac (by have := hfuel cond; omega)

/-! ## `slots_slot` from `NoSlotSource` -/

/-- **`slots_slot` from `NoSlotSource`.** Every tmp that `defsOf` registers as a
`.slot slot'` carries its canonical `slotOf`. `defsOf` only ever emits `.slot (slotOf t)`
(the gas/sload spill routes and the call/create result routes), with ONE exception: it echoes
a source `.assign t (.slot n)` verbatim as `(t, .slot n)` — which `NoSlotSource` excludes. So
under `NoSlotSource` the registration is canonical: the `WellFormedLowered.slots_slot` field,
DERIVED (from a `WellFormed`-level field) rather than supplied. -/
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
  have canon : ∀ t' : Tmp, pr = (t', Expr.slot (slotOf t')) → slot' = slotOf tw := by
    intro t' hpair
    rw [hpair] at hpr hkey
    have hkey2 : t' = tw := hkey
    have hpr2 : Expr.slot (slotOf t') = Expr.slot slot' := hpr
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
          -- the only non-canonical route: a source `.assign t' (.slot n)`, excluded by `NoSlotSource`.
          exfalso
          obtain ⟨i, hi, hbget⟩ := List.mem_iff_getElem.mp hbmem
          obtain ⟨j, hj, hsget⟩ := List.mem_iff_getElem.mp hsmem
          exact hns ⟨i⟩ b j t' n
            (by show prog.blocks[i]? = some b
                rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hbget])
            (by rw [List.getElem?_eq_getElem hj, hsget])
      | imm w => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | tmp t'' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | add a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | lt a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
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
