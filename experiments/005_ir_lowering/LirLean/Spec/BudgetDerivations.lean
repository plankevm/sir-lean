import LirLean.Spec.WellFormed
import LirLean.CfgSim.LowerConforms
import LirLean.Frame.Match
import LirLean.Decode.DecodeAnchors
import LirLean.Decode.Layout
import LirLean.Sim.SimStmt

namespace Lir

open Lir.Frame
open Evm

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

theorem termOf_emit_le (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    Lir.termOf prog L + (Lir.emitTerm (matCache prog)
          (Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length
      ≤ (flatBytes prog).length := by
  have hend := block_end_le_flatBytes prog L b hb
  rw [Lir.termOf_eq_anchor prog L b hb]
  omega

theorem offsetTable_lt_of_codeFits (prog : Program) (hcode : codeFits prog) (i : Nat) :
    Lir.offsetTable (matCache prog) (defsOf prog) prog.blocks i < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (offsetTable_le_flatBytes prog i) hcode

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

theorem foldl_max_init_le {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl (fun a y => max a (f y)) init := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons y ys ih =>
    intro init
    rw [List.foldl_cons]
    exact le_trans (le_max_left init (f y)) (ih (max init (f y)))

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

theorem termChargeDepth_le_max (prog : Program) (b : Block) (hb : b ∈ prog.blocks.toList) :
    termChargeDepth prog b.term ≤ maxChargeDepth prog := by
  unfold maxChargeDepth
  rw [← Array.foldl_toList]
  refine le_trans ?_ (le_foldl_max_of_mem
    (fun b => max (termChargeDepth prog b.term)
      (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0)) prog.blocks.toList 0 hb)
  exact le_max_left _ _

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
  callCallee := by
    intro sloadChg L b pc cs hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.call cs) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := stmtChargeDepth_le_max prog b (.call cs) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [stmtChargeDepth, chargeDepth] at hst
    omega
  callGasFwd := by
    intro sloadChg L b pc cs hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.call cs) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0)]
    have hst := stmtChargeDepth_le_max prog b (.call cs) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [stmtChargeDepth, chargeDepth] at hst
    omega
  createOperands := by
    intro sloadChg L b pc cs hb hs
    have hmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
    have hsmem : (Stmt.create cs) ∈ b.stmts := List.mem_of_getElem? hs
    rw [chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) cs.salt,
        chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) cs.initSize,
        chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) cs.initOffset,
        chargeCache_length_sloadChg_eq prog sloadChg (fun _ => 0) cs.value]
    have hst := stmtChargeDepth_le_max prog b (.create cs) hmem hsmem
    have hb1024 : maxChargeDepth prog ≤ 1024 := h
    simp only [stmtChargeDepth, chargeDepth] at hst
    exact ⟨by omega, by omega, by omega, by omega⟩

/-! ### Producer-shaped derivation lemmas (call/create static facts)

The CALL producer (`callRealises_of_recorded` in `Realisability/Machinery.lean`)
currently THREADS the call stack-room facts (`hstkCallee`/`hstkGasFwd`) and the
result-slot addressability (`hslotaddr`) as internal hypotheses. Each lemma below
exposes EXACTLY the threaded shape, derived from the public static bundle
(`stackFits` / `IRWellFormed`), so the later integration pass can swap the threaded
hypotheses for these at the use sites. The create twins are stated ahead of the
CREATE producer (mirroring CALL). -/

/-- The CALL producer's `hstkCallee` shape, derived from the `stackFits` budget:
the callee materialise fits above the five zero pushes of the call prologue. -/
theorem callStackRoom_callee_of_stackFits {prog : Program} (h : stackFits prog)
    (sloadChg : Tmp → ℕ) {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    (hb : blockAt prog L = some b) (hs : b.stmts[pc]? = some (.call cs)) :
    5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024 :=
  (stackBounds_of_stackFits prog h).callCallee sloadChg L b pc cs hb hs

/-- The CALL producer's `hstkGasFwd` shape, derived from the `stackFits` budget:
the gasFwd materialise fits above the five zero pushes plus the materialised callee. -/
theorem callStackRoom_gasFwd_of_stackFits {prog : Program} (h : stackFits prog)
    (sloadChg : Tmp → ℕ) {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    (hb : blockAt prog L = some b) (hs : b.stmts[pc]? = some (.call cs)) :
    6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024 :=
  (stackBounds_of_stackFits prog h).callGasFwd sloadChg L b pc cs hb hs

/-- The create-prologue stack-room bundle, derived from the `stackFits` budget: one
bound per CREATE2 operand at its emission depth (salt 0, initSize 1, initOffset 2,
value 3) — the shapes a CREATE producer mirroring CALL will thread. -/
theorem createStackRoom_of_stackFits {prog : Program} (h : stackFits prog)
    (sloadChg : Tmp → ℕ) {L : Label} {b : Block} {pc : Nat} {cs : CreateSpec}
    (hb : blockAt prog L = some b) (hs : b.stmts[pc]? = some (.create cs)) :
    (chargeCache prog sloadChg cs.salt).length ≤ 1024
    ∧ 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024
    ∧ 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024
    ∧ 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024 :=
  (stackBounds_of_stackFits prog h).createOperands sloadChg L b pc cs hb hs

/-- The CALL producer's `hslotaddr` shape, derived from `IRWellFormed.slotAddr`'s
call-result arm: the result temp's spill slot is byte- and platform-addressable. -/
theorem callResult_slotAddr_of_IRWellFormed {prog : Program} (hwf : IRWellFormed prog)
    {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    (hb : blockAt prog L = some b) (hs : b.stmts[pc]? = some (.call cs)) :
    ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits :=
  fun t ht => hwf.slotAddr L b pc t hb (Or.inr (Or.inr (Or.inl ⟨cs, hs, ht⟩)))

/-- The create twin of `callResult_slotAddr_of_IRWellFormed`, from `IRWellFormed.slotAddr`'s
create-result arm. -/
theorem createResult_slotAddr_of_IRWellFormed {prog : Program} (hwf : IRWellFormed prog)
    {L : Label} {b : Block} {pc : Nat} {cs : CreateSpec}
    (hb : blockAt prog L = some b) (hs : b.stmts[pc]? = some (.create cs)) :
    ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits :=
  fun t ht => hwf.slotAddr L b pc t hb (Or.inr (Or.inr (Or.inr ⟨cs, hs, ht⟩)))

theorem slots_slot_of_defsOf (prog : Program) :
    ∀ (tw : Tmp) (slot' : Nat), defsOf prog tw = some (.slot slot') → slot' = slotOf tw := by
  intro tw slot' hd
  simp only [defsOf] at hd
  obtain ⟨pr, hf, hpr⟩ := Option.map_eq_some_iff.mp hd
  have hkey := List.find?_some hf
  rw [beq_iff_eq] at hkey
  have hmem := List.mem_of_find?_eq_some hf
  obtain ⟨b, hbmem, hbmap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, hsmem, hsmap⟩ := List.mem_filterMap.mp hbmap
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

end Lir
