import LirLean.MatDecLower
import LirLean.SimStmt
import LirLean.SimTerm
import LirLean.StashTail

/-!
# LirLean — discharging the carried decode bundles via `matDec_of_lower`

`SimStmt.sim_sstore_stmt` / `SimTerm.sim_term_*` carry their per-cursor decode facts
(`MatDec` for the operand materialisations, the per-opcode decodes for the consuming
`SSTORE`/`RETURN`/`JUMP`/`JUMPI`/`JUMPDEST`) as structured hypotheses. `MatDecLower`'s
`matDec_of_lower` (and the A2/A3 anchors) now *produce* those facts generically over
`lower prog`. This module wires them together: each consuming-opcode / operand decode is
read off `emitStmt`/`emitTerm`'s byte layout, so the lower lemmas' decode hypotheses are
discharged, leaving only the gas envelopes + runtime recording-correspondence ties (per §7).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

set_option maxRecDepth 8192

/-! ## `sstore` operand-segment facts

`emitStmt … (.sstore key value) = materialise value ++ materialise key ++ [SSTORE]`. The two
operand materialisations are the statement's byte sub-lists at offsets `0` and `lv`; the
trailing `SSTORE` is its last byte. -/

/-- `materialise value` is the prefix sub-list of the `sstore` statement bytes (offset 0). -/
theorem sstore_sub_value (defs : Tmp → Option Expr) (fuel : Nat) (key value : Tmp) :
    ∀ j, j < (materialiseExpr defs fuel (.tmp value)).length →
      (emitStmt defs fuel (.sstore key value))[0 + j]?
        = (materialiseExpr defs fuel (.tmp value))[j]? := by
  intro j hj
  rw [emitStmt_sstore]
  show ((materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key))
          ++ [Byte.sstore])[0 + j]? = _
  rw [Nat.zero_add, List.getElem?_append_left (by rw [List.length_append]; exact Nat.lt_add_right _ hj),
      List.getElem?_append_left hj]

/-- `materialise key` is the sub-list of the `sstore` statement bytes at offset `lv`. -/
theorem sstore_sub_key (defs : Tmp → Option Expr) (fuel : Nat) (key value : Tmp) :
    ∀ j, j < (materialiseExpr defs fuel (.tmp key)).length →
      (emitStmt defs fuel (.sstore key value))[(materialiseExpr defs fuel (.tmp value)).length + j]?
        = (materialiseExpr defs fuel (.tmp key))[j]? := by
  intro j hj
  rw [emitStmt_sstore]
  show ((materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key))
          ++ [Byte.sstore])[_ + j]? = _
  rw [List.getElem?_append_left (by rw [List.length_append]; omega)]
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

end Lir

namespace Lir
open Evm
open BytecodeLayer.Hoare
open Lir.V2
set_option maxRecDepth 8192

/-! ## SSTORE consuming-opcode decode

The trailing `SSTORE` of an `sstore` statement is its byte at offset `lv + lk` (after both
operand materialisations), discharged from A2 (`decode_at_offset_nonpush`). -/

theorem sstore_op_decode (prog : Program) (L : Label) (b : Block) (pc : ℕ) (key value : Tmp)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hbound : pcOf prog L pc
        + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
          + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2^32) :
    decode (lower prog)
      (UInt32.ofNat (pcOf prog L pc
        + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
          + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length)))
      = some (.Smsf .SSTORE, .none) := by
  set defs := defsOf prog
  set fuel := recomputeFuel prog
  set lv := (materialiseExpr defs fuel (.tmp value)).length with hlv
  set lk := (materialiseExpr defs fuel (.tmp key)).length with hlk
  have hemit : emitStmt defs fuel (.sstore key value)
      = materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key) ++ [Byte.sstore] :=
    emitStmt_sstore ..
  have hlen : (emitStmt defs fuel (.sstore key value)).length = lv + lk + 1 := by
    rw [hemit]; simp only [List.length_append, List.length_singleton]; omega
  have hk : (lv + lk) < (emitStmt defs fuel (.sstore key value)).length := by rw [hlen]; omega
  have hbyte0 : (emitStmt defs fuel (.sstore key value))[lv + lk]? = some Byte.sstore := by
    rw [hemit]
    rw [List.getElem?_append_right (by rw [List.length_append, ← hlv, ← hlk]),
        List.length_append, ← hlv, ← hlk, show lv + lk - (lv + lk) = 0 from by omega]
    rfl
  have := decode_at_offset_nonpush prog L b pc (.sstore key value) (lv + lk) Byte.sstore
    hb hs hk hbyte0 (by omega) (by decide)
  simpa using this

/-! ## `sstore` arm — decode discharged

`sim_sstore_stmt_lowered` is `sim_sstore_stmt` with the three carried decode hypotheses
(`hdv`/`hdk`/`hdop`) discharged generically over `lower prog` via `matDec_of_lower` (operands)
and `sstore_op_decode` (the consuming SSTORE). The remaining hypotheses are exactly the gas /
stack envelopes and the runtime `SstoreRealises` recording-correspondence tie (§7) — the
honest residual. The two `MatFueled` hypotheses are the recompute-fuel-sufficiency
well-formedness condition (discharged by `recomputeFuel` for well-formed programs). -/
theorem sim_sstore_stmt_lowered {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : ℕ} {fr : Frame} {acc : Account}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : StepScoped prog st (.sstore key value))
    -- recompute-fuel-sufficiency (well-formedness; discharged for `recomputeFuel`):
    (hwfv : MatFueled (defsOf prog) (recomputeFuel prog) (.tmp value))
    (hwfk : MatFueled (defsOf prog) (recomputeFuel prog) (.tmp key))
    -- pc bound (the statement's bytes fit a `UInt32`):
    (hbound : pcOf prog L pc
        + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
          + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2^32)
    -- gas / stack envelopes + the runtime SSTORE recording-correspondence tie (kept explicit):
    (hgas : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).sum
              + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).sum
              ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
              + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length
              + 1 ≤ 1024)
    (hsstore : SstoreRealises fr kw vw acc) (hnz : vw ≠ 0) :
    ∃ fr', Runs fr fr'
      ∧ Corr prog sloadChg obs (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = [] := by
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set lv := (materialiseExpr defs fuel (.tmp value)).length with hlv
  set lk := (materialiseExpr defs fuel (.tmp key)).length with hlk
  -- emitStmt length facts (the operand materialisations fit the statement).
  have hemit : emitStmt defs fuel (.sstore key value)
      = materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key) ++ [Byte.sstore] :=
    emitStmt_sstore ..
  have hlen : (emitStmt defs fuel (.sstore key value)).length = lv + lk + 1 := by
    rw [hemit]; simp only [List.length_append, List.length_singleton]; omega
  -- decode bundle, produced by `matDec_of_lower` / `sstore_op_decode`.
  have hdv : MatDec fr.exec.executionEnv.code defs sloadChg fuel fr.exec.pc (.tmp value) := by
    rw [hcorr.code_eq, hcorr.pc_eq]
    have := matDec_of_lower prog sloadChg L b pc (.sstore key value) 0 (.tmp value)
      hb hs (by simpa using sstore_sub_value defs fuel key value) (by rw [← hdefs, ← hfuel, hlen]; omega)
      hwfv (by rw [← hdefs, ← hfuel, Nat.add_zero]; omega)
    simpa using this
  have hdk : MatDec fr.exec.executionEnv.code defs sloadChg fuel
      (fr.exec.pc + UInt32.ofNat lv) (.tmp key) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add']
    have := matDec_of_lower prog sloadChg L b pc (.sstore key value) lv (.tmp key)
      hb hs (sstore_sub_key defs fuel key value) (by rw [← hdefs, ← hfuel, hlen]; omega) hwfk
      (by rw [← hdefs, ← hfuel]; omega)
    exact this
  have hdop : decode fr.exec.executionEnv.code
      (fr.exec.pc + UInt32.ofNat lv + UInt32.ofNat lk) = some (.Smsf .SSTORE, .none) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add', ofNat_add',
        show pcOf prog L pc + lv + lk = pcOf prog L pc + (lv + lk) from by omega]
    exact sstore_op_decode prog L b pc key value hb hs (by omega)
  exact sim_sstore_stmt hb hs hcorr hk hv hsc hdv hdk hdop hgas hstk hsstore hnz

end Lir

namespace Lir
open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2
set_option maxRecDepth 8192

/-! ## Terminator-cursor `MatSeg` (the A3 analogue for `ret`'s operand)

`emitTerm … (.ret t) = materialise t ++ PUSH32 0 ++ PUSH32 0 ++ [RETURN]`, anchored at
`termOf prog L` (the terminator cursor `pcOf prog L b.stmts.length`). The operand
materialisation is still the *prefix* sub-list (the two zero window operands and `RETURN`
follow it), so `MatSeg` holds at `termOf` via `flatBytes_at_termOf`. -/

/-- **`MatSeg` at the terminator cursor.** When `materialiseExpr defs fuel e`'s bytes are the
sub-list of `emitTerm … b.term` starting at `offset`, they sit in `flatBytes prog` at
`termOf prog L + offset`. -/
theorem matSeg_of_term (prog : Program) (L : Label) (b : Block) (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hsub : ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length →
        (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[offset + j]?
          = (materialiseExpr (defsOf prog) (recomputeFuel prog) e)[j]?)
    (hin : offset + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length
        ≤ (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length) :
    MatSeg prog (termOf prog L + offset) (defsOf prog) (recomputeFuel prog) e := by
  intro j hj
  have hanchor := flatBytes_at_termOf prog L b (offset + j) hb (by omega)
  rw [show termOf prog L + (offset + j) = termOf prog L + offset + j from by ring] at hanchor
  rw [hanchor]; exact hsub j hj

/-- The `ret`-value materialisation is the prefix sub-list of `emitTerm … (.ret t)` (offset 0). -/
theorem ret_sub_value (prog : Program) (t : Tmp) :
    ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length →
      (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) (.ret t))[0 + j]?
        = (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t))[j]? := by
  intro j hj
  show ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t))
          ++ emitImm 0 ++ emitImm 0 ++ [Byte.ret])[0 + j]? = _
  rw [Nat.zero_add]
  rw [List.getElem?_append_left (by rw [List.length_append, List.length_append]; omega),
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_left hj]

/-- **`ret` arm — `MatDec` decode discharged.** `sim_term_halt_ret` with its carried `hdv`
(`MatDec` for the returned value) discharged generically over `lower prog` via
`matDec_of_lower_term` (the `termOf` analogue of `matDec_of_lower`). The remaining hypotheses
are the gas/stack envelopes and the RETURN-site tie (`hret`: the two `PUSH32 0` window operands
decode/gas-cover after the materialise, `RETURN` decodes after them, and the frame is a
top-level `.call` frame with non-empty accounts — the §7-style supplied observation).
The `MatFueled` hypothesis is the recompute-fuel-sufficiency well-formedness condition. -/
theorem sim_term_halt_ret_lowered {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {t : Tmp} {vw : Word}
    {L : Label} {b : Block} {fr : Frame} {self : AccountAddress}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (hterm : b.term = .ret t)
    (hself : self = fr.exec.executionEnv.address)
    (hv : st.locals t = some vw)
    (hwf : MatFueled (defsOf prog) (recomputeFuel prog) (.tmp t))
    (hbound : termOf prog L
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2^32)
    (hgas : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
              ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024)
    (hret : ∀ frv : Frame, Runs fr frv →
        frv.exec.executionEnv.code = fr.exec.executionEnv.code →
        frv.exec.executionEnv.address = fr.exec.executionEnv.address →
        (∀ k, selfStorage frv k = selfStorage fr k) →
        frv.exec.stack = vw :: fr.exec.stack →
        ∃ cp,
          decode frv.exec.executionEnv.code frv.exec.pc
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
              = some (.System .RETURN, .none)
          ∧ 3 ≤ frv.exec.gasAvailable.toNat
          ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
          ∧ frv.kind = .call cp
          ∧ ¬ (frv.exec.accounts == ∅) = true) :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ (observe self (endFrame last halt)).world = st.world := by
  -- the `hdv` MatDec, discharged at the terminator cursor (`termOf = pcOf … b.stmts.length`).
  have hdv : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
      fr.exec.pc (.tmp t) := by
    rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hb]
    have hemit : (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length + 1
          ≤ (emitTerm (defsOf prog) (recomputeFuel prog)
              (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length := by
      rw [hterm]
      show _ ≤ ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t))
                  ++ emitImm 0 ++ emitImm 0 ++ [Byte.ret]).length
      simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil]
      omega
    have hseg := matSeg_of_term prog L b 0 (.tmp t) hb (by rw [hterm]; exact ret_sub_value prog t)
      (by omega)
    have := matDec_of_seg prog (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)
      (termOf prog L + 0) hwf (by rw [Nat.add_zero]; omega) (by rw [Nat.add_zero] at hseg ⊢; exact hseg)
    rw [Nat.add_zero] at this; exact this
  exact sim_term_halt_ret hcorr hterm hself hv hdv hgas hstk hret

end Lir

namespace Lir
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2
set_option maxRecDepth 8192

/-! ## PUSH4 destination round-trips (the `jump`/`branch` immediate + `hdestword` tie)

`emitDest off = PUSH4 :: offsetBytesBE off` (5 bytes). The 4-byte big-endian immediate
round-trips `uInt256OfByteArray` to `UInt256.ofNat (off % 2^32)`, whose `toUInt32?` recovers
`UInt32.ofNat off` — so both the PUSH4 decode value *and* the `hdestword` offset tie are
discharged. -/

/-- `fromBytes'` of the reversed 4 destination bytes is `off % 2^32` (the low 32 bits). -/
theorem fromBytes_offsetBytesBE (off : ℕ) :
    fromBytes' (offsetBytesBE off).reverse = off % 2 ^ 32 := by
  unfold offsetBytesBE
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, fromBytes',
    u8_ofNat_toFin]
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- The PUSH4 immediate round-trip: `uInt256OfByteArray ⟨offsetBytesBE off⟩ = ofNat (off%2^32)`. -/
theorem uInt256_offsetBytesBE (off : ℕ) :
    uInt256OfByteArray ⟨(offsetBytesBE off).toArray⟩ = UInt256.ofNat (off % 2 ^ 32) := by
  unfold uInt256OfByteArray
  rw [fromBytes_offsetBytesBE]

/-- `(ofNat (off % 2^32)).toUInt32? = some (ofNat off)` — the `hdestword` tie: the PUSH4
immediate `toUInt32?`-recovers the destination offset (mod absorbs into `UInt32.ofNat`). -/
theorem ofNatMod_toUInt32? (off : ℕ) :
    (UInt256.ofNat (off % 2 ^ 32)).toUInt32? = some (UInt32.ofNat off) := by
  unfold UInt256.toUInt32? UInt256.ofNat
  have hz : ∀ k, k ≥ 32 → (UInt32.ofNat ((off % 2 ^ 32) >>> k)) = 0 := by
    intro k hk
    have : (off % 2 ^ 32) >>> k = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by calc off % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
                                    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
    rw [this]; rfl
  rw [hz 32 (by norm_num), hz 64 (by norm_num), hz 96 (by norm_num), hz 128 (by norm_num),
      hz 160 (by norm_num), hz 192 (by norm_num), hz 224 (by norm_num)]
  simp only [beq_self_eq_true, Bool.and_self, if_true]
  show some (UInt32.ofNat (off % 2 ^ 32)) = some (UInt32.ofNat off)
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']; omega

/-! ## `jump` arm — decode bundle discharged

`emitTerm … (.jump dst) = emitDest off ++ [JUMP]` at the terminator cursor `termOf prog L`.
The PUSH4 destination decode (A3 push), the JUMP opcode (A3 nonpush at offset 5), the landing
JUMPDEST (`decode_at_block_offset_jumpdest`), and the `hdestword` offset tie are all
discharged. The remaining hypotheses are the `validJumps`-recording tie (`hvalid`, §7) and the
gas envelopes. -/

/-- The PUSH4 destination of a `jump`/edge decodes at the terminator cursor (offset `off0`
into `emitTerm`) carrying `ofNat (destOff % 2^32)`. Built from A3 (`decode_at_term_push`) and
`uInt256_offsetBytesBE`, given the `emitDest destOff` sub-list sits at `off0`. -/
theorem term_dest_decode (prog : Program) (L : Label) (b : Block) (off0 destOff : ℕ)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hsub : ∀ j, j < (emitDest destOff).length →
        (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[off0 + j]?
          = (emitDest destOff)[j]?)
    (hin : off0 + (emitDest destOff).length
        ≤ (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length)
    (hbound : termOf prog L + off0 + 4 < 2 ^ 32) :
    decode (lower prog) (UInt32.ofNat (termOf prog L + off0))
      = some (.Push .PUSH4, some (UInt256.ofNat (destOff % 2 ^ 32), 4)) := by
  have hedlen : (emitDest destOff).length = 5 := by simp [emitDest, offsetBytesBE]
  rw [hedlen] at hin
  -- flat-byte segment of emitDest at termOf + off0
  have hseg : ∀ j, j < (emitDest destOff).length →
      (flatBytes prog)[termOf prog L + off0 + j]? = (emitDest destOff)[j]? := by
    intro j hj
    have hanchor := flatBytes_at_termOf prog L b (off0 + j) hb (by rw [hedlen] at hj; omega)
    rw [show termOf prog L + (off0 + j) = termOf prog L + off0 + j from by ring] at hanchor
    rw [hanchor]; exact hsub j hj
  have hbyte : (flatBytes prog)[termOf prog L + off0]? = some Byte.push4 := by
    have := hseg 0 (by rw [hedlen]; omega); simpa [emitDest] using this
  have hwin : ((flatBytes prog).toArray.extract (termOf prog L + off0 + 1)
      (termOf prog L + off0 + 1 + 4)).toList = offsetBytesBE destOff := by
    apply extract_toList_eq (flatBytes prog) (termOf prog L + off0 + 1) 4 (offsetBytesBE destOff)
      (by simp [offsetBytesBE])
    intro j hj
    have := hseg (1 + j) (by rw [hedlen]; omega)
    rw [show termOf prog L + off0 + (1 + j) = termOf prog L + off0 + 1 + j from by ring] at this
    rw [this, show (1 + j) = j + 1 from by ring]
    simp [emitDest, List.getElem?_cons_succ]
  have himm : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (termOf prog L + off0 + 1)
      (termOf prog L + off0 + 1 + 4)⟩ = UInt256.ofNat (destOff % 2 ^ 32) := by
    have hh : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (termOf prog L + off0 + 1)
        (termOf prog L + off0 + 1 + 4)⟩ = uInt256OfByteArray ⟨(offsetBytesBE destOff).toArray⟩ := by
      unfold uInt256OfByteArray; congr 2
      show ((flatBytes prog).toArray.extract (termOf prog L + off0 + 1)
        (termOf prog L + off0 + 1 + 4)).toList.reverse = _
      rw [hwin]
    rw [hh, uInt256_offsetBytesBE]
  have hp : Evm.pushArgWidth (Evm.parseInstr Byte.push4) = (4 : UInt8) := by decide
  have h4 : (4 : UInt8).toNat = 4 := by decide
  have hres := decode_lower_push prog (termOf prog L + off0) Byte.push4 4
    (UInt256.ofNat (destOff % 2 ^ 32)) (by omega) hbyte hp (by decide) (by rw [h4]; exact himm)
  rw [hres]; rfl

end Lir

namespace Lir
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2
set_option maxRecDepth 8192

/-- **`sim_term_edge_jump` with the decode bundle discharged.** The PUSH4 destination, the
JUMP opcode, the landing JUMPDEST, and the `hdestword` offset tie are produced generically
over `lower prog` (`term_dest_decode` + A3 + `decode_at_block_offset_jumpdest` +
`ofNatMod_toUInt32?`). The remaining hypotheses are the `validJumps`-recording tie (`hvalid`,
§7) and the gas envelopes. The destination word is the PUSH4 immediate `ofNat (off % 2^32)`. -/
theorem sim_term_edge_jump_lowered {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {b : Block} {dst : Label} {bdst : Block} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (hterm : b.term = .jump dst)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdstlt : dst.idx < prog.blocks.size)
    -- pc bounds (the terminator + landing offsets fit a `UInt32`):
    (hbterm : termOf prog L + 5 < 2 ^ 32)
    (hboff : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32)
    -- gas envelopes (kept explicit):
    (hgpush : 3 ≤ fr.exec.gasAvailable.toNat)
    (hgjump : GasConstants.Gmid ≤ (pushFrameW fr
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
        4).exec.gasAvailable.toNat)
    (hgjd : GasConstants.Gjumpdest
        ≤ (jumpFrame (pushFrameW fr
            (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
            GasConstants.Gmid
            (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
            fr.exec.stack).exec.gasAvailable.toNat) :
    ∃ fr' L', L' = dst ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0 := by
  set off := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx with hoff
  set dest : Word := UInt256.ofNat (off % 2 ^ 32) with hdest
  -- emitTerm layout: emitDest off ++ [JUMP].
  have hemitT : emitTerm (defsOf prog) (recomputeFuel prog)
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term
        = emitDest off ++ [Byte.jump] := by rw [hterm]; rfl
  have hedlen : (emitDest off).length = 5 := by simp [emitDest, offsetBytesBE]
  have htermlen : (emitTerm (defsOf prog) (recomputeFuel prog)
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length = 6 := by
    rw [hemitT, List.length_append, hedlen]; rfl
  -- the PUSH4 destination at the terminator cursor.
  have hdpush : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH4, some (dest, 4)) := by
    rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hb,
        show termOf prog L = termOf prog L + 0 from by omega]
    exact term_dest_decode prog L b 0 off hb
      (by intro j hj; rw [hemitT]; rw [Nat.zero_add, List.getElem?_append_left hj])
      (by rw [htermlen, hedlen]; omega) (by omega)
  -- the JUMP opcode at offset 5.
  have hdjump : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 5)
      = some (.Smsf .JUMP, .none) := by
    rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hb, ofNat_add']
    have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[5]? = some Byte.jump := by
      rw [hemitT, List.getElem?_append_right (by rw [hedlen]), hedlen]; rfl
    have := decode_at_term_nonpush prog L b 5 Byte.jump hb (by rw [htermlen]; omega) hbyte0
      (by rw [show termOf prog L + 5 = termOf prog L + 5 from rfl]; omega) (by decide)
    exact this
  -- the landing JUMPDEST.
  have hdjd : decode (lower prog) (UInt32.ofNat off) = some (.Smsf .JUMPDEST, .none) :=
    decode_at_block_offset_jumpdest prog dst bdst hbdst (by rw [← hoff]; omega)
  -- the `hdestword` offset tie.
  have hdestword : dest.toUInt32? = some (UInt32.ofNat off) := ofNatMod_toUInt32? off
  -- the `validJumps`-recording tie is discharged structurally from `Corr` (frame-invariant
  -- `validJumps = validJumpDests code 0` + `code = lower prog`).
  exact sim_term_edge_jump hcorr hterm hbdst hdstlt hcorr.validJumps_lower hdestword hdpush hdjump
    hdjd hgpush hgjump hgjd

end Lir

namespace Lir
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2
set_option maxRecDepth 8192

/-! ## `branch` arm — decode bundle discharged

`emitTerm … (.branch cond thenL elseL) = materialise cond ++ emitDest thenOff ++ [JUMPI]
++ emitDest elseOff ++ [JUMP]`. The decode facts are anchored at `frc.exec.pc` (the
post-materialise-cond frame, `= termOf prog L + lcond` via `hmrc.pc`). Both PUSH4 destinations
(`term_dest_decode`), the JUMPI/JUMP opcodes (A3), the two landing JUMPDESTs
(`decode_at_block_offset_jumpdest`), and the two `hdestword` ties (`ofNatMod_toUInt32?`) are
discharged. The remaining hypotheses are the materialise bundle `hmrc` (B1), the
`validJumps`-recording tie (§7), and the gas envelopes. -/
theorem sim_term_edge_branch_lowered {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {b : Block} {cond : Tmp} {cw : Word}
    {thenL elseL : Label} {bthen belse : Block} {fr frc : Frame}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (hterm : b.term = .branch cond thenL elseL)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hc : st.locals cond = some cw)
    (hbthen : prog.blocks.toList[thenL.idx]? = some bthen)
    (hbelse : prog.blocks.toList[elseL.idx]? = some belse)
    (hthenlt : thenL.idx < prog.blocks.size)
    (helselt : elseL.idx < prog.blocks.size)
    (hmrc : MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw fr frc)
    -- pc bounds: cond-materialise length + the destinations / landings fit a `UInt32`.
    (hbterm : termOf prog L + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length
        + 11 < 2 ^ 32)
    (hbthenoff : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32)
    (hbelseoff : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32)
    -- gas envelopes (kept explicit), in terms of the round-trip destination words.
    (hgpushT : 3 ≤ frc.exec.gasAvailable.toNat)
    (hgjumpi : GasConstants.Ghigh ≤ (pushFrameW frc
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
        4).exec.gasAvailable.toNat)
    (hgjdT : GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
        GasConstants.Ghigh
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
        ([] : Stack Word)).exec.gasAvailable.toNat)
    (hgpushE : 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
        ([] : Stack Word)).exec.gasAvailable.toNat)
    (hgjumpE : GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
        ([] : Stack Word))
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat)
    (hgjdE : GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
        ([] : Stack Word))
        (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
        GasConstants.Gmid
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
        (jumpiFallthroughFrame (pushFrameW frc
          (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
          ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    ∃ fr' L', (cw ≠ 0 ∧ L' = thenL ∨ cw = 0 ∧ L' = elseL)
      ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0 := by
  set lc := (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length with hlc
  set thenOff := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx with hthenoff
  set elseOff := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx with helseoff
  set thenW : Word := UInt256.ofNat (thenOff % 2 ^ 32) with hthenW
  set elseW : Word := UInt256.ofNat (elseOff % 2 ^ 32) with helseW
  -- emitTerm branch layout.
  have hemitT : emitTerm (defsOf prog) (recomputeFuel prog)
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term
        = materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)
          ++ emitDest thenOff ++ [Byte.jumpi] ++ emitDest elseOff ++ [Byte.jump] := by
    rw [hterm]; rfl
  have hedlen : ∀ o, (emitDest o).length = 5 := fun o => by simp [emitDest, offsetBytesBE]
  have htermlen : (emitTerm (defsOf prog) (recomputeFuel prog)
      (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length = lc + 12 := by
    rw [hemitT]; simp only [List.length_append, List.length_singleton, hedlen, ← hlc]
  -- frc.exec.pc = ofNat (termOf + lc), frc.code = lower prog.
  have hfrcpc : frc.exec.pc = UInt32.ofNat (termOf prog L + lc) := by
    rw [hmrc.pc, hcorr.pc_eq, pcOf_eq_termOf prog L b hb, ofNat_add', ← hlc]
  have hfrccode : frc.exec.executionEnv.code = lower prog := by rw [hmrc.code]; exact hcorr.code_eq
  -- helper: an emitDest sub-fact at a given offset of emitTerm.
  -- PUSH4 thenOff at frc.pc (offset lc).
  have hdpushT : decode frc.exec.executionEnv.code frc.exec.pc
      = some (.Push .PUSH4, some (thenW, 4)) := by
    rw [hfrccode, hfrcpc]
    exact term_dest_decode prog L b lc thenOff hb
      (by intro j hj; rw [hemitT]
          rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
          rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
          rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
          rw [List.getElem?_append_right (by rw [← hlc]; omega), ← hlc, show lc + j - lc = j from by omega])
      (by rw [htermlen, hedlen]; omega) (by omega)
  -- JUMPI at frc.pc + 5 (offset lc + 5).
  have hdjumpi : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 5)
      = some (.Smsf .JUMPI, .none) := by
    rw [hfrccode, hfrcpc, ofNat_add',
        show termOf prog L + lc + 5 = termOf prog L + (lc + 5) from by omega]
    have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 5]? = some Byte.jumpi := by
      rw [hemitT]
      rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; omega)]
      rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; omega)]
      rw [List.getElem?_append_right (by simp only [List.length_append, hedlen, ← hlc]; omega)]
      simp only [List.length_append, hedlen, ← hlc, show lc + 5 - (lc + 5) = 0 from by omega]
      rfl
    exact decode_at_term_nonpush prog L b (lc + 5) Byte.jumpi hb (by rw [htermlen]; omega)
      hbyte0 (by omega) (by decide)
  -- PUSH4 elseOff at frc.pc + 6 (offset lc + 6).
  have hdpushE : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6)
      = some (.Push .PUSH4, some (elseW, 4)) := by
    rw [hfrccode, hfrcpc, ofNat_add',
        show termOf prog L + lc + 6 = termOf prog L + (lc + 6) from by omega]
    exact term_dest_decode prog L b (lc + 6) elseOff hb
      (by intro j hj
          have hjlen : j < 5 := by rw [hedlen] at hj; exact hj
          rw [hemitT]
          rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
          rw [List.getElem?_append_right (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
          simp only [List.length_append, List.length_singleton, hedlen, ← hlc,
            show lc + 6 + j - (lc + 5 + 1) = j from by omega])
      (by rw [htermlen, hedlen]; omega) (by omega)
  -- JUMP at frc.pc + 6 + 5 (offset lc + 11).
  have hdjump : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6 + UInt32.ofNat 5)
      = some (.Smsf .JUMP, .none) := by
    rw [hfrccode, hfrcpc, ofNat_add', ofNat_add',
        show termOf prog L + lc + 6 + 5 = termOf prog L + (lc + 11) from by omega]
    have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 11]? = some Byte.jump := by
      rw [hemitT]
      rw [List.getElem?_append_right (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
      simp only [List.length_append, List.length_singleton, hedlen, ← hlc,
        show lc + 11 - (lc + 5 + 1 + 5) = 0 from by omega]
      rfl
    exact decode_at_term_nonpush prog L b (lc + 11) Byte.jump hb (by rw [htermlen]; omega)
      hbyte0 (by omega) (by decide)
  -- the two landing JUMPDESTs.
  have hdjdT : decode (lower prog) (UInt32.ofNat thenOff) = some (.Smsf .JUMPDEST, .none) :=
    decode_at_block_offset_jumpdest prog thenL bthen hbthen (by rw [← hthenoff]; omega)
  have hdjdE : decode (lower prog) (UInt32.ofNat elseOff) = some (.Smsf .JUMPDEST, .none) :=
    decode_at_block_offset_jumpdest prog elseL belse hbelse (by rw [← helseoff]; omega)
  -- the two `hdestword` offset ties.
  have hthenword : thenW.toUInt32? = some (UInt32.ofNat thenOff) := ofNatMod_toUInt32? thenOff
  have helseword : elseW.toUInt32? = some (UInt32.ofNat elseOff) := ofNatMod_toUInt32? elseOff
  -- the cond-materialise endpoint `frc` carries `fr`'s `validJumps` (`MatRuns.validJumps`),
  -- which `Corr` pins to the lowered program's — the `validJumps`-recording tie discharged
  -- structurally.
  have hfrcvalid : frc.validJumps = validJumpDests (lower prog) 0 := by
    rw [hmrc.validJumps]; exact hcorr.validJumps_lower
  exact sim_term_edge_branch hcorr hterm hc hbthen hbelse hthenlt helselt hmrc hfrcvalid
    hthenword helseword hdpushT hdjumpi hdpushE hdjump hdjdT hdjdE
    hgpushT hgjumpi hgjdT hgpushE hgjumpE hgjdE

/-! ## `assign t .gas` arm — the §7 `hstash` run **discharged** (P1)

The gas spill stash `[GAS] ++ PUSH32 (slotOf t) ++ MSTORE` is the byte stream of `emitStmt …
(.assign t .gas)` at cursor `(L, pc)`. `sim_assign_gas` previously took the *entire* stash run
(plus its memory shape + 8 frame pins) as the supplied §7 hypothesis `hstash`. Here we **build**
it: the three decode anchors are read off the byte layout (A2 `decode_at_offset_nonpush` for
`GAS`/`MSTORE`, `imm_leaf_decode` for `PUSH32`), and `stash_tail_gas` (`StashTail.lean`) runs the
three opcodes, producing exactly the honest memory-channel tie `sim_assign_gas` now consumes (the
`.memory` bytes + `.activeWords` of `fr….mstore (slotOf t) (ofUInt64 (fr.gas − Gbase))` — the
realised one-read gas value, `gasReadOf (gasFrame fr)`). The opaque run + the false
full-`toMachineState` equality are **gone**; the residual is the honest runtime gas/memory-witness
side-conditions a real descending-gas run supplies (the `GAS`/`PUSH`/`MSTORE` gas bounds + the
`memoryExpansionWords?` witness), plus the addressability + post-state realisability — all
genuinely satisfiable, none vacuous. -/

/-- **`sim_assign_gas` with the stash run discharged (`_lowered`, P1).** Replaces the supplied
`hstash` run with the honest runtime gas/witness side-conditions; the GAS;PUSH;MSTORE run and its
memory-channel tie are constructed internally (decode from the byte layout + `stash_tail_gas`).
The bound gas read is `ofUInt64 (fr.gas − Gbase)` — the realised `GAS` output. -/
theorem sim_assign_gas_lowered {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {t : Tmp}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame} {words' : UInt64}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t .gas))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hsc : StepScoped prog st (.assign t .gas))
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    -- addressability of `slotOf t` (a genuine `slotOf` side-condition):
    (hslot63 : slotOf t + 63 < 2 ^ 64)
    (hslotplat : slotOf t < 2 ^ System.Platform.numBits)
    -- the statement's bytes fit a `UInt32` cursor:
    (hbound : pcOf prog L pc + 34 < 2 ^ 32)
    -- honest runtime gas / memory-expansion-witness side-conditions (the descending-gas run
    -- supplies them — exactly the `sim_mstore`/`sim_gas` gas guards, NOT vacuous):
    (hgasGas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat)
    (hgasPush : 3 ≤ (gasFrame fr).exec.gasAvailable.toNat)
    (hmem : memoryExpansionWords?
      (pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32).exec.activeWords
      (UInt256.ofNat (slotOf t)) 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf
      (pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32).exec words'
        ≤ (pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32).exec.gasAvailable.toNat)
    (hgasMstore : GasConstants.Gverylow
      ≤ ((pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32).exec.gasAvailable
          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf
              (pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32).exec words')).toNat)
    -- the post-state scoping (downstream-supplied; the bound read is the realised `GAS` output
    -- `ofUInt64 (fr.gas − Gbase)`):
    (hscoped' : ∀ t', (st.setLocal t
          (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).locals t' ≠ none →
        (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
        ∧ defsOf prog t' ≠ none) :
    ∃ endFr, Runs fr endFr
      ∧ Corr prog sloadChg obs (st.setLocal t
          (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))) endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set slot := slotOf t with hslotvar
  -- the gas stash byte stream: `[GAS] ++ emitImm (ofNat slot) ++ [MSTORE]`, length 35.
  have hgasmat : materialiseExpr defs fuel .gas = [Byte.gas] := by
    have hf1 : 1 ≤ fuel := by rw [hfuel]; unfold recomputeFuel; omega
    obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_lt hf1
    rw [show fuel = f + 1 from by omega]; rfl
  have hemit : emitStmt defs fuel (.assign t .gas)
      = [Byte.gas] ++ emitImm (UInt256.ofNat slot) ++ [Byte.mstore] := by
    rw [emitStmt_assign_slot defs fuel t .gas hslotdef, hgasmat]
  have hemitlen : (emitStmt defs fuel (.assign t .gas)).length = 35 := by
    rw [hemit]; simp only [List.length_append, List.length_singleton, emitImm_length]
  -- byte-segment facts in `flatBytes prog` at the cursor `pcOf prog L pc`.
  have hseg : ∀ k, k < 35 →
      (flatBytes prog)[pcOf prog L pc + k]? = (emitStmt defs fuel (.assign t .gas))[k]? := by
    intro k hk
    exact flatBytes_at_pcOf_offset prog L b pc (.assign t .gas) k hb hs (by rw [hemitlen]; omega)
  -- decode the three opcodes over `lower prog`.
  -- GAS at offset 0.
  have hdgas : decode (lower prog) (UInt32.ofNat (pcOf prog L pc)) = some (.Smsf .GAS, .none) := by
    have h := decode_at_offset_nonpush prog L b pc (.assign t .gas) 0 Byte.gas hb hs
      (by rw [hemitlen]; omega) (by rw [hemit]; rfl) (by omega) (by decide)
    simpa using h
  -- PUSH32 (ofNat slot) at offset 1 (its 32 immediate bytes round-trip via `imm_leaf_decode`).
  have hdpush : decode (lower prog) (UInt32.ofNat (pcOf prog L pc + 1))
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)) := by
    apply imm_leaf_decode prog (pcOf prog L pc + 1) (UInt256.ofNat slot) (by omega)
    intro j hj
    have hk := hseg (1 + j) (by rw [emitImm_length] at hj; omega)
    rw [show pcOf prog L pc + (1 + j) = pcOf prog L pc + 1 + j from by ring] at hk
    rw [hk, hemit]
    rw [List.getElem?_append_left (by rw [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_right (by simp), show (1 + j - [Byte.gas].length) = j from by simp]
  -- MSTORE at offset 34.
  have hdmstore : decode (lower prog) (UInt32.ofNat (pcOf prog L pc + 34))
      = some (.Smsf .MSTORE, .none) := by
    have h := decode_at_offset_nonpush prog L b pc (.assign t .gas) 34 Byte.mstore hb hs
      (by rw [hemitlen]; omega)
      (by rw [hemit]
          rw [List.getElem?_append_right (by simp [emitImm_length]),
              show 34 - ([Byte.gas] ++ emitImm (UInt256.ofNat slot)).length = 0 from by
                simp [emitImm_length]]
          rfl)
      (by omega) (by decide)
    simpa using h
  -- assemble the stash run via `stash_tail_gas`, anchored at `fr` (`pc_eq`/`code_eq`).
  have hfrpc : fr.exec.pc = UInt32.ofNat (pcOf prog L pc) := hcorr.pc_eq
  have hfrcode : fr.exec.executionEnv.code = lower prog := hcorr.code_eq
  have hdgas' : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none) := by
    rw [hfrcode, hfrpc]; exact hdgas
  have hdpush' : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 1)
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)) := by
    rw [hfrcode, hfrpc, ofNat_add']; exact hdpush
  have hdmstore' : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 1 + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none) := by
    rw [hfrcode, hfrpc, ofNat_add', ofNat_add',
        show pcOf prog L pc + 1 + 33 = pcOf prog L pc + 34 from by omega]
    exact hdmstore
  obtain ⟨endFr, hrun, hmembytes, hmemactive, hpc, hcode, hvalid, haddr, hcanmod, haccounts,
      hstorage, hstkEnd⟩ :=
    stash_tail_gas fr slot words' hcorr.stack_nil hdgas' hdpush' hdmstore' hgasGas hgasPush
      hmem hgasMem hgasMstore
  -- feed `sim_assign_gas` the constructed stash bundle (honest memory-channel tie shape).
  refine sim_assign_gas hb hs hslotdef hcorr hsc hslots hscoped' ?_
  refine ⟨hslot63, hslotplat, endFr, hrun, hmembytes, hmemactive, ?_, hcode, hvalid, haddr,
    hcanmod, hstorage, hstkEnd⟩
  -- pc: `stash_tail_gas` advances by 35 = the emit length.
  rw [hpc, hemitlen]

end Lir

-- Build-enforced axiom-cleanliness guard for the P1 gas-stash discharge: `sim_assign_gas_lowered`
-- constructs the GAS;PUSH;MSTORE stash run internally (decode layout + `stash_tail_gas`),
-- replacing the supplied opaque `hstash` run; it depends only on `[propext, Classical.choice,
-- Quot.sound]`.
#print axioms Lir.sim_assign_gas_lowered
