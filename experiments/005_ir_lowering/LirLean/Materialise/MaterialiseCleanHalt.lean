import LirLean.Materialise.MatFoldChannel
import LirLean.Materialise.CleanHaltExtract

/-!
# LirLean — `materialise_runsC_of_cleanHalt` (the gas-dropping twin of the value channel)

The **FoldLemma** track, over the fold. `materialise_runsC` (`Materialise/MatFoldChannel.lean`)
takes the whole-expression gas envelope `(chargeExpr sloadChg (chargeCache prog sloadChg) e).sum
≤ fr.gas.toNat` as a *supplied* hypothesis. This module **derives** that envelope from a single
`CleanHaltsNonException fr` witness at the entry cursor — the same clean-halt approach the
Option A ripple used for the per-op runtime envelopes (`CleanHaltExtract.lean` §3) — and
re-exports the full `MatRunsC` conclusion bundle with the gas bound now a *derived* extra
conjunct.

## The gas-FOLD (`materialise_chargeC_le_of_cleanHalt`)

The heart is a recursion over the same well-founded measure as `MatDecC`/`materialise_runsC`
(`matDecMeasure`, descending the def-env at the `.tmp t → definiens` step via
`matDecMeasure_remat_lt`) that **accumulates the charge sum** while
descending the materialise run, deriving `(chargeExpr sloadChg (chargeCache prog sloadChg)
e).sum ≤ fr.gas.toNat` from clean-halt. Each materialise op is a *continuing* op, so
`CleanHaltsNonException` (via the `next_*_of_cleanHalt` family) forces a `.next` step and reads
off that op's charge ≤ this cursor's gas. The fold reuses `materialise_runsC` itself to
**produce the intermediate post-frames** (`frb`/`fra`/`frp`) and their `gasToNat` descent
(`frb.gas = fr.gas − sum_b`), then `cleanHaltsNonException_forward` threads the clean-halt
across each sub-run so the next cursor's clean-halt is in hand. Combining the per-op bounds
with the `gasToNat` descents reassembles the aggregate `(chargeExpr …).sum ≤ fr.gas`.

Because the fold leans on `materialise_runsC` for frame production, it inherits its
value-channel premises (`MatDecC`, `DefsSound`, the scoping `Or`, `StorageAgree`,
`MemRealises`, `evalExpr`) verbatim. The *difference* is exactly the swap
`hgas (supplied) ↦ CleanHaltsNonException (witness)`; the `hstk` stack-room hypothesis is
**kept** (the stack-room fold is a separate structural argument from the gas fold — the sim
ties supply `hstk` from the block-entry stack-nil + the 1024 budget, not from clean-halt).

## The deliverable (`materialise_runsC_of_cleanHalt`)

The `materialise_runsC` twin: same conclusion `∃ fr', MatRunsC … ∧ (chargeExpr …).sum ≤
fr.gas.toNat`. Derives the gas bound via the fold, then feeds it to `materialise_runsC` for
the run; the bound is re-exported as the second conjunct so consumers (the SSTORE
aggregate-charge / SLOAD key-prefix sim ties) read it off directly instead of supplying it.

This module is kept **out** of `MatFoldChannel.lean` to avoid a
`CleanHaltExtract → MatFoldChannel` import tangle at the value-channel core
(`CleanHaltExtract` needs only the endpoint bundles, not the linchpin proof).

No `sorry`, no `axiom`, no `native_decide`. Axiom-cleanliness guard comment at the end
(the build-enforced `#print axioms` guards live in `LirLean/Audit.lean`).
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.CleanHaltExtract

/-! ## The gas-FOLD — `materialise_chargeC_le_of_cleanHalt`

Derives the whole-expression charge bound from clean-halt, by the `matDecMeasure` recursion
(the same descent as `materialise_runsC`), mirroring it arm-for-arm but tracking only the Nat
gas accumulation. The post-frames are produced by `materialise_runsC` (the value channel is in
scope); the clean-halt is threaded across each sub-run by `cleanHaltsNonException_forward`. -/

/-- **The gas FOLD.** From `CleanHaltsNonException fr` at the materialise entry cursor (plus the
value-channel premises and the stack-room bound), the whole-expression charge sum fits under the
entry frame's gas: `(chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤
fr.exec.gasAvailable.toNat`. This is the exact `hgas` hypothesis `materialise_runsC` consumes —
now derived. -/
theorem materialise_chargeC_le_of_cleanHalt {prog : Program} (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (I : Tmp → Prop) (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSoundS prog I st)
    (hfree : RematClosureFree prog I e)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hcs : CleanHaltsNonException fr)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024) :
    (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat := by
  match e, hfree, hdec, hne, hnsl, heval, hstk with
  | .imm v, _, hdec, _, _, heval, hstk =>
      -- `chargeExpr .imm = [Gverylow]`; PUSH32 clean-halt ⟹ `Gverylow ≤ fr.gas`.
      have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
          = some (.Push .PUSH32, some (v, 32)) := by rw [matDecC_imm] at hdec; exact hdec
      have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
        simp only [chargeExpr_imm, List.length_cons, List.length_nil] at hstk; omega
      obtain ⟨hg, _⟩ := next_push_of_cleanHalt fr .PUSH32 v 32 hcs (by decide) hdec'
        (by decide) (by decide) hszfr
      simp only [chargeExpr_imm, List.sum_cons, List.sum_nil]
      omega
  | .gas, _, _, hne, _, _, _ => exact absurd rfl hne
  | .sload k, _, _, _, hnsl, _, _ => exact absurd rfl (hnsl k)
  | .tmp t, hfree, hdec, _, _, heval, hstk =>
      have hloc : st.locals t = some w := heval
      cases hal : allocate prog t with
      | none =>
          exfalso
          have hdn : defsOf prog t = none := hal
          exact (hscoped t (by rw [hloc]; simp)).2 hdn
      | some loc =>
          cases loc with
          | slot n =>
              -- == MLOAD-readback arm: `matCache t = PUSH32 n ; MLOAD`, charge `[Gverylow, Gverylow]` ==
              have hmd := hdec
              rw [matDecC_tmp_slot prog hdc hord fr.exec.executionEnv.code fr.exec.pc t n hal]
                at hmd
              obtain ⟨hdpush, hdmload⟩ := hmd
              have hchg : chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)
                  = [Gverylow, Gverylow] := by
                simp only [chargeExpr_tmp]
                exact chargeCache_slot prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
                rw [hchg] at hstk
                simp only [List.length_cons, List.length_nil] at hstk; omega
              -- step 1: PUSH32 n, clean-halt ⟹ `Gverylow ≤ fr.gas`, and drive to `frp`.
              obtain ⟨hgPush, hpushNext⟩ := next_push_of_cleanHalt fr .PUSH32
                (UInt256.ofNat n) 32 hcs (by decide) hdpush (by decide) (by decide) hszfr
              set frp := pushFrameW fr (UInt256.ofNat n) 32 with hfrp
              have hstepPush : StepsTo fr frp := stepsTo_of_next hpushNext
              have hcsP : CleanHaltsNonException frp :=
                cleanHaltsNonException_forward hcs (Runs.single hstepPush)
              -- `frp`'s gas, pc, code, stack.
              have hgv3 : (Gverylow : ℕ) = 3 := rfl
              have hfrpgasN : frp.exec.gasAvailable.toNat
                  = fr.exec.gasAvailable.toNat - Gverylow := by
                show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
                rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow (by rw [hgv3]; omega)
                  (by rw [hgv3]; omega)]
              have hfrpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
              have hfrppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
                rw [hfrp, pushFrameW_pc, push32_pcΔ]
              have hfrpstk : frp.exec.stack = (UInt256.ofNat n) :: fr.exec.stack := rfl
              have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; simp; omega
              -- MLOAD decode at `frp`.
              have hmloaddec : decode frp.exec.executionEnv.code frp.exec.pc
                  = some (.Smsf .MLOAD, .none) := by
                rw [hfrpcode, hfrppc]
                have : (emitImm (UInt256.ofNat n)).length = 33 := emitImm_length _
                rw [show fr.exec.pc + UInt32.ofNat 33
                      = fr.exec.pc + UInt32.ofNat (emitImm (UInt256.ofNat n)).length from by
                      rw [this]]
                exact hdmload
              -- step 2: MLOAD clean-halt ⟹ expansion witness + both charges at `frp`.
              obtain ⟨words', _hmem, hgasMem, hgasMl, _⟩ :=
                next_mload_of_cleanHalt frp (UInt256.ofNat n) fr.exec.stack hcsP
                  hmloaddec hfrpstk hfrpsz
              -- `Gverylow ≤ frp.gas - memExp ≤ frp.gas`, and `frp.gas = fr.gas - Gverylow`,
              -- so `Gverylow + Gverylow ≤ fr.gas` — the `[Gverylow, Gverylow]` sum bound.
              have hsubLe : (frp.exec.gasAvailable
                  - UInt64.ofNat (memExpansionChargeOf frp.exec words')).toNat
                    ≤ frp.exec.gasAvailable.toNat :=
                BytecodeLayer.Precompiles.toNat_sub_ofNat_le hgasMem
              rw [hchg]
              simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
              have hgMlW : Gverylow ≤ frp.exec.gasAvailable.toNat := le_trans hgasMl hsubLe
              rw [hfrpgasN] at hgMlW
              omega
          | remat e' =>
              -- == pure recompute path (`DefsSound`) — recurse into the definiens ==
              have hcc : chargeCache prog sloadChg t
                  = chargeExpr sloadChg (chargeCache prog sloadChg) e' :=
                chargeCache_remat prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              obtain ⟨hremt, he'ng, he'nsl⟩ := defsOf_of_allocate_remat prog hal
              have htmd : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e' := by
                rw [matDecC_tmp_remat prog hdc hord fr.exec.executionEnv.code fr.exec.pc t e' hal]
                  at hdec
                exact hdec
              have hnr : ¬ NonRecomputable prog t := by
                rcases (hscoped t (by rw [hloc]; simp)).1 with hnr | ⟨s, hcrdef⟩
                · exact hnr
                · exfalso
                  have hdeft : defsOf prog t = some (Loc.remat e') := hal
                  rw [hdeft] at hcrdef
                  exact absurd hcrdef (by simp)
              obtain ⟨hfree_t, hfree_remat⟩ := RematClosureFree.tmp_inv hfree
              have hdfs : some w = evalExpr st 0 e' :=
                hsound t e' w hremt hnr hfree_t hloc
              have heval' : evalExpr st obs e' = some w := by
                rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
              have hstk' : fr.exec.stack.size
                  + (chargeExpr sloadChg (chargeCache prog sloadChg) e').length ≤ 1024 := by
                have hx := hstk; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              have hbound := materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I e' w fr
                htmd hsound (hfree_remat e' hal) hscoped hstore he'ng he'nsl hmemreal heval' hcs hstk'
              simp only [chargeExpr_tmp]
              rw [hcc]
              exact hbound
  | .add a b, hfree, hdec, _, _, heval, hstk =>
      -- operand values from `heval`.
      obtain ⟨va, hla, vb, hlb, _⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
            ∧ w = UInt256.add va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      rw [matDecC_add] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hcadd := chargeExpr_add sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hcadd]; simp only [List.length_append, List.length_singleton]
      -- (1) recursive gas-fold on b at `fr`: `sum_b ≤ fr.gas`.
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hlen_split] at hx
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length :=
          chargeCache_length_pos prog sloadChg a
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.add_inv hfree
      have hsumb := materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp b) vb fr
        hdb hsound hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hcs hstkb
      -- (2) produce `frb` via the value channel with the just-derived `sum_b ≤ fr.gas`.
      obtain ⟨frb, hmrb⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp b) vb fr hdb hsound
        hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hsumb hstkb
      -- forward clean-halt `fr → frb`.
      have hcsB : CleanHaltsNonException frb := cleanHaltsNonException_forward hcs hmrb.runs
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      -- (3) recursive gas-fold on a at `frb`: `sum_a ≤ frb.gas`.
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length :=
          chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      have hsuma := materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp a) va frb
        hda' hsound hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hcsB hstka
      -- (4) produce `fra` via the value channel.
      obtain ⟨fra, hmra⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp a) va frb hda' hsound
        hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hsuma hstka
      have hcsA : CleanHaltsNonException fra := cleanHaltsNonException_forward hcsB hmra.runs
      -- (5) ADD at `fra`: `Gverylow ≤ fra.gas`.
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .ADD, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length :=
          chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      obtain ⟨hgAdd, _⟩ := next_add_of_cleanHalt fra va vb fr.exec.stack hcsA hadec hastk haszle
      -- (6) reassemble: `sum_b + sum_a + Gverylow ≤ fr.gas`.
      rw [hsum_split]
      have hfrbgasN := hmrb.gasToNat
      have hfragasN := hmra.gasToNat
      simp only [chargeExpr_tmp] at hfrbgasN hfragasN hsumb hsuma
      rw [hfragasN, hfrbgasN] at hgAdd
      rw [hfrbgasN] at hsuma
      omega
  | .lt a b, hfree, hdec, _, _, heval, hstk =>
      obtain ⟨va, hla, vb, hlb, _⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
            ∧ w = UInt256.lt va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      rw [matDecC_lt] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hclt := chargeExpr_lt sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hclt]; simp only [List.length_append, List.length_singleton]
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hlen_split] at hx
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length :=
          chargeCache_length_pos prog sloadChg a
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.lt_inv hfree
      have hsumb := materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp b) vb fr
        hdb hsound hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hcs hstkb
      obtain ⟨frb, hmrb⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp b) vb fr hdb hsound
        hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hsumb hstkb
      have hcsB : CleanHaltsNonException frb := cleanHaltsNonException_forward hcs hmrb.runs
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length :=
          chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      have hsuma := materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp a) va frb
        hda' hsound hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hcsB hstka
      obtain ⟨fra, hmra⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp a) va frb hda' hsound
        hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hsuma hstka
      have hcsA : CleanHaltsNonException fra := cleanHaltsNonException_forward hcsB hmra.runs
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .LT, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length :=
          chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      obtain ⟨hgLt, _⟩ := next_lt_of_cleanHalt fra va vb fr.exec.stack hcsA hadec hastk haszle
      rw [hsum_split]
      have hfrbgasN := hmrb.gasToNat
      have hfragasN := hmra.gasToNat
      simp only [chargeExpr_tmp] at hfrbgasN hfragasN hsumb hsuma
      rw [hfragasN, hfrbgasN] at hgLt
      rw [hfrbgasN] at hsuma
      omega
  termination_by matDecMeasure prog e
  decreasing_by
    all_goals
      first
        | (simp only [matDecMeasure]; omega)
        | (exact matDecMeasure_remat_lt prog hdc hord (by assumption))

/-! ## The deliverable — `materialise_runsC_of_cleanHalt`

The `materialise_runsC` twin: derive the gas bound via the fold, feed it to
`materialise_runsC` for the run, and re-export the bound as the second conjunct. -/

/-- **The value channel's gas-dropping twin.** Same conclusion as `materialise_runsC` plus the
derived gas envelope: from `CleanHaltsNonException fr` (replacing the supplied `hgas`) and the
value-channel premises, running `matExpr (matCache prog) e` lands the whole `MatRunsC` bundle
**and** the charge sum is shown to fit under the entry gas (`(chargeExpr sloadChg
(chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat`). The SSTORE aggregate-charge /
SLOAD key-prefix sim ties consume this derived bound instead of supplying it. -/
theorem materialise_runsC_of_cleanHalt {prog : Program} (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (I : Tmp → Prop) (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSoundS prog I st)
    (hfree : RematClosureFree prog I e)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hcs : CleanHaltsNonException fr)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024) :
    ∃ fr', MatRunsC prog sloadChg e w fr fr'
      ∧ (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat := by
  have hgas : (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum
      ≤ fr.exec.gasAvailable.toNat :=
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I e w fr hdec hsound hfree hscoped
      hstore hne hnsl hmemreal heval hcs hstk
  obtain ⟨fr', hmr⟩ := materialise_runsC hdc hord sloadChg st obs I e w fr hdec hsound hfree hscoped
    hstore hne hnsl hmemreal heval hgas hstk
  exact ⟨fr', hmr, hgas⟩

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the FoldLemma deliverables
-- (`Lir.V2.materialise_chargeC_le_of_cleanHalt` / `Lir.V2.materialise_runsC_of_cleanHalt`)
-- live in `LirLean/Audit.lean`: both depend only on `[propext, Classical.choice, Quot.sound]`.
