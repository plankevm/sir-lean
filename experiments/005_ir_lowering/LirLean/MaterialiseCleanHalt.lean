import LirLean.MaterialiseRuns
import LirLean.CleanHaltExtract

/-!
# LirLean — `materialise_runs_of_cleanHalt` (the gas-dropping twin of B1)

The **FoldLemma** track. `materialise_runs` (B1, `MaterialiseRuns.lean`) takes the whole-expression
gas envelope `(chargeOf …).sum ≤ fr.gas.toNat` as a *supplied* hypothesis. This module **derives**
that envelope from a single `CleanHaltsNonException fr` witness at the entry cursor — the same
clean-halt approach the Option A ripple used for the per-op runtime envelopes
(`CleanHaltExtract.lean` §3) — and re-exports B1's full conclusion bundle with the gas bound now a
*derived* extra conjunct.

## The gas-FOLD (`materialise_charge_le_of_cleanHalt`)

The heart is a structural fold over `materialiseExpr`'s recursion that **accumulates the charge
sum** while descending the materialise run, deriving `(chargeOf defs sloadChg fuel e).sum ≤
fr.gas.toNat` from clean-halt. Each materialise op is a *continuing* op, so
`CleanHaltsNonException` (via the `next_*_of_cleanHalt` family) forces a `.next` step and reads off
that op's charge ≤ this cursor's gas. The fold reuses B1 `materialise_runs` itself to **produce the
intermediate post-frames** (`frb`/`fra`/`frp`) and their `gasToNat` descent
(`frb.gas = fr.gas − sum_b`), then `cleanHaltsNonException_forward` threads the clean-halt across
each sub-run so the next cursor's clean-halt is in hand. Combining the per-op bounds with the
`gasToNat` descents reassembles the aggregate `(chargeOf …).sum ≤ fr.gas`.

Because the fold leans on B1 for frame production, it inherits B1's value-channel premises
(`DefsSound`, the scoping `Or`, `StorageAgree`, `MemRealises`, `evalExpr`) verbatim. The
*difference* from B1 is exactly the swap `hgas (supplied) ↦ CleanHaltsNonException (witness)`; the
`hstk` stack-room hypothesis is **kept** (the stack-room fold is a separate structural argument from
the gas fold — the §7 ties supply `hstk` from the block-entry stack-nil + the 1024 budget, not from
clean-halt).

## The deliverable (`materialise_runs_of_cleanHalt`)

The B1 twin: same conclusion `∃ fr', MatRuns … ∧ (chargeOf …).sum ≤ fr.gas.toNat`. Derives the gas
bound via the fold, then feeds it to B1 `materialise_runs` for the run; the bound is re-exported as
the second conjunct so consumers (the SSTORE aggregate-charge / SLOAD key-prefix §7 ties) read it
off directly instead of supplying it.

This module is kept **out** of `MaterialiseRuns.lean` to avoid a `CleanHaltExtract → MaterialiseRuns`
import cycle (`CleanHaltExtract` imports `CleanHalt` only).

No `sorry`, no `axiom`, no `native_decide`. `#print axioms` guard at the end.
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.CleanHaltExtract
open Lir.V2 (CleanHaltsNonException cleanHaltsNonException_forward)

/-! ## The gas-FOLD — `materialise_charge_le_of_cleanHalt`

Derives the whole-expression charge bound from clean-halt, by induction on `fuel` then `cases e`,
mirroring `materialise_runs` arm-for-arm but tracking only the Nat gas accumulation. The post-frames
are produced by B1 `materialise_runs` (the value channel is in scope); the clean-halt is threaded
across each sub-run by `cleanHaltsNonException_forward`. -/

/-- **The gas FOLD.** From `CleanHaltsNonException fr` at the materialise entry cursor (plus the B1
value-channel premises and the stack-room bound), the whole-expression charge sum fits under the
entry frame's gas: `(chargeOf defs sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat`. This is the
exact `hgas` hypothesis B1 `materialise_runs` supplies — now derived. -/
theorem materialise_charge_le_of_cleanHalt {prog : Program} (sloadChg : Tmp → ℕ)
    (fuel : Nat) (st : V2.IRState) (obs : Word) :
    ∀ (e : Expr) (w : Word) (fr : Frame),
      MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e →
      DefsSound prog st →
      (∀ t, st.locals t ≠ none →
        (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
        ∧ defsOf prog t ≠ none) →
      StorageAgree st fr →
      e ≠ .gas →
      (∀ k, e ≠ .sload k) →
      MemRealises prog st fr →
      V2.evalExpr st obs e = some w →
      CleanHaltsNonException fr →
      fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg fuel e).length ≤ 1024 →
      (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat := by
  set defs := defsOf prog with hdefs
  induction fuel with
  | zero =>
      intro e w fr hdec _ _ _ _ _ _ heval hcs hstk
      cases e with
      | imm v =>
          -- `chargeOf .imm = [Gverylow]`; PUSH32 clean-halt ⟹ `Gverylow ≤ fr.gas`.
          have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
              = some (.Push .PUSH32, some (v, 32)) := by rw [matDec_imm] at hdec; exact hdec
          have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
            rw [chargeOf_imm] at hstk
            simp only [List.length_cons, List.length_nil] at hstk; omega
          obtain ⟨hg, _⟩ := next_push_of_cleanHalt fr .PUSH32 v 32 hcs (by decide) hdec'
            (by decide) (by decide) hszfr
          rw [chargeOf_imm]; simpa [List.sum_cons] using hg
      | slot slot => exact absurd heval (by simp [V2.evalExpr])
      | _ => exact absurd hdec (by simp [MatDec])
  | succ f ih =>
      intro e w fr hdec hsound hscoped hstore hne hnsl hmemreal heval hcs hstk
      cases e with
      | imm v =>
          have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
              = some (.Push .PUSH32, some (v, 32)) := by rw [matDec_imm] at hdec; exact hdec
          have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
            rw [chargeOf_imm] at hstk
            simp only [List.length_cons, List.length_nil] at hstk; omega
          obtain ⟨hg, _⟩ := next_push_of_cleanHalt fr .PUSH32 v 32 hcs (by decide) hdec'
            (by decide) (by decide) hszfr
          rw [chargeOf_imm]; simpa [List.sum_cons] using hg
      | slot slot => exact absurd heval (by simp [V2.evalExpr])
      | gas => exact absurd rfl hne
      | sload k => exact absurd rfl (hnsl k)
      | tmp t =>
          have hloc : st.locals t = some w := heval
          cases ht : defs t with
          | none =>
              exact absurd (by rw [← hdefs, ht] : defsOf prog t = none)
                (hscoped t (by rw [hloc]; simp)).2
          | some e' =>
              rcases Classical.em (∃ slot, e' = .slot slot) with ⟨slot, he'⟩ | hncr
              · -- == MLOAD-readback arm: `materialise = PUSH32 slot ; MLOAD`, charge `[Gverylow, Gverylow]` ==
                  have hdeft : defsOf prog t = some (.slot slot) := by rw [← hdefs, ht, he']
                  have hmd : MatDec fr.exec.executionEnv.code defs sloadChg (f + 1) fr.exec.pc
                      (.tmp t) := hdec
                  rw [matDec_tmp_some fr.exec.executionEnv.code defs sloadChg f fr.exec.pc t e' ht,
                      he', matDec_slot] at hmd
                  obtain ⟨hdpush, hdmload⟩ := hmd
                  have hchg : chargeOf defs sloadChg (f + 1) (.tmp t) = [Gverylow, Gverylow] := by
                    rw [chargeOf_tmp_some defs sloadChg f t e' ht, he']; cases f <;> rfl
                  have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
                    rw [hchg] at hstk
                    simp only [List.length_cons, List.length_nil] at hstk; omega
                  -- step 1: PUSH32 slot, clean-halt ⟹ `Gverylow ≤ fr.gas`, and drive to `frp`.
                  obtain ⟨hgPush, hpushNext⟩ := next_push_of_cleanHalt fr .PUSH32
                    (UInt256.ofNat slot) 32 hcs (by decide) hdpush (by decide) (by decide) hszfr
                  set frp := pushFrameW fr (UInt256.ofNat slot) 32 with hfrp
                  have hstepPush : StepsTo fr frp := stepsTo_of_next hpushNext
                  have hcsP : CleanHaltsNonException frp :=
                    cleanHaltsNonException_forward hcs (Runs.single hstepPush)
                  -- `frp`'s gas, pc, code, stack.
                  have hgv3 : (Gverylow : ℕ) = 3 := rfl
                  have hfrpgasN : frp.exec.gasAvailable.toNat = fr.exec.gasAvailable.toNat - Gverylow := by
                    show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
                    rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow (by rw [hgv3]; omega)
                      (by rw [hgv3]; omega)]
                  have hfrpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
                  have hfrppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
                    rw [hfrp, pushFrameW_pc, push32_pcΔ]
                  have hfrpstk : frp.exec.stack = (UInt256.ofNat slot) :: fr.exec.stack := rfl
                  have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; simp; omega
                  -- MLOAD decode at `frp`.
                  have hmloaddec : decode frp.exec.executionEnv.code frp.exec.pc
                      = some (.Smsf .MLOAD, .none) := by
                    rw [hfrpcode, hfrppc]
                    have : (emitImm (UInt256.ofNat slot)).length = 33 := emitImm_length _
                    rw [show fr.exec.pc + UInt32.ofNat 33
                          = fr.exec.pc + UInt32.ofNat (emitImm (UInt256.ofNat slot)).length from by
                          rw [this]]
                    exact hdmload
                  -- step 2: MLOAD clean-halt ⟹ expansion witness + both charges at `frp`.
                  obtain ⟨words', _hmem, hgasMem, hgasMl, _⟩ :=
                    next_mload_of_cleanHalt frp (UInt256.ofNat slot) fr.exec.stack hcsP
                      hmloaddec hfrpstk hfrpsz
                  -- `Gverylow ≤ frp.gas - memExp ≤ frp.gas`, and `frp.gas = fr.gas - Gverylow`,
                  -- so `Gverylow + Gverylow ≤ fr.gas` — the `[Gverylow, Gverylow]` sum bound.
                  have hsubLe : (frp.exec.gasAvailable
                      - UInt64.ofNat (memExpansionChargeOf frp.exec words')).toNat
                        ≤ frp.exec.gasAvailable.toNat :=
                    BytecodeLayer.Precompiles.toNat_sub_ofNat_le hgasMem
                  rw [hchg]
                  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
                  -- `Gverylow ≤ frp.gas - memExp`, weaken to `Gverylow ≤ frp.gas`, and `frp.gas =
                  -- fr.gas - Gverylow`, so `Gverylow + Gverylow ≤ fr.gas`.
                  have hgMlW : Gverylow ≤ frp.exec.gasAvailable.toNat := le_trans hgasMl hsubLe
                  rw [hfrpgasN] at hgMlW
                  omega
              · -- == pure recompute path (B3 `DefsSound`) — `e'` is NOT a call result ==
                  have htmd : MatDec fr.exec.executionEnv.code defs sloadChg f fr.exec.pc e' := by
                    rw [matDec_tmp_some fr.exec.executionEnv.code defs sloadChg f fr.exec.pc t e' ht]
                      at hdec
                    exact hdec
                  have hstk' : fr.exec.stack.size + (chargeOf defs sloadChg f e').length ≤ 1024 := by
                    rw [chargeOf_tmp_some defs sloadChg f t e' ht] at hstk; exact hstk
                  have hnr : ¬ NonRecomputable prog t := by
                    rcases (hscoped t (by rw [hloc]; simp)).1 with hnr | ⟨slot, hcrdef⟩
                    · exact hnr
                    · exfalso
                      apply hncr
                      have : some e' = some (Expr.slot slot) := by
                        rw [← ht, hdefs]; exact hcrdef
                      exact ⟨slot, Option.some.inj this⟩
                  have he'ng : e' ≠ .gas := by
                    rintro rfl
                    exact defsOf_ne_gas prog t (by rw [← hdefs]; exact ht)
                  have he'nsl : ∀ k, e' ≠ .sload k := by
                    intro k; rintro rfl
                    exact defsOf_ne_sload prog t k (by rw [← hdefs]; exact ht)
                  have hdfs : some w = V2.evalExpr st 0 e' :=
                    hsound t e' w (by rw [← hdefs, ht]) hnr hloc
                  have heval' : V2.evalExpr st obs e' = some w := by
                    rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
                  have hbound := ih e' w fr htmd hsound hscoped hstore he'ng he'nsl
                    hmemreal heval' hcs hstk'
                  rw [chargeOf_tmp_some defs sloadChg f t e' ht]; exact hbound
      | add a b =>
          -- operand values from `heval`.
          obtain ⟨va, hla, vb, hlb, hwadd⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.add va vb := by
            simp only [V2.evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwadd
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hcadd : chargeOf defs sloadChg (f + 1) (.add a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_add defs sloadChg f a b
          have hevb : V2.evalExpr st obs (.tmp b) = some vb := hlb
          have heva : V2.evalExpr st obs (.tmp a) = some va := hla
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.add a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.add a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hcadd]; simp only [List.length_append, List.length_singleton]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          -- (1) fold IH on b at `fr`: `sum_b ≤ fr.gas`.
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hlen_split] at hstk; omega
          have hsumb := ih (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
            hmemreal hevb hcs hstkb
          -- (2) produce `frb` via B1 with the just-derived `sum_b ≤ fr.gas`.
          obtain ⟨frb, hmrb⟩ := materialise_runs sloadChg f st obs (.tmp b) vb fr hdb hsound hscoped
            hstore (by nofun) (by nofun) hmemreal hevb hsumb hstkb
          -- forward clean-halt `fr → frb`.
          have hcsB : CleanHaltsNonException frb := cleanHaltsNonException_forward hcs hmrb.runs
          have hfrbgasN : frb.exec.gasAvailable.toNat
              = fr.exec.gasAvailable.toNat - (chargeOf defs sloadChg f (.tmp b)).sum := hmrb.gasToNat
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length := hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          -- (3) fold IH on a at `frb`: `sum_a ≤ frb.gas`.
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          have hsuma := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hcsB hstka
          -- (4) produce `fra` via B1.
          obtain ⟨fra, hmra⟩ := materialise_runs sloadChg f st obs (.tmp a) va frb hda' hsound
            hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hsuma hstka
          have hcsA : CleanHaltsNonException fra := cleanHaltsNonException_forward hcsB hmra.runs
          have hfragasN : fra.exec.gasAvailable.toNat
              = frb.exec.gasAvailable.toNat - (chargeOf defs sloadChg f (.tmp a)).sum := hmra.gasToNat
          -- (5) ADD at `fra`: `Gverylow ≤ fra.gas`.
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .ADD, .none) := by rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          obtain ⟨hgAdd, _⟩ := next_add_of_cleanHalt fra va vb fr.exec.stack hcsA hadec hastk haszle
          -- (6) reassemble: `sum_b + sum_a + Gverylow ≤ fr.gas`.
          rw [hsum_split]
          rw [hfragasN, hfrbgasN] at hgAdd
          omega
      | lt a b =>
          obtain ⟨va, hla, vb, hlb, hwlt⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.lt va vb := by
            simp only [V2.evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwlt
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hclt : chargeOf defs sloadChg (f + 1) (.lt a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_lt defs sloadChg f a b
          have hevb : V2.evalExpr st obs (.tmp b) = some vb := hlb
          have heva : V2.evalExpr st obs (.tmp a) = some va := hla
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hclt]; simp only [List.length_append, List.length_singleton]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hlen_split] at hstk; omega
          have hsumb := ih (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
            hmemreal hevb hcs hstkb
          obtain ⟨frb, hmrb⟩ := materialise_runs sloadChg f st obs (.tmp b) vb fr hdb hsound hscoped
            hstore (by nofun) (by nofun) hmemreal hevb hsumb hstkb
          have hcsB : CleanHaltsNonException frb := cleanHaltsNonException_forward hcs hmrb.runs
          have hfrbgasN : frb.exec.gasAvailable.toNat
              = fr.exec.gasAvailable.toNat - (chargeOf defs sloadChg f (.tmp b)).sum := hmrb.gasToNat
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length := hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          have hsuma := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hcsB hstka
          obtain ⟨fra, hmra⟩ := materialise_runs sloadChg f st obs (.tmp a) va frb hda' hsound
            hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hsuma hstka
          have hcsA : CleanHaltsNonException fra := cleanHaltsNonException_forward hcsB hmra.runs
          have hfragasN : fra.exec.gasAvailable.toNat
              = frb.exec.gasAvailable.toNat - (chargeOf defs sloadChg f (.tmp a)).sum := hmra.gasToNat
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .LT, .none) := by rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          obtain ⟨hgLt, _⟩ := next_lt_of_cleanHalt fra va vb fr.exec.stack hcsA hadec hastk haszle
          rw [hsum_split]
          rw [hfragasN, hfrbgasN] at hgLt
          omega

/-! ## The deliverable — `materialise_runs_of_cleanHalt`

The B1 twin: derive the gas bound via the fold, feed it to B1 `materialise_runs` for the run, and
re-export the bound as the second conjunct. -/

/-- **B1's gas-dropping twin.** Same conclusion as `materialise_runs` plus the derived gas envelope:
from `CleanHaltsNonException fr` (replacing B1's supplied `hgas`) and the B1 value-channel premises,
running `materialiseExpr defs fuel e` lands the whole `MatRuns` bundle **and** the charge sum is
shown to fit under the entry gas (`(chargeOf …).sum ≤ fr.exec.gasAvailable.toNat`). The §7 SSTORE
aggregate-charge / SLOAD key-prefix ties consume this derived bound instead of supplying it. -/
theorem materialise_runs_of_cleanHalt {prog : Program} (sloadChg : Tmp → ℕ)
    (fuel : Nat) (st : V2.IRState) (obs : Word) :
    ∀ (e : Expr) (w : Word) (fr : Frame),
      MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e →
      DefsSound prog st →
      (∀ t, st.locals t ≠ none →
        (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
        ∧ defsOf prog t ≠ none) →
      StorageAgree st fr →
      e ≠ .gas →
      (∀ k, e ≠ .sload k) →
      MemRealises prog st fr →
      V2.evalExpr st obs e = some w →
      CleanHaltsNonException fr →
      fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg fuel e).length ≤ 1024 →
      ∃ fr', MatRuns (defsOf prog) sloadChg fuel e w fr fr'
        ∧ (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat := by
  intro e w fr hdec hsound hscoped hstore hne hnsl hmemreal heval hcs hstk
  have hgas : (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat :=
    materialise_charge_le_of_cleanHalt sloadChg fuel st obs e w fr hdec hsound hscoped hstore
      hne hnsl hmemreal heval hcs hstk
  obtain ⟨fr', hmr⟩ := materialise_runs sloadChg fuel st obs e w fr hdec hsound hscoped hstore
    hne hnsl hmemreal heval hgas hstk
  exact ⟨fr', hmr, hgas⟩

end Lir

-- Build-enforced axiom-cleanliness guards for the FoldLemma deliverable.
