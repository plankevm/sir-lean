# exp005 Remediation Plan — 2026-07-02

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


> **SUPERSEDED (2026-07-03):** plan of record is `target-architecture-2026-07-02.md` + `execution-plan-2026-07-02.md`; the gas-law apparatus (Mono/Oracle/HonestGasTie) was deleted in Phase 2 (commit `7685131` — open decision #1 resolved as option (b), `HonestGasTie.lean` deleted with it).

*Synthesized from the audit (`audit-2026-07-02.md`), a 7-agent planning fleet, and three prior-art forks (Verity, verifereum, vyper-hol). Governs the fix for: the conditional headline, the dropped gas motivation, and the vestigial scaffolding. Read `gas-decision.md` first.*

Branch: `exp005-honesty-cleanup` (off `ir-convergence` @ a9335aa). Build: `cd experiments/005_ir_lowering && lake build` (target `LirLean`, ~1164 jobs). Baseline green/sorry-free/axiom-clean.

## Prior-art lessons (what to copy, what's novel)

- **The realisability closure is genuinely novel.** Verity's IR→native success-path headline *supplies* the run-match as a hypothesis (`EndToEnd.lean:128`), and `TRUST_ASSUMPTIONS.md:64` admits the general closure "has not been built yet." No fork has built what we're about to. Do not cite a fork as precedent that it exists.
- **The pattern to copy (verifereum `Collect`/`Enforce`, `vfmExecutionScript.sml:494`):** run once in *collect* mode to record oracle values (gas/sload/call), then state conformance *fed exactly those recorded values* → exact equality. This is precisely `runWithLog` → feed oracles → prove `=`.
- **Ties must be OUTPUTS, proved bottom-up (verifereum `decreases_gas`, `vfmDecreasesGasScript.sml`).** Their per-cursor property is a compositional monad predicate proved per-combinator with **zero hypotheses**, then assembled at the top — the exact inversion of our supplied `StmtTies`/`TermTies`. Mirror the bind-threading discipline; assemble the headline only at the very top (kills the `sim_call_stmt` 28-hyp mega-bundle smell).
- **State-relation shape (Verity `runtimeStateMatchesIR`; vyper-hol `*PreservationScript`):** encoding-fn + coupling invariant threaded per statement + boundary projection; the *theorem* keeps only observable projection. Our `Corr` already is this; keep it, make the ties derived.
- **Caution:** all forks target structured Yul/IR interpreters — **no pc/stack/jumpdest reasoning**. Our bytecode layer (decode anchors, offset tables, jumpdest validity) has no fork analogue; that machinery stays and is genuinely ours.

## Phases

### Phase 1 — Honesty cleanup: dead code (LOW risk, green-by-construction) — **executing now**
Partitioned by file-owner so no two edits collide; each target grep-confirmed to have no live proof-term references. Salvageable bricks are *retained with a label* (not deleted) because Phase 3 needs them.

| Owner | File(s) | Action |
|---|---|---|
| A | `MaterialiseGas.lean` | delete 7 dead gas-charge lemmas (`materialiseGasCharge_{tmp_some,gas,sload}`, `chargeOf_tmp_none_eq_imm`, `charge_sloadPost_gas`, `charge_runs_gas`, `subCharges_chargeOf_sload`) + their `#print` lines |
| B | `Match.lean` | delete 5 superseded per-construct sims (`sim_jump`, `sim_branch`, `sim_pop`, `applyCall_reflects_lowered`, `bindCallResult_reflects_lowered`). Keep `call_reflects_oracle` (audit §9). |
| C | `LowerConforms.lean` + `SimStmt.lean` | delete `simStmtStep_sstore`, `codeFrame_addr`, `paramsFor`(+`_entersAsCode`) + `#print`s; drop `sim_call_stmt`'s 3 unused binders `_hself/_hcallee/_hgasfwd` and fix the sole caller (LowerConforms.lean:423) |
| D | `LirLean.lean` + `lakefile.lean` | move `WorkedCall.lean`(1752), `Decode.lean`(199), `WorkedCallParity.lean`(211) → `_attic/` (already build-excluded; grep-confirm not imported); update NOTE comments |
| E | `TieDischarge.lean` + `MaterialiseRuns.lean` | delete the gas-advance island's *dead producers* (`driveCorrPlus_run_stmts_gasadvance`/`_drop`, `_gas_cursor_advance`, `_norecord_cursor_advance`, `_gasval_of_witness`, `{gas,sload}LogAligned_matRuns`, `selfPresent_matRuns`); delete the `:= h`/`P→P` identity bricks (`sstorePresence_of_self`, `selfPresent_{addFrame,ltFrame,sloadFrame,gasFrame,pushFrameW}`, `sloadLogAligned_step_norecord`); delete dead wrappers (`driveCorrPlus_step_stop`/`_ret`/`_run_stmts`) + `#print`s; **retain-with-label** the salvageable bricks (`aligned_read_eq_obs`, `gasRealises_obs_of_witness`, `sloadRealises_charge_of_witness`, `memRealises_setLocal_nonspilled`, `driveCorrPlus_assign_remat_memRealises`, `driveCorrPlus_sload_value(_world)`) and the relocatable RBMap facts — mark `-- RETAINED for Phase 3 realisability closure (audit §3)` / `-- RELOCATE to exp003 (audit §7)`; fix the overclaiming docstrings; sweep `MaterialiseRuns.lean` dangling docstrings |

Then one `lake build` → commit if green.

### Phase 2 — Gas-law removal + alignment-channel + hprec (MED risk, coordinated)
Per `gas-decision.md`. Grep-confirm no on-cone use, then: delete `Mono.lean` + `Oracle.lean` (whole files) and their imports; narrow `Law.lean` to determinism-only (keep the four `.det`); delete RunLog's gas-monotonicity section (`geToNat`/`bound_mono`/`driveLog_gas_inv`/`realisedGas_monotone` + `#print`) and its now-dead `import`s; delete the `GasLogAligned`/`SloadLogAligned` island in TieDischarge; **remove the vacuous `DriveCorrPlus` alignment fields** (`gasAcc/gasFrs/sloadAcc/sloadFrs` + `gasAligned/sloadAligned`) and thread the params out of entry/edges/headline; **add the `hprec` headline variant** (`lower_conforms_cyclic_assembled_hprec`, deriving `hcall := callPreservesSelf_modGuards hprec`). Contested: `HonestGasTie.lean` — the SLOAD retired-universal regression witnesses may be worth keeping in a tiny standalone file; **lead decision** (see below). Build + axiom-check between the file-deletes and the structural DriveCorrPlus change.

### Phase 3 — Realisability closure (the real milestone; HIGH; multi-session)
Turn the conditional headline into a real theorem, using the `Collect`/`Enforce` pattern.
1. Reshape the `StmtTies` gas/sload **value** conjuncts so the consumed value is pinned to the positionally-consumed trace head, not a free `∀ ob` (the critical design fix; determines how invasively `simStmtStep_block` changes — see open Q).
2. `stmtties_gas_of_runWithLog` — the new joint induction over `driveLog`: recorded gas prefix = in-order `gasReadOf` of post-GAS frames at `Corr` cursors ⇒ consumed `ob = ofUInt64(fr.gas − Gbase)`. (Salvaged bricks from Phase 1 feed this.)
3. `sstore_realises_of_corr` (world channel, from `Corr.storageAgree`); `callrealises_of_runWithLog` (from recorded `CallRecord` via `realisedCall_eq_evmV2`, RunLog.lean:280).
4. Assemble `stmtties_of_runWithLog` / `termties_of_runWithLog`; discharge structural fields from `Acyclic`.
5. Top-level **unconditional** `lower_conforms_cyclic` from `runWithLog p (seedFuel p.gas) = some log` + `hprec` + `hcc` + `hrb` + entry facts.
6. At least one **concrete `lower prog` instantiated end-to-end** (the non-vacuity witness the audit §3 / Verity witness-files both lack). verifereum's `deploy_result_correct` (compute-evaluated concrete run) is the template.
7. Also state the gas-introspection-free `lower_conforms_cyclic_gasfree` (secondary flagship).

### Phase 4 — Relocate + unify engine layer to exp003 (HIGH; gated on Phase 1+2)
Unify first: prove `stepFrame_next_execEnvAddr` once, derive the ~920-line `SelfAt`/`_next_self` walk as the `a:=self` corollary of `_next_accMono` (saves ~1000 lines). Then move the pure-`Evm` engine layer (dispatch walks, `drive_accounts_find_mono`, begin/end/checkpoint/resume facts, RBMap primitives — per-decl, not a contiguous cut) into a new `EVM/BytecodeLayer/Hoare/AccountsMonotone.lean`; re-wire exp005 imports. Build both experiments green.

## Open decisions for the lead
1. **`HonestGasTie.lean` — now BLOCKING Phase 2.** Keep the retired-universal regression witnesses (tiny standalone file) or delete with the gas apparatus? **Newly discovered entanglement (2026-07-02):** `Oracle.lean` defines `Lir.GasRealises`, which `HonestGasTie.lean` *uses* in its witnesses; and `Oracle` ← `RunLog`, `Mono` ← `Oracle`/root, `HonestGasTie` ← root. So deleting `Mono`/`Oracle` (the gas-law files) forces reworking or deleting `HonestGasTie` in the same change — i.e. Phase 2's "uncontested" gas-law deletion is *not* uncontested; it requires this decision first. Options: (a) keep a minimal `HonestGasTie` by inlining the one `Oracle.GasRealises` def it needs, then delete `Oracle`/`Mono`; (b) delete `HonestGasTie` too (the retired-universal guard is arguably obsolete once the whole gas-law apparatus is gone); (c) defer all of Phase 2's gas-file deletion until the realisability closure (Phase 3) settles what gas machinery survives. **Recommend (b)** — once gas is a log-fed exact-equality oracle, a regression witness guarding a retired *monotonicity* universal no longer guards anything live.
2. **Secondary theorem:** is `lower_conforms_cyclic_gasfree` a documented co-flagship, or just an optional side result?
3. **Phase-3 tie-reshape strategy** (index by consumed-trace prefix vs existential-supplied-by-recorder vs per-cursor value function) — affects blast radius of `simStmtStep_block`.
4. **`SelfPresent`:** wire `driveCorrPlus_step_stop/_ret` in so it's load-bearing, or drop the field + `hwf` premise? (Phase 2 currently drops; Phase 3 may re-add it as a genuine world premise.)

## Execution log
- 2026-07-02: audit + map committed (ef9dbab). Plan + gas-decision written (3b0af5f).
- 2026-07-02: **Phase 1 DONE + green + axiom-clean** (3aaed43). 1164 jobs; headline `lower_conforms_cyclic_assembled` on `[propext, Classical.choice, Quot.sound]`; zero sorry/native_decide/errors/warnings. Removed ~742 lines net of dead scaffolding across 8 files; `TieDischarge.lean` 5027→4507; 3 leaf examples archived to `_attic/`; salvage bricks retained-with-label; overclaiming docstrings fixed. Living docs revitalized. `main` working tree left clean (repo-root doc edits relocated onto this branch).
- 2026-07-02: **Phase 2 NOT started** — grep found the `Oracle`↔`HonestGasTie` entanglement (open decision #1); the gas-law deletion is coupled to the contested `HonestGasTie` call, so it awaits the lead. Phases 2–4 staged.
