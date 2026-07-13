# Final adversarial audit — exp005 "honesty cleanup" (branch `exp005-honesty-cleanup`)

Date: 2026-07-03. Diff range `6980831..HEAD`. Method: static reading only (no `lake build`;
build-green 1172/1165 and axiom-cleanliness are established facts, re-verified structurally
via `LirLean/Audit.lean`'s `#guard_msgs` guards). Fleet output (25 skeptic verdicts +
completeness critic) synthesized and spot-re-checked against the sources.

**VERDICT: CLEAN.** No reintroduced vacuity, no silent weakening, disclaimers accurate. The
cleanup did what it claimed. Four non-blocking hygiene follow-ups are listed at the end; none
is a correctness defect and none gates Phase 3.

---

## Q1 — Did the cleanup actually reduce the supplied-hypothesis surface? YES.

Two headlines now coexist, and the reduction is real *in the statements*:

* **Prior headline, retained + quarantined.** `Lir.lower_conforms_cyclic_assembled`
  (`LirLean/Drive/Headline.lean:783`) is frozen verbatim by `Audit.lean:62-104`'s
  `#check` guard. Its supplied surface is large and includes the two diseased ties
  `StmtTies`/`TermTies` (`Audit.lean:76-78`), plus `blockPresent`/`jumpPresent`/
  `branchPresent`/`stkBranch`/`CallPreservesSelf`/`RunDefinable`/`DriveCorr`. This headline
  is **still VACUOUS as stated** (its `StmtTies`/`TermTies` antecedents remain unsatisfiable
  for essentially every nonempty program). The cleanup did *not* fix it — it **relabeled it
  honestly** (`Spec/Conformance.lean:19-32, 40-45, 97-102`) and marked it superseded.

* **Plan-of-record flagship, reshaped.** `Lir.lowering_conforms` (R11,
  `RealisabilitySpec.lean:1360-1376`) supplies only: two definitional pins (`hcode`/`hmod`),
  three decidable entry facts (`hself`/`hgas`), one static checkable bundle (`hwl :
  WellLowered`), three decidable scope premises (`hsingle`/`hone`/`hclean`), one runtime
  premise (`hrun`), one two-field seam structure (`hseams`), one named scope seam (`hnzw`).
  **The ties are gone from the supplied surface** — they are now *derived from the run* by
  `stmtTies'_of_runWithLog` (R10a, `:1323-1335`) and `termTies'_of_runWithLog` (R10b,
  `:1339-1343`). `DriveCorr`/`CallPreservesSelf`/`hpresent`/`obs`/`{T}` are all eliminated
  (derived, definitional, or dead-phantom), per the ledger at `:1350-1359`.

Net: the diseased supplied ties are demoted from *hypotheses of the headline* to *conclusions
of sorry'd obligations*. That is a genuine surface reduction — **conditional on the R1–R12
sorries landing** (`RealisabilitySpec.lean` is the Nightly-only sorry lib; `lakefile.lean:31-32`,
default `LirLean` stays sorry-free and does not import it). The disclaimers state exactly this.

## Q2 — Anything NEW refutable or vacuous? NONE (statement-level). All new debt is "sorry body, statement fine."

The fleet adversarially attacked all 25 new Props/defs/ties in `RealisabilitySpec.lean` for the
free-`∀` disease (a `∀`-bound variable pinned to a run-specific value with no linking
antecedent). Every one is **satisfiable / non-vacuous**; the single "not-a-prop" (`invalStep`,
`:329`) is correctly a total dataflow transfer function, not a claim. I independently re-checked
the load-bearing reshapes and confirm no disease was reintroduced:

* **`StmtTies'`** (`:697-790`): every formerly-free *value* variable is now antecedent-pinned —
  `w` by `evalExpr st0 0 e = some w` (`:709`); `kv` by `st0.locals k = some kv` (`:726`, the
  lesson-5 fix); the gas word by the R1 conjunct `gS.head? = some …` where `gS` is pinned by
  `RecorderCoupled log fr0 gS sS cS` (`:748, 753`); `vw ≠ 0` only under the threaded
  `NonzeroSstores fr0` antecedent (`:770, 775`, lesson-3 fix). The unsatisfiable
  `∃ acc, SstoreRealises …` conjunct is **dropped** (`:762-763`); its content returns
  point-wise at the concrete frame in R4 (`sstoreRealises_at_frame`, `:1124-1133`).
* **Call arm / `CallRealisesS`** (`:399-457`): the oracle is pinned by
  `o = evmV2CallOracle result pd fr0.exec.executionEnv.address` (`:408`) and instantiated at the
  call site to `realisedCall log self` with the address antecedent `fr0.…address = self`
  (`:789`), so the equation is reverse-solvable, not adversarially refutable. This is the exact
  cure of the prior headline's free adversarial `o`.
* **`TermTies'`** (`:798-907`): address/kind/self-presence demands are now *antecedents*
  (`:806-808`), all gas guards sit under `CleanHaltsNonException` (`:805, 814, 847, 871`), the
  ret epilogue's inner `∀ frv` is `Runs`+pc-pinned (`:822, 827`), condition `cw` is pinned by
  `st'.locals cond = some cw` (`:872`). No free value-`∀` survives.
* **`StepScopedS`/`StackRoomOK`** (`:365, 186-204`): state-free static residues. `StackRoomOK`'s
  flagged free `∀ sloadChg` is benign — `chargeOf`'s `.length` is provably invariant under
  `sloadChg` (each `.sload` arm appends exactly one element `[sloadChg k]` regardless of value;
  `MaterialiseGas.lean:73-87`), so no adversarial resolver flips the bound.
* **`RunDefinableG`** (`:233-251`) replaces the in-tree `RunDefinable`, whose `.call` arm was
  literally `False` and whose assign arm demanded `e ≠ .gas` — **unsatisfiable for every
  gas/call program** (lesson 4). `WellLowered.defs` uses `RunDefinableG` (`:469`); the
  definability is threaded along `RunStmts`, so the entry-state `∀` is a state-uniform
  over-approximation (conclusion is about the derivation-pinned `st'`, not the free `st`).
* **`DefsConsistent`** (`:270-278`) is newly added to `WellLowered` (`:474`), closing the
  lesson-6 first-find/spill-stash shadowing hole that `RunDefinableG` alone leaves open (its
  gas arm is unconditionally true).
* The **one machine-checked refutation**, `not_defsSound_stale` (`:1295-1301`), is correctly
  *proved* (non-sorry) — it is the point (the un-scoped `DefsSound` is false at the loop-exit
  mid-block state, motivating R0b). `singleCall_exProg` (`:1263`) and `defsSoundS_empty_iff`
  (`:351`) are the other two non-sorry anchors; all three are genuine.

Anti-vacuity machinery is present and honest: `exProg` (`:1242-1259`) exercises gas-read +
spilled-sload + nonzero-sstore + single-call + genuine cycle at once; R9 states a *sound AND
accepts-the-witness* checker existentially (`:1309-1311`, the second conjunct is the anti-vacuity
guard); R12a/R12b (`:1438, 1453`) force the flagship's antecedent true somewhere; `RunFromAll`
(`:968`) closes the drop-the-suffix channel that bare `RunFrom` leaves open (§4).

## Q3 — Are the wave-2/3 moves faithful? YES (no added hypothesis, no weakened conclusion, cone unchanged).

* **Gas-law removal** (`7685131`): `Mono.lean`, `Oracle.lean`, `HonestGasTie.lean`
  deleted; `Law` narrowed to determinism. The retired object was the `∀`-over-frames
  *universal* gas tie; the point-wise `Lir.GasRealises obs fr` at a single pinned frame survives
  as a live, satisfiable def (`MaterialiseRuns.lean:553`, used at `Drive/SelfPresent.lean:216`) —
  consistent with header lesson 1 (`RealisabilitySpec.lean:15`).
* **Engine/Spec/Drive reorg** (`8417d67`..`5f83590`, `4610980`..`1384b16`): per commit messages
  these are whole-file/theorem-extraction *moves*; the flagship names and shapes are unchanged
  (`Headline.lean:666, 783`), and the `Audit.lean:62-104` `#check` freeze pins the assembled
  headline's full signature byte-for-byte — any cone drift is a hard build error.
* **`Spec` forwarders**: `lower_conforms_cyclic_of_obligations` (`Conformance.lean:110-129`) is a
  pure application — it destructures a `RealisabilityObligations` bundle and applies the frozen
  assembled lemma to exactly its fields (`:126-129`); **no new hypothesis, identical conclusion**.
  The two `alias`es (`:95, 102`) are defeq re-exports. `Audit.lean:113-127` axiom-guards all four
  `Spec` surface decls.

## Disclaimer accuracy — ACCURATE.

`Spec/Conformance.lean:13-32` and `RealisabilitySpec.lean:3-99` are candid: "register of debt,
NOT a claim of truth"; the prior ties "UNSATISFIABLE for essentially every nonempty program …
VACUOUS as stated"; "EVERY `sorry` IN THIS FILE IS TRACKED DEBT"; per-decl SUPPLIED-vs-DERIVED
status. No overclaiming found. The scope seams (`RunLog.clean` zero-gas-revert cut `:86-90`;
`NonzeroSstores` `:91-95`) are explicitly disclosed as sound narrowings (hypothesis-false ⇒
theorem-silent, never unsound).

## Audit-net coverage — SOUND for the default tree; Nightly deliberately uncovered.

`Audit.lean` pins 10 load-bearing default-tree lemmas + the flagship `#check` freeze + 4 `Spec`
surface decls, imported LAST in the root (`LirLean.lean:53-54`). The Nightly sorry-lib is
deliberately *not* guarded (`RealisabilitySpec.lean:1462-1467`: guarding `sorryAx` would only
pin the debt's existence; guards migrate over as sorries land). Wave 4 deleted the 226 scattered
`#print axioms` (`53c2063`). Sorry-count 25 in the Nightly lib matches the tracked figure;
default tree is sorry-free (all "No sorry" hits are docstrings).

---

## Confirmed defects: NONE.

No statement in the wave-2/3/4 changes is vacuous, refutable-on-its-face, or a silent
weakening. All new incompleteness is honest `sorry` bodies over satisfiable, non-vacuous
statements.

## Prioritized non-blocking follow-ups (hygiene, not defects)

1. **Stale docstring references to deleted modules** (violates the project's own
   sweep-on-delete rule). ~10 files carry comment references to `HonestGasTie.lean`,
   `Oracle.lean`, `Mono.lean`, `RunLog.lean` after those files were deleted —
   e.g. `MaterialiseRuns.lean:53,507,530,550,552`, `Drive/SelfPresent.lean:96,101` (`Oracle.
   GasRealises` / `Oracle.lean` path now `MaterialiseRuns.lean`). Sweep the paths.
2. **`BytecodeLayer/Hoare/MemAlgebra.lean:948-976` retains 8 `#guard_msgs in #print axioms`** outside the
   "authoritative net." Harmless (still fail-hard on drift) but inconsistent with the
   "Audit.lean is the net" narrative — either fold into `Audit.lean` or note the exception in
   `docs/exec/audit-net.md`.
3. **The prior VACUOUS headline is retained, not deleted.** `lower_conforms_cyclic_assembled`
   stays (frozen for the `#check` signature guard) and is honestly labeled VACUOUS, but a
   future reader could still cite it as if load-bearing. Consider a follow-up that either drops
   it once the audit net can freeze the new flagship, or renames it with a `_vacuous`/`_legacy`
   marker.
4. **Main flagship keeps the suffix-drop channel open.** `lowering_conforms` uses `RunFrom`
   (drops leftover trace); only `lowering_conforms_all` (`:1381`) pins leftover `[]` via
   `RunFromAll`. Acknowledged in §4 — ensure the Phase-3 landing order proves the `_all`
   strengthening (and its two `RunFromLeft` adequacy sorries `:977,983`), not only `RunFrom`.

## Bottom line

The honesty cleanup is faithful: it demoted the diseased supplied ties to run-derived
obligations, replaced the two unsatisfiable in-tree bundles (`RunDefinable`, `SstoreRealises`)
with satisfiable reshapes, added the missing static consistency guard (`DefsConsistent`), moved
all staleness accounting into an explicit invalidation set, and disclaimed every remaining seam
and every `sorry` accurately. No new vacuity, no silent weakening, cone frozen. CLEAN to enter
Phase 3, modulo the four hygiene items above.

## Post-audit actions (2026-07-03)

The four non-blocking follow-ups above were triaged the same day; three are actioned, one is Phase-3
work:

- **#1 (stale docstring references to deleted modules) — DONE.** The dangling comment references to
  `{HonestGasTie,Oracle,Mono,RunLog}.lean` were swept from the in-code docstrings (commit
  `76278be`).
- **#3 (the prior VACUOUS headline retained) — DONE, by DELETION.** Rather than rename/quarantine it,
  the vacuous cyclic conformance headline `lower_conforms_cyclic_assembled` **and its whole apparatus**
  were **DELETED** (commits "delete vacuous conformance surface 1/4..4/4", `ba42b63..7b763dc`): also
  `_tiefree`, `lower_conforms_wf`, the `lower_conforms_acyclic*` family, `StmtTies`/`TermTies`, the
  Plus assembly, and the `Spec` `RealisabilityObligations`/`_of_obligations`/re-export layer
  (`Spec/Conformance.lean` is now a disclaimer stub). `LirLean/RealisabilitySpec.lean` (Nightly,
  R0–R12) is now the sole conformance surface. `Audit.lean` was repointed: the deleted-decl guards and
  the flagship `#check` signature-freeze were removed; the net now pins 8 salvage lemmas +
  `Lir.Spec.callPreservesSelf_of_precompiles`. Retained Phase-3 salvage: `Lir.DriveCorrPlus` + the
  value/gas channels in `Drive/Headline.lean`, the acyclicity ⇒ `WellFormedLowered` core in
  `Acyclic.lean`, and `Lir.CallRealises` / `Lir.WellFormedLowered` / `Lir.toList_of_blockAt`.
- **#2 (MemAlgebra 8-axiom guards outside `Audit.lean`) — DONE, by DOCUMENTING.** The intentional-
  local-guard exception is now recorded in `docs/exec/audit-net.md` (they still fail-hard on drift;
  noted so "Audit.lean is the net" is not read as exclusive).
- **#4 (RunFromAll suffix-drop strengthening) — OPEN, Phase-3 work.** Unchanged: the Phase-3 landing
  order must prove the `lowering_conforms_all` strengthening (and its two `RunFromLeft` adequacy
  sorries), not only the `RunFrom` flagship.

### Recorder course-correction (2026-07-03, branch `p3/recorder`, commit `82e7453`)

A Phase-3 correctness fix landed after the audit above, on the recorder rather than the audited
`exp005-honesty-cleanup` surface. **Finding:** the returning-CALL record (`recordCall` in
`Spec/Recorder.lean`, invoked in `driveLog`'s `.call` delivery branch) was **UNGATED** — it
recorded a *descended callee's* inner returning CALLs too, contradicting both its own docstrings
("the top-level program's own returning external CALLs") and the sibling gas/sload gates, which
already fire only on the top-level frame (`stack.isEmpty`).

**Fix (Option B).** The returning-CALL record is now gated on the resumed pending stack being empty
(`rest.isEmpty`), so it fires ONLY for the top-level program's own returning CALL — mirroring the
gas/sload `stack.isEmpty` gates. A descended callee's inner CALLs resume on a nonempty `rest` and are
now black-boxed structurally, exactly as `Runs.call` black-boxes them. `recordCall` itself is
unchanged; only its two call sites are gated. (`Spec/Recorder.lean`, `RealisabilitySpec.lean`;
default `lake build` stays sorry-free, `Nightly` green.)

**Consequence.** R7e (`recorderCoupled_call`) now holds **UNCONDITIONALLY** — the single-call
`hone` hypothesis was dropped, statement unchanged — via the new recorder-composition lemma
`driveLog_frame_nonempty` (a nonempty bottom stack fails every gate, so the inline child records
nothing), fuel-reconciled with the black-box child run and peeled by `driveLog_acc_hom`.
Axiom-clean. `realisedCall` is now faithful even when the top-level call's callee *itself* calls,
which unblocks the R3' multi-call generalization. The orthogonal `hone : log.calls.length ≤ 1`
premises on R3/R10a/the flagships (guarding *multiple top-level* calls, where `callOracleOf` reads
only the head record) are untouched. Rationale for choosing the gate over the Nightly-only stopgap
is recorded in `docs/recorder-model-note.md`.
