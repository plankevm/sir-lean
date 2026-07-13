# Handoff — exp005 Phase 3, Round 4 (the home stretch) — 2026-07-04

You are picking up the exp005 IR→EVM lowering-conformance proof. Phase 3 (proving the R0–R12
obligation skeleton in `LirLean/RealisabilitySpec.lean`) is **13 `sorry`s from done**. Your
job: launch and drive **Round 4** (the last major fan-out), merging between waves, until the
flagship `lowering_conforms` is proven (or down to a short named punch list).

## Where things are

- **Branch**: `exp005-honesty-cleanup`, checked out in worktree
  `/Users/eduardo/workspace/evm-semantics/.worktrees/ir-lowering`. Pushed to
  `origin/exp005-honesty-cleanup`. **Never push without the lead's say-so; never touch `main`.**
- **Build state**: from `.../ir-lowering/experiments/005_ir_lowering`:
  `lake build` (default `LirLean`) = 1172 jobs, GREEN and **sorry-free** (invariant: keep it so —
  you only ever edit the Nightly file). `lake build Nightly` = 1166 jobs green (the 13 sorries are
  the tracked Phase-3 debt). The `.lake` there is WARM.
- **The only file Phase-3 proofs edit** is `LirLean/RealisabilitySpec.lean` (the `Nightly`
  lean_lib). The default target `LirLean` must stay sorry-free.

## What is already CLOSED (real, axiom-clean `[propext, Classical.choice, Quot.sound]`)

R0b; R7a–e (the recorder-coupling spine; R7e is UNCONDITIONAL after the recorder course-correction);
R1 (gas recorder bridge — the "riskiest"); R2; R4; R5 (all four terminator arms); R8; R9; plus the
`exProg` non-vacuity witness pieces and many helpers (`driveLog_acc_hom`, `driveLog_frame_nonempty`,
`recorderCoupled_call_extract`, `recorderCoupled_stepsTo_other`, `runs_kind`,
`atReachableBoundary_entry`/`_of_runs`/`not_runs_atReachableBoundary`).

Course-correction already landed (Option B, sanctioned): the recorder's `recordCall` was ungated
(recorded nested callee calls); it is now gated on `rest.isEmpty` in the default-target
`Spec/Recorder.lean`, matching gas/sload. Rationale: `docs/recorder-model-note.md`.

## The 13 remaining `sorry`s (two buckets)

**Hard leaves (substantive proofs):**
- **R3** `callRealises_of_recorded` (~:1291) — Piece-A done (`recorderCoupled_call_extract`);
  needs Piece-B, an **arg-push machine-run producer** (materialise of call args `Runs` to the
  CALL-site frame). SECONDARY RISK: `resumeAfterCall` frame-pins may need a **default-target
  lemma** — if so, the track STOPS and reports a brief; surface it to the lead (do NOT touch the
  default target unilaterally — treat like the recorder Option A/B decision).
- **R6** `runs_atReachableBoundary` (~:2130) — statement already fixed (`hne`+`hsize`, don't
  change it); needs the **STEP/CALL boundary-walk edge lemmas** feeding `atReachableBoundary_of_runs`.
  Genuinely hard pc-reachability geometry (Round 3 landed nothing here).

**CFG simulation / adequacy (mostly mechanical; may cite the open leaves by statement):**
- R10a/R10b `stmtTies'_of_runWithLog` / `termTies'_of_runWithLog` (~:3253/:3269) — ties built from the run.
- R11 `lowering_conforms` (~:3290) — THE flagship; R11-all (`lowering_conforms_all`); gasfree co-flagship.
- R12a/R12b — the concrete non-vacuity witness (exProg satisfies + instantiates the flagship).
- RunFromLeft adequacy `runFrom_of_runFromLeft` / `runFromLeft_exists` (~:986/:994); `realisedGas_nil_of_noGasReads`.

Because it's a sorry-skeleton, **the assembly can be proven now citing the open leaves by
statement** — the flagship goes axiom-clean automatically once R3/R6/R10/RunFromLeft close.

## HOW TO RUN ROUND 4

The workflow is written and ready: `experiments/005_ir_lowering/scripts/phase3-round4.mjs`
(6 tracks: `asm-ties`, `asm-flagship`, `asm-adequacy`, `asm-witness`, `leaf-r3`, `leaf-r6`;
each `plan → implement → review`).

**Step 1 — set up worktrees + warm CoW caches** (from repo root
`/Users/eduardo/workspace/evm-semantics`):
```
for t in asm-ties asm-flagship asm-adequacy asm-witness leaf-r3 leaf-r6; do
  git worktree add .worktrees/p3-$t -b p3/$t exp005-honesty-cleanup
  cp -Rc .worktrees/ir-lowering/experiments/005_ir_lowering/.lake .worktrees/p3-$t/experiments/005_ir_lowering/.lake
done
```
`cp -Rc` is APFS copy-on-write — instant, ~no disk. This is the whole trick: agents build
INCREMENTALLY (~1–2 min), not cold (~1 h). Never `lake update`, never delete a `.lake`.

**Step 2 — launch**: `Workflow({ scriptPath: ".../experiments/005_ir_lowering/scripts/phase3-round4.mjs" })`.
It runs in the background; you get a completion notification.

**Step 3 — merge (the lead/main-thread step, between waves)**: merge each `p3/<track>` branch
into `exp005-honesty-cleanup` in the `ir-lowering` worktree. Expect conflicts in
`RealisabilitySpec.lean` (all tracks edit it) — they're almost always **"both added distinct
lemma blocks at the same spot"**: resolve by KEEPING BOTH (remove the `<<<`/`===`/`>>>` markers),
unless it's a genuine dedup (two tracks edited the same decl — keep the owner's). After merging:
`lake build` (default, must be green + sorry-free) AND `lake build Nightly` (green); then do an
INDEPENDENT `#print axioms` on any newly-closed load-bearing decl (append `#print axioms
Lir.<decl>` to the Nightly file, `lake build Nightly`, grep, then `git checkout` the file).
Commit the merge, then `git worktree remove --force` + `git branch -D` the retired tracks.

**Step 4 — iterate**: whatever leaf didn't close (likely R3 and/or R6) gets a focused follow-up
round; the assembly closes to axiom-clean once the leaves land. R12 closing = the machine-checked
non-vacuity milestone = Phase 3 essentially done.

## Standing rules / gotchas (from this session)

- Per-obligation **plan → implement → review**; the review's job is the vacuity/soundness bar
  (statement byte-unchanged, no new sorry/admit/native_decide, axiom-clean, no false-hypothesis
  reliance). Round 1–3 review CAUGHT two real statement bugs (R6 refutable, R7e recorder) — keep
  that adversarial standard.
- **Statement changes to an obligation are honesty-critical** — allowed only to fix a
  refutable/over-specified statement, never to dodge, and the reviewer must confirm the added
  hypothesis is legitimate well-formedness. (R6 `hne`/`hsize`, R5 branch-arm restriction were
  vetted this way; R5 introduced one tracked `hretEmit` static pc-bound for R10b to supply.)
- **Default-target changes need the lead's call** (like the recorder). Tracks are told to
  STOP-and-report a brief instead of touching `LirLean` unilaterally.
- Delegate the proof grind to the workflow; keep the main thread for merging + decisions.

## Key references
- `docs/achievements-since-main.md` — the since-main summary.
- `docs/target-architecture-2026-07-02.md` §2 (flagship shape), §5 (R0–R12 + landing order).
- `docs/final-audit-2026-07-03.md` — the CLEAN adversarial audit of the honesty cleanup.
- `docs/recorder-model-note.md` — the recordCall-gating course-correction.
- Memory: `[[exp005-target-architecture]]` (has the 2026-07-04 Phase-3-underway status).
