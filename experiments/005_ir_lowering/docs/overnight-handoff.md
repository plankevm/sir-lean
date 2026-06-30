# exp005 overnight handoff (2026-06-29)

Branch `ir-convergence`; worktree `.../evm-semantics-wt/ir-lowering`. Single file
touched all night: `LirLean/V2/TieDischarge.lean`. `main` untouched, nothing pushed.

**Build state (re-verified just now): `Build completed successfully (1158 jobs)`.**
All touched `#print axioms` lines = `[propext, Classical.choice, Quot.sound]` (the two pure
red-black-tree lemmas `forM_from_nil`/`all2_nil_false` are `[propext]` only — a subset).
No `sorry`/`axiom`/`native_decide` in proof bodies (sole grep hit is the line-70 clean-claim
docstring). Each task was independently re-built + re-axiom-checked by a reviewer before accept.

---

## (a) What LANDED tonight (commit shas + lemmas, all green + axiom-clean)

| sha | task | lemmas |
|-----|------|--------|
| `6af3d73` | C1 | `gasLogAligned_matRuns`, `sloadLogAligned_matRuns` (alignment+reachability transport across a MatRuns sub-run) |
| `9956091` | HYP | `stepPreservesSelf` (**discharges** the `StepPreservesSelf` edge outright — fully general, no `lower prog` hyp), + its bottom-up bricks (`stepFrame_next_self`, `dispatch_next_self`, `systemOp_next_self`, per-op combinator bricks, `sstore/tstore_self_present`, `callArm/createArm_next_self`, `resumeAfterCall/Create_selfAt`, `charge_accounts_env`, `selfAt_replaceStackAndIncrPC`), `resumeAfterCall_self_of_accounts` + `endCall_revert/exception_accounts` (revert/exception halves of CallPreservesSelf), `selfPresent_runs_of_call` |
| `ca06b62` | C3 | `memRealises_setLocal_nonspilled`, `driveCorrPlus_assign_remat_memRealises` (S7), `driveCorrPlus_sload_value` + `_world` (S2), `driveCorrPlus_run_stmts` (**L2.0** — the no-P3 value channels) |
| `516f166` | WRAP | `forM_from_nil`, `all2_nil_false`, `find?_some_ne_empty`, `accounts_ne_empty_of_selfPresent`, `driveCorrPlus_step_stop` (T1), `driveCorrPlus_step_ret` (T2) — the two halt-terminator wrappers over L2.0 |

Headline of the night: `StepPreservesSelf` went from supplied-edge to **proven theorem**, and the
`accounts ≠ ∅` terminator fact is now **derived** from `SelfPresent` (via the new pure
`find?_some_ne_empty`), not supplied.

## (b) Vacuity / circularity findings surfaced

- **All accepts were genuine** — no vacuous/circular/overclaimed lemma landed.
- `selfPresent_runs` is a clean `Runs`-induction; it does **not** re-supply its own conclusion.
- C1's `*_matRuns` return the input alignment **verbatim** — honest preservation-only repackaging,
  explicitly **not** a no-record-inside / byte-freeness claim (deferred). Flagged in docstrings.
- C3's S7/S2 conjuncts are **logical free-riders**: their proofs use only the caller-supplied
  per-cursor `Corr`/`EvalStmt`, never the run (`hsim`/`hrun`). Sound and non-vacuous, but bundling
  them into `driveCorrPlus_run_stmts` buys nothing over the standalone cursor lemmas. One docstring
  word ("reached") slightly overstates run-coupling — **non-blocking cleanup**, not unsound.
- **R4 avoided (the key trap):** the terminator ties are emitted in **Route-4b INDEXED** form (bound
  to the L2.0-reached `frT`/`frv`), NOT the universal `∀ st' frT, Corr → … ∧ accounts≠∅` of
  `TermTies` — that universal is *unprovable* here (`SelfPresent` holds only at the reached frame;
  "Corr at terminator ⇒ SelfPresent" is false). Restating it would be vacuous-or-false.
- **S3 (gas positional value) correctly NOT smuggled:** adversarial reading of `EvalStmt.assignGas`
  vs `aligned_read_eq_obs` showed it is a **trace↔recorder bridge**, not a value-only have-block.
  Kept supplied rather than faked.

## (c) Hypotheses DISCHARGED vs still-SUPPLIED

**DISCHARGED tonight (now theorems / derived):**
- `StepPreservesSelf` — proved fully general (`stepPreservesSelf`). No longer an open edge.
- Revert/exception shapes of `CallPreservesSelf` — `resumeAfterCall_self_of_accounts` + the
  `endCall_*_accounts` rfl facts close 2 of the 3 `CallResult` shapes.
- `accounts ≠ ∅` at a terminator/return frame — **derived** from `SelfPresent` (not supplied).
- C3 value channels **S7** (assign-remat MemRealises) and **S2** (sload IR-value).

**Still SUPPLIED — each satisfiable, not vacuous (why):**
- `CallPreservesSelf` (.success shape) — residual `drive_accounts_find_mono` (account-presence
  monotone across a child `drive` run). Satisfiable: **no** bytecode-layer `drive` path
  `RBMap.erase`s a map entry (only erase is the outer `Semantics.lean` dead-account sweep, outside
  `drive`; SELFDESTRUCT halts via `haltOp` without erasing). It's a whole-child-run induction of
  P5-spine magnitude — out of scope, not faked.
- `SimStmtStep prog … L b` (`hsim`) — what `simStmtStep_block` builds from `WellFormedLowered` + §7
  ties; folds the structural channels **S1/S5/S6**. Inhabited by any concrete lowered sstore/call
  block. Consumed in L2.0 **only** for the Runs+Corr+stack triple (so not circular w.r.t. S7/S2).
- `NotCreate` / `CallsCode` (per reachable frame, in `Modellable.lean`) — `NotCreate` structurally
  true for `lower prog` but pinning it at an arbitrary reachable pc needs the `ReachesBoundary`
  walk (separate track); `CallsCode` is a genuine runtime residual (callee addr off the stack;
  precompile targets 1..10 violate it — vacuous for call-free IR, satisfied for ordinary targets).
- **S3** gas positional value + **S4** gas runtime envelopes (`Gbase ≤ gas`, `3 ≤ gasFrame gas`,
  memExpansion) — S3 = the trace↔recorder bridge above; S4 needs the **clean-halt forward** split
  (`cleanHalts_forward` → `Runs.linear_to_halt`), not pure `gasAvailable_le` descent. Both
  satisfiable on any successfully-halting lowered run.
- WRAP `hkind` (terminator frame is a `.call` codeFrame), `hv` (`.ret t` binds `t`), `hgas`
  (descending-gas envelope), `hretsite` (concrete PUSH32;PUSH32;RETURN epilogue decode + gas
  margins) — all indexed to the reached frame, inhabited at a real run, mirror
  `sim_term_halt_stop/_ret`'s supplied bundles.

## (d) Remaining obstacles

1. **`drive_accounts_find_mono`** — the one hard residual gating the .success CALL self-edge. A
   whole-child-run induction threading account-map non-erasure through every `stepFrame` /
   nested `resumeAfterCall`. Until it lands, the CALL tie stays the supplied seam (this is the
   designed ext-call-oracle seam, R1 — acceptable, but it *is* the gap).
2. **Trace↔recorder bridge invariant** — to discharge S3, `DriveCorr(Plus)` must additionally carry
   `IR-trace-consumed-prefix = gasAcc` AND the gas-channel structural walk must extend `gasFrs` by
   `gasLogAligned_step_gas` at each gas cursor (needs the GAS-op decode/step facts). Same machinery
   needed for the deferred alignment EXTENSION (tonight's alignment is carried **verbatim**, never
   advanced).
3. **Clean-halt forward split to a cursor** (`cleanHalts_forward` threaded to an arbitrary reachable
   gas/MSTORE cursor) — gates S4 envelopes.
4. **Entry-self equality** `frT.address = fr0.address` across the drive `Runs` — deferred to F2/
   Tier-3 address-invariance; the wrappers keep `self := frT.address` (self-conjunct rfl), so they
   do **not** yet claim entry-self. A consumer must not assume it.

## (e) Roadmap for the unreached checkpoints

- **C3 structural/call channels S1/S5/S6** — the serialized post-P3 spine: forward-from-real-run
  production of the sload-stash (S1), sstore (S5), and call (S6) per-statement simulations. Blocked
  on P3 .success (obstacle 1) for the call arm; S1/S5 need the per-op decode/step walk. These are
  currently folded inside the supplied `hsim` — the job is to *produce* `hsim` from the run.
- **Edge wrappers L2.3/L2.4** (non-halt terminators: branch / jump) — the C5 successor-carrying
  analogues of tonight's L2.1/L2.2 halt wrappers. Strictly harder: they must carry a *successor*
  `DriveCorrPlus` invariant to the next block, not just emit a halt bundle. Need the
  `ReachesBoundary`/`JumpValid` boundary walk (also what pins `NotCreate`).
- **C6 Tier-3 recursion** — assemble the per-block wrappers (L2.1–L2.4) into a whole-CFG drive
  induction (`sim_cfg_along_drive`), threading `DriveCorrPlus` block-to-block, advancing the
  alignment (the deferred EXTENSION) and the entry-self invariance (obstacle 4) along the way.
- **C8 Route 4b** — thread the Route-4b indexed tie families (S7/S2 today, plus S1/S3/S4/S5/S6 once
  produced) up through `sim_cfg_along_drive` into the conformance statement, replacing the universal
  `StmtTies`/`TermTies` predicates with their run-indexed witnesses.
- **C9 P6 tie-free headlines** — the final gas / sload / sstore / control-flow headlines stated
  *tie-free* (IR gas-/call-/sload-agnostic via the oracles), with only the documented satisfiable
  seams (CALL .success, precompile `CallsCode`) remaining supplied. This is the deliverable; today's
  work is the preservation spine feeding it.

**Net honest status:** the *preservation substrate* (self-presence engine-wide, alignment transport,
the no-P3 value channels, halt wrappers) is closed and clean. The *structural production* spine
(S1/S5/S6, gas-channel walk, S3/S4, edge wrappers, CFG recursion) and the *.success CALL seam* are
the genuine remaining work — none of it faked or vacuously dressed tonight.
