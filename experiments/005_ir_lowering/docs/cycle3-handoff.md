# exp005 cycle-3 handoff (2026-06-29)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Branch: `ir-convergence`. Baseline at cycle-3 start: `bec9f76` (green + axiom-clean).
HEAD after cycle-3: `62a9c53`. Build re-verified: **`lake build` → "Build completed
successfully (1158 jobs)"**. No `sorry`/`axiom`/`native_decide` in touched files (sole grep
hit is a docstring at TieDischarge.lean:70). All new lemmas `#print axioms` →
`[propext, Classical.choice, Quot.sound]` (guards appended in-file, re-verified in build log).

Two tasks landed this cycle: **RUNSFACTOR** (gas) and **HMONO** (CALL seam). Both are pure
ADDITIONS — zero existing signature/structure changes, paramsRemoved = [] on both.

---

## (a) What LANDED

### RUNSFACTOR — commit `1ec1304`
File: `experiments/003_bytecode_layer/BytecodeLayer/Hoare.lean` (+41 lines, pure addition,
right after `Runs.step_to_halt`).
- **`Runs.step_cancel`** `{fr mid fr'} (hrun : Runs fr fr') (hstep : StepsTo fr mid) :
  Runs mid fr' ∨ fr = fr'` — single deterministic-step FRONT cancellation. Mirror of the
  green `step_to_halt`: `cases hrun` three-arm inversion (`.refl → Or.inr rfl`;
  `.step → StepsTo.det` then `Or.inl rest`; `.call → vacuous` via `.next ≠ .needsCall`).
  This is **fully PROVEN** (no supplied hyps).
- **`Runs.gas_cancel`** `(hrun) (hdec) (hsz) (hgas) (hne : fr ≠ fr') : Runs (gasFrame fr) fr'`
  — gas-specialized wrapper: feeds `StepsTo fr (gasFrame fr)` via
  `stepsTo_of_next (stepFrame_gas …)` and resolves the disjunct with `hne`. **PROVEN modulo
  the single supplied residual `hne`** (load-bearing, satisfiable — see (b)).

### HMONO — commit `62a9c53`
File: `experiments/005_ir_lowering/LirLean/TieDischarge.lean` (+1217 lines, pure addition,
engine bricks ~1803–2996, wrapper ~3567–3583).
- **`Evm.stepFrame_next_accMono`** (Brick C / `hmono`) — THE deliverable: fully-general
  arbitrary-address `a` re-derivation of the proven SELF-address dispatch family. PROVEN,
  every `.next` opcode case closed (exhaustive `cases` over dispatch/systemOp/smsfOp).
  Supporting bricks all PROVEN: `dispatch_next_accMono`, `systemOp_next_accMono`,
  `smsfOp_next_accMono` (all 15 SmsfOp), `callArm_next_accMono`, `createArm_next_accMono`,
  `pushOp/unOp/binOp/ternOp/dup/swap/logArm/unStateOp_next_accMono`,
  `charge_sstore/charge_tstore_next_accMono`, `sstore_accMono`, `tstore_accMono`,
  `dispatch_simple_arm_next_accMono`, `accMono_replaceOfBase`, `replaceStackAndIncrPC_accounts`.
- **`Evm.stepFrame_needsCall_inv`** — PROVEN (`hcall_acc` + `hcall_kind` + `hcall_self`),
  via stepFrame→systemOp→callArm needsCall inversion.
- **`Evm.stepFrame_halted_success_accMono`** (`hhalt`) — PROVEN: STOP/RETURN verbatim,
  SELFDESTRUCT honestly case-split as verbatim / ≤2 inserts (no `RBMap.erase`).
- **`Lir.callPreservesSelf_modGuards`** — PAYOFF wrapper instantiating the 5 proven facts.

---

## (b) Vacuity / circularity findings (reviewer-accepted both tasks)

- `Runs.step_cancel`: NOT vacuous — both disjuncts reachable (2+-step run → `Or.inl`;
  `Runs.refl` → `Or.inr`). NOT circular — consumes only the generic `Runs` inductive +
  `StepsTo.det`, zero gas/Corr reference; the `.step` arm's `Runs mid fr'` is the run's OWN
  tail `rest`, not a re-handed Runs.
- `Runs.gas_cancel.hne` (`fr ≠ fr'`): load-bearing, NOT vacuous — at `fr = fr'` the conclusion
  is generally false, so `hne` is correct not a dodge; satisfiable because GAS advances pc.
- `stepFrame_next_accMono`: NOT vacuous — exhaustive opcode coverage, green build rules out a
  missing/too-narrow case. SELFDESTRUCT genuinely case-split (no erase). NOT circular —
  engine lemmas reference `CallPreservesSelf` only in docstrings; discharge flows one way
  (proven engine facts → `callPreservesSelf_modGuards`).
- No overclaim: `paramsRemoved = []` confirmed by pure-addition diffs; `callPreservesSelf`
  itself KEEPS all 7 hyps; commit messages explicitly disclaim "hypothesis-free".

---

## (c) CALL seam — PRECISE status of the 7 `callPreservesSelf` hyps

PROVEN engine-level this cycle (5 of 7):
1. `hmono` — `stepFrame_next_accMono`. **PROVEN.**
2. `hcall_acc` — from `stepFrame_needsCall_inv`. **PROVEN.**
3. `hcall_kind` — from `stepFrame_needsCall_inv`. **PROVEN.**
4. `hcall_self` — from `stepFrame_needsCall_inv`. **PROVEN.**
5. `hhalt` — `stepFrame_halted_success_accMono`. **PROVEN.**

Still SUPPLIED (2 of 7) — genuinely conditional, NOT discharged:
6. `hprec` (beginCall `.inr` precompile-output presence) — opaque precompile output map in the
   `accounts'' ≠ ∅` branch; satisfiable (the `==∅` and out-of-1..10 fallbacks return
   `params.accounts`; vacuous for call-free lowered IR) but NOT structurally provable for an
   arbitrary precompile target. Kept supplied honestly.
7. `hncr` (EngineReaches-scoped no-CREATE seam) — drive's CREATE-fault arm sets
   `accounts := ∅` (a REAL erase). Correctly scoped to the child run's reachable frames (NOT
   the false universal ∀fr). Discharge via a decidable `WellFormedLowered.NotCreate` guard is
   a designated follow-on.

**`callPreservesSelf` itself is UNCHANGED — it still carries all 7 supplied hyps.** The
reduction "7 → 2 supplied" is realized ONLY in the NEW `callPreservesSelf_modGuards` wrapper,
which feeds the 5 proven facts and leaves `hprec` + `hncr` supplied.

**Downstream `hcall : CallPreservesSelf` param: NOT removed anywhere.** This is by design and
sound: `callPreservesSelf` does NOT become hypothesis-free (the precompile/CREATE ∅-arms
really can erase), so the bundled `CallPreservesSelf` abstraction stays at `selfPresent_runs`
/ L2.0 / halt+edge wrappers — they consume the bundle and need no change. The honest status is
**CALL seam REDUCED-modulo-2-supplied, not closed.**

---

## (d) GAS — Runs left-cancellation and the walk

- **Runs left-cancellation: LANDED** as `Runs.step_cancel` (PROVEN) + `Runs.gas_cancel`
  (PROVEN modulo satisfiable `hne`). This is the missing brick that cycle-2 flagged as the
  blocker (RUNSFACTOR).
- **Gas-advancing walk: STILL BLOCKED-as-deferred, NOT yet landed.** The full per-cursor
  induction `driveCorrPlus_run_stmts_gasadvance` was intentionally NOT implemented this cycle.
  RUNSFACTOR delivered the CAPABILITY to factor `Runs fr0 fr0'` into `Runs (gasFrame fr0) fr0'`
  (continuation past a `.gas` cursor), so the walk is now UNBLOCKED on the left-cancellation
  axis — but it remains a separate larger task that still consumes the unchanged cycle-2 S4
  decode/gas envelope bundle per `.gas` cursor and needs `hne` supplied (derivable later from
  `stepFrame fr0 = .next _ → fr0 ≠ fr0'`, since gasPost advances pc). Honest status:
  **left-cancellation proven; the walk that uses it is the next task, not done.**

---

## (e) Remaining obstacles + roadmap to C9

Standing supplied/conditional residuals (all honest, none vacuous):
- CALL seam: `hprec` (opaque precompile) + `hncr` (no-CREATE erase seam) — fold `hncr` into a
  decidable `WellFormedLowered.NotCreate` guard; `hprec` is vacuous for call-free lowered IR.
- GAS: the S4 decode/gas envelope bundle (S3/S4 runtime envelopes, unchanged) + the
  `gasadvance` walk itself.

Roadmap (plan §C4–C9, `docs/p5-discharge-plan.md` ~271–278):
- C4 halt wrappers (T1/T2), C5 edge wrappers (T3/T4/D2/D3) — landed earlier (`516f166`,
  `bec9f76`) as `driveCorrPlus_step_stop/_ret/_jump/_branch`.
- **NEXT**: implement `driveCorrPlus_run_stmts_gasadvance` (gas walk, now unblocked by
  `Runs.gas_cancel`); then the decidable `NotCreate` guard to discharge `hncr`.
- C6 Tier-3 strengthened recursion (`runFrom_of_driveCorrPlus`).
- C7 P2 (`modellableStep_lower`) ⇒ entry `CleanHalts`.
- C8 Route 4b (`sim_cfg_along_drive`) — thread emitted ties into the world equation.
- C9 P6 (L5.1 → L5.2) — the tie-free headlines (`lower_conforms_cyclic_tiefree`).
