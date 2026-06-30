# exp005 — Cycle-2 handoff (2026-06-29)

Branch `ir-convergence`, HEAD **bec9f76**. Build: `lake build` → **Build completed
successfully (1158 jobs)**. Every touched lemma `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. No `sorry` / `axiom` / `native_decide`
in any proof body (sole grep hit is the line-70 docstring describing the invariant).

This cycle advanced **three independent fronts** on top of baseline 73f2d6b
(GAS channel, CALL seam, EDGE wrappers). It did **not** close the C9 tie-free
headlines, and it deliberately did not fake the heavy residuals. Read this
alongside `overnight-handoff.md` and `p5-discharge-plan.md`.

---

## (a) What LANDED — commits + lemmas (all green + axiom-clean)

### GAS — commit `5c8395c` (TieDischarge.lean §7, ~1655/1700)
- `driveCorrPlus_gas_cursor_advance` — the genuine STEP-1 structural advance.
  At a `.assign t .gas` cursor, from `GasLogAligned gasAcc gasFrs` + the GAS-op
  facts (decode=GAS, `Gbase ≤ fr0.gas`, boundary reachability, stack-nil) it
  **PRODUCES** `GasLogAligned (gasAcc ++ [ofUInt64 (gasFrame fr0).gas]) (gasFrs ++ [gasFrame fr0])`
  + `Runs fr0 (gasFrame fr0)` + the snoc `getLast?`. Routes only through
  `sim_gas` + `Dispatch.stepFrame_gas` + `gasLogAligned_step_gas`. The appended
  word is the recorder's literal splice — a real extension, not a re-supply.
- `driveCorrPlus_norecord_cursor_advance` — non-gas cursor: alignment carried
  VERBATIM + reachability threaded via `Runs.trans`. Trivial-but-honest
  preservation; docstring explicitly disclaims any "no-record-inside" /
  byte-freeness claim (`_hnotgas` is genuinely unused).

### CALLMONO — commit `9ea5fa7` (TieDischarge.lean, +582 lines)
The `.success` shape of `CallPreservesSelf` is **DISCHARGED engine-level**.
- `drive_accounts_find_mono` (Brick D) — strong-fuel induction over `drive`'s
  recursion (template `drive_fuel_succ`), threading `DrivePresent a` = presence
  at `a` in the running map AND the running frame's kind-checkpoint AND every
  pending ancestor's checkpoint. This is the genuine whole-child-run induction.
- Supporting bricks: `accounts_find?_insert_mono` (A), `accPresent_ne_empty` +
  `accMono_emptySwap` (B), `accMono_of_accounts_eq`, `beginCall_inl_accounts_present/_checkpoint`,
  `endFrame_accPresent` (KEY: **both** `endCall` and `endCreate` are
  presence-preserving — success=insert, failure=checkpoint rollback; no
  frame-kind exclusion needed), `resumeAfterCreate_*`.
- `callPreservesSelf_success` / `callPreservesSelf` instantiate Brick D at the
  child run, build `DrivePresent` non-vacuously from `SelfPresent callFr`, close
  via the landed `resumeAfterCall_self_of_accounts`.

### EDGE — commit `bec9f76` (TieDischarge.lean §9, +176 lines)
- `driveCorrPlus_step_jump` (L2.3) / `driveCorrPlus_step_branch` (L2.4) —
  DriveCorrPlus liftings of the green `drive_step_block_jump/_branch`. Identical
  bytecode construction (`sim_stmts_block` → supplied edge bundle → JUMPDEST
  landing → `corr_at_jumpdest_landing` → `cleanHalts_forward` → `totalGas_succ_lt`
  → `RunFrom.{jump,branchThen,branchElse}`), with exactly two additions at the
  successor boundary: SelfPresent via `selfPresent_runs_of_call` (P3 hop) and
  alignment carried VERBATIM. Successor DriveCorrPlus is existentially bound to
  the reached `jumpdestFrame fj` (Route-4b indexed; not the forbidden universal).
  Zero ripple — DriveCorrPlus consumed and re-produced unchanged.

---

## (b) Vacuity / circularity findings (screened, clean)

- **GAS brick non-circular:** `driveCorrPlus_gas_cursor_advance` produces the
  extended alignment from the GAS-op facts via `gasLogAligned_step_gas`; it never
  takes an extended-alignment hyp and returns it. Appended word is the recorder's
  literal splice `gasReadOf (gasFrame fr0)`, not a free word — so not vacuously
  satisfiable.
- **norecord honest-scope:** preservation + threading ONLY. Does NOT claim "no
  GAS byte fired inside the segment" — a non-gas statement can still materialise a
  `.gas` operand. Byte-freeness is DEFERRED (same status as `*_matRuns`).
- **CALLMONO:** Brick D is well-founded fuel induction (`ih` at strictly smaller
  fuel); `hmono` is *consumed* at the `.next` arm, not self-supplied. No `.erase`
  exists anywhere in the semantics (grep-verified) — every account write is
  insert-only or checkpoint-rollback, so the supplied monotonicity is genuinely
  TRUE, not in the `gasRealises_universal_unsatisfiable` danger class.
- **EDGE P3 non-circular:** `selfPresent_runs_of_call` consumes the GIVEN
  boundary `hdc.selfPresent` + a genuinely-assembled `Runs fr (jumpdestFrame fj)`,
  producing SelfPresent at a DIFFERENT frame. Alignment-verbatim is a predicate on
  the accumulator/witness pair alone (never references the frame), so the carry is
  trivially sound and makes no execution claim.
- **No falsely-unconditional headline:** `callPreservesSelf` correctly stays a
  7-hypothesis supplied theorem; it is NOT stated hypothesis-free (that would be
  FALSE — the precompile/CREATE `∅`-arms really erase).

---

## (c) DISCHARGED vs still-SUPPLIED

### DISCHARGED this cycle
- `StepPreservesSelf` (baseline, fully general).
- `CallPreservesSelf` **.success shape** — engine-level monotonicity via Brick D.
  (.revert/.exception were already structural.)
- GAS per-cursor advance at a single `.gas` cursor (the brick).

### Still SUPPLIED (each satisfiable, not vacuous)
- **hmono (GAS Brick C):** per-`.next`-step arbitrary-address account-presence
  mono. SATISFIABLE — universally true (insert/verbatim only); self-address
  instance is the proven `stepFrame_next_self`. Unproven only because it is the
  ~800–1000-line parallel re-derivation of the `_next_self` dispatch family.
- **GAS S3 (positional value):** `st'.locals t = ofUInt64 (fr0.gas − Gbase) = gasAcc[i]`.
  SATISFIABLE — exactly `aligned_read_eq_obs` once the witness pairing
  `gasFrs[i] = gasFrame fr0` is threaded. Needs a NEW carried trace↔gasAcc
  invariant (`EvalStmt.assignGas` peels the trace head; `driveLog` consumes
  `gasAcc` — independent today). NOT vacuous; it is the genuine bridge.
- **GAS S4 (runtime envelopes):** `Gbase ≤ gas`, `3 ≤ gasFrame gas`, memExpansion +
  MSTORE bounds. SATISFIABLE on any halting lowered run; CONSUMED by the brick as
  a precondition. To PRODUCE needs `cleanHalts_forward → Runs.linear_to_halt`
  threaded to the cursor, not pure `gasAvailable_le` descent.
- **CALL no-erase seam (hncr/hprec):** EngineReaches-scoped (NOT the false
  `∀ fr`). SATISFIABLE for CREATE-free lowered children. Genuinely needed —
  drive's CREATE-fault arm sets `accounts := ∅`, a real erase.
- **CallPreservesSelf** itself in `selfPresent_runs` / L2.0 / halt + edge
  wrappers — kept supplied (no param removal is safe; it is not hypothesis-free).
  Strictly more closed than before (.success now proven mod the no-erase seam).
- **hjump / hbranch (EDGE bundles):** VERBATIM from the green
  `drive_step_block_jump/_branch`; indexed `∀ frT, Corr → ∃ fj …` so non-vacuous.
  Stay supplied because PRODUCING them from the run is the boundary-walk channel.
- **hsim : SimStmtStep:** folds S1/S5/S6; consumed only for the Runs+Corr+stack
  triple. Inhabited by any concrete lowered block.

---

## (d) Remaining obstacles (concrete, not hand-waved)

1. **GAS Brick C (hmono):** mechanical but P5-spine-sized. Parallelizable by
   dispatch sub-family (System/Smsf/ArithLogic/Env/Block/Push/Dup/Swap/Log);
   swap two closers — `selfAt_replaceOfBase → accMono_of_accounts_eq` (verbatim
   arms), `sstore/tstore_self_present → accounts_find?_insert_mono` (insert arms).
2. **Rebuilt gas-advancing walk (`driveCorrPlus_run_stmts_gasadvance`):** BLOCKED
   on a missing `Runs` left-cancellation / determinism lemma. At a `.gas` cursor
   the supplied segment `Runs fr0 fr0'` covers the WHOLE statement (GAS;PUSH;MSTORE),
   but the brick only gives `Runs fr0 (gasFrame fr0)`; continuing the walk needs
   `Runs (gasFrame fr0) fr0'` — i.e. factoring `Runs fr0 fr0'` at the prefix.
   No frame-level Runs determinism exists (only EvalStmt/RunStmts in V2/Law.lean).
   Building it is a separate spine-magnitude task.
3. **GAS S3 trace↔recorder bridge:** the carried trace↔gasAcc invariant + witness
   pairing. Ripples DriveCorrPlus + all consumers if folded into the struct;
   PREFER a separate invariant. Out of scope this cycle.
4. **GAS S4 envelopes:** clean-halt FORWARD split threaded to an arbitrary
   reachable gas/MSTORE cursor.
5. **CALL no-erase seam → WellFormedLowered:** folding the EngineReaches-scoped
   NotCreate guard into a decidable structural fact would make `callPreservesSelf`
   hypothesis-free and enable downstream `hcall`-param removal. Follow-on.
6. **EDGE bundle production:** `hjump/hbranch` still need to be PRODUCED from the
   run by the boundary-walk channel (S1/S5/S6 spine + ReachesBoundary).

---

## (e) Roadmap to the C9 tie-free headlines

Remaining spine (none of it landed this cycle; all is genuine work):

- **Tier-3 DriveStepPlus** (`driveStepPlus_of_block`, `runFrom_of_driveCorrPlus`)
  — assemble the per-block DriveCorrPlus step from L2.0 + the four wrappers
  (halt ×2 now + edge ×2 landed). Then the **drive-recursion induction**
  (`sim_cfg_along_drive`, Route-4b) lifting DriveStepPlus across the whole CFG —
  the analogue of `runs_of_drive_ok`, threading SelfPresent + alignment + descent.
- **GAS value channel:** needs Brick C (hmono) → the gas-advancing walk
  (blocked on Runs-factoring, obstacle #2) → S3 trace↔recorder bridge → S4
  envelopes. Until these land the gas *positional value* tie stays supplied;
  the gas *alignment* substrate is in place (single-cursor advance proven).
- **CALL seam:** monotonicity is done; only the EngineReaches-scoped no-erase
  guard remains (discharge via WellFormedLowered to go hypothesis-free, #5).
- **Route-4b / CFG recursion:** consume the edge + halt wrappers' indexed
  DriveCorrPlus conclusions; this is where SelfPresent + alignment + gas descent
  compose into the whole-program statement, feeding the C9 tie-free headlines
  (`lower_conforms_cyclic` / `'`).

**Honest status:** the supporting substrate is materially stronger
(StepPreservesSelf + Call .success discharged; gas single-cursor advance; both
edge wrappers lifted). The headlines remain gated on (i) Brick C, (ii) the
Runs-factoring lemma, (iii) the S3 trace bridge, (iv) S4 envelopes, and (v) the
Tier-3 + Route-4b CFG recursion — none of which were faked or claimed done.
