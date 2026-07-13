# exp005 — what the `exp005-honesty-cleanup` branch achieved since `main`

Date: 2026-07-04. Audience: the project lead. One-file summary of the arc from `main`
to HEAD (`9e219ed`). Companion detail lives in
`docs/target-architecture-2026-07-02.md` (plan of record),
`docs/final-audit-2026-07-03.md` (the CLEAN gate), and
`docs/recorder-model-note.md` (the recorder course-correction). The reviewable proof
surface is `LirLean/RealisabilitySpec.lean` (the `Nightly` lib).

---

## 1. What exp005 is

A Lean 4 formalization of a high-level IR lowered to EVM bytecode, proving the lowering
**preserves semantics** under a **record-then-replay conformance** discipline:

1. Run the lowered bytecode with a recording interpreter (`runWithLog` / `driveLog`,
   `LirLean/Spec/Recorder.lean`) to produce a `RunLog`.
2. Harvest the run-observed **gas** stream (`realisedGas log`) and **external-call**
   results (`realisedCall log self`) from that log.
3. Feed those harvested values back as oracles into the IR-level semantics and prove the
   bytecode's observable **storage** matches the IR world (`Conforms`).

The flagship is `Lir.lowering_conforms` (`RealisabilitySpec.lean:3306`): one runtime
premise (`hrun`), decidable statics (`WellLowered`), and a small set of **named seams**
(`PrecompileSeams`) yield `∃ O, RunFrom prog (realisedCall log self) (entryState params)
(realisedGas log) prog.entry O ∧ Conforms params.recipient log O`.

## 2. The honesty cleanup (2026-07-02..03)

A 5-agent design fleet plus an adversarial skeptic pass found the prior headline
`lower_conforms_cyclic_assembled` was **VACUOUS**, not merely conditional: its supplied
`StmtTies` / `TermTies` hypotheses were **unsatisfiable for essentially every nonempty
program** — a repeated free-`∀` shape (a variable universally quantified in the tie but
pinned to a run-specific value in the conclusion, with no antecedent linking it to the
run). A green, axiom-clean theorem that carried no information on the interesting domain —
the exact failure mode the no-sorry policy exists to prevent, resurfaced as
supplied-hypothesis debt. Full diagnosis: `docs/target-architecture-2026-07-02.md` §1.

The response (waves 1–4) was to **delete the entire vacuous conformance surface** rather
than paper over it:

- the vacuous headlines (`lower_conforms_cyclic_assembled` + `_tiefree` +
  `lower_conforms_wf` + the `lower_conforms_acyclic*` family);
- the diseased tie definitions (`StmtTies` / `TermTies`);
- the "Plus" assembly apparatus;
- the `Spec` re-export layer (`RealisabilityObligations` / `_of_obligations`;
  `Spec/Conformance.lean` is now a disclaimer stub).

The obligations were then **reshaped** into `LirLean/RealisabilitySpec.lean` (the
non-default `Nightly` lib) as the **R0–R12 honest-sorry skeleton**, where the ties are
**DERIVED from the run** (`stmtTies'_of_runWithLog` R10a, `termTies'_of_runWithLog` R10b),
**not supplied**. The reshaped `StmtTies'` / `TermTies'` (`:694`, `:793`) antecedent-pin
every formerly-free value variable, so no free-`∀` disease survives. Two other
unsatisfiable in-tree bundles were replaced with satisfiable versions (`RunDefinable` →
`RunDefinableG`; the `SstoreRealises` conjunct dropped, its content returned point-wise at
the concrete frame by R4), and the missing static consistency guard `DefsConsistent` was
added.

A final **110-agent adversarial audit** (`docs/final-audit-2026-07-03.md`) returned
**CLEAN**: no reintroduced vacuity, no silent weakening, disclaimers accurate; the diseased
ties are demoted from *hypotheses of the headline* to *conclusions of sorry'd obligations*.

The design principle vindicated here: **a well-placed `sorry` is more honest than a vacuous
green theorem.**

## 3. Phase 3 (2026-07-03..04) — the proof grind

Closing the R0–R12 obligations via per-track plan→implement→review workflows running in
parallel git worktrees with copy-on-write `.lake` caches.

**Closed, axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

- **R7a–e** — the recorder-coupling spine (entry coupling + the four preservation edges);
- **R0b** — the shadowing-aware sim-machinery reshape criterion;
- **R1** — the gas recorder bridge (flagged the *riskiest* obligation);
- **R2** — clean scope read off the log;
- **R4** — SSTORE realisation, point-wise at the concrete frame;
- **R5** — terminator ties from the walk vocabulary;
- **R8** — presence threading;
- **R9** — the static `WellLowered` checker;
- plus the **`exProg` non-vacuity witness pieces** (`singleCall_exProg`,
  `defsSoundS_empty_iff`, the machine-checked refutation `not_defsSound_stale`,
  `revalidatesPerBlock_exProg`, the `WellLowered exProg` construction).

Net: **21 of ~34 tracked Phase-3 proof obligations closed → 13 `sorry`s remain** in
`RealisabilitySpec.lean` (the top-level proof-body count went 25 at skeleton entry → 13).

**Course-correction that landed mid-grind** (`docs/recorder-model-note.md`, commit
`82e7453`): the recorder's returning-CALL record (`recordCall`) was **ungated** — it also
recorded a *descended callee's* inner returning CALLs, contradicting its own docstrings and
the sibling gas/sload `stack.isEmpty` gates. Fixed by gating it on `rest.isEmpty` in the
default target (**Option B** — fix the definition, don't supply a hypothesis around it),
which made **R7e hold unconditionally** (the single-call `hone` premise dropped, statement
unchanged) and made `realisedCall` faithful even when the top-level call's callee itself
calls (unblocking the R3′ multi-call generalization).

## 4. Remaining — 13 sorries

Two **hard leaves**:

- **R3** — call realisation (`CallRealisesS`, `:1303`); needs an arg-push machine-run
  producer, possibly a default-target lemma. Piece A (recorder CALL extraction + arg-push
  transport) has landed; Piece B is the open core.
- **R6** — the boundary walk (`:2140`, `:2143`); the pc-reachability geometry (the two
  `AtReachableBoundary` edge lemmas). The R6 statement itself was already fixed —
  originally REFUTABLE, now carries the `0 < prog.blocks.size` side condition, with the
  refutation `not_runs_atReachableBoundary` machine-checked.

The **assembly + closure** layer:

- **R10a / R10b** (`:3265`, `:3273`) — build `StmtTies'` / `TermTies'` from the run;
- **R11** flagship `lowering_conforms` (`:3306`) and **R11-all** `lowering_conforms_all`
  (`:3327`, the exact-stream-consumption strengthening);
- the **gasfree co-flagship** `lowering_conforms_gasfree` (`:3351`) + its companion
  `realisedGas_nil_of_noGasReads` (`:3361`);
- **R12a / R12b** — the concrete non-vacuity witnesses (`r12_hypotheses_inhabited` `:3378`,
  `r12_end_to_end` `:3390`);
- **RunFromLeft adequacy** (`:988`, `:994`) — the `RunFromLeft ↔ RunFrom` mirror lemmas
  that back the `_all` strengthening.

## 5. Build state

- Default **`LirLean`**: last recorded ~1172 jobs, **GREEN and sorry-free** (it does not
  import the Nightly lib; `lakefile.lean:31-32`).
- **`Nightly`** (`RealisabilitySpec.lean` only): ~1166 jobs green; the **13 sorries are the
  tracked Phase-3 debt**, every one a `sorry` body over a satisfiable, non-vacuous
  statement.

The `LirLean/Audit.lean` guard net (`#guard_msgs`-pinned, build-failing) pins the
load-bearing default-tree lemmas and their axiom-cleanliness; the Nightly lib is
deliberately left unguarded (guarding `sorryAx` would only pin the debt's existence — guards
migrate over as sorries land).

## 6. What is genuinely novel

From `docs/target-architecture-2026-07-02.md` §9: a **generic record-then-replay
conformance theorem for programs that observe gas AND make external calls**, with residual
trust confined to **named seams**. No EVM-compiler formalization does this generically —
Verity does not model gas at all and supplies the entire cross-layer result equivalence as a
hypothesis; other forks evade pc/jumpdest/landing reasoning rather than discharge it. Once
R11/R12 close, this is the fork-comparable milestone the experiment was built to reach.
