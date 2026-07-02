# exp005 Target Architecture — 2026-07-02

*Synthesis of the 5-agent high-level design fleet (`docs/fleet-2026-07-02/`) + a skeptic
verification pass. Signatures-first, per the lead's directive: get the theorem statements right,
kill the vacuous/circular material, track dischargeable gaps as honest sorries. This document
SUPERSEDES the priority framing of `remediation-plan-2026-07-02.md` (its phases survive, re-ordered
and amended below) and sharpens `audit-2026-07-02.md` §3.*

---

## 1. The headline finding: the conditional headline is VACUOUS, not merely conditional

Confirmed by adversarial verification (`fleet-2026-07-02/skeptic-f1-verdict.md`): the supplied
`StmtTies`/`TermTies` hypotheses of `lower_conforms_cyclic_assembled` (TieDischarge.lean:4292) are
**unsatisfiable for essentially every nonempty program**, due to a repeated free-`∀` shape (a
variable universally quantified in the tie, pinned to a run-specific value in the conclusion, with
no antecedent linking it to the run):

- gas conjunct: free `ob` pinned to `fr0.gasAvailable` (LowerConforms.lean:1307-1323); no Corr
  field mentions `gasAvailable`, so Corr is adversarially inhabitable and `∀ ob, ob = c` is false;
- sload conjunct: free `w` (:1284-1306); assign conjunct: free `st0'` + `MemRealises` (:1275-1283),
  plus an outright static contradiction (the assign conjunct demands gas-assign tmps NOT be
  spilled; `defsOf` spills them, Lowering.lean:247);
- TermTies: address/kind/nonempty-accounts/gas-guard demands over Corr-frames that Corr does not
  pin — unsatisfiable for every block with ANY terminator.

So the green, axiom-clean headline carries no information on the interesting domain. This is the
exact failure mode the no-sorry policy was meant to prevent, resurfaced as supplied-hypothesis
debt — and it vindicates the policy shift: **a well-placed sorry is more honest than a vacuous
green theorem**. The in-tree comment at TieDischarge.lean:3637 shows the shape problem was known
("unreconstructable from a single run") but its consequence (antecedent = False) was not drawn.

Also confirmed: `callOracleOf` (RunLog.lean:263) reads only the FIRST CallRecord — the log-fed
call oracle is correct only for single-CALL programs. This must be surfaced in the flagship
statement (a `SingleCall prog` premise now; calls-as-consumed-stream later), never silently shipped.

**Consequence for priorities: the R0 tie reshape (§3) is a correctness precondition, not polish.**
Nothing built on the current tie shapes is salvageable as-stated; the walk/driver/landing/extractor
machinery below the ties IS salvageable (it never consumed the vacuous conjuncts — the audit's §4#2
already established the real work flows through the SimStmtStep spine).

## 2. The flagship (target statement, settled shape)

One runtime premise, decidable statics, named seams (full design:
`fleet-2026-07-02/flagship-signature.md` §1):

```lean
theorem lowering_conforms
    (hcode : params.codeSource = .Code (lower prog))
    (hmod  : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas  : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl   : WellLowered prog)                     -- static bundle, checker-dischargeable (R9)
    (hrun  : runWithLog params (seedFuel params.gas) = some log)   -- THE run
    (hclean : log.clean)                           -- decidable non-exception scope
    (hseams : PrecompileSeams prog params) :       -- hprec + CallsCode, the honest boundary
    ∃ O, RunFrom prog (realisedCall log params.recipient)
           (entryState params) (realisedGas log) prog.entry O
       ∧ Conforms params.recipient log O
```

Key statement decisions:
- **Pin the oracles**: `T := realisedGas log`, `o := realisedCall log self`, `st₀ := entryState
  params` (definition, replaces the supplied entry StorageAgree). The current headline's free `{T}`
  is part of the vacuity; kill it.
- Fold `hpresent/hjumpPresent/hbranchPresent/hstkBranch/hwfl/hdef` into one static `WellLowered`
  structure with a decidable checker (R9). `hcall : CallPreservesSelf` is replaced by the `hprec`
  seam + the already-proven 260-line discharge chain (wired at last).
- The `obs`/`sloadChg` phantom/threading params: `obs` is unused by Corr — delete; `sloadChg`
  pinned or existentially closed inside.
- **Strengthening worth taking**: a `RunFromAll` variant pinning the leftover gas trace to `[]`
  (exact stream consumption) — closes the last drop-the-suffix vacuity channel.
- **Multi-CALL**: state now with a `SingleCall prog` premise, tracked decision to generalize calls
  to a consumed stream (the gas channel already solved this positionally).

## 3. Tie reshape (open decision #3 — SETTLED: recorder-suffix coupling)

Replace the four vacuously-empty `DriveCorrPlus` accumulator lists with ONE real coupling field:
"restarting the recorder at the current boundary frame reproduces exactly the un-consumed suffix
of the log." Ties then say: the head of the gas suffix equals the machine GAS output at this
cursor, and the invariant advances to the tail. Why: matches the head-consumption shape of
`EvalStmt`/`driveLog` exactly; cyclic-correct (same cursor revisited with different gas —
per-cursor value functions are UNSOUND here, option iii rejected); black-boxes child calls the
same way `Runs.call` does; and it is the verifereum Collect/Enforce pattern the remediation plan
already blessed. Blast radius: ~15-20 walk signatures + the two StmtTies value conjuncts +
`simStmtStep_block` arms + ~300-500 new recorder lemmas. **No change to Machine.lean/IRRun.lean**
(the IR spec surface is untouched).

## 4. The four open decisions — all settled

1. **HonestGasTie.lean: DELETE** (unblocks Phase 2). Once the gas-law apparatus (`Mono.lean`,
   `Oracle.lean`) leaves, the retired-universal guard guards nothing live. Condition: the
   unsatisfiability lesson moves to the Phase-3 spec file's docs, and the concrete end-to-end
   instantiation (R12) becomes the machine-checked non-vacuity evidence — delete in the same
   commit that adds the spec file.
2. **Gas-free secondary theorem: CO-FLAGSHIP, proven FIRST.** With the §3 reshape,
   `lowering_conforms_gasfree` (`NoGasReads prog`) needs no positional gas bridge — it exercises
   every Phase-3 obligation except the riskiest (R1), making it the de-risking checkpoint AND the
   fork-comparable theorem (Verity/vyper-hol scope).
3. **Tie reshape: option (i)** (§3).
4. **SelfPresent: WIRE IT, don't drop.** Phase 3 needs it twice (SstoreRealises presence at the
   SSTORE frame; killing the unsatisfiable TermTies address/kind/nonempty conjuncts requires the
   walk invariant to carry exactly these facts). Extend the invariant with the two rfl-preserved
   companions (address pin, kind pin) in the same edit. Dropping in Phase 2 then re-adding is churn.

## 5. Phase 3 as a reviewable spec file (the honest-sorry skeleton)

New file `LirLean/V2/RealisabilitySpec.lean` (statements only, every proof `sorry`, nightly-built,
not imported by the main target): obligations R1-R12 per
`fleet-2026-07-02/flagship-signature.md` §5 — gas recorder bridge (R1), clean-scope-from-log (R2),
call realisation from log (R3 + the R3' multi-call decision), SSTORE-through-walk (R4), term ties
(R5), boundary walk / hrb (R6), recorder-coupling edge lemmas (R7), presence threading (R8),
static checker (R9), tie assembly (R10), flagship (R11), concrete non-vacuity witness (R12).

Landing order (each step green, monotonically fewer sorries):
**R0 (reshape) → R9 → R2 → R8 → R5/R4 → R6 → gasfree co-flagship → R7 → R1 → R3 → R10 → R11 → R12.**

Substantial proofs: R1, R3, R6 only. Everything else is static folds and assembly.

## 6. Bytecode-layer interface (why the abstraction failed; what exp003 must export)

Diagnosis (`fleet-2026-07-02/bytecode-interface.md`): exp003 exports two altitudes — single-opcode
steps on Frames, and whole-call outcomes (`Behaves`, used by exp005 ZERO times) — with nothing in
between. A lowering proof is a forward simulation and needs the mid-run band: block-level
composition, code-geometry algebra for EMITTED bytecode, engine invariants along `Runs`, a
recording interpreter. exp005 built all of it in-house; its headline even has `Runs`/`stepFrame`
in the conclusion, violating exp003's own "Runs never appears in an exported statement" promise
(Hoare.lean:27). Measured: of exp005's ~24.7k lines, ~20% is misplaced pure engine theory, ~57%
frame-level lowering machinery, <10% actual IR content.

Target exp003 surface (five spec files; signatures in the report):
1. `Exec.lean` — big-step `Exec params code O` (wraps Runs+halted+observe); the flagship restates
   frame-free through it.
2. `Exec/Recorder.lean` — `runWithLog` relocated + **`RunsEv`** (event-indexed Runs) + adequacy;
   `RunsEv.det_events` turns the Phase-3 positional bridge into a one-time exp003 fact.
3. `Exec/Invariants.lean` — self-present/find-mono/clean-halt/per-op envelopes as laws, with the
   `CallsCodeAlong` seam surfaced once instead of threaded through 28-hyp bundles.
4. `Asm.lean` — structured assembly (blocks + labeled jumps + data segments) + verified `assemble`
   with the decode/jumpdest/landing algebra proven ONCE. This is where allocator/data-segment
   NON-DETERMINISM naturally lives (placement = assembler freedom). **Phase 5, strictly after
   Phase 3** — it churns exactly the files Phase 3 rewrites.
5. `Exec/CyclicSim.lean` — the IR-agnostic gas-descent cyclic simulation driver.

Honest feasibility: pc/jumpdest/landing reasoning cannot be *eliminated* (it is the semantic
content of "bytes implement this CFG"; no fork does it — they evade the problem, not solve it),
but it can be *paid once*. IR #2 then proves only: its lowering into Asm, per-statement effect
sims, its coupling invariant's semantic fields, its value channel, its oracle ties.

## 7. Future-proofing (memory / allocator / data segments / multi-IR)

Full analysis: `fleet-2026-07-02/future-proofing.md`. Correction to the running narrative: spills
already go to EVM **memory** (`slotOf t = t.id * 32`, MSTORE/MLOAD readback), not storage. What's
missing is IR-*visible* memory and non-deterministic placement.

Settled design directions:
- **Non-determinism = ∀-quantified placement** (option a): `lower : Placement → Program →
  ByteArray`, theorem `∀ π, ValidPlacement prog π → …`. Offset-independence is enforced by the
  theorem's SHAPE (the IR observable is pinned before π is chosen). Rejected: existential placement
  (loses exactly that), relational semantics (destroys determinism + makes log-feeding ill-posed).
- **IR memory = object-granular** (`alloc/mstore/mload` over handles), NOT flat `Word → Word`
  (flat re-couples programs to placement). The "poor man's memory injection" is one Corr clause —
  `MemRealises` generalized from `slotOf`-indexed to `π`-indexed. Full CompCert injections only
  needed if Plank IR ever casts pointers to words.
- **UB = stuckness + `MemDefinable` supply** (the existing `RunDefinable` pattern), decidable on
  concrete programs so it is discharged by evaluation, never a supplied universal. Anti-pattern to
  avoid: stating UB-freedom as a bytecode-run property (undischargeable direction).
- **Data segments: after memory; data-after-code as a design commitment** (keeps Layout anchors
  untouched). The instruction-aligned `SegAlignedSafe` walk is UNSOUND over a data suffix — the fix
  is the same pc-reachability scoping as the existing `hrb` residual (R6): design them jointly.
- **The one BREAKS-level overfit**: the `slot' = slotOf tw` pins (LowerConforms.lean:1289, 1312).
  Replace with a `ValidPlacement` parameter DURING the Phase-3 reshape (those exact conjuncts are
  being rewritten anyway).
- **Endomorphism passes**: statable today, purely IR-level (`RunFrom (pass p) … → RunFrom p …`),
  composing with the flagship because it concludes in `RunFrom`. Needed: a trace-remap discipline
  for passes that change gas-read counts (or the cheap syntactic rule "passes may not
  duplicate/eliminate `.gas` reads"); a composition lemma (cheap, post-Phase-3).
- **Sequencing: close Phase 3 on the toy IR first**, with two generality guards smuggled in:
  (1) ValidPlacement instead of slotOf pins; (2) boundary walk designed with the data-suffix in
  mind. Then alloc-generalization → memory → data segments. Defer any `IRLang` typeclass until
  IR #2 exists.

## 8. Reorganization (spec/proof split, audit surface, linting)

Full plan: `fleet-2026-07-02/reorg-legibility.md`. Highlights:
- **Spec core ≈ 1,800 lines / 8 files** (`Spec/IR, Semantics, Lowering, Layout, Recorder,
  Correspondence, Seams, Conformance`) — the reviewer path is `Spec/` + `Examples/EndToEnd.lean` +
  `Audit.lean`. Flagship as Pattern A (statement-as-def in spec file, proof elsewhere);
  obligations as a `RealisabilityObligations` structure (Pattern B) — supplied-hypothesis debt
  becomes one named, greppable term.
- **`Audit.lean`**: replace the 252 scattered `#print axioms` with `#guard_msgs`-pinned,
  build-failing guards — axiom-cleanliness of flagship + seams, a SIGNATURE FREEZE on the flagship
  (no hypothesis sneaks in unreviewed), non-vacuity witnesses. Expensive executable witnesses in a
  separate nightly lib.
- **Linting**: Batteries' `runLinter` (unusedArguments etc.) works TODAY via
  `lake exe runLinter LirLean` — zero lakefile changes; freeze a `nolints.json` baseline. Honest
  limit: it catches syntactically-dead binders only; the dischargeable-but-supplied class is
  caught by the signature freeze + seam whitelist instead.
- File-tree target: no file over ~1,300 lines; exp005 shrinks ~24.7k → ~20-21k (Phase 2 −1.7k,
  Phase 4 −3.1k incl. the ~1,000-line SelfAt/AccMono walk unification). Keep the `Lir.V2`
  NAMESPACE (rename files/dirs only).

## 9. Verity (the lead's question, answered)

`fleet-2026-07-02/verity-fact-check.md`: Eduardo is right that Verity's supplied run-match is not
about gas — **gas is not modeled at all** in their verified semantics ("Gas is not modeled",
TRUST_ASSUMPTIONS.md:61; their Gas/ dir is an unverified CLI estimator) and their language has no
gas introspection. But it is also **not calls-only**: `hNative : nativeResultsMatchOn …`
(EndToEnd.lean:128) assumes the ENTIRE observable result equivalence (success flag, return value,
observable storage slots, events) between their IR interpreter and the native execution — the
whole cross-layer correspondence, supplied. External calls in Verity are excluded from the
verified fragment or trusted per-module (ECM `proofStatus := .assumed`). No current Verity theorem
feeds run-harvested values into IR semantics (their legacy oracle stack was removed). Credit where
due: Verity has ONE hypothesis-free concrete instance (SimpleStorage) — exactly the R12-shaped
milestone Phase 3 should also produce first. What Phase 3 would establish that no fork has: a
GENERIC record-then-replay conformance theorem for programs that observe gas and perform external
calls, residual trust confined to named seams.

## 10. Execution order (supersedes remediation-plan phase numbering)

- **Step 0 [pure, do first]**: `Audit.lean` guards + delete the 252 scattered `#print axioms` +
  linter baseline. The regression net for everything below.
- **Step 1 [semantic]** = Phase 2, now unblocked: delete `Mono.lean`/`Oracle.lean`/
  `HonestGasTie.lean` (decision §4.1), narrow `Law.lean`, delete RunLog monotonicity section.
  KEEP the DriveCorrPlus accumulator params (they become the §3 coupling field — do not remove
  then re-add).
- **Step 2 [semantic→pure]** = Phase 4 first half, BEFORE Phase 3: unify the SelfAt/AccMono walks
  (~1,000 lines saved), relocate category-(i) engine facts to exp003
  (`Exec/Invariants`-shaped, spec/proof split from day one; include MemAlgebra, CleanHalt,
  CleanHaltExtract §0-§2, DriveRuns, Charges, recorder), split the TieDischarge remnant. Halves
  the context any Phase-3 agent must hold.
- **Step 3 [pure]**: `Spec/` extraction of the stable files + `Seams.lean` +
  `RealisabilitySpec.lean` (the R0-R12 sorry skeleton) + conditional `Conformance.lean` honestly
  docstringed.
- **Step 4 [the milestone]** = Phase 3: R0 reshape (recorder-suffix coupling + ValidPlacement
  generalization + SelfPresent wiring), then the R-obligation landing order (§5), gasfree
  co-flagship mid-sequence, R12 concrete witness last.
- **Step 5 [post-closure]**: consolidation (Corr hoisting, LowerConforms split, landing-lemma
  factoring) + Phase 5 Asm layer extraction → the IR #2 kit + memory/allocator/data-segments
  per §7 ordering.

## 11. Report-integrity notes

- The audit's "headline is a conditional over un-built runtime facts" is now sharpened to
  "vacuous": update `audit-2026-07-02.md` readers accordingly (this doc is the correction of
  record; the audit file is kept as history).
- `p5-walk-status` / EXPERIMENT-REPORT claims of "headline REACHED (green, axiom-clean)" remain
  true as build facts but must not be read as conformance facts — the honest status is: the walk
  machinery is real and salvageable; the tie interface it was fed is unsatisfiable; Phase 3 with
  R0 is where the theorem becomes true-and-meaningful.
