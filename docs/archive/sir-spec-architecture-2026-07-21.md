# SIR code organization — spec/support separation, naming, AGENTS.md

> **Archived 2026-07-23 — superseded.** The layout this plan proposes was
> executed and then evolved under review: blocks now nest inside functions,
> `iret` steps to a `returned` control (there is no `ReturnsFrom`), and
> `Step` no longer depends on `WellFormed` — so the file inventory and
> import-order claims below no longer match the code. Kept for the
> rationale record.

Date: 2026-07-21. Status: PROPOSAL v2 (adversarially reviewed against the code;
nothing moved yet).
Scope: the `sir/` package on `edu/sir-determinism` (mixed-step calls line), the
root `AGENTS.md`, and repo-root hygiene. Written to be executed by an
implementation agent as a mostly-mechanical reorg before the PR goes up.

Grounding inputs:
- Full read of `sir/` at `.worktrees/mixedstep` (15 modules, ~3k lines).
- Phil's feedback in `spec_feedback.md` (root), which independently states the
  same requirements this doc addresses: utility defs out of spec, proofs out of
  spec unless trivially short, methodical minimal comments, consistent oracle
  naming, WellFormed hypotheses justified or cut.
- The `002_ssa_cfg` local rules (`Spec.lean`/`Proof.lean` split) as precedent.
- A line-level adversarial review of v1 of this doc against the code; its
  corrections are folded in below.

---

## 1. The organizing principle

The spec/support boundary is **not** "who wrote it" (human vs agent) — that is
unenforceable and rots. The enforceable rule is:

> **The audit surface is the transitive closure of every exported theorem
> statement.** Any definition reachable from the *statement* (not proof) of an
> exported theorem, plus the IR/semantics definitions themselves, is spec.
> Everything else is support and must be quarantined where a reviewer never
> has to look.

This subsumes the human/agent distinction: an agent-coined definition (`QDiv`,
`MemOracleFree`, `StmtReady`) that appears in an exported statement is *already*
spec whether we like it or not — the only honest options are (a) promote it to
spec quality (real name, docstring, spec placement) or (b) reformulate the
theorem so it doesn't need it. What is *not* allowed is the current state:
spec-reachable definitions living in a file called `Metatheory.lean` with
cryptic names.

"Exported theorem" includes Examples-level results: the non-vacuity witnesses
(`initializedLoad_deterministic`, `zeroSizeStore_not_deterministic`,
`witnessAddProgram_runs`) are results a reviewer relies on, so their statements
must also be Spec-only (they already are today; keep it that way).

## 2. Target layout for `sir/`

Spec import order matters and is part of the design (Step depends on `ownedBy`
via `EvalFn.intro`, so WellFormed precedes Step):

```
sir/Sir/
  Spec/                  -- the audit surface; Phil reads this and only this
    Ir.lean              -- VarId/BlockId/FunctionId, Expr, Stmt, Terminator,
                         --   BasicBlock, Function, Program  (Core/Types + IR/CFG)
    State.lean           -- World, Allocation/MemoryState, Locals, Globals,
                         --   MachineState, cursor/control/BlockPosition, IRError,
                         --   Event/Trace, CallContext/CallInput/CallResult/CallRecord,
                         --   Program.block?/function?/paramsOf,
                         --   BasicBlock.absoluteToPosition/startPosition,
                         --   Program.decodeStmt/terminatorAt, the MonadLift
                         --   instances (scoped into Sir; see §6 hygiene note)
    WellFormed.lean      -- Program.ownedBy, callEdge, Program.WellFormed,
                         --   readiness predicates (Locals.Defined, ExprReady,
                         --   StmtReady, JumpReady, TerminatorReady)
    Step.lean            -- Expr.eval + eval_* per-statement transitions (defs
                         --   only), SmallStep / Steps / EvalFn
    Run.lean             -- entryState, Runs / RunsTo / RunsInit / RunsMain
    Observation.lean     -- Event.query, Query, ObservableOutcome,
                         --   NextObservableEffect, DeterministicFrom /
                         --   Deterministic, Trace.QueryDivergence (né QDiv),
                         --   Program.MemOracleFree, Stmt.isMemOracle
    Interp.lean          -- Oracle, InterpM, interpCallee, interpStmt,
                         --   interpSteps, interpFn, interpRun
  Theorems.lean          -- ALL exported results, statements in Spec vocabulary
                         --   only, proofs are one-line delegations into Proofs/
  Proofs/                -- machinery; layered to respect actual dependencies:
    Steps.lean           -- Steps.inductionOn (@[elab_as_elim]), single/trans/
                         --   head, head_decomp, Stuck, eq_of_stuck,
                         --   stuck_of_halted, stuck_at_iret,
                         --   decodeStmt_mem, decodeStmt_next_block,
                         --   terminatorAt_inv, decodeStmt_terminatorAt_exclusive,
                         --   MemOracleFree.not_mallocUninit/not_mload32
    StepDet.lean         -- smallStep_*_det, smallStep_call_constructor_det,
                         --   eval_call_ok / eval_call_record_result /
                         --   eval_call_record_input (moved out of Eval.lean)
    Dialogue.lean        -- StepDialogue/RunDialogue/FnDialogue, dialogue_*
                         --   per-constructor lemmas, stepDialogue_all /
                         --   runDialogue_all / fnDialogue_all,
                         --   dialogue trichotomy engine
    Determinism.lean     -- query_eq_at, halted_no_event, stuck_trace_det,
                         --   prefix_det/trace_det internals, preserves_owned
                         --   (incl. eval_jump_control), deterministicFrom guts
    Progress.lean        -- eval_*_ok characterizations, eval_jump_ok,
                         --   Expr.eval_total, progress_stmt/terminator/nonIcall
                         --   internals
    WellFormed.lean      -- mapM_ok_size, Locals.bindValues_total,
                         --   WellFormed.icall_* / evalFn_arity internals
    Adequacy.lean        -- interpCallee_sound / interpStmt_sound /
                         --   interpSteps_sound internals (uses preserves_owned
                         --   from Proofs/Determinism.lean)
  Examples/
    TwoFunction.lean     -- witnessAddProgram + WellFormed witness + run
                         --   (merges Semantics/Witness.lean), constOracle +
                         --   interp_witnessAdd demo (moved out of Interp.lean)
    Memory.lean          -- initializedLoad / zeroSizeStore + their
                         --   (non-)determinism results (Examples/Determinism.lean;
                         --   keeps its confined BytecodeLayer.Hoare.MemAlgebra
                         --   import — nothing else in sir touches BytecodeLayer)
```

Dissolved files and where their content goes:
- `Core/Types.lean`, `IR/CFG.lean` → `Spec/Ir.lean`.
- `Semantics/{World,Memory,State}.lean` → `Spec/State.lean`.
- `Semantics/Eval.lean` → defs to `Spec/Step.lean`; its three multi-line
  theorems (`eval_call_ok`, `eval_call_record_result`, `eval_call_record_input`)
  to `Proofs/StepDet.lean` — they are case-bash proofs, not spec.
- `Semantics/SmallStep.lean` → the mutual inductives to `Spec/Step.lean`; the
  trailing theorems (`inductionOn`, `single`, `trans`, `head`) to
  `Proofs/Steps.lean`. (`trans` can additionally be surfaced in `Theorems.lean`
  if we consider trace concatenation a result worth exporting.)
- `Semantics/Run.lean` → `Spec/Run.lean` unchanged.
- `Semantics/Determinism.lean` → `Spec/Observation.lean` wholesale (it is all
  spec, including `Query`).
- `Semantics/Metatheory.lean` → split per the Proofs/ layering above; `QDiv`
  and `MemOracleFree` promoted to `Spec/Observation.lean`.
- `Semantics/DeterminismBridge.lean` → exported results to `Theorems.lean`,
  private lemmas to `Proofs/Determinism.lean`. "Bridge" is dev-narrative naming
  — it records that two agent tracks were reconciled, which is meaningless to a
  reader of the final code.
- `Semantics/WellFormedLemmas.lean` → readiness predicates to
  `Spec/WellFormed.lean`; everything else to `Proofs/{Progress,WellFormed}.lean`.
- `Semantics/Witness.lean`, `Examples/Determinism.lean` → `Examples/` as above.
- `Sir.lean` (root module) → rewritten: `import Sir.Theorems` +
  `import Sir.Examples.*` (its import list is the build root per
  `lakefile.lean` `roots := #[`Sir]`).
- `Main.lean` + the `lean_exe sir` stanza: **delete — it is already broken**
  (`Main.lean` references `hello`, which is defined nowhere; the exe target
  cannot compile and CI only builds the lib).

### What goes in Theorems.lean

The exported surface, restated in Spec vocabulary with one-line delegation
proofs. Current candidates:

- `Program.deterministic_of_memOracleFree` (the headline) and
  `MemOracleFree.deterministicFrom`.
- `Program.RunsTo.unique_or_queryDivergence` (né `dialogue_det`).
- `Steps.confluence_or_queryDivergence` (né `dialogue_trichotomy`),
  `Steps.prefix_confluence`.
- `SmallStep.prefix_det` / `SmallStep.trace_det`, `EvalFn.prefix_det` /
  `EvalFn.trace_det` (note: there is no `Steps.prefix_det`; keep the family
  prefixes explicit to avoid ambiguity).
- Progress: `progress_stmt`, `progress_terminator`, `progress_nonIcall`.
- Well-formedness consequences: `WellFormed.evalFn_arity`,
  `WellFormed.icall_step`.
- Adequacy: `interpSteps_sound`, `interpFn_sound`, `interpRun_sound`,
  `interpRun_sound_runsTo`.
- `Steps.preserves_owned` (used by adequacy but also a result in itself).

Policy for theorems that are both exported and internally consumed
(`preserves_owned`, the trichotomy, `prefix_confluence`): the proof lives in
`Proofs/` under the same statement; `Theorems.lean` restates with a one-line
delegation. Internal consumers call the `Proofs/` name; reviewers read
`Theorems.lean`. Mild duplication, and exactly what buys the clean surface.

On `Stuck`: today `stuck_trace_det`'s statement mentions `Stuck`, which would
drag it into Spec. Instead, reformulate the exported version in `RunsTo` terms
(final states with `control = .halted` — its only real use site applies it via
`stuck_of_halted`), and keep `Stuck` + the stuck lemmas Proofs-internal. If a
genuinely `Stuck`-shaped export turns out to be wanted later, promote `Stuck`
to Spec at that point, deliberately.

### Import discipline

- `Spec/*` imports only `Spec/*` (in the order Ir → State → WellFormed → Step
  → Run → Observation → Interp) and the `Evm` base. **No proofs in Spec beyond
  one-liners** (`Decidable` instances, `rfl`-lemmas needed for statements).
- `Theorems.lean` imports Spec + Proofs. Statements must elaborate against
  Spec alone.
- `Proofs/*` imports Spec and lower Proofs layers (Steps → StepDet → Dialogue
  → Determinism; Progress and WellFormed off Steps/StepDet; Adequacy on top).
- `Examples/*` imports anything.

Proof declarations keep their natural namespaces (`Sir.Steps.*`,
`Sir.Program.WellFormed.*`, …) — a `Sir.Proofs` namespace was considered and
rejected: it breaks dot-notation at dozens of call sites (`hwf.icall_paramsOf`,
`hu.eq_of_stuck`, `induction … using Steps.inductionOn`) for no real gain.
Enforcement is by *module*, not namespace:

### Enforcement (part of the reorg, not a later phase)

`Sir/Audit.lean`, CI-gated (precedent: exp005's `LirLean/Audit.lean` guard
net): for each theorem in `Theorems.lean` (and each Examples-level exported
result), walk the constants in its *type* and assert each resolves to a module
under `Sir.Spec` (or the Lean/Evm base). ~40 lines of meta code. This turns
"the audit surface is Spec + Theorems statements" from a promise into a build
failure, and is what lets agents keep working in `Proofs/` without review
anxiety.

## 3. Naming: the rename table

Principle (goes into AGENTS.md): **no coined abbreviations in spec
vocabulary.** A reviewer must be able to read a statement aloud. Agent
shorthand is fine inside `Proofs/` bodies; the moment a name crosses into a
statement it gets the full-word name and a docstring saying what it means
*and why it exists*.

| Current | Proposed | Note |
|---|---|---|
| `QDiv` | `Trace.QueryDivergence` | "identical prefix, then differing events that pose the same query". Name is fresh (no collisions in sir/ or EVM/). |
| `Program.RunsTo.dialogue_det` | `Program.RunsTo.unique_or_queryDivergence` | the headline; name should state the dichotomy, not the proof technique. |
| `Steps.dialogue_trichotomy` | `Steps.confluence_or_queryDivergence` | it is run-level confluence (the longer run passes through the shorter one's end state), not a mere trace-prefix statement — don't name it "prefix". |
| `Program.MemOracleFree` | keep (or `Program.NoMemoryOracles`) | fine either way; the *docstring* is what's missing (below). Define via `Stmt.isMemOracle`. |
| `eval_assign`, `eval_sstore`, … | `evalAssign`, … or keep | snake_case is off-house-style (Phil flagged oracle-naming inconsistency); batch-rename is cheap now, expensive later. Decide once, apply uniformly. |
| `smallStep_*_det`, `dialogue_*` | keep | Proofs-internal after the move (note: the `smallStep_*_det` family is currently *public*; it should not be re-exported). |
| `witnessAddProgram` etc. | keep | examples may be informal. |

The `MemOracleFree` docstring is load-bearing and currently absent. The reason
the hypothesis exists is subtle and *is the story of the determinism theorem*:

> gas and external-call oracle responses are **recorded in the trace** as
> events, so two runs consulting inconsistent oracles diverge *observably* —
> that is exactly `QueryDivergence`. The memory oracles (`mallocUninit`,
> `mload32`) answer **off the record**: no event is emitted, so runs can
> diverge silently and determinism-up-to-divergence is simply false for them
> (witness: `zeroSizeStore_not_deterministic` in `Examples/Memory.lean`).
> `MemOracleFree` carves out the fragment where the trace is a complete
> transcript of all nondeterminism.

That paragraph (tightened) belongs on the definition in `Spec/Observation.lean`.
This is the "methodical little-language comments" Phil asked for: one paragraph
of *why* on each spec concept, near-zero comments elsewhere.

## 4. `Program.WellFormed` readability and honesty

Phil's feedback (on the bytecode layer, but it transfers verbatim): "well-formed
is hard to understand ... very artificial. do we need all of these assumptions
and definitions?" Two treatments:

**(a) Shared vocabulary for the recurring shapes.** The genuinely repeated
pattern is not block/statement quantification (only `icallArity` has that
shape) but "the terminator of block `b`":

```lean
def Program.terminatorOf (p : Program) (b : BlockId) : Option Terminator :=
  (p.block? b).map (·.terminator)
```

hits 5+ sites today (`ownedBy` ×3, `iretArity`, `noEntryIret`,
`terminatorAt_inv`, the Witness proofs). Secondary, smaller win:

```lean
def Program.HasStmt (p : Program) (s : Stmt) : Prop :=
  ∃ b ∈ p.blocks, s ∈ b.statements
```

serves `icallArity`, `MemOracleFree`, and `callEdge`'s inner existential, and
gives `decodeStmt_mem` a clean statement. Both are readability helpers, not a
rewrite of every field.

**(b) Annotate every field with its consumer — or cut it.** Verified by grep
across the package:

| field | consumer |
|---|---|
| `icallArity` | `WellFormed.icall_paramsOf` (WellFormedLemmas.lean:45) |
| `iretArity` | `WellFormed.evalFn_arity` (WellFormedLemmas.lean:70) |
| `acyclicCalls` | **unconsumed** (proved for the witness, consumed nowhere) |
| `disjointCFGs` | **unconsumed** |
| `initEntryNullary` | **unconsumed** |
| `mainEntryNullary` | **unconsumed** |
| `noEntryIret` | **unconsumed** |

Some of the unconsumed five are real spec-intent (recursion-freedom mirrors a
Rust-side compiler invariant; entry-nullary matches the ABI). The honest states
are: consumed here, or explicitly marked in the docstring as an invariant
mirrored from the compiler / reserved for the lowering proof. An unconsumed,
unmarked hypothesis is exactly the "artificial" smell Phil called out — and an
invitation for a reviewer to ask whether the theorems secretly don't need
well-formedness at all. Decide per field (human decision), then annotate or
delete.

## 5. AGENTS.md rewrite

Current root `AGENTS.md` is conventions-plus-history. The conventions
(cruft rule, axiom-silence, reviewer standard, review-report rule) survive; the
experiment-pointer material goes. Proposed replacement outline:

```markdown
# AGENTS.md

This repo formalizes Plank's EVM IR (SIR) and its compilation to EVM bytecode
in Lean. Working code lives in EVM/ and sir/; experiments/ is a frozen archive.

## Layout
EVM/          bytecode layer (semantics, Hoare, assembler, conformance)
sir/          SIR: CFG IR + mixed-step semantics (small-step opcodes,
              big-step internal calls, oracle external calls)
experiments/  frozen exploratory lines — read for context, never extend
forks/        vendored reference repos (read-only)
docs/         planning/review/archive

## Spec architecture (applies to EVM/ and sir/)
- Audit surface = Spec/ + the statements in Theorems.lean (and any exported
  Examples results). The rule: every constant reachable from an exported
  theorem STATEMENT must live in Spec/. CI-enforced via the Audit metaprogram.
- Spec/ contains definitions and (at most) one-line proofs. All other proofs,
  proof-internal defs, and characterization lemmas live in Proofs/. Proofs
  never unfold spec defs directly — go through characterization lemmas.
- Theorems.lean holds exported results; proofs there are one-line delegations.
- New definitions land in Proofs/ by default. Promoting a definition into
  Spec/ is a human decision: it needs a full-word name (no coined
  abbreviations) and a docstring stating what it means and why it exists.
- Every WellFormed-style hypothesis field states its consumer in its
  docstring, or is marked as an invariant mirrored from the Rust compiler.

## Comments
Near-zero comments outside Spec/. In Spec/: one short paragraph of rationale
per concept ("why does this exist"), not restatements of the code.

## Hygiene
[cruft rule, sweep-on-rename, doc archival — carried over unchanged]

## Reporting
[axiom-silence rule, reviewer standard, lean-review-report rule — unchanged]
```

Notably *removed*: the per-experiment rules paragraph (subsumed: experiments
are frozen), the 002-specific pointer (its Spec/Proof rule is now the
repo-wide one, generalized).

## 6. Repo-root and misc hygiene (pre-PR)

The root directory currently shows a reviewer: `currentplan.md` (619 lines of
2026-06 orchestration state, explicitly stale), `HANDOFF.md`,
`EXPERIMENT-REPORT.md`, `spec_feedback.md`, `run-1783635643073.log`,
`smithers.db*`, `BOX.md`. Disposition:

- `currentplan.md`, `HANDOFF.md`, `EXPERIMENT-REPORT.md` → `docs/archive/`
  with the standard superseded-banner.
- `spec_feedback.md` → `docs/review/spec-feedback-<date>.md` (it's Phil's
  review input; keep, but not at root).
- `run-*.log`, `smithers.db*` → delete + `.gitignore`.
- `BOX.md` → `docs/reference/` if still accurate, else archive.

In-package hygiene caught during review:
- The `MonadLift (StateM σ) (StateT σ (Except ε))` instance at
  `State.lean:7` sits in the **root namespace** — a global instance leak.
  Scope it (`namespace Sir` or `scoped instance`).
- `Main.lean`'s broken `hello` reference (see §2) — delete with the exe.

## 7. Sequencing

1. Eduardo signs off on layout + rename table + per-field WellFormed decisions
   (this doc).
2. Mechanical reorg on the mixed-step branch by the codex implementer.
   One commit per phase — moves ≠ renames ≠ WellFormed-field audit ≠
   Audit.lean — so review stays sane.
3. AGENTS.md replacement + root hygiene.
4. `lean-review-report` run over the reorganized package → the PR narrative.
5. PR.

Explicitly out of scope here: any change to the semantics themselves (Steps
head-vs-tail flip, frameless-icall discussion with Phil's PR#8) — those are
separate conversations and should not ride a reorg PR.

## Addendum — 2026-07-21

The interpreter and adequacy layer described in §2 was removed from the working
branch as out of scope for the mixed-step specification. It is preserved on
branch `edu/sir-interp-adequacy` for possible future use, such as differential
testing against the SIR compiler's evaluator.
