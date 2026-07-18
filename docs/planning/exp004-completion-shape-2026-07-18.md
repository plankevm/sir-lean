# exp004 completion study — the B3/B4 shape report (2026-07-18)

**Status**: study complete; three tracks built, reviewed, one mustFix applied; build green
(verified 2026-07-18: `lake build` in `experiments/004_nested_evmyul/`, exactly 3 sorry
warnings, all classified). Nothing committed; all work sits uncommitted on
`codex/sir-internal-functions`. The three new files are LABELED EXPLORATORY SHAPE STUDIES
that deliberately suspend the house proof-first/no-sorry rule — **they are not foundations
to build on**, and this report is their deliverable.

**The one question**: is nested-native reasoning — theorems over the recursive-function
`Θ/Ξ/X/step/call` semantics (`EVMYulLean/EvmYul/EVM/Semantics.lean:139-821`) — ergonomic,
now that the B3 reasoning layer (PLAN.md:43-45, never previously attempted) has finally been
built? And how does its shape compare to the flat layer's paid-for
`Runs`/`Runs.call`/`runs_*` surface (`EVM/BytecodeLayer/Hoare.lean`)? This is the missing
data point flagged in `docs/planning/sir-memory-model-frames-mixed-step-2026-07-17.md` §4e
("since B3 was never built, the repo has NO data point on nested-native reasoning").

**One-paragraph answer**: nested-native reasoning is ergonomic at exactly two altitudes and
a logic-free zone at the third. *Below the caller* (procedure specs, call-site rule, framing,
two-call composition) the ∀-fuel Hoare encoding is cheap — the whole surface closed
sorry-free, including the two inversions pre-classified as medium. *Above the caller* (triple
→ observable) it is pure plumbing — `rw`+`rfl` projection lemmas. *Inside the caller* (the
straight-line code between two CALLs) there is no vocabulary at all: no per-opcode step
rules, no loop-decomposition lemma, and the naive way of even *stating* the call-site tie is
refutable. Additionally, the fuel-existential relational encoding (but NOT the ∀-fuel one)
pays a one-time keystone tax — a 6-layer fuel-irrelevance mutual induction — that the flat
single-interpreter drive never pays. "Nested was harder" was about incidentals plus one
identifiable, avoidable encoding choice — not about nesting itself.

---

## 1. What was built

Three new files under `experiments/004_nested_evmyul/NestedEvmYul/` (auto-included by the
lakefile's `.andSubmodules` glob — no lakefile edit), 1043 lines total, importing only
existing modules; nothing under `EVMYulLean/` or `NeverOutOfFuel.lean` touched.

### T1 — `ThetaRuns.lean` (246 lines): fuel-existential relational veneer

`ΘRuns w res := ∃ fuel, Θ fuel … = .ok res` — the graph closure of `Θ` over
`NestedWorld`/`ThetaResult`, the nested analog of putting a relation above an interpreter.

| Statement | Status | Note |
|---|---|---|
| `ΘRuns` (def), `ΘRuns.intro`, `ΘRuns.of_runΘ` | PROVED | pure `∃`/`Except` logic |
| `ΘRuns_doNothing` (non-vacuity) | PROVED | rides the closed `runΘ_doNothing` |
| `Θ_fuel_mono_ok` (:150) | **SORRY — hard** | the keystone: fuel-irrelevance of `.ok` results |
| `Θ_fuel_mono_error` (:168) | **SORRY — hard** | error half; same bundled induction, marginal cost ≈ 0 |
| `ΘRuns.deterministic` | PROVED given keystone | lift both witnesses to `max f₁ f₂` |
| `ΘRuns.runΘ_complete` (adequacy, `e ≤ 1024`) | PROVED given keystone | OOF arm killed by closed `runΘ_never_outOfFuel` |
| `ΘRuns.total_of_adequate` | PROVED sorry-free | totality up to semantic error; no keystone needed |

The keystone is a fresh 6-layer `res_mono` mutual strong induction over
`step`/`call`/`Θ`/`Ξ`/`Lambda`/`X`, mirroring `gas_mono`'s shape
(NeverOutOfFuel.lean:4018-4133) but proving a different invariant — nothing existing
transports a *result* across fuels. The full per-layer predicate skeleton is written as a
comment in the file (ThetaRuns.lean:86-143); the real cost is re-proving the ~1500-line
Stage-1 per-arm helper family (`call_result_gas_le`:2542 … `X_loop_gas_le_bdd`:3968) for
result-stability while dodging `step`'s 140-arm match. Reviewer independently verified the
statement is TRUE (every layer's fuel-zero arm is exactly `.error .OutOfFuel`; decremented
fuel appears only in recursive-call positions), so this is priced work, not a wrong statement.

### T2 — `XiTriple.lean` (419 lines): the B3 milestone proper — **ZERO sorries**

`XiTriple P I Q` and `ThetaTriple P c Q` are success-only partial-correctness triples
quantified over **all** fuels (revert/error/OOF vacuous; `ThetaTriple` gated on `z = true`,
`P` over the PRE-transfer `σ` — a flagged design decision).

| Statement | Status | Note |
|---|---|---|
| `XiTriple`, `ThetaTriple` (defs) | — | ∀-fuel; no monotonicity keystone by construction |
| `conseq` / `conj` (both triples) | PROVED | pure logic, 4-10 lines each; conj feeds the SAME fuel into both |
| `PreservesAccount` (def) + `XiTriple.frame` | PROVED | semantic footprint; frame rule is definition-chasing |
| `Xi_one`, `X_one_stop`, `Xi_two_stop` (helpers) | PROVED | small-fuel garbage arms for the witness below |
| `preservesAccount_stop` (non-vacuity) | PROVED | fuels 0/1/2 vacuous; `f+3` via closed `Refinement.Xi_stop` |
| `theta_of_xi` (Ξ-triple ⇒ Θ-triple) | **PROVED** | planned SORRY-CLASS medium — closed instead |
| `call_spec` (the call-site rule) | **PROVED** | planned medium — closed (`maxHeartbeats 2000000`) |
| `twoCall_spec` (two-call composition) | PROVED | literally `⟨call_spec …, call_spec …⟩` |

Reviewer independently confirmed via `#print axioms`: all of the above depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorryAx` — and the two inversions are genuine
(no degenerate-definition cheats). The `NeverOutOfFuel.call_result_gas_le` inversion recipe
(`simp only [f, bind, Except.bind]` + `split at` + constructor injection, never opening
`step`'s match) transferred verbatim to the `Θ` and `call` do-blocks. `call_spec`'s key shape
fact: `x = ⟨1⟩` forces both `z = true` and the covered Θ-branch, so the rule carries no
balance/depth side conditions.

### T3 — `ObservableTriple.lean` (378 lines): B4 seed + the honest gap statement

| Statement | Status | Note |
|---|---|---|
| `completedWith` (def) | — | flat `Outcome.completedWith` analog at `SharedObservable` altitude |
| `observe_ok_tag`, `observe_storageAt` | PROVED | each literally `rw [h]; rfl` |
| `completedWith_of_thetaTriple` | PROVED sorry-free | T2 triple → observable: pure plumbing |
| `doNothing_completedWith` | PROVED sorry-free | inhabited instance via `nested_refines_emptyObs` |
| `ΘRuns_completedWith` | PROVED given T1 keystone | inherits the sorry transitively (disclosed; `sorryAx` confirmed) |
| `IterStep`, `IterCallStep`, `IterHalt`, `Iters`, `callerEntry` | stated only | seed vocabulary for the missing X-loop logic |
| `nested_twoCall_completedWith` (:287) | **SORRY — hard** | the endgame; its shape IS the finding (§2.3) |

Review round: the endgame statement was initially **vacuous** (call outputs shared endpoint
states with `step` successors — contradictory, since every `step` `.ok` successor carries the
unconditional `execLength + 1` bump at Semantics.lean:234 while `call` outputs preserve
`execLength`/`pc`/stack). Fixed: fresh output states `evR₁`/`evR₂`, CALL-pinned
`IterCallStep`, and the refutability argument recorded as a sharpened finding (§2.3).

Final sorry census: **3** — T1's keystone pair (one bundled induction) + T3's endgame. All
`SORRY-CLASS: hard`, all with reasons; `grep -n sorry` matches the classified list exactly.

## 2. Ergonomics findings

### 2.1 Where the function encoding helped

- **∀-fuel triples are fuel-free for free** — the study's cheap trick. A universal-fuel
  triple never transports a result across fuels: composition feeds the outer run's own fuel
  into the inner hypothesis. The entire logical layer (conseq/conj/frame) is pure logic with
  zero semantics contact, and `twoCall_spec` is two function applications plus `And.intro` —
  versus flat's *earned* `Runs.call`/`Runs.trans` machinery (Hoare.lean:140-170).
- **The do-block inversion recipe transfers verbatim.** Both pre-classified-medium proofs
  (`theta_of_xi`, `call_spec`) closed in one session each: the structured `Except`-do bodies
  of `Θ` and `call` are genuinely invertible with `simp only [·, bind, Except.bind]` +
  `split at` + injection, without ever opening `step`'s 140-arm match. The medium
  classification was an overestimate; the T1-proved recipe absorbed the cost.
- **The relational veneer is ~free within one fuel witness.** T1's def + intro + non-vacuity
  + totality took zero unfolding of the semantics (~50 lines of proof riding two
  already-closed theorems). `total_of_adequate` sorry-free is a genuine free win: totality
  quantifies over one drive, so no cross-fuel transport arises.
- **The observable layer earns its keep.** Both T3 projection lemmas close with literally
  `rw [h]; rfl` (the `.ok (…, true, …)` literal reduces `observe_nested`'s match/ite
  definitionally); phrasing storage predicates in the def's own source syntax dodges all
  RBMap theory. Triple-to-observable is one instantiation — no transport.
- **Semantic framing is statable without an opcode sweep.** `PreservesAccount` needs no
  syntactic writes-analysis to state, and the frame rule is trivial (discharging footprints
  is another matter — §2.3).

### 2.2 Where it fought — the keystone tax (existential encoding only)

Every cross-fuel statement on T1's `∃ fuel` encoding — determinism, adequacy, veneer →
observable, any future gluing — funnels through the single unproved fuel-irrelevance
keystone: a fresh 6-layer mutual strong induction whose real cost is re-proving the
~1500-line Stage-1 helper family for result-stability. On a flat single-interpreter drive,
determinism is definitional (one function, one run) and fuel never appears at the spec level,
so this induction is a **nested-native tax with no flat counterpart** — paid once, after
which the relational surface is as cheap as the flat one. The T2-vs-T1 side-by-side in T3 is
the cleanest contrast in the study: `completedWith_of_thetaTriple` (∀-fuel route) reaches the
observable axiom-clean by pure instantiation, while `ΘRuns_completedWith` (existential route)
reaches the *same conclusion* dragging the keystone's `sorryAx`. **The tax is a property of
the existential encoding, not of nesting**: pick ∀-fuel triples and it never falls due.

Lesser frictions, precisely located:

- **19-positional-argument `Θ` signature** — each keystone application is a wall of ~21
  underscores, four times over in T1; `completedWith_of_thetaTriple` has a 25-underscore
  instantiation. `NestedWorld` bundling contains it at the veneer layer, but the keystone
  statements must stay unbundled for the induction. Clerical, intrinsic to the vendored
  signature.
- **Small-fuel garbage arms** — a nested-only tax that scales per-program:
  `preservesAccount_stop` needed three bespoke evaluation lemmas (`Xi_one`, `X_one_stop`,
  `Xi_two_stop`) just to kill fuels 1/2 before the closed `Xi_stop` shape at `f+3` applies.
- **Tuple noise** — `Θ`'s raw 6-tuple result forces quintuple `Prod.mk.injEq` rewrites and
  `res.2.2.2.2.1` projections; readable statements, ugly proofs.
- **Minor**: one `maxHeartbeats 2000000` crank (`call_spec`); a `cases`-motive quirk on
  `runΘ w`; `whnf` leaving tuple-projection forms where `decide` fails but
  `Bool.noConfusion` + `show`-ascription succeeds; `theta_of_xi` shifting the transfer
  preamble and `σ'' == ∅` rollback onto client-supplied `habsorb`/`hroll` hypotheses (honest
  for a shape study; a real foundation would want canonical wp-style handling).

### 2.3 The headline negative result: the caller is a logic-free zone

The Hoare surface is **consumer-only**. Nothing in it can *produce* a success run, discharge
a `PreservesAccount` for nontrivial code, or establish the mid-sandwich `P₂ ev₂` between two
calls. The full B4 endgame (`nested_twoCall_completedWith`, the mirror of flat
`twoCall_completedWith`, TwoCallExample.lean:103) is blocked on three missing pieces, none of
which exist:

1. **X loop-decomposition** — `Iters` + `IterHalt` → `X fuel … = .ok (.success …)` at all
   sufficient fuels: a fresh induction over `X`'s fuel recursion, PLUS fuel transport for
   each `IterStep`'s private `∃ f` step-fuel witness — T1's keystone again, resurfacing even
   on the ∀-fuel route the moment individual steps are decomposed.
2. **The step-CALL-arm tie** — linking an `IterCallStep` to the `call`/`Θ` recursion. The
   sharpened finding (T3 review round): below per-opcode granularity the vocabulary is not
   merely lemma-poor — **naive statements about it are wrong**. Sharing endpoints between the
   `call` equation and the `IterStep` successor is refutable outright (`execLength` bump vs
   preservation), because `step`'s real CALL arm invokes `call` on the post-`Z` bumped state
   and then applies `replaceStackAndIncrPC`, so a raw `call` output is never a `step`
   successor. The tie is exactly `step`'s CALL arm, unreachable without opening the 140-arm
   match per-opcode.
3. **Q-propagation/framing through the middle and suffix segments** to derive the halt-state
   storage fact — flat does this with `runs_*` + framing; nested has the frame *rule* but
   nothing to discharge footprints per-opcode.

Between its two CALLs, the caller's straight-line code has no reasoning surface: its
intermediate states can only be hypothesized, never derived. That missing X-loop program
logic — which flat has (`runs_push1` … `runs_mload`, Hoare.lean:364-620) and nested lacks —
is the entire remaining distance from B3-shaped triples to the B4 observable endgame.

## 3. Comparison against the flat surface

| Concern | Flat (`EVM/BytecodeLayer/Hoare.lean`) | Nested (this study) |
|---|---|---|
| Determinism | definitional (one drive) | keystone-gated on `∃ fuel`; N/A on ∀-fuel triples |
| Cross-fuel transport | never arises | the one hard keystone (existential encoding only) |
| Call composition | earned: `Runs.call` + `CallReturns` + `Runs.trans` | free: `call_spec` twice + `And.intro` |
| Logical rules (conseq/conj/frame) | comparable | pure logic, 4-10 lines |
| Per-opcode program logic | **exists** — `runs_*` family | **absent** — the headline gap |
| Middle-of-sandwich discharge | `hmiddle` dischargeable via `runs_*` | `hP₂ ev₂` hypothesis-only, underivable |
| Call-site tie statement | `CallReturns` (consistent by construction) | naive shape refutable; needs step's CALL arm |
| Observable link | `twoCall_completedWith` closed | projection lemmas `rw`+`rfl`; endgame blocked on the gap |
| Small-fuel garbage cases | none (no fuel) | per-program tax (`Xi_one`/`Xi_two_stop` pattern) |
| Signature ergonomics | `Frame` records | 19 positional args, 6-tuple results |

Net: the two surfaces have **complementary** cost profiles. Flat paid up front for a
per-opcode step vocabulary and got composition wired through `Runs`; nested gets composition
free from ∀-fuel quantification but never built the per-opcode vocabulary. Neither cost is
fundamental to its encoding — flat could have skipped `runs_*` (and been equally stuck at
callers), and nested could build an X-loop logic (and reach the endgame).

## 4. Verdict on the §4e historical question

**"Nested is harder" was about incidentals and one avoidable encoding choice, not about
nesting.** With the B3 data point in hand:

- The §4e fleet verdict ("not evidence against nested relational edges") is **confirmed and
  strengthened**. The nested recursion itself was never the obstacle: the call-site rule, the
  procedure-spec layer, and two-call composition — precisely the things nesting was feared to
  complicate — turned out *cheaper* than flat's equivalents, closing sorry-free in one
  session each. The recursion boundary (`call` → `Θ`) inverts cleanly with a stock recipe.
- The genuine nested-specific taxes are now precisely enumerated: (a) the fuel-irrelevance
  keystone — but only for fuel-*existential* relational encodings, avoidable by ∀-fuel
  quantification, and of the same "mechanization cost, not complexity-class blowup" character
  as the already-closed never-OOF proof; (b) small-fuel garbage arms; (c) the vendored
  signature/tuple clerical drag — an incidental of the port, not of nesting.
- The one *shared* wall is not about nesting at all: per-opcode program logic must be built
  under either encoding, and exp004 simply never built it. The 140-arm unabstracted match
  (already tagged incidental in §4e) makes building it expensive here — but flat paid the
  same kind of bill for `runs_*`, one opcode at a time.
- One finding §4e could not have anticipated: at sub-opcode granularity the recursive-
  function encoding is **actively treacherous to specify against** — the refutable call-site
  tie shows that plausible-looking statements about interpreter internals can be false for
  bookkeeping reasons (`execLength` bumps) invisible without opening the match. Relations
  built above the function must sit at opcode granularity or above.

## 5. Implications for the SIR mixed-step rebuild

SIR's mixed-step derivation trees (§4c′: relation-encoded because oracles forbid the function
encoding) are the *third* encoding of the same tree. The study's transferable lessons:

1. **Quantifier discipline is the whole ballgame for fuel-like indices.** If any fuel/depth/
   step-count index survives into SIR's judgments, put hypotheses in ∀-form and conclusions
   in a form that never demands cross-index transport — or budget a `res_mono`-shaped
   induction on day one. SIR's relational `Steps` (refl+tail, per the PR#2 decision) has no
   fuel, which dissolves the entire T1 keystone class by construction — a point *for* the
   relation-native choice.
2. **Build the per-instruction rule family with the semantics, not after.** The single
   largest asymmetry in this study is flat's `runs_*` vs nested's nothing. For SIR: every
   instruction's small-step rule should ship with its inversion/forward lemma as it lands.
   This is the cheap-when-fresh, prohibitive-when-retrofitted item.
3. **Make the call edge a first-class relation constructor.** Flat's `CallReturns` and SIR's
   nested call edge state the caller/callee tie *by construction*; the nested-function side
   had to reverse-engineer it out of `step`'s CALL arm and got a refutable statement on the
   first try. Relation encodings are immune to this failure mode — the constructor IS the
   tie. This is the strongest single point in favor of SIR's mixed-step trees.
4. **Semantic footprints are statable for free but dischargeable only per-instruction.**
   `PreservesAccount`'s lesson for SIR's frame/separation story (§5 of the mixed-step doc):
   the frame *rule* will be trivial; budget for the per-instruction preservation lemmas that
   feed it, or a writes-analysis + soundness proof.
5. **Keep an observable altitude.** The `rw`+`rfl` projection-lemma pattern (pin the
   observable's read shape once; phrase all postconditions in that exact syntax) transfers
   directly and is cheap insurance against map/lookup theory leaking into specs.

None of this changes the mixed-step plan of record; it removes the last empirical excuse for
fearing the nested/tree shape, and sharpens where the real budget goes (per-instruction
rules), which the mixed-step PR should front-load.

## 6. Honest limitations

- **Sorry density is load-bearing.** The two flagship T1 theorems (`ΘRuns.deterministic`,
  `ΘRuns.runΘ_complete`) and T3's `ΘRuns_completedWith` carry no syntactic sorry but inherit
  the keystone's `sorryAx` transitively — `lake build` output under-reports this; anyone
  citing them must run `#print axioms`. The keystone was *priced* (skeleton + helper-family
  estimate, statement independently verified true), not *paid*; the "one induction, paid
  once, then parity with flat" claim is a well-grounded projection, not a theorem.
- **The endgame sorry is a statement, not a near-proof.** `nested_twoCall_completedWith`'s
  hypotheses (`Iters` segments, `IterCallStep`s, `hread`) are supplied, not derivable; the
  seed vocabulary (`IterStep` etc.) has zero lemmas. `IterStep` also requires `decode = some`
  whereas `X` treats undecodable bytes as STOP via `.getD` — a fidelity gap acceptable for
  stated-only vocabulary.
- **Not attempted**: the X-loop program logic itself (any single `runs_*`-analog); an
  end-to-end demo that `call` returns `.ok (⟨1⟩, ev')` on concrete code (the Θ-level
  `z = true` witness exists via `runΘ_doNothing`, so a call-level demo is plausibly one
  inversion away — the call-site rules currently lack a firing demo); CREATE/`Lambda`
  anywhere; a post-transfer-`σ₁` `ThetaTriple` variant (the pre-transfer choice trades
  `theta_of_xi` fiddliness for call-site readability — only one point was sampled); wp-style
  handling of Θ's preamble/rollback (absorbed into client hypotheses); a concrete
  instantiated `IsDoNothing` world (non-vacuity is conditional on satisfiability, which is
  obvious but unwitnessed here).
- **Single-sample caveat**: T2's "medium was an overestimate" rests on two inversions by one
  recipe on two structured do-bodies; opcodes whose semantics live *inside* the 140-arm
  match were deliberately never opened, and everything hard about them remains unmeasured —
  that is exactly the unbuilt X-loop logic.
- `completedWith` is the spec-dictated tag+storage analog of flat's `Outcome.completedWith`
  at `SharedObservable` altitude, not a syntactically verbatim mirror (flat's is an ∃-form
  over `Outcome`).

## File index

- `experiments/004_nested_evmyul/NestedEvmYul/ThetaRuns.lean` — T1 (2 sorries: :150, :168)
- `experiments/004_nested_evmyul/NestedEvmYul/XiTriple.lean` — T2 (0 sorries)
- `experiments/004_nested_evmyul/NestedEvmYul/ObservableTriple.lean` — T3 (1 sorry: :287)
- Flat comparanda: `EVM/BytecodeLayer/Hoare.lean`,
  `EVM/BytecodeLayer/Examples/TwoCallExample.lean`
- Question provenance: `docs/planning/sir-memory-model-frames-mixed-step-2026-07-17.md` §4e

---

## Addendum (overnight run, T1 — X-loop program logic, 2026-07-18)

**Status: LANDED, sorry-free, axiom-clean.** The "logic-free zone" of §2.3/§6 is now
colonized: `experiments/004_nested_evmyul/NestedEvmYul/XLoop.lean` (new file, 0 sorries;
`#print axioms` on `X_decompose`/`X_branch`/`step_call_eq`/`X_sstore`/`X_jumpi_taken`/
`IterHaltU.stop`/`ItersN_X` all report exactly `[propext, Classical.choice, Quot.sound]`).
Repo-wide census unchanged at 3 sorries (ThetaRuns :150/:168 keystone pair,
ObservableTriple endgame — untouched, per track ground rules; its line number shifted
:287 → :298 from the SUPERSEDED pointer comment added above the seed vocabulary).

### What tonight's proofs CONFIRMED from the study

- **The dispatcher-equation bet (the "incantation" question) — confirmed, stronger than
  priced.** For every concrete non-CALL/CREATE opcode tried (PUSH1, PUSH0, SSTORE, JUMP,
  JUMPI, STOP), `EVM.step (f+1) cost (some (op, arg)) s = EvmYul.step op arg (debit s cost)`
  closes by bare `rfl` — the 140-arm match reduces through one concrete-constructor arm
  during unification, exactly as `gas_EvmYul_step`'s sweep predicted (PLAN.md:540-543). No
  heartbeat crank was needed **anywhere in the file** (no `set_option maxHeartbeats` at all).
  §6's "everything hard about the 140-arm match remains unmeasured" is now measured: it costs
  `rfl`.
- **∀-fuel rules for free — confirmed.** The dispatcher RHS never mentions `f`, so every
  per-opcode rule is `∀ f, X (f+2) vj s = X (f+1) vj s'` with `s'` explicit, and the
  sequencing vocabulary (`IterStepU`/`IterHaltU`) carries a fuel-*universal* step clause
  dischargeable by those rules. The study's `∃ f` fuel-transport trap (diagnosis point (1) of
  the endgame sorry) is structurally dead: `X_decompose` is pure Nat-offset bookkeeping
  (`ItersN_X` + one halting iteration), no fuel transport anywhere. **Consequence: the
  keystone (`Θ_fuel_mono_ok`, the ~1500-line priced induction) is NOT needed for the
  per-opcode/decomposition layer.** It remains priced-not-paid, but its blast radius shrinks
  to the fuel-existential `ΘRuns` veneer only (T4 decides whether it is needed at all).
- **The execLength-bump refutation — confirmed and now stated correctly.** `step_call_eq`
  (proved, `rfl` after stack destructuring) exposes the CALL arm as `call f cost … (bump s)`
  (bump = execLength+1 only, **no gas pre-debit** — unlike the default arm's `debit`)
  post-processed by `replaceStackAndIncrPC (rest.push x)`. The raw `call` output is indeed
  never a `step` successor; the consistent tie the study said was unstatable without opening
  the match is now a theorem.
- **The `.getD` fidelity gap — confirmed as real and fixed.** All XLoop decode hypotheses go
  through `X`'s own `decode … |>.getD (.STOP, .none)` read; the study's `IterStep`
  (`decode = some`) is marked SUPERSEDED in ObservableTriple.lean (kept verbatim as labeled
  artifact until T4 retires it against the new vocabulary).

### What tonight's proofs CORRECTED

- **The planned `X_decompose` fuel offset was off by one.** The track spec's
  `X (f + n + 1)` shape is wrong at `f = 0` (the halting iteration's `step` needs positive
  fuel *inside* `X (f+1)`); the proved statement is
  `ItersN vj n s sEnd → IterHaltU vj sEnd sHalt out → ∀ f, X (f + n + 2) vj s = .ok (.success sHalt out)`.
- **Two technique notes vs. the recipe sheet:** (a) `unfold X` unfolds *every* `X`
  occurrence including the RHS target — the working incantation is `conv_lhs => unfold X`
  then `simp only [bind, Except.bind]` + `rw` the four hypotheses with `simp only []` iota
  steps between; (b) the shared-arm forward lemmas close by
  `obtain ⟨sh, pc, stk, el⟩ := s; dsimp only at hstk; subst hstk; rfl` (concrete cons-cells
  let `pop*` reduce) — no `show`-ascription/`Bool.noConfusion` gymnastics were needed.
- **One new instance was required:** `LawfulBEq UInt256` (derived `BEq` compares the wrapped
  lawful `Fin`s) to route JUMPI's `μ₁ != ⟨0⟩` guard through `bne_iff_ne`. Lives in
  `NestedEvmYul.XLoop`; harmless if the vendor later ships one (instance resolution will
  prefer either consistently — revisit only if a diamond ever surfaces).

### Parity status vs docs/flat-vs-nested-convergence.md §1.3/§1.4

Nested column GAINS (all proved, ∀-fuel): per-opcode rules (`X_push1`, `X_push0`,
`X_sstore`, `X_jump`, `X_jumpi_taken`, `X_jumpi_fallthrough` — the parity list's
load-bearing SSTORE + JUMP/JUMPI pair included), the branch combinator (`X_branch`,
flat `runs_branch` analog), sequencing/decomposition (`ItersN.single/.trans`, `ItersN_X`,
`X_decompose` — flat `Runs.trans`/`drive_reconcile` analog), and the CALL-arm dispatcher
equation (`step_call_eq`, the call-site tie's `step` half; the full tie + endgame observable
theorem are T4's). STILL ABSENT vs flat: the `Behaves`-style for-all-programs predicate and
the `messageCall`-bridge analog — that is the residual gap; tonight's work does NOT claim
full parity.

## Overnight addendum — T2 (forall-fuel pivot of the ΘRuns veneer), 2026-07-18

Build green (exit 0), sorry census unchanged at exactly 3 — now all fenced: the quarantined
keystone pair (ThetaRuns.lean:349/:367, inside `section DeprecatedFuelExistential`) plus the
endgame statement (ObservableTriple.lean:294). `#print axioms` on `ΘRuns.deterministic`,
`ΘRuns.runΘ_complete'`, `Θ_doNothing`, `ΘRuns_doNothing`, `ΘRuns_doNothing_runΘ`, and the
migrated `ΘRuns_completedWith`: all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### What tonight's proofs CONFIRMED from the study

- **The offset-cofinal re-encoding kills the veneer's keystone tax — confirmed.**
  `ΘRuns w res := ∃ k, ∀ f, Θ (k + f) ⟨19 args⟩ = .ok res` makes determinism a 6-line pure
  instantiation (each witness at the other's offset + one `Nat.add_comm` + `Except.ok.inj`)
  and adequacy-under-side-condition (`k ≤ seedFuel w`, instantiate `f := seedFuel w - k`)
  a 3-line proof. The study's headline claim — "every cross-fuel lemma funnels through the
  ~1500-line fuel-irrelevance keystone" — was true *of the existential encoding only*; the
  cofinal encoding needs no transport at all. The keystone's blast radius is now exactly the
  quarantined section (T4 proves-or-deletes).
- **Shape lemmas are naturally cofinal producers — confirmed.** `Xi_stop` was already
  `∀ f, Ξ (f+3) … = .ok …`-shaped; the only work to make the do-nothing world a cofinal
  witness was hoisting the per-fuel existential witnesses OUT of the fuel quantifier
  (`step_stop_cofinal`/`X_stop_cofinal`/`Xi_stop_cofinal`), which is definitional because
  T1's `XLoop.step_eq_shared_stop` RHS is fuel-free — the T1 dispatcher-equation technique
  paying off a second time. `Θ_doNothing` (∀-fuel at offset 4, one Θ-peel mirroring
  `runΘ_doNothing`'s simp recipe + terminal `rfl`) then gives `ΘRuns_doNothing` with witness
  `k := 4`, connected to `runΘ` by `4 ≤ seedFuel w` (`fuelBound_pos` + omega).

### What tonight's proofs CORRECTED / what the pivot honestly gives up

- **The ∀-encoding surrenders single-point introduction and unconditional adequacy.**
  `of_runΘ` (one fueled success enters the veneer) and keystone-backed unconditional
  `runΘ_complete` exist only for the quarantined `ΘRunsE`. A bare `runΘ w = .ok res` does
  NOT enter the new veneer; producers must supply cofinal witnesses. The `k ≤ seedFuel w`
  side condition is irremovable without the keystone (`runΘ_never_outOfFuel` excludes one
  error at one seeding; it transports nothing) — this is the API's honest boundary, priced
  in docstrings, not papered over.
- **Consumer migration is a signature change, not a proof change.**
  `ΘRuns_completedWith` now takes the explicit offset `k`, `k ≤ seedFuel w`, and the
  cofinal family (the `∃ k` bundle can't carry the side condition); its body is the same
  two projection lemmas over `ΘRuns.runΘ_complete'`. It drops the old `w.e ≤ 1024`
  hypothesis (never-OOF is no longer consulted) and its sorry-inheritance docstring.
- **Doc status rewritten per-theorem:** ThetaRuns.lean and ObservableTriple.lean headers no
  longer claim exploratory-study status for the surviving surface (foundation-grade,
  sorry-free); study status is retained ONLY by the fenced `DeprecatedFuelExistential`
  section and the endgame statement. XiTriple.lean's prose references to the existential
  `ΘRuns` were swept to point at `ΘRunsE`/the fence.

## Overnight addendum — T3 (end-to-end firing demo: `call_spec` fired twice), 2026-07-18

New file: `NestedEvmYul/TwoCallDemo.lean` (foundation-grade, sorry-free). Build green;
sorry census unchanged at 3 (ThetaRuns keystone pair + ObservableTriple endgame);
`#print axioms` on `demo_twoCall`/`demo_twoCall_storage`/`demo_call₁`/`demo_call₂`/
`demoTriple`/`Θ_stop_forward`/`thetaTransfer_find?`/`Xi_stop_explicit`: all
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `ofReduceBool`.

### What was proved

The flat `twoCall_completedWith` analog, with **no hypotheses left**: a concrete caller
(`demoCaller`, default state over a singleton map holding a STOP-code callee at `0xff`
with storage cell `⟨0⟩ ↦ ⟨42⟩`) fires `call` twice; `twoCall_spec` applies with every
side condition discharged — `hΘ` via `theta_of_xi` (habsorb proven genuinely universally),
`hP₁`/`hP₂` by `rfl`, `hcall₁`/`hcall₂` as forward-evaluated ∀-fuel equations
`call (f+5) … = .ok (⟨1⟩, demoAfter₁/₂)` with the post-states explicit records — and the
resulting `Q₁ ∧ Q₂` yields the plain-storage punchline (`demo_twoCall_storage`): the cell
still reads `⟨42⟩` after both calls, read out of `Q` alone via the pinned
`find?`/`lookupStorage` match shape (§2.1 lesson applied, no RBMap lemma owed at readout).

### What tonight's proofs CONFIRMED from the study

- **The "one inversion away" item closes — the T2/B3 surface is non-vacuous end-to-end.**
  The study proved `call_spec` by inversion but never fired it. Firing needed exactly one
  new technique: an **existential-free** STOP-run producer chain. T2's `Xi_stop`/
  `Xi_stop_cofinal` hide the final gas behind `∃ g'`, which sits between the ambient
  universals and the fuel and therefore blocks `rw`-based forward evaluation of `call`'s
  do-block. T1's dispatcher equations dissolve it: `step_eq_shared_stop` +
  `shared_step_stop` have explicit fuel-free RHSes, so `stopState`/`stopGas` are plain
  definitions and `X_stop_explicit`/`Xi_stop_explicit`/`Θ_stop_forward` are ∀-fuel
  *equations* (zero existentials, all ambient args universal). `Θ_stop_forward` then
  `rw`s straight into the reduced `call` body with unification instantiating 14 arguments,
  and the rest of the firing lemma is one `rfl` — the T1 technique paying off a third time.
- **The Θ-forward recipe generalizes from ∅ to non-empty maps as priced.** The new content
  over `Θ_doNothing`: `hfind` (recipient present → credit is an insert rewriting only the
  balance), `hexec` (`toExecute σ r = .Code ⟨#[0x00]⟩`, an RBMap/π computation, `rfl` at
  every concrete use), `hs` (sender absent from the post-credit map → debit arm no-op),
  and `hne` (post-transfer map beq-nonempty → the `σ'' == ∅` rollback arms do NOT fire —
  a concrete beq-false the do-nothing world never needed). All four are `rfl` at both
  call sites, including the second, re-derived on the post-transfer literal `demoMap₁`
  (landmine (e) as predicted: `Θ` returns the post-transfer map, so the second
  `toExecute`/`find?` facts are facts about THAT literal).
- **`theta_of_xi`'s habsorb is the one genuinely-universal leg** (as its docstring
  flags): `ThetaTriple` quantifies over all senders/recipients/values, so the demo owed a
  real lemma — `thetaTransfer_find?`: the callee's entry survives the transfer preamble
  for arbitrary `s`/`r`/`v` with at most its balance rewritten. Cost: a
  `Std.TransCmp` instance for the `AccountAddress` `compare` (definitionally
  `compareOn (·.val)` + `TransOrd Nat` — 2 lines) unlocking Batteries'
  `RBMap.find?_insert`, plus ~60 lines of two-stage (credit/debit) case analysis. The
  balance-`∃` in `P_ξ`/`Q` (`∃ b, find? = some {demoAcct with balance := b}`) is what
  absorbs the rewrite; `hroll` is then structure-eta (`demoAcct` IS
  `{demoAcct with balance := demoAcct.balance}`), and `hΞ` is `preservesAccount_stop`.

### What tonight's proofs CORRECTED / honest boundaries

- **§2.3's "logic-free zone" is narrowed, not colonized, by this demo.** `twoCall_spec`'s
  middle state is hypothesis-supplied; the demo discharges it by choosing
  `ev₂ := demoAfter₁` — the caller calls again *immediately*. That is legitimate (the
  firing equation pins `demoAfter₁` explicitly, so `hP₂`/`hcall₂` are `rfl`/`rw`
  dischargeable), but a caller that runs opcodes BETWEEN the calls still needs T1's
  X-loop logic to step from `demoAfter₁` to the second call site. The demo proves the
  triple surface composes end-to-end; the caller-code middle run remains T1/T4 territory.
- **Nothing else needed correction.** The guard (`value ≤ balance ∧ depth < 1024`),
  the failure disjunction (`!z || notEnoughFunds || depthLimit`), `Ccallgas`, and the
  degenerate memory machinery all discharged as the plan priced them: guard by
  `decide`, disjunction inside the terminal `rfl` (the kernel never has to normalize
  `Ccallgas` — it rides inertly into `demoAfter₁`'s explicit gas field, and `Q` never
  reads gas).

### Technique notes (for future firing demos)

- Structure-instance literals spanning lines must use newline-separated fields — comma
  separators break at the line boundary in this toolchain (parse error "expected `}`").
- `simp only []` does NOT iota-reduce the do-desugared match over an `Except.ok` literal
  in the goal; the working incantation is `show <post-match form> = _` (defeq `change`)
  followed by the `hne` rewrite and `rfl`. Inside `rcases hr : scrut with _ | x` branches
  the scrutinee is already substituted, so a bare `simp only []` suffices there.
- `rw [if_pos (by decide)]` (Z_stop's `if_neg` idiom, forward direction) discharges the
  funds/depth guard; `decide` kernel-evaluates the concrete `find?`/`≤`/`<` instances.
- The demo is ∀-fuel throughout (`call (f+5)` for every `f`) with fuel offsets exactly as
  priced: `call (f+5) → Θ (f+4) → Ξ (f+3) → X (f+2) → step (f+1)` — landmine (d) never
  fired because each layer's lemma is stated at its own offset.

### Parity status vs docs/flat-vs-nested-convergence.md §1.3/§1.4

The nested column now also has the **worked two-call composition demo** (flat:
`TwoCallExample.lean` `twoCall_messageCall`/`twoCall_completedWith`; nested:
`TwoCallDemo.lean` `demo_twoCall`/`demo_twoCall_storage`) — with the nested version
fully concrete (the flat example composes hypothesis-supplied `Runs`/`CallReturns`
witnesses; the nested demo discharges ALL its hypotheses against a concrete world).
Still absent vs flat: the Behaves-style for-all-programs predicate and the
messageCall-bridge analog (unchanged by T3; see T1's addendum).

## Overnight addendum — T4 (endgame proved; keystone found FALSE and deleted), 2026-07-18

Sorry census after this track: **0** (start of night: 3). Both deliverables landed
axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]` on
`nested_twoCall_completedWith`, `Θ_code_forward`, `Xi_forward`, `X_call_iter`,
`X_stop_halt`, `Z_ok_toState`, `step_fuel_irrelevant`, `ΘRuns_completedWith`,
`demo_twoCall_storage`).

### (a) The endgame is a theorem

`nested_twoCall_completedWith` (ObservableTriple.lean) — the full nested analog of flat
`twoCall_completedWith` — is **proved sorry-free**, restated on T1's lemma-backed
vocabulary exactly as §2.2/§2.3 anticipated:

- The three recorded blockers dissolved as predicted: (1) X-decomposition = `ItersN_X`
  chain transport + omega-normalized fuel bookkeeping; (2) the call-site tie =
  `step_call_eq` packaged as the new `XLoop.X_call_iter` (the successor is the
  DERIVED post-processed call output `evRᵢ.replaceStackAndIncrPC (restᵢ.push ⟨1⟩)`,
  never a hypothesis — the study's refutability finding is preserved in the docstring
  HISTORY note); (3) Q-propagation = sidestepped by the **empty-suffix** design (halt
  immediately after call₂, as flat's TwoCallExample does): the final map is chased to
  `evR₂.accountMap` via the new `XLoop.X_stop_halt` (explicit `stopHaltState`
  successor) + `XLoop.Z_ok_toState` (`Z` touches only `gasAvailable`), so `hread` is
  DERIVED from `Q₂` — v1 supplied it raw at the halt state.
- The one design point flagged in the plan (CALL-site fuel plumbing) landed as the
  cofinal shape `∀ f, call (f + kᵢ) … = .ok (⟨1⟩, evRᵢ)` on the **bumped** post-`Z`
  state — T2's encoding, and exactly the shape T3's `demo_call₁/₂` produce (`kᵢ = 5`).
  Both callee `ThetaTriple`s fire via `call_spec`; the conclusion also delivers
  `Q₁` at call 1's post-state, so neither triple is decorative.
- Fuel side condition: `n₁ + n₂ + k₁ + k₂ + 6 ≤ seedFuel w` (the honest cofinal-pivot
  residue), fuel chain `Θ (f+m+4) → Ξ (f+m+3) → X (f+m+2)` with
  `m = n₁+n₂+k₁+k₂+2`. New forward plumbing: `Xi_forward` (one `Ξ`-unfold) and
  `Θ_code_forward` (one `Θ`-unfold; goal-side `split` on the `Ξ` match, each branch
  tied to the supplied family by `Eq.trans` with the elaborator settling the
  `thetaTransfer` ↔ inline-match defeq — the `theta_of_xi` trick, forward direction).
- Honest boundary: the per-segment decomposition data (chains, decode/`Z`/stack
  facts, call families) enters as hypotheses — same altitude as flat's `Runs`
  hypotheses. A fully concrete two-CALL caller instance (real bytecode, all
  hypotheses discharged) was NOT built tonight; T3's demo discharges the same
  hypothesis *shapes* concretely, but gluing a concrete caller through the new
  endgame is open (and is the natural next acceptance test).

### (b) The keystone correction — §2.2's pricing is moot: the pair is FALSE

The study priced `Θ_fuel_mono_ok`/`Θ_fuel_mono_error` as a ~1500-line 6-layer
`res_mono` mutual induction. Tonight's attempt found something sharper: **the pair is
unprovable because it is false as stated.** `step`'s CREATE/CREATE2 arms match the
inner `Lambda` result with a `| _ =>` catch-all
(EVMYulLean/EvmYul/EVM/Semantics.lean:286, :344) that ABSORBS `.error .OutOfFuel`
into an ordinary result `(0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)` —
execution continues with `x = 0` as if the create had failed *semantically*. So a
non-`OutOfFuel` result at low fuel (premise satisfied) need not be reproduced at high
fuel (once the init-code run completes, `x = a ≠ 0`, different map), and the leak
lifts through `X`/`Ξ`/`Θ`. The CALL family is NOT leaky (its do-bind propagates
`OutOfFuel` honestly); the ~130 non-recursive arms are fuel-irrelevant and this
fragment is now PROVED as `XLoop.step_fuel_irrelevant` (140-leaf `rfl` sweep over the
two-level `Operation` sum, 8M-heartbeat crank, ~2min). Caveat: an in-Lean kernel
refutation would need the high-fuel side of a concrete CREATE, which crosses the
`opaque` `ffi.KEC` — the same keccak wall as exp005's CREATE witnesses — so the
falsity rests on the absorption argument, not a `decide` witness.

Dispositions taken (house no-sorry'ed-scaffolds rule): the quarantined
`DeprecatedFuelExistential` section (ΘRunsE + keystone pair + dependents) is
**deleted**; a keystone post-mortem note stands in its place in ThetaRuns.lean
(deleted material readable at commit 6315c911). Consequence worth promoting: the T2
cofinal pivot is not the *cheaper* encoding but the *only correct one* — the
`k ≤ seedFuel w` adequacy side condition and the loss of single-fuel-point
introduction are load-bearing, not deferred debt.

### Parity status vs docs/flat-vs-nested-convergence.md §1.3/§1.4 (post-T1+T4)

The nested column now has: per-opcode rules (`X_push1`/`X_push0`/`X_sstore`/`X_jump`/
`X_jumpi_*`), the branch combinator (`X_branch`), sequencing/decomposition
(`ItersN`/`ItersN_X`/`X_decompose`), the call-site tie (`step_call_eq`/`X_call_iter`),
triples + frame rule (T2/B3), a fully concrete firing demo (T3), and the endgame
observable theorem (`nested_twoCall_completedWith` — flat `twoCall_completedWith`'s
analog, with the storage read derived from the callee spec). **Still absent vs
flat**, named as the residual gap (do not claim full parity): (1) a `Behaves`-style
for-all-programs predicate (nested conclusions are per-decomposition, not quantified
over all programs of a syntax class); (2) a `messageCall`-bridge analog (flat's
`messageCall_runs` packages the segment data behind a program-level driver; nested
segment data enters per-theorem). Nested-only surplus, in exchange: the never-OOF
envelope (`runΘ_never_outOfFuel`) and the fuel-free observable driver (`runΘ` +
`ΘRuns` cofinal veneer).

### T5 addendum — CREATE-side seed landed (LambdaTriple.lean, sorry-free)

The stretch track landed WHOLE, including its optional half:
`NestedEvmYul/LambdaTriple.lean` ships `Lambda_zero`, `LambdaTriple`
(+`conseq`/`conj`), `lambdaInit`, `lambda_of_xi`, `lambda_success_out_empty`,
`createInit`, and `create_spec` — all proved, zero sorries, all six
declarations axiom-clean (`[propext, Classical.choice, Quot.sound]`).

Shape facts read off `Lambda` (not assumed): the result is a **7-tuple** with
the created `AccountAddress` first, so the triple's postcondition is
`Q : AccountAddress → AccountMap → Substate → ByteArray → Prop` — parametric in
the address, which is `ffi.KEC`-derived and never evaluated (the keccak wall
respected by construction). Success output is hardwired `.empty` (proved as
`lambda_success_out_empty`); the deposit flag `F` is killed by the `z = true`
gate. The EIP-7610 collision swap (`i ↦ ⟨#[0xfe]⟩`) surfaces honestly as a
disjunctive code premise in `lambda_of_xi` (occupancy at a hash-derived address
is undecidable without the hash).

Technique findings worth recording:
- The `theta_of_xi` inversion recipe transferred VERBATIM to `Λ` (`simp only
  [Lambda, bind, Except.bind]` + `split at` + ctor injection); the new `L_A`
  RLP Option-bind splits without computing any RLP. The pattern-let
  `(i, createdAccounts) := if …` desugars to PROJECTIONS of the ite, not a
  match — no extra split; the collision-ite is handled by a goal-side `split`
  on the code-disjunction obligation (both arms `rfl`).
- `step_create_eq` proved UNNECESSARY: CALL's arm is one helper call (small
  `rfl` equation), but CREATE's is a 60-line inline block; `create_spec`
  inverts it directly via the proven `create_result_gas_le` split sequence, so
  no arm-transcription equation exists or is needed.
- `create_spec`'s success gate differs from CALL's `x = ⟨1⟩` by necessity:
  CREATE's result word is `.ofNat a` with `a` hash-derived, so the side
  condition is `hx : s'.stack ≠ ⟨0⟩ :: rest` and the conclusion is existential
  in the created address. The three failure branches (nonce-overflow,
  `Λ`-error, guard-else) die by PURE DEFEQ: their `z` is a literal
  `decide False`, so the failure-word ite's `Or`-instance short-circuits and
  `s'.stack ≡ ⟨0⟩ :: rest` — `exact absurd rfl hx`, no splits. In the `Λ`-ok
  branch, `cases lamz` first (its false case is the same defeq kill), then two
  `split at hx` (the `returnData`-ite is the first candidate in record-field
  order, the pushed-word ite second).

Parity-status delta vs docs/flat-vs-nested-convergence.md:162-187: the nested
column additionally gains a CREATE-side procedure-triple surface + creation-site
tie, which the FLAT side does not have at all (flat has no Lambda-level rule) —
a nested-only surplus item. The residual gaps named in the main parity note
(Behaves-style for-all-programs predicate; messageCall-bridge analog) are
unchanged, and the CREATE endgame/observable layer remains future work.
