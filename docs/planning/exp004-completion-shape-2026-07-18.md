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
