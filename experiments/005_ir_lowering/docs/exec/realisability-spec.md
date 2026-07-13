# Track E — Realisability Spec Skeleton: design rationale (2026-07-02)

Deliverable: `LirLean/RealisabilitySpec.lean` (namespace `Lir`), registered as the
NON-DEFAULT `lean_lib Nightly` in `lakefile.lean`. All `def`s/`structure`s are REAL; the
`sorry`s are exactly the theorem proofs (R-obligations + mirror-adequacy lemmas) — tracked
debt by design; current count 25 after the round-3 fix added R0b + the revalidates anchor
(see §8 for the authoritative build record). Default `lake build` = untouched and sorry-free.

Statement sources: `docs/execution-plan-2026-07-02.md` (Track E), `docs/
target-architecture-2026-07-02.md` §2/§3/§5, `docs/fleet-2026-07-02/flagship-signature.md`
§1/§5, `docs/fleet-2026-07-02/skeptic-f1-verdict.md` (the review standard: every statement
skeptic-drilled for satisfiability before acceptance).

## 1. Where the briefed near-Lean statements were wrong on inspection

Five discrepancies found by the track planner, plus four more found by the implementer's
per-arm skeptic drill. Each resolution is in the file with a docstring; this is the ledger.

### Planner findings (1–5)

1. **`ResultNonException` does not exist**, and `FrameResult` cannot express "non-exception"
   exactly: `endCall` maps `.exception` to `success := false, gasRemaining := 0`, identical
   to a zero-gas revert. → `RunLog.clean` demands `success ∨ gasRemaining ≠ 0`; **a genuine
   zero-gas revert is conservatively out of scope** (hypothesis false ⇒ flagship silent,
   never unsound). Tracked decision.
2. **The fleet flagship was missing the nonzero-SSTORE scope premise** (`sim_sstore_stmt`
   requires `vw ≠ 0`; `EvalStmt.sstore`'s scope is nonzero writes). As drafted it was
   unprovable for zero-writing runs. → new seam `NonzeroSstores` (frame-level, op/stack
   shapes copied from `sim_sstore_stmt`'s `hdop`/stack facts), flagship gains `hnzw`.
   Tracked decision: extend `sim_sstore` to zero writes, or record SSTOREs in the log.
3. **`SstoreRealises` is itself free-∀ unsatisfiable** (a fifth instance beyond
   skeptic-f1's four): it concludes gas facts about EVERY frame pinned only by
   address+stack, so an adversarial zero-gas frame refutes it and
   `∃ acc, SstoreRealises fr kw vw acc` is false for every `fr`. → the reshaped sstore arm
   DROPS it; R4 (`sstoreRealises_at_frame`) restates its three conclusions point-wise at
   the concrete frame, gas half derived from clean-halt, presence half = the threaded
   `SelfPresent` (decision 4 wired).
4. **`ReachableFrom` (fleet sketch) did not exist** → defined
   (`∃ fr₀, beginCall params = .inl fr₀ ∧ Runs fr₀ fr'`), making `PrecompileSeams.callsCode`
   exactly the `hcc` shape `cleanHalts_of_runWithLog` consumes.
5. Minor: `entryState` needs its own accounts lens (`storageAt` reads a `Frame`) — it
   mirrors `resultStorageAt`'s `find?/lookupStorage` on `params.accounts`; the `Corr`
   phantom `obs` is pinned to `0` everywhere (slated for Phase-3 deletion; NOT deleted here
   — no edits to existing files); the R1 gas word `gasAvailable − Gbase` was verified
   against `driveLog`'s recording point (post-charge) and `StmtTies` :1318; `sloadChg` is
   `∀`-quantified in the static bounds (provable: `chargeOf`-LENGTH is `sloadChg`-independent).

### Implementer findings (A–D) — deviations from the plan, each with justification

**A. `RunDefinable` is unsatisfiable for every program with a call or gas read** (the
critical one). `StmtDefinable`'s `.call` arm is literally `False`, its assign arm demands
`e ≠ .gas`, and `RunDefinable.stmts` demands `StmtsDefinable` for every present block — so
folding `RunDefinable` into `WellLowered` (as the plan and the fleet report both directed)
would make the flagship's antecedent FALSE on exactly the gas-reading/calling domain: the
same vacuity disease, one level down. Neither the audit nor the fleet caught this (the
fleet flagged only the ∀-state over-approximation). → `WellLowered.defs` is the new
`RunDefinableG`: definability threaded along `RunStmts` derivations themselves (the
semantics natively supplies the gas word / call bundle), state-uniform only in the
block-ENTRY state. This also incidentally reveals the in-tree cyclic headline's `hdef` as
a fifth unsatisfiable supplied hypothesis for gas/call programs — reviewers of
`p5-walk-status` claims should note it.

**B. The planned sload value conjunct `∃ w, evalExpr st0 0 (.sload k) = some w` is itself
refutable**: an empty-locals `Corr` witness at the sload cursor makes `evalExpr = none`.
→ the key binding `st0.locals k = some kv` is an ANTECEDENT (exactly the sstore arm's
long-standing operand-binding pattern) and the value conjunct is the definitional
`evalExpr … = some (st0.world kv)` with the post-state pinned to `st0.setLocal t
(st0.world kv)`.

**C. The planned ret-arm conclusion `∃ vw, st'.locals t = some vw` is refutable the same
way** (empty-locals `Corr` witness). → dropped; the epilogue block sits under the
`∀ vw`-antecedent the original already had. Additionally the inner `∀ frv` epilogue gained
an explicit **pc-pin antecedent** (`frv.pc = frT.pc + |materialise t|`): without it the
decode conclusions quantify over every stack-coincident `Runs`-reachable frame (a
plausible refutation via value-coincidence elsewhere in the run); with it they are static
`DecodeAnchors` facts at a pinned offset, and the consumer (`MatRuns.pc`) has the pin
anyway.

**D. The planned sstore conclusion `vw ≠ 0` is underivable from coupling+clean-halt
alone** (the log does not record SSTOREs, so an adversarial coupled zero-writing frame
satisfies every antecedent and refutes the conclusion). → the arm carries
`NonzeroSstores fr0` as an antecedent; `DriveCorrLog` gained the `nonzeroSstores` field
(a deviation from the planned invariant) to thread it — sound because `NonzeroSstores` is
`Runs`-monotone, seeded from the flagship's `hnzw`. Consequently R10a does NOT take
`hnzw` (the arm's antecedent carries it), while R11 keeps it.

Also per the same drill: the **call arm** is NOT "kept as-is" as the plan stated — bare
`CallRealises` is refutable by an OOG-at-CALL `Corr` witness (its `CallReturns` existential
needs the call to actually return). It sits under coupling + clean-halt + address-pin
antecedents (the address pin is what identifies `realisedCall log self` with
`evmV2CallOracle … fr0.address`).

### Minor deviations

- `TermTies'` binds its log parameter as `_log` (unused until the RETURN-value channel;
  matches the in-tree `TermTies`'s `_o` convention; keeps the build warning-free).
- The optional `Bool`-valued `RunLog.cleanb` twin was omitted (the `clean` branches are
  `Bool`/`DecidableEq` facts; the executable twin belongs to the R9 checker work).
- `singleCall_exProg` is PROVED (`by unfold SingleCall; decide`) — a free non-sorry anchor.
- The **loop caveat** on `SingleCall` (a syntactically-single call inside a loop fires
  dynamically per iteration) was initially recorded only as a docstring note; the review
  fix round (§7) closed it at the theorem surface with the log-side premise `hone`.

## 2. `RecorderCoupled` — field-by-field satisfiability argument

The coupling (target-architecture §3, option (i)) replaces every free value variable with
suffix-head pinning. Why each field:

- `restart` (load-bearing): `driveLog` is a FUNCTION, so
  `driveLog fuel' [] (.inl fr) [] [] [] = .ok (log.observable, gS, sS, cS)` pins the three
  suffixes AND the observable simultaneously to `fr`'s deterministic future. An adversarial
  `(fr, gS, …)` must genuinely reproduce the recorded future — that is what converts the
  tie conclusions from refutable claims into derivable ones. Pending stack `[]` because the
  coupling is stated only at top-level boundaries (`Corr.stack_nil`), the same
  `stack.isEmpty` gate the recorder records under.
- `gasPrefix`/`sloadPrefix`/`callPrefix`: make "consumed so far" explicit; the R10 assembly
  reads them; entry instance = whole log with `pre = []`.
- Child black-boxing: a descended CALL's internals are invisible to the restart exactly as
  to the original recording, so `recorderCoupled_call` (R7e) consumes exactly one
  `CallRecord` and NO gas/sload entries — mirroring `Runs.call`.
- Cyclic-correctness: the coupling is indexed by the FRAME (whose gas differs per loop
  visit), never the cursor — no per-cursor value function anywhere (rejected option (iii)
  is unsound for cycles).

**R1's clean-halt antecedent is load-bearing** (recorded in its docstring): an OOG-at-GAS
frame satisfies the coupling with the restart ending in the exception observable and
`gS = []`, refuting the head equation; under `CleanHaltsNonException` the first restart
step IS the recorded top-level GAS read with the post-charge word.

**R10's off-run robustness** (its docstring): the builders must prove the arm conclusions
for ANY antecedent-satisfying `(st0, fr0, suffixes)` — including off-run adversarial ones —
which works because every conclusion is (i) a static program fact derivable from `hwl` +
the cursor, (ii) carried over from the arm's own antecedents (`Corr`'s
`wellScoped`/`memAgree` channels, the threaded `NonzeroSstores` seam), or (iii) computed
from `fr0` + restart determinism. *(Round-3 precision fix: the original wording claimed
only (i)+(iii) — "static or computed from `fr0`" — which overclaimed; source (ii) is real
and the file's §3 docstring now states the trichotomy.)* That analysis (per arm, §8's
table) is what makes the reshape non-vacuous rather than merely differently-shaped.

## 3. R9's existential-with-witness shape

A premature `lowerCheck` def would be worse than debt: wrong-but-real misleads, and
`fun _ => false` is the vacuity dual (sound, useless). So R9 states
`∃ check, (∀ prog, check prog = true → WellLowered prog) ∧ check exProg = true` — the
second conjunct is the anti-vacuity guard (it forces `WellLowered exProg`, `RunDefinableG`
included, to be actually true). The checker DEFINITION is the debt.

## 4. `exProg` (R12) — why this shape

One block of straight-line gas-read → sload → nonzero-sstore → CALL (forwarding the read
gas — introspection coupled to the call channel), then a genuine CYCLE (block 1 loops on a
gas-derived `lt` until gas < 1000 — the domain where per-cursor gas functions are unsound),
then `stop`. The CALL is outside the loop (single dynamic firing; see the `SingleCall`
caveat). Callee `0x100` is beyond the precompile range (keeps `CallsCode` satisfiable).
`r12_hypotheses_inhabited` keeps `params` existential on purpose: a literal `CallParams`
needs `BlockHeader`/`ProcessedBlocks` plumbing that belongs to the R12 grind, not the spec.

## 5. What the reviewer should attack

1. Every arm of `StmtTies'`/`TermTies'`, the way skeptic-f1 attacked the originals — the
   per-arm antecedent sets above are the designed defense; if any conclusion is still
   refutable by an antecedent-satisfying witness, that is a review failure of this track.
2. `RunDefinableG`: is it satisfiable for `exProg` (it must be — R9's anchor forces it),
   and is it STRONG enough for the `RunFrom`-existence construction (the `stmts` field's
   prefix-run threading was designed against `runStmts_exists`'s fold)?
3. `RecorderCoupled.restart`'s fuel existential: is `∃ fuel'` the right quantifier (vs a
   pinned residual fuel)? Chosen because `driveLog`'s fuel is monotone-irrelevant past
   sufficiency and the restart is consumed only through determinism; a pinned-fuel variant
   would thread arithmetic through every edge lemma for no statement gain.
4. The single-call scope (`hsingle` + `hone`, post-§7) and the zero-gas-revert cut — both
   are honest scope reductions; confirm they are acceptable seams rather than silent losses.
5. `recorderCoupled_call` (R7e) does not pin `rec` to the call's `(result, pending)`; the
   pin is delivered inside R3 via restart determinism. Confirm that split is provable.

## 6. Build/verification record

- `lake env lean LirLean/RealisabilitySpec.lean`: clean at each of the three content
  commits (only `declaration uses 'sorry'` warnings).
- `lake build Nightly`: **Build completed successfully (1159 jobs)**, 23 sorry warnings.
- `lake build` (default): **Build completed successfully (1164 jobs)** — unchanged; the
  `LirLean` root does not import the new module (Track A owns its tail).
- Track-B-casualty grep (`MonotoneGas|GasRealises|gasMonotone|driveLog_gas_inv|
  realisedGas_monotone|geToNat|bound_mono|Lir.Oracle|Lir.Mono|HonestGasTie`): only prose
  lesson-mentions in docstrings; zero declaration references.
- No `#print axioms` in the Nightly module by design (§7 of the file): sorry'd decls carry
  `sorryAx`; guards migrate to `Audit.lean` obligation-by-obligation as sorries close.

## 7. Review fix round (2026-07-02) — two blockers, refuted-and-repaired

The independent review re-ran the adversarial drill and refuted two statements INSIDE
their hypothesis envelopes. Both fixes landed (commit `ff7e2ab`); both are one-field /
one-premise, exactly as the review prescribed.

**Blocker 1 — the `defsOf`-consistency hole (header lesson 6).** `defsOf` is a
FIRST-find over program order (its `Lowering.lean` docstring says "last" — a discrepancy
flagged for a Wave-4 sweep; not this track's edit surface), and `emitStmt` keys its spill
stash on `defsOf t`. So `[.assign t0 (.imm 1), .assign t0 .gas]` registers `t0 ↦ .imm 1`,
emits NO GAS byte at the shadowed gas assign, yet `EvalStmt.assignGas` demands a
gas-stream head from the empty `realisedGas log` — refuting `lowering_conforms` (and
`_all`/`_gasfree`/`stmtTies'_of_runWithLog`) with every hypothesis satisfied:
`RunDefinableG`'s gas arm is unconditionally true, i.e. the very generalization that
opened the gas domain (finding A) opened this hole. The per-cursor fact was ALREADY
consumed by the walk (`defsSound_preserved_assignPure`'s `hself`) but lived only in
per-lemma side conditions — a free-∀-ADJACENT disease instance: a scope assumption absent
from the statement's hypothesis surface. Fix: static decidable `DefsConsistent prog`
(every def-site agrees with `defsOf`'s first-find registration; pure assign ↦ own RHS,
gas/sload/call-result ↦ `.slot (slotOf t)`; also excludes pure/pure shadowing with a
different RHS, which breaks recompute-on-use the same way) as the new field
`WellLowered.defsCons`. Satisfiability re-checked: TRUE at every `exProg` def-site
(scratch `#eval` over all blocks, `defsOf exProg t` vs the field's match — `true`);
single-assignment programs satisfy it trivially, so benign programs stay in scope.

**Blocker 2 — syntactic `SingleCall` vs the dynamic head-projection oracle (header
lesson 7).** `callOracleOf` replays only the HEAD `CallRecord`, so a syntactically-single
call inside a loop that fires per iteration with differing child outcomes refutes R3 (and
the flagships' `Conforms` channel) at the second iteration — and the previous skeleton
knew it only as a docstring caveat, which is not a hypothesis. Fix: the decidable
LOG-side premise `hone : log.calls.length ≤ 1` (read off the run, `hclean`'s pattern;
exactly the domain on which head-projection is correct per the skeptic report) added to
R3, R10a, and all three flagships, plus the matching conjunct in R12a's inhabitation
(satisfied by `exProg` — its call is outside the loop). `SingleCall` stays syntactic;
R3′ remains the tracked stream-generalization decision.

**Minors folded in:** `PrecompileSeams`'s docstring now records that R12a doubles as the
machine-check that `noErase` is TRUE of the current exp003 `beginCall` precompile stub
(a failure there diagnoses a SEAM/engine problem, not an `exProg` problem);
`DefsConsistent`'s docstring carries the first-find-semantics note and the Lowering.lean
docstring-discrepancy flag.

Post-fix build: `lake build Nightly` green (1159 jobs, exactly 23 sorry warnings — no new
sorries; the fixes are hypothesis/field additions, not new debt); default `lake build`
green (1164 jobs, untouched).

## 8. Round-3 fix (2026-07-02) — the scoping-conjunct blocker, refuted-and-repaired

The round-2 review re-ran the drill on the NON-VALUE conjuncts and refuted the ties
INSIDE their hypothesis envelopes **at the file's own witness**: `Lir.StepScoped`'s
live-scope clause (`DefsSound.lean:514` — "no currently-bound tmp's registered def reads
the assign target") is FALSE at `exProg`'s second loop-iteration entry. Concretely, with
clean-running params of ≥ 2 loop iterations (R12a asserts they exist): at (block 1, pc 0)
the real state has `t8` bound from iteration 1 while `defsOf exProg t8 = some (.lt t6 t7)`
reads the rebind target `t6` — every arm antecedent (`Corr`, `RecorderCoupled`,
`CleanHaltsNonException`) satisfied, conclusion refuted. Same exposure at (1, pc 1)
(`t7 := 1000` vs the same reader) for arm 1; the sload arm and the call arm
(`CallRealises` embeds `StepScoped (.call cs)`) carry the same disease shape (for the
record: NOT refutable at `exProg` itself — no registered def reads `t2` or `t5` — but
refutable in-envelope for any `WellLowered` program whose sload/call result has a
registered reader; the file's docstrings state this precisely). Root cause, deeper: on the
loop-EXIT iteration, between the `t6` rebind and `t8`'s reassign, **recompute-on-use
`DefsSound` is itself false at the real mid-block states** (`t8` holds stale `0`,
`evalExpr (.lt t6 t7) = 1`) — the un-scoped invariant is incompatible with rebinding a
tmp that has live dependents, which the cyclic witness exercises by construction.

**Decision (lead): route (i), shadowing-aware scoping.** The lowering's rematerialisation
is exercised only at USE sites, so mid-block staleness of a bound-but-unused dependent is
harmless to the lowered code — the INVARIANT was overclaiming, not the lowering
misbehaving. **The witness `exProg` stays as is** (rebinding-with-live-dependents is why
it caught this); the machinery, not the witness, gets reshaped.

### What changed (file: `LirLean/RealisabilitySpec.lean`)

1. **New shadowing-aware carrier — shape (b), an explicit invalidation set** (§1 of the
   file, after `DefsConsistent`): `ReadsOf` (static registered-reader relation),
   `invalStep` (per-statement set transfer: rebinding `t` invalidates its registered
   readers; the target re-validates unless self-reading; `sstore`/result-free calls are
   identity — `defsOf` never registers a `.sload`, so no recompute reads the world),
   `DefsSoundS` (recompute soundness OUTSIDE the set), `StepScopedS` (the state-FREE
   static residue of `StepScoped`), `RevalidatesPerBlock` (the per-block boundary
   re-validation criterion), `CallRealisesS` (the `CallRealises` kernel with
   `StepScopedS` in place of the embedded `StepScoped`), and the PROVED bridge
   `defsSoundS_empty_iff` (`DefsSoundS` at `∅` = `DefsSound`).
   *Why (b) over (a) ("validSince"):* validity-since-binding is history-indexed — it
   cannot be stated on a single `(prog, st)` pair without walk data, so it carries the
   same set implicitly; the explicit set costs one `def` and buys a preservation lemma
   with NO per-state side conditions (the live-scope demands are gone, not relocated)
   plus a decidable-in-principle boundary criterion for the R9 checker. A SEMANTIC
   invalidation predicate ("live but stale") was rejected as a tautology-maker.
   *Liveness-insensitivity:* `invalStep` invalidates readers whether or not they are
   bound — harmless (the invariant claims nothing about unbound tmps) and it keeps the
   transfer a pure function of program text + statement.
2. **Tie reshape**: `StmtTies'` arms 1–4 conclude `StepScopedS` (static) instead of
   `Lir.StepScoped` (arm 4 was not refutable but carried the same state-quantified shape;
   replaced for uniformity); arm 5 and R3 conclude `CallRealisesS` instead of
   `Lir.CallRealises`. Dropped along the way: pure-assign's `usesInExpr t e = 0`
   self-read clause (absorbed — a self-reading rebind leaves its target in the set
   instead of demanding a side condition; the old clause was ALSO in-envelope refutable,
   see table row 1.2).
3. **R3 restated**: conclusion = the value/trace kernel + `StepScopedS` (weakened,
   shadowing-aware scoping) + it now takes `hwl : WellLowered prog` — the static bundle
   the round-2 reviewer flagged as missing (it derives the `StepScopedS` residue, the
   result-slot registration of the post-state fold, and the Route-B addressability).
4. **Header lesson 8** added (the scoping conjuncts carried the same refutable-∀ disease;
   mechanism: live-scope clause vs loop rebinding; invariant-overclaim vs lowering).
5. **R0b — new tracked obligation** (`defsSoundS_preserved_step`, sorry'd): one
   `EvalStmt` step of a program statement preserves `DefsSoundS` along `invalStep`, with
   no per-state side conditions (site premises + `DefsConsistent` pin the registration —
   the unpinned version is refutable by a foreign statement; that drill was run on the
   new statement too). Its docstring records the MACHINERY FINDING as reshape criteria:
   the current sim machinery (`Corr.defsSound` at every statement cursor) cannot traverse
   a loop-exit iteration of a rebinding program — (1) mid-block `Corr.defsSound` →
   `DefsSoundS` at the threaded set; (2) boundary re-validation via `RevalidatesPerBlock`
   + `defsSoundS_empty_iff`; (3) per-arm sim lemmas re-plumbed to `StepScopedS` +
   use-site non-invalidation (a USE of an invalidated tmp is where IR-vs-lowered
   divergence would be real). Anchors: `revalidatesPerBlock_exProg` (sorry'd — finite
   fold, `decide`-able once the R9 checker lists the tmp universe) and the PROVED
   `not_defsSound_stale` (¬`DefsSound exProg staleSt` at the real mid-block loop-exit
   state — the machine-check of the root cause). Note the boundary statements SURVIVE:
   iteration-entry states are mutually consistent (`DriveCorrLog` at block entries is
   satisfiable at exProg for every iteration); the falsity is strictly mid-block.
6. **Overclaim fixes** (round-2 minor): the file's §3 header no longer says "NO free-∀"
   (now "no free value-∀" + a precision note); the "conclusions are computed from
   `fr0`/`frT` and restart determinism" claims (file §3 + R10a docstring + this doc's §2)
   now state the honest trichotomy: (i) static from `hwl`+cursor, (ii) carried from the
   arm's own antecedents, (iii) `fr0`+restart-determinism values.

### The adversarial drill, re-run conjunct-by-conjunct (every non-value conjunct)

Verdicts: **PASS** = true on `exProg`'s real run AND no antecedent-satisfying refutation
found in the R10a/R10b hypothesis envelope (derivation source given). The attacks column
records the strongest adversarial instance tried.

| # | Conjunct (arm) | Attack tried | Verdict / source |
|---|---|---|---|
| 1.1 | assign: `∀ n, defsOf t ≠ .slot n` | `t` also gas-defined elsewhere ⇒ `defsCons` forces `defsOf t = e` AND `.slot (slotOf t)` | PASS — needs `e = .slot _`, blocked by the `evalExpr st0 0 e = some w` antecedent (`evalExpr (.slot _) = none`); derives from `defsCons` |
| 1.2 | assign: `StepScopedS (.assign t e)` | (old form) live reader of `t`: REFUTED at exProg (1,1), iter 2 (`t7` vs `t8`); (old self-read clause) `t := add t t` with Corr-consistent `st0 = {t ↦ 0}` (`0 = 0+0` satisfies `DefsSound`): REFUTED in-envelope | PASS now — state-free; pure clause from `defsCons` at the cursor; gas/sload clauses vacuous under the arm's `e`-antecedents |
| 1.3 | assign: `setLocal`-wellScoped fold | adversarial extra live tmp with `defsOf = none` | PASS — old bindings from the `Corr.wellScoped` antecedent (an adversarial live tmp violating it fails `Corr`); the new `t` from `defsCons` (registration ≠ none) + the 1.1 argument for ¬`NonRecomputable`-or-slot |
| 1.4 | assign: `MemRealises (st0.setLocal t w) fr0` | make the new binding slot-registered so the unchanged `fr0` memory misses it | PASS — blocked by 1.1 (not spilled ⇒ the `MemRealises` quantifier sees only old bindings, supplied by `Corr.memAgree`) |
| 2.1 | sload: `defsOf t = .slot (slotOf t)` | mixed-shadowing (the round-2 blocker-1 shape) | PASS — exactly `defsCons`'s sload clause |
| 2.2 | sload: `StepScopedS` | (old form) live reader of `t`: not refutable at exProg (`t2` has no registered readers) but refutable in-envelope for a program whose sload result feeds a later registered def, reader live at a Corr-consistent adversarial `st0` | PASS now — `isSloadDef` from cursor membership (`hb`+`hcur`) |
| 2.3 | sload: slot canonicity `∀ tw slot'` | adversarial non-canonical registration | PASS — static, `hwl.wf.slots_slot` |
| 2.4 | sload: wellScoped fold | as 1.3 | PASS — `Corr.wellScoped` + slot disjunct for `t` (2.1) |
| 2.5 | sload: addressability pair | — | PASS — static (`hwl.wf` slot addressability; `slotOf t = 32·id`) |
| 2.6 | sload: stack fold (`fr0.stack.size + …`) | big runtime stack | PASS — `Corr.stack_nil` pins size 0; then static `StackRoomOK.sloadKey` |
| 2.7 | sload: activeWords flatness `∀ frk, MatRuns …` | key recompute MLOADs an UNCOVERED slot ⇒ memory expansion | PASS — every MLOAD in the materialise is at a live spilled tmp's slot: `Corr.defsSound` forces the operands of live recomputable tmps live (via `evalExpr = some`), inductively through pure defs (`.slot` stops recursion), and `Corr.memAgree`'s active-clause (`slot+32 ≤ activeWords·32`) makes covered MLOADs expansion-free (`mload_covered_congr` geometry). Flagged: the R10a proof leans on this coverage argument |
| 3.1 | gas: `defsOf t = .slot (slotOf t)` | shadowed gas def (round-2 blocker 1) | PASS — `defsCons` gas clause |
| 3.2 | gas: `StepScopedS` | (old form) **THE HEADLINE REFUTATION** — exProg (1,0) iter 2: `t6 := gas` vs live `t8 ↦ lt t6 t7` | PASS now — `isGasDef` from the cursor itself; no live-set demand |
| 3.3 | gas: slot canonicity | — | PASS — static (as 2.3) |
| 3.4 | gas: wellScoped fold over the pinned head value | as 1.3 | PASS — `t` slot-registered (3.1) ⇒ second disjunct |
| 3.5 | gas: addressability + `pcOf + 34 < 2^32` | overflow cursor | PASS — static (`hwl.wf` bounds) |
| 4.1 | sstore: `StepScopedS (.sstore …)` | find `defsOf`-registered `.sload` | PASS — structurally true of ALL programs (`defsOf` routes sloads to `.slot`; the `defsOf_ne_gas` twin). Old form true but state-quantified; replaced for uniformity |
| 4.2 | sstore: stack fold | — | PASS — static `StackRoomOK.sstore` |
| 4.3 | sstore: `vw ≠ 0` | coupled zero-writing frame (round-1 fix D) | PASS — under the threaded `NonzeroSstores fr0` antecedent; derivation path: clean-halt gives the materialise run to the SSTORE op, `Corr`'s channels pin the stacked value to `st0.locals value` |
| 5.1 | call: `StepScopedS (.call cs)` (in `CallRealisesS`) | (old embedded `hscope`) program `[call{…,some t5}; t9 := add t5 t5]`, `st0 = {t5↦0, t9↦0}` is Corr-consistent (`DefsSound`: `0 = 0+0`; `wellScoped`: `t5` spilled, `t9` registered) ⇒ old clause REFUTED in-envelope (not at exProg — nothing reads `t5`) | PASS now — `isCallResult` from cursor membership |
| 5.2 | call: oracle pin / argsLen / arg-push run+pins / `CallReturns` / resume pins | OOG-at-CALL frame (round-1) | PASS — value/trace kernel under the `CleanHaltsNonException` antecedent, `fr0` + restart determinism (unchanged this round) |
| 5.3 | call: post-state wellScoped fold | as 1.3 + result tmp | PASS — prior-live from the `Corr` antecedent (world swap keeps locals); result tmp slot-registered via `defsCons`'s call clause |
| 5.4 | call: Route-B tail (`∀ flag …` anchors/gas/endFr) | stack-coincident foreign frame | PASS — `flag` antecedent-pinned by the resume stack pin; anchors static at the pinned pc; gas/endFr from `fr0`'s future under clean halt |
| T.1 | stop: `¬(accounts == ∅)` | empty-accounts frame | PASS — `SelfPresent` is an antecedent (supplied by the walk); `accounts_ne_empty_of_selfPresent` |
| T.2 | ret: charge sum ≤ gas; length ≤ 1024 | zero-gas `frT` | PASS — clean-halt antecedent (an under-gassed materialise would exception); length static (`StackRoomOK.ret`) |
| T.3 | ret: epilogue `∀ vw, ∀ frv` block | value-coincident foreign frame elsewhere in the run (round-1 fix C) | PASS — pc-pin antecedent makes the decode conclusions static anchors; kind/presence via `Runs`-preservation from the antecedent pins |
| T.4 | jump: 3 gas guards | zero-gas `frT` (skeptic sub-claim 4) | PASS — under `CleanHaltsNonException` (`jump_landing_of_cleanHalt`) |
| T.5 | branch: `∃ frc, MatRuns … cw …` + 6 guards | stale cond (the lesson-8 worry, aimed at the terminator) | PASS — stated at the block-END boundary where `Corr` (strong `DefsSound`) is an antecedent and exProg's `t8` was JUST reassigned; `cw` antecedent-pinned; guards under clean halt. NOTE: this boundary is exactly what R0b criterion (2) must re-establish (`RevalidatesPerBlock`) |
| H.1 | `DefsConsistent` (hypothesis) | — | satisfiable: TRUE at every exProg def-site (round-2 `#eval` check) |
| H.2 | `RunDefinableG` (hypothesis, ∀ over states) | unbound-operand entry states | satisfiable at exProg: prefix-runs bind each cursor's operands from ANY block-entry state; R9's anchor forces it |
| H.3 | `DriveCorrLog`/`RecorderCoupled` (walk invariant) | mid-block staleness | boundary-only by construction — iteration-ENTRY states are mutually consistent at exProg (staleness is strictly mid-block), so the invariant remains satisfiable at every iteration |
| N.1 | `DefsSoundS`/`invalStep` (new) | semantic-set tautology; foreign-statement rebind vs R0b | not tautological (set is explicit static data, not "stale"); R0b carries site premises + `DefsConsistent` precisely because the unpinned version is refutable |
| N.2 | `RevalidatesPerBlock` (new) | a block that rebinds without healing | discriminating: false for `[t := gas; u := lt t t7]`-style blocks that end with `u` unhealed; TRUE at exProg (fold trace: block 1 = ∅ → {t8} → {t8} → ∅) |

### Build/verification record (round 3)

- `lake env lean LirLean/RealisabilitySpec.lean`: clean — only `declaration uses
  'sorry'` warnings, **25** of them = 23 prior + 2 new tracked obligations (R0b
  `defsSoundS_preserved_step`, `revalidatesPerBlock_exProg`). New PROVED (non-sorry)
  anchors: `defsSoundS_empty_iff`, `not_defsSound_stale`.
- `lake build Nightly`: **Build completed successfully (1159 jobs)**.
- `lake build` (default): **Build completed successfully (1164 jobs)** — untouched.
