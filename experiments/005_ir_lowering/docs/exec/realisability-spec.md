# Track E — Realisability Spec Skeleton: design rationale (2026-07-02)

Deliverable: `LirLean/V2/RealisabilitySpec.lean` (namespace `Lir.V2`), registered as the
NON-DEFAULT `lean_lib Nightly` in `lakefile.lean`. All `def`s/`structure`s are REAL; the 23
`sorry`s are exactly the theorem proofs (R-obligations + 2 mirror-adequacy lemmas) — tracked
debt by design. `lake build Nightly` = 1159 jobs green (23 sorry warnings); default
`lake build` = 1164 jobs, untouched and sorry-free.

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
- A **loop caveat** on `SingleCall` is recorded in its docstring: a syntactically-single
  call inside a loop can fire dynamically more than once; `exProg` deliberately keeps its
  call outside the loop, and the R10/R11 grind must confirm or strengthen the premise
  (tracked with R3′).

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
which works because every conclusion is either a static program fact or computed from
`fr0` + restart determinism. That analysis (per arm, above) is what makes the reshape
non-vacuous rather than merely differently-shaped.

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
4. The `SingleCall` loop caveat and the zero-gas-revert cut — both are honest scope
   reductions; confirm they are acceptable seams rather than silent losses.
5. `recorderCoupled_call` (R7e) does not pin `rec` to the call's `(result, pending)`; the
   pin is delivered inside R3 via restart determinism. Confirm that split is provable.

## 6. Build/verification record

- `lake env lean LirLean/V2/RealisabilitySpec.lean`: clean at each of the three content
  commits (only `declaration uses 'sorry'` warnings).
- `lake build Nightly`: **Build completed successfully (1159 jobs)**, 23 sorry warnings.
- `lake build` (default): **Build completed successfully (1164 jobs)** — unchanged; the
  `LirLean` root does not import the new module (Track A owns its tail).
- Track-B-casualty grep (`MonotoneGas|GasRealises|gasMonotone|driveLog_gas_inv|
  realisedGas_monotone|geToNat|bound_mono|V2.Oracle|V2.Mono|HonestGasTie`): only prose
  lesson-mentions in docstrings; zero declaration references.
- No `#print axioms` in the Nightly module by design (§7 of the file): sorry'd decls carry
  `sorryAx`; guards migrate to `Audit.lean` obligation-by-obligation as sorries close.
