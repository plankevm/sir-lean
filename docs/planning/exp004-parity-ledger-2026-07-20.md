# exp004 parity ledger — night 3 (2026-07-20)

**Scope:** closes out the night-3 parity push (tracks T1–T5) against the charge sheet of
`docs/flat-vs-nested-convergence.md` §1.3 (:162–187) and the named gaps of
`docs/planning/exp004-parity-verdict-2026-07-19.md` §4. All entries verified against the
actual commits on `codex/sir-internal-functions`:

| Commit | Track | File |
|---|---|---|
| `45bff523` | T1-behaves-analog | `experiments/004_nested_evmyul/NestedEvmYul/Behaves.lean` (229 lines) |
| `0d2fa198` | T2-concrete-endgame-caller | `experiments/004_nested_evmyul/NestedEvmYul/EndgameDemo.lean` (524 lines) |
| `62ea4e54` | T3-create-firing-demo | `experiments/004_nested_evmyul/NestedEvmYul/CreateDemo.lean` (410 lines) |
| `39420ce4` | T4-messagecall-bridge-STRETCH | `experiments/004_nested_evmyul/NestedEvmYul/MessageBridge.lean` (488 lines) |
| *(uncommitted, docs)* | T5-fuel-laundering-investigation | `docs/planning/fuel-laundering-note-2026-07-20.md` |

All four Lean tracks: build green, zero sorries, reviewer-run `#print axioms` on every
headline declaration = `[propext, Classical.choice, Quot.sound]`. All five tracks
gate-approved (T5 approve-with-nits; the gate itself corrected one substantive claim in
the note — see §3 below). T5 was read-only by charter: zero `.lean`/vendored edits.

---

## 1. Updated parity ledger (vs `flat-vs-nested-convergence.md:162–187`)

The §1.3 charge — "nested has essentially nothing above `Θ` … no `Runs`, no observable
projection, no `Ξ`-triple, no frame rule as a theorem" — is now **fully answered**,
item by item. This ledger supersedes the table in `exp004-parity-verdict-2026-07-19.md` §2.

| Flat surface (:163–168) | Nested analog | Status after night 3 | Remaining effort |
|---|---|---|---|
| `Runs` (`refl`/`step`/`call`) + `Runs.trans` | `IterStepU`/`IterHaltU`/`ItersN` (refl+tail) + `.single`/`.trans`, `X_call_iter` | **built, proved** (night 2) | none |
| seven `runs_*` opcode rules | six `X_*` rules (PUSH1/PUSH0/SSTORE/JUMP/JUMPI×2) + `IterStepU.*` intros + `step_call_eq` | **built, proved**; extending coverage is mechanical (`rfl`-grade dispatcher equations) | none for parity; per-opcode extension on demand |
| `runs_branch` CFG combinator | `X_branch` | **built, proved** (night 2) | none |
| `Runs.call` composition + `drive_reconcile` | `call_spec`/`twoCall_spec`/`theta_of_xi`, fired concretely | **built, proved, demonstrated** | none |
| `Observables`/`Outcome`/`completedWith` | `ObservableTriple.completedWith` + `ΘRuns_completedWith` + `nested_twoCall_completedWith` | **built, proved** (night 2) | none |
| `messageCall_runs` bridge | **`MessageBridge.lean`** (`39420ce4`): `runΘ_of_X_family`, `runΘ_of_decomposition`, `completedWith_of_decomposition`, `ΘRuns_of_X_family`, gas-derived `completedWith_of_gasDerived` | **CLOSED night 3** (was §4 gap #2) | none; see §2 for the honest envelope residue |
| `Behaves` for-all-programs predicate | **`Behaves.lean`** (`45bff523`): `Behaves` at the shared-observable altitude, `.conseq`/`.conj`, producers `behaves_of_cofinal`/`behaves_of_thetaTriple`, non-vacuity `behaves_doNothing`, consumer `Behaves.storage_out` fired hypothesis-free at a concrete 19-field world (`doNothingWorld_storage_zero`) | **CLOSED night 3** (was §4 gap #1); parity **exceeded** — flat's `Behaves` has zero producers AND zero consumers (grep-verified) | none |
| *(acceptance test, §4 item 3)* concrete caller through the endgame | **`EndgameDemo.lean`** (`0d2fa198`): `egEndgame` discharges all ~20 hypotheses of `nested_twoCall_completedWith` on a concrete 31-byte two-CALL world; punchline `endgame_fired` is hypothesis-free (`tag = "ok"`, `storageAt 0xff 0 = 42`); `#eval` cross-check confirms cold-then-warm CALL gas (100000 − 42 − 2600 − 100 = 97258) | **CLOSED night 3**; *more* concrete than flat's hypothesis-supplied `TwoCallExample` | none |
| *(no flat counterpart)* CREATE triple surface | `LambdaTriple` + `create_spec` (night 2) + **`CreateDemo.lean`** (`62ea4e54`): concrete `demoCreateTriple` via `lambda_of_xi` with all three side conditions discharged (incl. an honest semantics-grounded EIP-7610 collision arm via `Xi_invalid`), `demo_create` firing `create_spec` down to the keccak wall (`hstep`/`hx` only) | **nested-only surplus, non-vacuity nit killed night 3** | CREATE endgame/observable layer optional; not parity-relevant (flat has no CREATE reasoning) |
| unconditional adequacy / fuel-monotone veneer | `runΘ_complete'` under `k ≤ seedFuel w`; `Θ_fuel_mono` refuted (night 2), envelope now **derived from gas** on the call-free fragment (`completedWith_of_gasDerived`: no numeric fuel hypothesis, only `w.e ≤ 1024`) | **permanent structural asymmetry in flat's favor**, now precisely located and quantified (§2) | not closable as-is; contingent on the fuel-laundering decision (§3) |
| conformance execution infra (`lake exe conform`) | — | **still excluded by design** (out of scope for all parity nights) | multi-day engineering (§4) |

**Bottom line: every named reasoning-parity gap from the verdict's §4 (#1 Behaves, #2
bridge, #3 concrete endgame caller, #4 CREATE-firing non-vacuity) is now closed and
committed.** What remains is structural residue (fuel envelope) and engineering
(conformance harness), not proof-surface parity.

---

## 2. The messageCall-bridge outcome (verdict §4 gap #2 — LANDED, with a precisely-priced residue)

`MessageBridge.lean` (`39420ce4`, 21 declarations, axiom-clean) delivers:

1. **General bridge** `runΘ_of_X_family`: for ANY `NestedWorld w` with `w.c = .Code cd`,
   a cofinal `X` success family at offset `m` with `m + 4 ≤ seedFuel w` pins `runΘ w` —
   the endgame's inline steps hoisted into one reusable theorem. This is the flat
   `messageCall_runs` (`EVM/BytecodeLayer/Spec.lean:70`) analog.
2. **Side-condition localization**: `ΘRuns_of_X_family` proves the same family enters
   the fuel-free `ΘRuns` veneer with **no envelope** — so the `≤ seedFuel w` residue
   lives entirely in adequacy (veneer → seeded driver), not in the layer crossing.
3. **Program-level drivers**: `runΘ_of_decomposition` + `completedWith_of_decomposition`
   (ItersN chain + halting link in, top-level `runΘ` equation + observable out).
4. **Stretch half — envelope DERIVED on the call-free fragment**: gas-witnessed chains
   `IterStepG`/`ItersG` (every link burns ≥ 1 gas, so chain length ≤ `w.g.toNat`;
   `seedFuel_ge_gas` absorbs the offset), yielding `completedWith_of_gasDerived` with
   **no numeric fuel hypothesis at all**.

**The precise obstruction (why the envelope is permanent on the general bridge)** —
recorded in the module docstring and the verdict addendum:

- **(A) CREATE-absorption leak**: absorbed creates inhabit `IterStepU`; proving even
  those debit gas needs child gas conservation (a `Lambda`-level induction).
- **(B) CALL links uninhabited but not worth refuting** (`call 0` OOFs, killing any
  ∀-fuel CALL step clause; refutation costs a CALL-arm sweep for a door nothing uses).
- **(C) the irreducible, quantitative one**: call offsets `kᵢ` are children's *fuel
  budgets* — `fuelBound`'s PRODUCT `(1025 − e)·(g + 8)` per descent. No linear-in-gas
  premise bounds `Σkᵢ`; collapsing the depth factor = re-proving NeverOutOfFuel's
  stage-2 recurrence. So the envelope is permanent for a **product-vs-sum** reason on
  top of the qualitative keystone falsity.

Residual: the optional refactor making `nested_twoCall_completedWith` consume the bridge
was skipped on import-direction friction (~20 duplicated lines, docstring-flagged).

---

## 3. Fuel-laundering investigation (T5) — findings and THE DECISION EDUARDO NEEDS TO MAKE

Full note: `docs/planning/fuel-laundering-note-2026-07-20.md` (read-only investigation;
gate re-verified every citation, including a live re-check of upstream). Headline
findings, **verbatim from the note**:

> **Verdict on this sub-question: the arm is not merely unfaithful, it is also
> state-corrupting on the absorbed path.** Every subsequent SLOAD/BALANCE/CALL in
> the parent frame reads a wiped world, and the wipe propagates up through
> `X`/`Ξ`'s success packaging (`:559-563` returns `evmState'.accountMap`).

(That is: on the CREATE/CREATE2 catch-all path, `accountMap := ∅` **survives into the
returned `.ok` state** — a new finding beyond the charter's suspicion. The parent also
permanently forfeits `L(gasAvailable)` with `g' = 0`.)

> **Confirmed conclusion (the seeded question, sharpened):** a child's genuine
> GAS exhaustion arrives as `Ξ = .error .OutOfGass` and is *already* packaged by
> `Lambda` as a `z = false` failed create — it never reaches the step arm as an
> error. The catch-all's live input is therefore **exclusively interpreter-FUEL
> exhaustion** (plus a provably-dead RLP branch). The arm is not modeling the
> legitimate failed-create outcome — `Lambda:661` already does that, correctly.
> It is laundering the model-internal totality device (fuel) into a semantic
> result (a failed create with a wiped world and forfeited gas).

> **The CREATE/CREATE2 arms at `:286`/`:344` are the only place in the entire
> nested tower where `.OutOfFuel` is converted into a non-error result.**

Flat comparison (verbatim): "flat genuinely avoids the leak **by construction**, not by
a more careful arm: fuel-vs-gas conflation requires an inner-interpreter result to
launder, and flat has no inner interpreter." (`drive_fuel_mono` is ~10 lines vs the
nested keystone's ~1500-line pricing.)

Upstream (checked live 2026-07-20): NethermindEth/EVMYulLean `main` HEAD `047f6307`
(2025-09-23, dormant ~10 months) still has both catch-alls byte-identical; no upstream
fix exists; a report would be novel and can cite the ∅-map corruption.

**Gate correction Eduardo should read before deciding** (fixed in the note's §7(a)):
the claim that the absorbed path "never fires on the proved envelope" is design intent,
**NOT a proved invariant** — `Θ_never_outOfFuel`'s CREATE cases are discharged by the
unconditional swallow lemmas themselves (`noOOF_step_create*`, used at
`NeverOutOfFuel.lean:4570-4571`), so the theorem holds *even if* the arm fires inside a
seeded run; no in-tree theorem rules that out.

### The decision (note §7, verbatim trade-off menu — no recommendation-as-decision):

> **(a) Status quo.** Keep the vendored tree untouched; the offset-cofinal
> `ΘRuns` encoding stays the permanent adequacy surface, `k ≤ seedFuel w` stays
> load-bearing, and this note plus the ThetaRuns post-mortem document the
> residue. *For:* zero cost, never-edit-vendored rule intact, the cofinal
> encoding is already proven correct and sufficient for everything exp004
> currently claims; the absorbed path is *believed* unreachable under the
> `fuelBound` seeding used by all headline theorems (the product seed is sized
> so inner `Lambda` descents never bottom out). **Precision caveat (gate
> review):** that unreachability is design intent, NOT a proved invariant —
> `Θ_never_outOfFuel`'s CREATE cases are discharged by the unconditional
> swallow lemmas themselves (`noOOF_step_create*`, used at
> `NeverOutOfFuel.lean:4570-4571`), so the theorem holds *even if* the arm
> fires inside a seeded run; no in-tree theorem rules that out. *Against:* the
> model, taken as a definition, remains unfaithful off-envelope (wrong result
> AND wiped world at insufficient fuel) — and per the caveat above, on-envelope
> avoidance of the arm is itself unproven; and `Θ_fuel_mono` remains
> unprovable — permanently forfeiting single-fuel introduction.
>
> **(b) Minimal vendored patch** (two-line `| .error e => .error e`, both arms).
> **Requires Eduardo's explicit authorization to break the never-edit-vendored
> rule.** *For:* fixes laundering + gas forfeiture + state wipe at the root;
> turns `Θ_fuel_mono` provable-in-principle; simplifies `create_result_gas_le` /
> `create_spec` error branches; honest CALL/CREATE symmetry. *Against:* diverges
> the vendored subtree (future upstream syncs conflict); triggers a moderate
> rework of `noOOF_step_create*` and their consumers (§4 table); the big prize
> still costs the ~1500-line mutual induction to actually collect; none of the
> currently-committed headline theorems *need* the fix.
>
> **(c) Upstream issue/PR to NethermindEth/EVMYulLean.** *For:* the bug is real
> upstream (semantic corruption on the absorbed path, not just a proof
> inconvenience); a merged fix lets exp004 re-vendor cleanly, combining (b)'s
> benefits without a local fork. *Against:* upstream is dormant (last commit
> 2025-09-23), so latency is unbounded; and an accepted fix still leaves the
> local pin at `066dc8b` until a deliberate re-vendor (its own churn). Composable
> with (a): report upstream now, stay on status quo until/unless it lands.

Note per §4 of the investigation: with fix (b), `runΘ_complete'`'s `k ≤ seedFuel w`
side condition becomes removable in principle (single-fuel introduction, unconditional
`of_runTheta` restored) — but only after the ~1500-line B3 keystone induction. The fix
buys the *option*, not the obligation.

---

## 4. What remains before declaring the bake-off answered

The reasoning-parity half of the bake-off question is **now answered with data on both
sides** (verdict §5's conclusion stands, strengthened by night 3: both named gaps
closed, acceptance test fired, CREATE non-vacuity witnessed). What still separates a
full "bake-off answered" declaration:

1. **The fuel-laundering decision (§3)** — decision-blocked on Eduardo, not
   effort-blocked. Under status quo (a), the ledger's asymmetry rows are final: the
   `k ≤ seedFuel w` adequacy residue and the conditional never-OOF are **permanent**
   costs of the nested encoding *as vendored*, and the bake-off's termination-ergonomics
   verdict (flat cheaper at the top-level boundary) is closed. Under (b)/(c) the
   asymmetry becomes *removable-at-a-price* (~1500-line keystone), which changes the
   bake-off's cost accounting, not its direction.
2. **Conformance execution infra (excluded by design, verdict §4 item 5)** — nested
   still has no in-repo `lake exe conform` harness; flat's executable-spec lineage runs
   conformance today. This is the largest single item and is **engineering, not proof**
   (multi-day). Until it exists, the bake-off's "conformance lineage" row is answered
   only by upstream EVMYulLean's harness, not in-repo — any final report must carry that
   caveat, or the harness must be wired up.
3. **Optional, not parity-blocking**: CREATE endgame/observable layer (flat has no
   CREATE reasoning to be at parity with); per-opcode `X_*` coverage extension
   (mechanical, on demand); the skipped endgame-consumes-bridge refactor (~20 duplicated
   lines); consolidation nits from the gates (`gas_sub_toNat` vs `gas_sub_le`;
   `Behaves.storage_out` ok-tag sibling; `completedWith_of_thetaTriple` `hc`-premise
   restatement).
4. **Housekeeping (working tree)**: two uncommitted doc artifacts predate this ledger —
   the T4 addendum to `docs/planning/exp004-parity-verdict-2026-07-19.md` (modified,
   verified good by the T4 gate) and `docs/planning/fuel-laundering-note-2026-07-20.md`
   (untracked, gate-corrected). Both should be swept into a docs commit.

**Proposed closure criterion**: the bake-off is answerable *now* for the reasoning-layer
question (verdict §5's per-layer conclusion, unchanged); it is answerable *in full* once
(1) is decided and either (2) is built or the final report explicitly scopes conformance
out as an engineering deferral.
