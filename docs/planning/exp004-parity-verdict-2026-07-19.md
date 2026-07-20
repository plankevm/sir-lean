# exp004 parity-push verdict — 2026-07-19

Verdict on the overnight exp004 completion push (tracks T1–T5, commits `2b6cbb22`,
`f96183e9`, `6315c911`, `37a61dd0`, `002a0b2d` on `codex/sir-internal-functions`),
answering the question posed by `docs/flat-vs-nested-convergence.md` §1.3 (:162–187):
**does the nested semantics now have, or have a clear path to, parity with the flat
reasoning surface — and all-things-considered which encoding is cheaper?**

All claims below were verified against the *committed* files (declarations grepped,
endgame statement read in full, sorry census re-run: **0 repo-wide**; every grep hit is
docstring prose). Reviewer-run `#print axioms` on every flagship:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `ofReduceBool`, no new
axioms. All five tracks approved (two with non-blocking nits). One known loose end:
the per-track addenda to `docs/planning/exp004-completion-shape-2026-07-18.md` are in
the working tree but uncommitted (outside the tracks' allowed commit paths); they
should be swept up in a doc commit.

---

## 1. What landed

Sorry ledger: the night started at 3 sorries (ThetaRuns keystone pair + the
ObservableTriple endgame) and ended at **0** — the endgame was *proved*, the keystone
pair was *refuted and deleted* (see §4). No `maxHeartbeats` crank anywhere in T1–T3;
T4/T5 needed three per-theorem cranks (8M for the 140-leaf `step_fuel_irrelevant`
sweep, 1M/4M for `lambda_of_xi`/`create_spec`), each docstring-noted.

### Theorem table (all PROVED unless marked; axioms as reviewer-verified)

| Track / file | Deliverables | Status |
|---|---|---|
| **T1** `NestedEvmYul/XLoop.lean` (new, 519→648 lines after T4) | Dispatcher equations `step_eq_shared_{push1,push0,sstore,jump,jumpi,stop}` (bare `rfl`), `step_call_eq`; shared-arm forwards `shared_step_*` (incl. `jumpi_taken`/`fallthrough`); `X_iter`, `X_iter_halt`; per-opcode rules `X_push1`, `X_push0`, `X_sstore`, `X_jump`, `X_jumpi_taken`, `X_jumpi_fallthrough`; CFG combinator `X_branch`; sequencing `IterStepU`/`IterHaltU`/`ItersN` (refl+tail) + `ItersN.single`/`.trans`, `IterStepU_X`, `ItersN_X`, `X_decompose`, intro rules `IterStepU.*`, `IterHaltU.stop`; `LawfulBEq UInt256` instance | all proved, axiom-clean, zero cranks |
| **T2** `ThetaRuns.lean` (rewritten), `ObservableTriple.lean` (migrated) | `ΘRuns` re-encoded offset-cofinal (`∃ k, ∀ f, Θ (k+f) … = .ok res`); `ΘRuns.intro`, `ΘRuns.deterministic` (6 lines — the study's keystone tax deleted), `ΘRuns.runΘ_complete'` (adequacy under `k ≤ seedFuel w`); `step/X/Xi_stop_cofinal`; `Θ_doNothing`, `seedFuel_ge_four`, `ΘRuns_doNothing(_runΘ)`; `ΘRuns_completedWith` migrated to the cofinal vocabulary | all proved, axiom-clean; keystone pair quarantined (later refuted by T4) |
| **T3** `TwoCallDemo.lean` (new, 489 lines) | `Std.TransCmp AccountAddress` + `addrCompare_eq_iff`; existential-free STOP chain `X_stop_explicit`/`Xi_stop_explicit`; `Θ_stop_forward` (∀-fuel Θ *equation*); universal habsorb leg `credit_stage`/`debit_stage`/`thetaTransfer_find?`; `demoTriple` (`theta_of_xi` fired); firing equations `demo_call₁/₂` (`call (f+5) … = .ok (⟨1⟩, demoAfter₁/₂)` at every fuel, fully explicit post-states); `demo_twoCall` (`twoCall_spec` with all six hypotheses discharged), `demo_twoCall_storage` (cell ⟨0⟩ reads ⟨42⟩, derived from `Q` alone) | all proved, axiom-clean, fully concrete |
| **T4** `ObservableTriple.lean`, `ThetaRuns.lean`, `XLoop.lean`, `XiTriple.lean` | **Endgame `nested_twoCall_completedWith` PROVED** (flat `twoCall_completedWith` mirror: ItersN prefix/middle, two call sites with cofinal call families and both `ThetaTriple`s firing via `call_spec`, empty suffix, `hread` *derived* from `Q₂`, fuel envelope `n₁+n₂+k₁+k₂+6 ≤ seedFuel w`); plumbing `Xi_forward`, `Θ_code_forward`, `X_call_iter`, `X_stop_halt`, `Z_ok_toState`; **keystone `Θ_fuel_mono_ok/_error` REFUTED** (false as stated — CREATE arm's `\| _ =>` catch-all absorbs inner Λ OutOfFuel into a non-error result; Semantics.lean:286/:344) and deleted with post-mortem; salvaged `step_fuel_irrelevant` (≈130 non-call/create arms) | endgame + plumbing axiom-clean; keystone disposition verified by reviewer against vendored source |
| **T5** `LambdaTriple.lean` (new, 368 lines) | `Lambda_zero`; `LambdaTriple` (∀-fuel, success-gated, address-first 7-tuple, `Q` parametric in created address — hash never evaluated); `.conseq`/`.conj`; `lambdaInit`/`createInit` (source-transcribed preambles); `lambda_of_xi` (EIP-7610 collision as disjunctive code premise); `lambda_success_out_empty`; **`create_spec`** (stretch half landed: CREATE-arm inversion, `hx`-gated) | all proved, axiom-clean; **nested-only surplus** — flat has no Λ-level rule |

Nothing was sorried; nothing failed except the keystone, which turned out to be
*false*, not hard (a strictly more informative outcome). No substitutions to the plan
beyond two recorded corrections (`X_decompose` fuel offset `f+n+2`; the `LawfulBEq
UInt256` instance).

---

## 2. The X-loop verdict: the logic-free zone was colonized

`flat-vs-nested-convergence.md` §1.3's charge was that nested had "essentially nothing
above Θ" — no `Runs`, no opcode rules, no CFG combinator, no observable projection.
That is no longer true. Mapping the flat inventory at :163–168 item-by-item:

| Flat surface (:163–168) | Nested analog now | Status |
|---|---|---|
| `Runs` (`refl`/`step`/`call`) + `Runs.trans` | `IterStepU`/`IterHaltU`/`ItersN` (refl+tail) + `ItersN.single`/`.trans`, `X_call_iter` for the call step | **built, proved** |
| seven `runs_*` opcode rules | six `X_*` rules (PUSH1/PUSH0/SSTORE/JUMP/JUMPI×2) + `IterStepU.*` intros + `step_call_eq`/`X_call_iter` for CALL | **built, proved** (comparable coverage; extending to more opcodes is mechanical — each is a `rfl`-grade dispatcher equation plus a one-term composition) |
| `runs_branch` CFG combinator | `X_branch` (motive-parametric, `by_cases`) | **built, proved** |
| `Runs.call` composition + `drive_reconcile` | `call_spec`/`twoCall_spec`/`theta_of_xi` (pre-existing shape, now *fired* concretely by T3 and consumed by the T4 endgame) | **built, proved, demonstrated** |
| `Observables`/`Outcome`/`completedWith` | `ObservableTriple.completedWith` + `ΘRuns_completedWith` + endgame `nested_twoCall_completedWith` | **built, proved** |
| `messageCall_runs` bridge | — | **gap** (§4) |
| `Behaves` for-all-programs predicate | — | **gap** (§4) |
| *(no flat counterpart)* | `LambdaTriple` + `create_spec` (CREATE-side triple + creation-site inversion) | **nested-only surplus** |

**What technique worked.** The single decisive discovery is the
**dispatcher-equation technique**: the vendored 140-arm `step` match — previously the
emblem of nested misery — yields per-opcode equations by *bare `rfl`* (concrete-op
defeq is even cheaper than the priced estimate; zero heartbeat cranks in all of T1).
It paid off three separate times: (1) per-opcode `X_*` rules, (2) fuel-free RHSes make
uniform-witness hoisting definitional, enabling T2's cofinal encoding, (3)
existential-free producers (`stopGas` a plain def rather than `∃ g'`) enable T3's
forward `rw`-evaluation and hence genuine firing equations. Supporting recipes that
generalized: state-destructure+`subst`+`rfl` for inline match arms (replacing
`show`/`Bool.noConfusion` gymnastics); `conv_lhs => unfold X`; goal-side `split` tied
by `(hΞ f).symm.trans heq` for forward Θ-unfolds across the `thetaTransfer` defeq;
`show`-based defeq change where `simp only []` fails to iota-reduce do-desugared
matches over `Except.ok` literals.

**What failed.** Only the fuel-monotonicity keystone — and it failed by being *false*
(see §4's keystone entry), which retroactively justifies the entire T2 pivot.
The naive endpoint-sharing call-site tie was confirmed refutable (every `step`
successor carries the `execLength+1` bump + `replaceStackAndIncrPC` postprocessing);
`step_call_eq` made the correct tie stateable, and the endgame's `hcallᵢ` families are
exactly that shape, never hypothesizing the successor.

**Verdict: colonized.** Nested-native per-opcode reasoning is cheap (T1's GO signal,
reviewer-endorsed), the composition surface fires end-to-end on a fully concrete
two-call program (T3 — *more* concrete than flat's hypothesis-supplied `Runs`
witnesses in `TwoCallExample.lean`), and the endgame theorem sits at the same altitude
as flat's `twoCall_completedWith` with the storage read *derived* from the callee's
postcondition.

---

## 3. The ∀-fuel pivot: correct by necessity, not just cheaper

T2 re-encoded `ΘRuns` from `∃ fuel, Θ fuel … = .ok res` to offset-cofinal
`∃ k, ∀ f, Θ (k + f) … = .ok res`. Outcomes:

- `ΘRuns.deterministic` collapsed from the study's underscore-wall keystone tax to 6
  lines (instantiate crosswise, `Nat.add_comm`, `Except.ok.inj`).
- Adequacy survives as `runΘ_complete'` under the side condition `k ≤ seedFuel w`;
  the honest surrenders (`of_runΘ`, unconditional adequacy) are documented as the API
  boundary, not hidden.
- The ∀-fuel `IterStepU` step clause makes fuel transport structurally unnecessary in
  the decomposition layer — the keystone's blast radius shrank to the veneer only.
- **T4 then proved the pivot was the *only correct* encoding, not merely the cheaper
  one**: `Θ_fuel_mono` is false (the CREATE/CREATE2 `| _ =>` catch-all absorbs an
  inner `Lambda` OutOfFuel into `(0, ∅-map, ⟨0⟩, False, .empty)` — a non-error,
  fuel-dependent result), so the existential encoding could never have been given a
  monotone veneer. The `k ≤ seedFuel w` side condition is load-bearing and permanent.
  (Caveat on record: an in-Lean kernel refutation is blocked by `opaque ffi.KEC` —
  the falsity argument is a reviewed source-level reading, same keccak wall as exp005.)

This is the pivot's final scorecard: it deleted a 2-sorry keystone, deleted the
underscore-wall determinism tax, cost one explicit offset argument at the consumer
seam, and turned out to be forced by the semantics rather than chosen for
convenience.

---

## 4. Remaining parity gaps, with effort estimates

Named gaps (no full-parity claim is made in any committed file — verified):

1. **`Behaves`-style for-all-programs predicate** (flat:
   `BytecodeLayer/Hoare/Behaves.lean#L45`). The nested vocabulary it would quantify
   over now exists (`ItersN`/`X_decompose`/`completedWith`). Estimate: **~1
   track-night** — definitional layer plus transport lemmas; no new proof technique
   required.
2. **`messageCall_runs`-bridge analog** — the theorem connecting the top-level
   entry point to the reasoning layer with reconciliation (flat's
   `drive_reconcile` role). `Θ_code_forward`/`ΘRuns_completedWith` are most of the
   plumbing; what's missing is the general veneer over arbitrary `NestedWorld`
   seeding. Estimate: **1–2 track-nights**, riskiest item (it touches the
   `seedFuel` side-condition arithmetic end-to-end).
3. **Concrete caller through the endgame** (acceptance test): the endgame's segment
   data enters as hypotheses — the same altitude as flat's `Runs` hypotheses, so this
   is parity-neutral — but a fully concrete two-CALL caller driven through
   `nested_twoCall_completedWith` was not built. T3's demo pieces (`demo_call₁/₂`
   produce exactly the `hcallᵢ` shape with `kᵢ = 5`) make this an assembly job.
   Estimate: **~1 night**.
4. **CREATE follow-through** (T5 was *attempted and landed*, ahead of plan — the
   triple surface plus `create_spec` are a nested-only surplus over flat). Remaining:
   a TwoCallDemo-style firing discharging `hx`/`hP` concretely (non-vacuity of
   `create_spec` is currently by proof structure only — reviewer nit), and the CREATE
   endgame/observable layer. Estimate: **~1 night** for the firing demo; endgame
   larger and not parity-relevant (flat has no CREATE reasoning either).
5. **Excluded by design — conformance execution infra**: nested still has no in-repo
   `lake exe conform` harness wired up (`flat-vs-nested-convergence.md` §1.4 lineage
   row notes EVMYulLean upstream has one). This was out of scope for the push and
   remains the largest engineering (not proof) item; estimate **multi-day
   engineering**, orthogonal to the reasoning-parity question.
6. **Structural residue, not closable**: the `k ≤ seedFuel w` side condition
   (keystone falsity, §3) and the conditional never-OOF bound (`fuelBound g e + 3 ≤
   fuel ∧ e ≤ 1024` vs flat's unconditional theorem) are permanent asymmetries in
   flat's favor.

---

## 5. Final verdict (updates `mixed-step-theory-notes-2026-07-18.md` §6)

§6's decisive-gap sentence — "the repo holds no data point on nested-native
*reasoning*" — is now **obsolete: the data point exists and it is favorable**. The
overnight push built, sorry-free and axiom-clean (`[propext, Classical.choice,
Quot.sound]` throughout, reviewer-verified), the nested analog of nearly the entire
flat surface enumerated at `flat-vs-nested-convergence.md:163–168`: chain vocabulary
with per-opcode rules and a CFG combinator, a fired call-composition triple, the
observable `completedWith` layer, and the flat-endgame mirror
`nested_twoCall_completedWith` — plus a CREATE-side triple flat does not have. §6's
misattribution finding is *confirmed and strengthened*: once the dispatcher-equation
technique neutralized the 140-arm vendored match, per-opcode reasoning closed by bare
`rfl` with zero heartbeat cranks, i.e. the historical misery really was incidental,
not intrinsic to nesting. But one genuinely *intrinsic* cost surfaced that §6 did not
predict: **nested Θ fuel-monotonicity is false** (the CREATE catch-all absorbs inner
OutOfFuel), so the ∀-fuel cofinal encoding with its `k ≤ seedFuel w` side condition
is forced, and unconditional adequacy is unrecoverable — a permanent, small,
honestly-documented ergonomic tax that flat (unconditional never-OOF, true fuel
threading) does not pay. **Answer to THE question: parity is not yet fully reached —
two named gaps remain (`Behaves` analog, `messageCall`-bridge analog), each estimated
at 1–2 track-nights on now-proven techniques, so the path is short and de-risked; and
all-things-considered the encodings are now at *technique parity* for program logic,
with flat cheaper at the top-level boundary (unconditional adequacy, shipped bridge,
conformance harness) and nested cheaper at the call/CREATE seam (subterm triples fire
directly; `LambdaTriple`/`create_spec` came as a one-night surplus). Neither
dominates: choose per-layer by what the proofs consume — which is exactly standing
conclusion 1 of the mixed-step notes, now backed by data on both sides.**

---

## Addendum (2026-07-20, T4 night-3): gap #2 closed — `MessageBridge`, and the
## envelope's final honest status

*Append-only addendum; nothing above is rewritten. New file:
`experiments/004_nested_evmyul/NestedEvmYul/MessageBridge.lean` (sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]`, build green).*

### What landed

1. **The general bridge** (`runΘ_of_X_family`): for ANY `NestedWorld` `w` with
   `w.c = .Code cd`, a cofinal `X` success family on `callerEntry w cd` at
   offset `m` with `m + 4 ≤ seedFuel w` and the non-firing rollback guard pins
   `runΘ w` — the endgame's inline steps (2)–(4)
   (ObservableTriple.lean:352–396) hoisted into one reusable theorem.
2. **The split that locates the side condition.** `ΘRuns_of_X_family` proves
   the SAME family enters the fuel-free veneer with **no envelope** (pure
   cofinal introduction). So the nested side's `≤ seedFuel w` residue lives
   entirely in *adequacy* (veneer → seeded driver), not in the layer crossing
   — the precise nested location of what flat gets free from true
   fuel-monotonicity.
3. **The program-level driver** (`runΘ_of_decomposition` +
   `completedWith_of_decomposition`): `ItersN` chain + `IterHaltU` halting
   link (X_decompose's inputs) in, top-level `runΘ` equation and observable
   `completedWith` out — the flat `messageCall_runs` (Spec.lean:70) analog
   with segment data entering as chain values, as flat's `Runs` argument does.
4. **The risky half PARTIALLY SUCCEEDED — envelope DERIVED on the call-free
   fragment.** New gas-witnessed link/chain vocabulary (`IterStepG`/`ItersG`,
   forgetful maps into `IterStepU`/`ItersN`, all six straight-line intro rules
   lifted with `decide`-discharged witnesses): every link provably burns ≥ 1
   gas (`Z_ok_gas` inversion + `gas_EVM_step_default` +
   `C'_pos_of_runnable`), so chain length ≤ `w.g.toNat`, and
   `seedFuel_ge_gas` (`w.g.toNat + 11 ≤ seedFuel w`, from `fuelBound_ge`)
   absorbs the offset. Headline `completedWith_of_gasDerived`: observable
   conclusion with **no numeric fuel hypothesis at all** — only the
   structural `w.e ≤ 1024` depth cap.

### The obstruction (why the derivation stops there — §4 item 6 sharpened)

* **CREATE-absorption leak, again:** a CREATE link *can* inhabit `IterStepU`
  (eternally-failing/absorbed creates satisfy a `∀`-fuel step clause via the
  Semantics.lean:286/:344 catch-all), and proving even those debit ≥ 1 gas
  crosses the arm's `.ofNat (a − L a + g′)` reconstitution, whose wrap-safety
  needs child gas conservation (a `Lambda`-level induction). Hence
  `¬ isCallCreate` is carried as a witness, not derived.
* **CALL links are uninhabited but not worth refuting:** `call 0 = .error
  .OutOfFuel` propagates honestly, so the `f = 0` instance kills any
  CALL-family `∀`-fuel step clause — but discharging that needs a CALL-arm
  sweep for a door real programs never use (call sites enter as
  `X_call_iter` cofinal families).
* **Call OFFSETS are the irreducible residue (the quantitative refinement of
  item 6):** in a composed family `m = Σnᵢ + Σkᵢ + c`, gas pays for the
  `Σnᵢ` (now proven) but the `kᵢ` are the children's fuel budgets —
  `fuelBound`'s PRODUCT `(1025 − e)·(g + fuelHops)` per descent. No
  linear-in-gas premise can bound `Σkᵢ`; collapsing the depth factor is
  exactly re-proving NeverOutOfFuel's stage-2 recurrence. Verdict: the
  envelope on the general bridge is permanent for a *quantitative* reason
  (product vs sum) on top of the qualitative one (keystone FALSE).

### Residual

The optional endgame refactor (making `nested_twoCall_completedWith` consume
the bridge) was skipped on import-direction friction (the bridge lives
downstream of ObservableTriple); ~20 duplicated proof lines, flagged in the
bridge's module docstring. Both §4 named gaps (#1 `Behaves`, #2 bridge) are
now closed.
