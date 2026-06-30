# CREATE / CREATE2 three-way consistency crosscheck

**Scope:** CREATE and CREATE2 only. Three-way: patched **EVMLean** (exp005 conformance base,
`experiments/003_bytecode_layer/EVMLean/Evm/Semantics/{System,Create,Interpreter,Halt}.lean`)
vs **EVMYulLean** (`experiments/004_nested_evmyul/EVMYulLean/EvmYul/EVM/Semantics.lean`)
vs the **Yellow Paper §7** (ground truth, `ethereum/yellowpaper` master `Paper.tex`).

This is a *deeper* follow-up to `semantics-crosscheck.md`, run **BEFORE** CREATE is added to the IR
surface, so a future `CreateSpec` / IR→CREATE lowering proof does not hit a reference surprise.
It explicitly closes the three open CREATE caveats the prior audit left dangling (§4).

Date: 2026-06-30.

---

## 1. Honesty banner

- **This is a read-only behavioral audit of the reference models, not a formal proof.** Nothing
  here is mechanized. Claims about arm equivalence were established by reading the Lean source and
  the YP text, not by a Lean `theorem`. A future `CreateSpec` conformance proof is what would make
  these claims load-bearing; this document is the *pre-flight reference check* for that work.
- **What was pulled from `Paper.tex` DIRECTLY (not via a Lean inline annotation):** §7 equations for
  Λ — `ADDR`/`L_A` (`\label{eq:new-address}`), the `σ*`/`a*`/`v'` setup, the `Ξ(σ*, g, A*, I)`
  init-code invocation, the consolidated failure predicate `F` (5 disjuncts), the `σ' / g' / A' / z`
  case blocks, `c ≡ G_codedeposit·‖o‖`, `DEAD`/EIP-161 pruning, and the OOG prose ("the evaluated
  state is defined as being the empty set ∅ … the entire create operation should have no effect on
  the state"). These are the citations marked **[YP-direct]** below.
- **What was verified directly against the Lean source in *this* checkout (not trusted from a
  summary):** the EVMLean patched begin-failure arm (`Interpreter.lean:60-82`,
  `accounts := exec.accounts`), the EVMYulLean `∅` catch-all (`Semantics.lean:286`/`:344`,
  `{evmState with accountMap := ∅}`), `resumeAfterCreate` gas/push (`Create.lean:153-174`), and the
  `beginCreate` `L_A`-none guard (`Create.lean:36`). These checks resolved a live contradiction
  between two candidate adjudications (see §4a).
- **What was NOT independently re-derived:** the per-field equality of the *success-deploy* happy
  path and the *internal* substate-warming traces were read once each; they are reported with their
  source line refs so the spec author can re-confirm. The EVMYulLean `Lambda` `where`-clause line
  numbers are taken from the audit (file confirmed present, not every line re-paginated).

---

## 2. Executive summary + headline verdict (project lead)

1. **GO for building `CreateSpec` against patched EVMLean.** No arm was found where patched EVMLean
   is the unfaithful side on a reachable, well-formed-transaction input. Every reachable
   CREATE/CREATE2 arm in patched EVMLean matches the YP and matches EVMYulLean observationally.
2. **The one genuine model-level divergence is EVMYulLean's fault, not EVMLean's.** EVMYulLean's
   `| _ =>` catch-all wipes the *entire caller world* to `∅` (`accountMap := ∅`,
   `Semantics.lean:286`/`:344`). **EVMLean has no such arm** — its begin-failure path preserves the
   caller world (`accounts := exec.accounts`, `Interpreter.lean:69-81`). So the engine you are
   proving against is the *faithful* one. This is the best possible orientation for the patch.
3. **NO arm where EVMLean is the unfaithful side.** (Stated loudly because that is the thing that
   would silently corrupt a CREATE proof — and it is absent.) Every candidate that *claimed*
   EVMLean was unfaithful turned out to be a source-misread (see §5).
4. **The EVMYulLean `∅`-wipe is UNREACHABLE on a gas-bounded well-formed tx.** It fires only via
   `OutOfFuel` (meta-interpreter fuel exhaustion, not part of EVM state). The address-derivation
   route into it (`L_A = none → StackUnderflow`) is **dead** — a 20-byte address + a `<2^64` nonce
   always RLP-encodes. Severity **LOW**, `affectsExp005Create = FALSE`.
5. **A live contradiction in the input audit was resolved in EVMLean's favor by reading source.**
   One candidate (`div-begin-failure-LA-rlp`) claimed EVMLean *also* wipes to `∅`; that is FALSE in
   this checkout (the patch replaced the old `accounts := ∅` with `accounts := exec.accounts`). The
   `div-lambda-error-empty-wipe` stood-up finding is the correct one. Do not regress this patch.
6. **Caveat (a) — YP-proxy circularity — CLOSED.** The world-revert-vs-wipe adjudication and the
   `F`/`σ'`/`g'`/`z` semantics are now backed by `Paper.tex` **directly**, not proxied through a
   Lean annotation. See §4a for the exact direct-vs-proxied split.
7. **Caveat (b) — `L_A`/RLP derivation-failure reachability — VERDICT: VACUOUS (dead).** The
   address-derivation-failure arm is structurally unreachable on both engines; a totality lemma
   (`Rlp.encode` of `(20B addr, ≤8B nonce)` ≠ `none`) discharges it once. See §4b.
8. **Caveat (c) — patched-arm `gasRemaining := 0` vs YP `L(gas)` — RESOLVED, not a faithfulness
   bug.** The patched begin-failure arm consumes the forwarded 63/64 (`gasRemaining := 0`), which is
   a *defensible interpreter choice* on a dead arm, and is internally consistent. But it is
   **asymmetric** with the `createArm` soft-fails (which refund `allButOneSixtyFourth`). Because the
   arm is dead, the asymmetry is unobservable. See §4c — flagged as a spec-authoring guardrail.
9. **CreateSpec must carry a "sufficient fuel" hypothesis** (the standard `NeverOutOfFuel` /
   fuel-monotonicity lemma family from exp003/exp004). Under it, `Lambda`/`Λ` never returns
   `OutOfFuel`, the `∅` catch-all is provably dead, and the cross-engine wipe cannot be exercised.
10. **CreateSpec must restrict / model two edge preconditions explicitly:** EIP-2681 nonce overflow
    (`nonce = 2^64-1` → push 0, world unchanged, full gas refund — both engines agree) and
    EIP-3860 init-size cap (`initSize > 49152` → hard OOG — both engines agree). Asserting an
    *always-bumped* nonce, or omitting the size cap, would be unprovable. These are spec obligations,
    not model divergences.
11. **The real CREATE risk surface for exp005 lives in the FAILURE arms, not the happy path.** The
    deploy-fail disjuncts of `F` (occupied/EIP-7610, EIP-3541 `0xEF`, EIP-170 size, deposit
    affordability) and the resume-time push-0 re-checks are where a sloppy `CreateSpec` could bind a
    wrong substate/gas channel. All currently agree across engines; the hazard is spec-authoring,
    not reference drift.
12. **No CREATE exists in the IR today** (verified: `IR.lean` `Expr` = imm/tmp/add/lt/sload/gas;
    `Stmt` = assign/sstore/call; `Term` = ret/stop/jump/branch). This audit is genuinely *ahead* of
    the surface — the intended pre-flight position.

---

## 3. Ranked standing-divergence table

Exactly one candidate stood up as a real model-level divergence. It is ranked #1; everything else is
in §5 (refuted/encoding-only).

| # | Divergence | Stands? | Faithful side | Severity | YP citation | Reachable? | affectsExp005Create |
|---|---|---|---|---|---|---|---|
| 1 | `div-lambda-error-empty-wipe` — EVMYulLean `accountMap := ∅` on `Λ = .error` catch-all (`Semantics.lean:286` CREATE / `:344` CREATE2). EVMLean has **no** counterpart. | **YES** | **EVMLean** | **LOW** | §7 [YP-direct]: `σ' ≡ σ` on `F ∨ σ**=∅` (revert to pre-creation caller world). The only `∅` in §7 targets the **new** account `a` on the success-DEAD path (EIP-161), never the caller world. The `∅` in the OOG prose is the *child evaluated state* `σ**` used as a failure **sentinel**, never an assignment to the world `σ`. EVMYulLean conflates "child σ** = ∅" with "set world to ∅" — a category error. | **No** (gas-bounded well-formed tx). Fires ONLY via `OutOfFuel` (fuel = 0 at `Lambda:597` entry, or `Ξ` re-throwing `OutOfFuel` at `:660`). Fuel is a meta-interpreter counter outside EVM state, supplied unbounded in real runs. The `L_A=none → StackUnderflow` route into it is **DEAD** (RLP of a 20B addr + `<2^64` nonce never returns `none`). | **FALSE** |

**Why #1 is `affectsExp005Create = FALSE`** (the load-bearing conclusion):

- (a) `CreateSpec` is proved against **patched EVMLean**, which has *no* wipe arm at all — EVMLean
  conformance never reaches the divergent code.
- (b) Even cross-engine, the arm is gated behind `OutOfFuel`, which a conformance obligation
  discharges via the standard `NeverOutOfFuel` / fuel-monotonicity lemma family already used in
  exp003/exp004. `CreateSpec` carries a "sufficient fuel" hypothesis, under which `Λ` never returns
  `OutOfFuel` and the catch-all is provably dead.
- So a well-formed `CreateSpec` witness cannot exercise the wipe, and it cannot threaten soundness.

**Recommendation (hygiene, NOT a soundness blocker):** in EVMYulLean, replace `accountMap := ∅` with
`evmState` (plain revert-to-caller), or propagate `OutOfFuel` as a top-level `.error` rather than
swallowing it into a state value. As written it is "encoding-adjacent": a real divergence in the
arm's *body*, but vacuous on the well-formed-tx surface exp005 cares about. EVMLean already does the
right thing — do not let the patch regress.

---

## 4. The three open caveats, each resolved

### 4a. Caveat (a): YP-proxy circularity — DIRECT vs PROXIED

**Question:** in the prior audit, several CREATE claims were justified by a Lean inline annotation
that *paraphrased* the YP. Which are now backed by `Paper.tex` directly, and which remain proxied?

**Now backed by `Paper.tex` DIRECTLY [YP-direct]:**

- The failure-state world contract: `σ' ≡ σ` on every failure (any `F` disjunct OR `σ**=∅`). Full
  revert of `σ`, never a per-account `∅` of the caller. **This is the citation that adjudicates the
  #1 divergence** — and it is read from the verbatim `\begin{cases}` block, not an annotation.
- The gas regimes: `F ⇒ g' = 0`; `¬F ⇒ g' = g** − c` with `c ≡ G_codedeposit·‖o‖`. The EIP-150
  all-but-1/64 (`L`) is applied **upstream** at the caller layer, NOT inside §7's `g'`. So "`g' =
  L(μ_g)`" is the *wrong* characterization of §7's output — important for caveat (c).
- The `z`/push determinant: `z = 0 ⇔ (F ∨ σ**=∅)`, push `a` iff `z=1` else push `0`.
- `ADDR`/`L_A` totality: the YP admits **no** address-derivation failure arm. `ADDR =
  B_{96..255}(KEC(L_A(…)))` is a total deterministic function. **This adjudicates caveat (b)** — and
  it is read directly.
- The `DEAD(σ**,a) ⇒ σ'[a]=∅` EIP-161 success-prune arm, and the `F` disjuncts encoding EIP-170
  (24576), EIP-3541 (`0xef`), and the orthogonality of the EIP-3860 (49152) cap (charged upstream,
  NOT in `F`).

**Still proxied (read from Lean source / model annotation, not the YP):**

- The exact *body* of EVMYulLean's `Lambda` `where`-clause (`:597`, `:603`, `:610`, `:659-691`,
  `:693-700`) — these are EVMYulLean's transcription of §7, read from its source. Faithful as far as
  read, but the §7 equations they implement are the YP-direct ones above.
- EVMLean's internal `checkpoint.substate = substateWithNew` warming trace (`Create.lean:41/88/129`)
  — read from EVMLean source; the *target* (`A' = A*` on `F`) is YP-direct.
- The OutOfFuel mechanics — these are a pure interpreter artifact with **no YP counterpart** (the YP
  has no fuel notion), so there is nothing to proxy; they are model-internal by construction.

**Verdict on (a):** the circularity is **broken** for every claim that adjudicates a divergence or a
caveat. The remaining proxied items are model-internal traces whose YP *target* is independently
cited direct. No adjudication in this report rests solely on a Lean annotation's paraphrase of the YP.

### 4b. Caveat (b): `L_A` / RLP address-derivation-failure reachability — VERDICT: VACUOUS (dead)

**Question:** is the address-derivation-failure arm (`beginCreate:36` `| .error .StackUnderflow` on
EVMLean; `L_A = none → StackUnderflow` lifted via `MonadLift` on EVMYulLean) a *real* reachable
divergence, or vacuous dead code?

**Verdict: VACUOUS / DEAD on both engines.** Reasoning (YP-direct + source):

- For **CREATE** (`ζ = none`): `L_A = RLP(.𝕃 [.𝔹 s, .𝔹 n])`, with `s` = 20-byte sender and `n =
  BE(nonce)` (`≤ 8` bytes, since `nonce < 2^64`). `Rlp.encode` returns `none` **only** when a
  payload reaches `≥ 2^64` bytes (`Rlp.lean:117,142` / `Wheels.lean` `R_b`/`R_l`). A 2-element list
  of a 20-byte string and a `≤8`-byte string is `~30` bytes `≪ 56 ≪ 2^64`, so encode always takes
  the `some` branch. The `none` guard is never selected.
- For **CREATE2** (`ζ = some`): `L_A = some (BE 255 ++ s ++ ζ ++ KEC i)` — unconditionally `some`,
  derivation cannot fail.
- The outer step is total on both: `(KEC preimage).extract 12 32 |> fromByteArrayBigEndian |>
  Fin.ofNat` (`Create.lean:38-39` ≡ EVMYulLean `Lambda:605-607`) — `Fin.ofNat` reduces mod `2^160`,
  never errors.
- **[YP-direct]:** §7 admits **no** derivation-failure case at all; `ADDR`/`L_A` is total. A model
  with a derivation-failure arm carries it for Lean totality, not YP fidelity.

**Consequence for the #1 divergence:** because this route is dead, EVMYulLean's `∅`-wipe is reachable
**exclusively** via `OutOfFuel`, never via `L_A=none`. That is what caps its severity at LOW.

**Consequence for `CreateSpec`:** the spec can soundly assume `Rlp.encode` succeeds (or discharge it
as a closed totality lemma `RLP(20B, ≤32B-preimage) ≠ none`) and need not thread an
address-derivation-failure case. The arm cannot be exercised by any IR-generated CREATE, which
supplies a concrete caller address and a bounded nonce. **Recommend deleting the dead `.error`/wipe
arms on both engines** (replace with the totality proof) to remove the misleading historical comment
— hygiene, not a blocker.

### 4c. Caveat (c): the patched arm's `gasRemaining := 0` vs YP `L(gas)`

**Question:** the patched EVMLean begin-failure arm sets `gasRemaining := 0` (`Interpreter.lean:75`),
so `resumeAfterCreate` returns `gas - allButOneSixtyFourth(gas) + 0` — i.e. the forwarded 63/64 is
fully consumed. Is that a faithfulness bug against the YP?

**Resolution: NOT a faithfulness bug, but a flagged asymmetry on a dead arm.**

- **[YP-direct]:** §7's `g'` is `0` (on `F`) or `g** − c` (on `¬F`). It is **NOT** `L(μ_g)` — the
  all-but-1/64 is an upstream caller-layer computation, never §7's output. So comparing the patched
  arm to "YP `L(gas)`" is comparing against the wrong quantity: §7 has no opinion about this arm
  because §7 has no address-derivation-failure arm at all (caveat b). The arm is **YP-unconstrained
  dead scaffolding**.
- Given that, `gasRemaining := 0` (consume everything, like an exceptional halt) is a *defensible*
  interpreter choice for an unreachable defensive branch. `resumeAfterCreate` is internally
  consistent with it: the 63/64 retention guard (`if (gas + gasRemaining).toNat <
  allButOneSixtyFourth gas.toNat then throw .OutOfGas`, `Create.lean:170`) is satisfied with
  `gasRemaining = 0` (`gas + 0 ≥ gas - gas/64`), so no spurious fault.
- **The asymmetry to flag:** the `createArm` *soft*-fails (insufficient balance / depth≥1024 /
  size>49152 / nonce-overflow) set `gasRemaining := allButOneSixtyFourth(gas)` and net out to a
  **full** gas refund (`gas - L + L = gas`). The begin-failure patched arm instead burns the 63/64.
  Two soft-failure shapes, two different gas outcomes. Because the begin-failure arm is **dead**
  (caveat b), this asymmetry is unobservable today.

**Consequence for `CreateSpec`:** state the gas channel on the **reachable** arms only —
`createArm` soft-fails (full refund) and the `F`/deploy-fail arms (`g'=0`) and success (`g'=g**−c`,
then the EIP-150 reclaim `gas - L(gas) + g'` at `Create.lean:173`). Do **not** bind the begin-failure
arm's `gasRemaining := 0` as if it were a reachable observable; discharge that arm by the `L_A`
totality lemma instead. **Guardrail:** if a future refactor ever makes the begin-failure arm
reachable (e.g. changing `AccountAddress` away from 20 bytes, or admitting unbounded nonce
preimages), this `gasRemaining := 0` vs the soft-fail `allButOneSixtyFourth` asymmetry would become a
real, observable inconsistency that a `CreateSpec` would have to choose between. It is not on the
exp005 roadmap, but the spec author should leave a `-- dead arm, totality lemma` marker so nobody
silently makes it live.

---

## 5. Refuted / encoding-only appendix

Every other CREATE candidate was refuted as encoding-only (same observable contract, different code
placement) or vacuous (real-but-dead). None affects exp005 CREATE soundness. Each row:
faithful side = **both** unless noted; severity = **vacuous**; `affectsExp005Create = false`.

| Candidate | Why refuted (one line) | Notable correction |
|---|---|---|
| `div-begin-failure-LA-rlp` | **Premise FALSE in this checkout.** Claimed EVMLean *also* wipes `accounts := ∅` on begin-failure. Verified: patched `Interpreter.lean:69-81` uses `accounts := exec.accounts` (world-preserving); the patch comment documents replacing the old `accounts := ∅`. The world-divergence the candidate alleged does not exist on EVMLean's side. | **This is the contradiction (§2.5).** The candidate's misread, if trusted, would have wrongly implicated EVMLean. The stood-up `div-lambda-error-empty-wipe` is the correct adjudication: only EVMYulLean wipes. |
| `div-static-mode` | EVMYulLean *does* enforce CREATE-under-STATIC, in `Z` (`Semantics.lean:473-474`, `W` at `:437-439`), run before `step` at `:502` — not in the dispatch block the source agent read in isolation. EVMLean inlines the same guard via `requireStateMod`. Identical contract: hard `.StaticModeViolation`. | Candidate's YP citation cited §7/`F`; correct authority is `Z`/`W` in §9.4.2. (`F` ≠ `Z`.) Cosmetic line drift: CREATE2 guard is `System.lean:156`, not `:155`. |
| `div-eip3860-hard-vs-soft` | EVMYulLean is NOT soft-only: `Semantics.lean:479-482` in `Z` hard-faults `.OutOfGass` on `initSize > 49152`; `Z` runs before `step`, shadowing the soft conjuncts. EVMLean `System.lean:151/158` hard-throws identically. | Both implement the EIP-3860 hard abort. Dead soft conjuncts exist on both sides; recommend dropping for clarity. |
| `div-own-cost-oog` | Both charge mem-expansion + create own-cost and OOG identically; EVMYulLean factors it into `Z` (`:443-451`), EVMLean inline (`System.lean:152-153,159-160`). [YP-direct]: governed by `Z`'s `μ_g < C` disjunct (§9.4.2+§9.5), before `Λ` gets gas — §7 correctly has no own-cost arm. | Candidate's "not surfaced in EVMYulLean create arms" is factually wrong — it IS surfaced in `Z`. |
| `div-nonce-overflow-gas` | Both: push 0, nonce unchanged, substate unchanged, **full** gas refund (`gas - L + L = gas`). `allButOneSixtyFourth = L` definitionally. EIP-2681 compliant on both. `≥ 2^64-1 ⇔ = 2^64-1` since nonce is `UInt64`. | Candidate's "EVMLean loses the retained 1/64" is arithmetically wrong. Spec obligation: model the overflow exception (don't assert always-bumped). |
| `div-precondition-balance-depth-size` | Soft-fail (balance/depth/size): both push 0, world = original σ (bump discarded), substate unchanged, full gas refund. EVMLean reconstructs pre-bump map via `failed.accounts := accounts`; EVMYulLean leaves `evmState` untouched — extensionally equal. | Spec hygiene: discharge that the computed-but-unused `accountsWithBump` cannot leak onto the failure path (it only reaches the `:102` needsCreate branch). |
| `div-stack-underflow-structural` | [YP-direct] eq.(158): underflow is a §9 opcode-cycle gate, not a §7 arm. Both yield bare exception, no push, no world effect; EVMYulLean's gas-debited local state is discarded on `.error` (error ctor carries no state). | Malformed-bytecode-only path; an IR→CREATE lowering materializes ≥3/4 operands by construction. |
| `div-success-deploy` | Happy path: field-by-field equal AND YP-faithful (nonce+1, balance debit/credit, created-set, deposit `200·‖o‖`, EIP-150 reclaim, push address, substate `A**`). "insert vs replace map" = data-structure equality; "store bytes vs `KEC(o)`" is a **shared** abstraction (both store bytes, expose via on-demand KEC). | This arm gives `CreateSpec` a clean agreed happy-path postcondition. |
| `div-success-dead-eip161` | [YP-direct] eq (115) genuinely has `σ'[a]=∅ if DEAD(σ**,a)`; neither model writes it — but the arm is **logically dead**: the new account is seeded `nonce := …+1` (`:633`/`Create.lean:63`) so `DEAD` (needs nonce=0) is never true. Both models DO run the tx-end EIP-161 sweep (`leanevm Semantics.lean:141-142`) — a different mechanism. | Vacuous (no input distinguishes behaviors). Becomes live only on a pre-Spurious-Dragon ruleset — out of scope. |
| `div-eip170-oversize`, `div-eip3541-0xef`, `div-deposit-oog`, `div-deploytime-occupied`, `div-eip7610-begin-occupied`, `div-initcode-revert`, `div-initcode-exception` | **All share one refuted premise:** the candidate read EVMLean's `checkpoint.substate` as the *cold* pre-CREATE substate. It is NOT. `beginCreate:41` builds `substateWithNew := params.substate.addAccessedAccount newAddress` (= YP `A*`), and `:88` stores it AS `checkpoint.substate`. So every failure arm returns `A*` (warm `a`), matching EVMYulLean's `A' := if F then AStar else AStarStar` (`:688`) and [YP-direct] `A' = A*` on `F`. World/gas/push already agreed; substate now shown equal too. | **The recurring misread.** Guardrail for `CreateSpec`: source `checkpoint.substate` from the warmed `substateWithNew` (as `beginCreate` does), NOT from raw pre-CREATE substate — a naive cold-revert WOULD introduce a genuine `A' ≠ A*` violation. |
| `div-nonf-empty-gas-quirk` | The YP's literal eq-114 `g'=g**−c` with `σ'=σ` on (`σ**=∅ ∧ o≠∅`) is a **known YP equation imprecision**; the YP's own adjacent prose + execution-specs say revert returns leftover gas with no deposit. Both Lean models implement the correct consensus behavior via a **dedicated `.revert` arm** (`Create.lean:132-139` / EVMYulLean `:662-663`) bypassing the `F`/deposit path. | Faithful side = both (vs the *self-contradicted* literal equation). Spec pitfall: keep `.revert` as its own observable arm — folding it into the `F` path would wrongly zero returned gas. |
| `div-address-derivation-nonce` | The `−1` nonce-undo is equivalent on both sides: EVMYulLean passes `σStar` (bumped) into `Lambda`, then `n := nonce − 1 = original` (`:603`); EVMLean bumps in `accountsWithBump` then `creatorNonce := …−1 = original` (`Create.lean:34`). Same preimage ⇒ same address. `contractAddressBytes` ≡ `L_A` character-identical. [YP-direct] `a ≡ ADDR(s, σ[s]_n−1, ζ, i)`. | Spec should state derivation over the observable (original nonce → address); both engines agree. |
| `div-resume-6364-guard` | The `resumeAfterCreate` 63/64 guard (`Create.lean:170` throw `.OutOfGas`) is redundant defensive code on both sides gating a provably-impossible condition (`gasRemaining < −G/64`). [YP-direct] §7 has no 63/64 arm (it's EIP-150, caller layer). Dead branch. | Unreachable under the same `Runs.gasAvailable_le` / monotone-toNat invariant the gas-model track already assumes. Delete during cleanup. |

---

## 6. Coverage + honest limits

**Arms covered (reachable, three-way checked):** opcode-entry static-mode, EIP-3860 size cap,
own-cost/mem-expansion OOG, structural stack underflow, `createArm` soft-fails (nonce-overflow /
balance / depth / size), begin-success → init-code success deploy, EIP-170 oversize, EIP-3541 `0xEF`,
deposit-OOG, deploy-time-occupied, EIP-7610 begin-occupied, init-code revert, init-code exception,
the begin-failure (`L_A`) arm, the `resume` 63/64 guard, the EVMYulLean `∅` catch-all, the non-F
`σ**=∅` gas quirk, and address-derivation (`−1` nonce). That is the full per-arm enumeration in the
attached per-model contracts.

**Honest limits — what was NOT independently reached or fully exercised:**

- **EIP-6780 (SELFDESTRUCT-only-same-tx)** is out of scope here — this audit is CREATE/CREATE2, and
  the interaction of a CREATE'd-then-self-destructed account *within the same tx* (relevant to
  re-creation collisions) was not traced. Flag for the spec author if `CreateSpec` ever composes
  with SELFDESTRUCT.
- **EIP-7610 storage-non-empty widening:** the YP text revision read states the collision predicate
  as code/nonce; EIP-7610 widened it to also storage-non-empty in practice. EVMLean's `beginCreate`
  7610 check (`Create.lean:52-59`) inspects `nonce≠0 ∨ code.size≠0 ∨ storage≠default` — i.e. it DOES
  include storage, going beyond the read YP text. Both engines were reported to include storage, so
  no *between-engine* divergence; but the YP-direct citation for the *storage* disjunct is weaker
  than for code/nonce (it rests on the EIP, not the §7 `F` text as read). Re-confirm against the EIP
  if `CreateSpec` asserts the storage disjunct.
- **Tx-finalization / top-level create-transaction** (as opposed to the CREATE/CREATE2 *opcode*):
  the tx-end EIP-161 dead-account sweep was confirmed present (`leanevm Semantics.lean:141-142`) but
  the full create-*transaction* entry path (intrinsic gas, upstream nonce bump, `o`-as-deployed-tx)
  was not three-way traced. exp005 will lower CREATE *opcodes*, so this is lower priority, but a
  whole-tx CreateSpec would need it.
- **The EVMYulLean `Lambda` `where`-clause** was confirmed present and its key lines read, but not
  every cited line number was re-paginated against the file in this checkout (the file lives in the
  exp004 worktree on a different toolchain and cannot co-import with exp003 — the
  flat/nested-toolchain lock). Cross-engine claims about EVMYulLean rest on a single read, not a
  mechanized check. The EVMLean side (the conformance base) WAS re-verified line-for-line in this
  checkout.
- **No mechanized proof exists.** Every "matches" in this document is a human source read. The point
  of this audit is to de-risk `CreateSpec`, not to substitute for it.

**Brutally honest bottom line:** the single thing that could corrupt a future CREATE proof — an arm
where the conformance-base engine (patched EVMLean) is the *unfaithful* side — is **absent**. The one
real divergence is EVMYulLean's, is dead on well-formed txs, and is on the engine you are NOT proving
against. Proceed to `CreateSpec`, carrying (1) a sufficient-fuel hypothesis, (2) the `L_A` totality
lemma to kill the dead derivation arm, (3) explicit nonce-overflow and init-size-cap preconditions,
and (4) the `checkpoint.substate = A*` (warm) guardrail so the failure arms don't bind a cold
substate. **GO.**
