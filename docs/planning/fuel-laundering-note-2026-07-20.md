# The CREATE fuel-laundering arm: findings and decision note

**Date:** 2026-07-20 (exp004 night-3, track T5 — read-only investigation)
**Scope:** the vendored-EVMYulLean catch-all that refuted `Θ_fuel_mono` (keystone
post-mortem at `NestedEvmYul/ThetaRuns.lean:231-283`). All line numbers verified
against the working tree on `codex/sir-internal-functions`; no code was edited.

---

## 1. The arms, exactly

Both creation opcodes in the nested step dispatcher
(`EVMYulLean/EvmYul/EVM/Semantics.lean`) match the inner `Lambda` result with a
catch-all that converts *any* `Lambda` error into an ordinary result tuple:

* **CREATE** — `Semantics.lean:274-286`:

  ```
  match Λ with
    | .ok (a, cA, σ', g', A', z, o) => (a, {evmState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
    | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)   -- :286
  ```

* **CREATE2** — `Semantics.lean:341-344`: byte-identical catch-all at `:344`.

Downstream of the tuple `(a, evmState', g', z, o)`:

* `x` (`:289-291`): `z = false` forces `x = ⟨0⟩` — the *semantic failed-create
  word* is pushed.
* `newReturnData` (`:292`): `if z then .empty else o` with `o = .empty` →
  `.empty` either way.
* The `OutOfGass` guard (`:293-294`) tests
  `(evmState.gasAvailable + g').toNat < L (evmState.gasAvailable.toNat)` with
  `g' = 0`; since `L n = n - n/64` (`EvmYul/Semantics.lean:135`) we have
  `L n ≤ n`, so the guard never fires on this path.
* Gas update (`:295-301`): `gasAvailable := gd - L gd + g'` with `g' = 0` — the
  parent **permanently forfeits `L(gasAvailable)`**, the entire all-but-1/64
  forwarded to the child, even though no child gas was actually consumed
  semantically.

### 1a. The `accountMap := ∅` DOES reach the successor state (state corruption)

The successor state is rebuilt at `:295-301` as `{ evmState' with activeWords := …,
returnData := …, gasAvailable := … }` — a record-update **on the tuple's
`evmState'` slot**, overwriting only those three fields. On the catch-all path
`evmState' = {evmState with accountMap := ∅}`, so the returned `.ok` state
(`:302`, `evmState'.replaceStackAndIncrPC (stack.push x)`) carries
**`accountMap = ∅`**: the parent continues executing against an empty world.
(Contrast the two non-`Λ` failure branches at `:253` and `:288`, which put the
*unmodified* `evmState` in that slot and are therefore benign; and contrast `Θ`
itself, which has an `if σ'' == ∅ then σ` sentinel-guard at `:813` — no such
guard exists in the step arm.)

**Verdict on this sub-question: the arm is not merely unfaithful, it is also
state-corrupting on the absorbed path.** Every subsequent SLOAD/BALANCE/CALL in
the parent frame reads a wiped world, and the wipe propagates up through
`X`/`Ξ`'s success packaging (`:559-563` returns `evmState'.accountMap`).
The only mitigating fact: the path also burned `L(gas)`, so the parent has at
most 1/64 of its gas left to do damage with.

## 2. What can actually reach the catch-all

`Lambda` (`Semantics.lean:566-700`) already separates interpreter fuel from
child gas. Its **complete** list of `.error` exits:

1. **`:597`** — `| 0 => .error .OutOfFuel` (fuel bottomed out at `Lambda`'s own
   entry).
2. **`:658-661`** — inner `Ξ` result: `if e == .OutOfFuel then throw .OutOfFuel`
   rethrows fuel exhaustion; **every other `Ξ` error** (`.OutOfGass`, stack
   errors, invalid ops, …) is packaged at `:661` as
   `.ok (a, createdAccounts, σ, ⟨0⟩, AStar, false, .empty)` — a **`z = false`
   ordinary failed create**, which is the correct YP behavior.
3. **`:604`** — `let lₐ ← L_A s n ζ i`, an `Option` lift through the local
   `MonadLift Option (Except …)` instance at `:136-137` (defaulting to
   `.StackUnderflow`). **Dead on reachable inputs**: for `ζ = none` (CREATE),
   `L_A` is `RLP (.𝕃 [.𝔹 s, .𝔹 n])` (`:699`) over a 20-byte address and a
   ≤33-byte nonce big-endian; `RLP` (`EvmYul/Wheels.lean:299-335`) returns
   `none` only when a payload size reaches `2^64`. For `ζ = some` (CREATE2),
   `L_A` is directly `.some` (`:700`). So this exit is mathematically
   unreachable (though not *proved* unreachable anywhere in-tree).

Nothing else in `Lambda` can error: the `Ξ` success/revert arms build `.ok`
tuples (`:662-691`).

**Confirmed conclusion (the seeded question, sharpened):** a child's genuine
GAS exhaustion arrives as `Ξ = .error .OutOfGass` and is *already* packaged by
`Lambda` as a `z = false` failed create — it never reaches the step arm as an
error. The catch-all's live input is therefore **exclusively interpreter-FUEL
exhaustion** (plus a provably-dead RLP branch). The arm is not modeling the
legitimate failed-create outcome — `Lambda:661` already does that, correctly.
It is laundering the model-internal totality device (fuel) into a semantic
result (a failed create with a wiped world and forfeited gas).

## 3. Does real EVM justify it? No — the two readings separated

* **(a) Child gas exhaustion = legitimate soft-fail.** Real EVM: an
  out-of-gas init-code run consumes the forwarded gas and the CREATE pushes 0.
  This is handled **upstream** by `Lambda`'s `z = false` packaging (`:661`,
  with `g' = ⟨0⟩` — forwarded gas consumed — and the parent-visible `σ`
  restored). The catch-all is not needed for this and never sees it.
* **(b) Interpreter fuel exhaustion = "the model gave up".** This has no
  YP counterpart and must propagate as an error. Everywhere else in the tower
  it does: `call` errors at `:150-151` and the four CALL-family arms forward
  them through do-binds (e.g. `:371-373`); `X` propagates `step`/`Z` errors
  (`:502-506`); `Ξ` propagates `X` (`:559`); `Lambda` rethrows (`:660`); `Θ`
  rethrows (`:804-806`, fuel-0 at `:745`).

**The CREATE/CREATE2 arms at `:286`/`:344` are the only place in the entire
nested tower where `.OutOfFuel` is converted into a non-error result.** This is
exactly the exclusion list of `step_fuel_irrelevant`
(`NestedEvmYul/XLoop.lean:129-153`: ~130 arms fuel-irrelevant by `rfl`, six
excluded — four CALL arms honestly recursive, two CREATE arms absorbing), and
exactly the failure point named by the keystone post-mortem
(`ThetaRuns.lean:243-261`): at fuel `n+1` with `Lambda n` out of fuel, `step`
returns a non-`OutOfFuel` result satisfying `Θ_fuel_mono`'s premise, while a
larger fuel completes the create with a different result — the statement, not
the proof, is false.

## 4. The faithful fix (shape only — NOT implemented)

Replace, in both arms, the catch-all with explicit propagation mirroring the
CALL family's do-bind discipline:

```
| .error e => .error e     -- was: | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
```

(mechanically: lift the `match Λ` out of the pure tuple-binding into the
surrounding `do`, or make the tuple-binding an `Except`-valued `←` bind).
This simultaneously fixes the laundering *and* the `accountMap := ∅`
corruption, since the corrupted tuple is deleted.

### Blast radius on committed exp004 proofs (all verified against current arms)

| Artifact | Current dependence on the catch-all | Effect of the fix |
| --- | --- | --- |
| `create_result_gas_le` (`NeverOutOfFuel.lean:2796`) | Has an explicit "`Lambda` not `.ok`: `g' = ⟨0⟩`" branch discharging `0 ≤ L gd` | Branch becomes `.error` propagation, killed by `hstep = .ok` noConfusion — **simpler** |
| `create_spec` (`LambdaTriple.lean:299`, error branch at `:355-360`) | Λ-errored branch discharged via `z = false → x = ⟨0⟩` against `hx` | Same: branch becomes contradiction with `.ok` — **simpler** |
| `lambda_of_xi` (`LambdaTriple.lean:175`) | Inverts `Lambda` itself, not the step arm | **Untouched** |
| `noOOF_step_create`/`noOOF_step_create2` (`NeverOutOfFuel.lean:2216-2231`) | **Unconditional precisely because of the swallow** (commentary at `:2158-2160`) | Become conditional on a `Lambda ≠ OutOfFuel` hypothesis, mirroring `noOOF_step_call*` (`:2186+`); the fuelBound-envelope machinery (`Lambda_outOfFuel_of` at `:1889`) already supplies it — **moderate rework, same architecture** |
| `Θ_never_outOfFuel` (`NeverOutOfFuel.lean:4665`) / `gas_mono` (`:4071`) | CREATE cases route through the above | Follow the `noOOF_step_create*` rework; `gas_mono`'s CREATE case keeps its `hΛ` bound (the `.error` branch drops out) — **contained** |
| `step_fuel_irrelevant` (`XLoop.lean:144`) | CREATE excluded | CREATE stays excluded (still recursive), but now *honestly* so, like CALL |
| **`Θ_fuel_mono` (deleted keystone)** | **REFUTED by the arm** (`ThetaRuns.lean:253-261`) | **No longer refuted — becomes provable-as-stated** |

### Would fuel-mono / unconditional adequacy actually come back?

In principle, yes: with the fix, every `step` arm either ignores fuel or
propagates `OutOfFuel`, which is precisely the induction invariant
`res_mono` needed. But the B3 pricing stands — a ~1500-line 6-layer mutual
induction mirroring `gas_mono` (`NeverOutOfFuel.lean:4071-…`), per the
post-mortem. With `Θ_fuel_mono` proved, `runΘ_complete'`'s `k ≤ seedFuel w`
side condition becomes removable (any single sufficient fuel point would
propagate to all larger fuels), restoring single-fuel-point introduction and
an unconditional `of_runTheta`. So: the fix converts the cofinal `ΘRuns`
encoding from "the only correct one of the two" (`ThetaRuns.lean:276-279`)
back to "the cheap one of two correct ones". The cofinal surface likely
remains the right *default* either way; the fix buys the *option*, not the
obligation, of the expensive keystone.

## 5. Flat comparison: the leak is structurally impossible there

Flat (`EVM/Evm/Semantics/Interpreter.lean:36-64`, `drive`) has **one shared
fuel on one trampoline**: a CREATE descent (`:60-64`) pushes the suspended
parent (`.create pending`) and continues into `beginCreate params`
(`Evm/Semantics/Create.lean:64`, total — its former dead `.error` guard was
removed) **with the same fuel counter**. There is no inner interpreter whose
`OutOfFuel` could be inspected — the only `OutOfFuel` producer is `drive`'s
own fuel-0 arm (`:39`), and it is returned, never matched on. No absorption
arm exists anywhere on the CREATE path (`stepFrame`'s CREATE arms build
`.needsCreate`, `System.lean:616/:627`-adjacent machinery; child failure
returns as a `FrameResult` through `Pending.resume`, `Interpreter.lean:13-16`).

Consequences, all proved unconditionally in flat:

* **`drive_fuel_succ`** — `EVM/BytecodeLayer/Semantics/Interpreter/Drive.lean:142-180`
  (flat proofs live under `BytecodeLayer/`, definitions under `Evm/`): one-step fuel
  monotonicity; its proof is an exhaustive case sweep in which *every* branch
  is either a same-fuel-drop recursion or the lone terminal `.ok` — the
  constructive demonstration that no absorption arm exists.
* **`drive_fuel_mono`** — `Drive.lean:185`: full fuel monotonicity (flat's
  `Θ_fuel_mono` analog, ~10 lines instead of ~1500).
* **`drive_not_outOfFuel_mono`** — `Drive.lean:197`: the OutOfFuel-preservation
  corollary (this is the lemma the track charter called "`drive_error_oof`";
  that name does not exist — `drive_not_outOfFuel_mono` is the real one).
* **`messageCall_never_outOfFuel`** — `Interpreter/NeverOutOfFuel.lean:144`
  (unconditional), via `messageCall_never_outOfFuel_of_gasFundsDescent`
  (`Interpreter/Measure.lean:237`) and the discharged `gasFundsDescent`
  (`NeverOutOfFuel.lean:137`).

So yes — flat genuinely avoids the leak **by construction**, not by a more
careful arm: fuel-vs-gas conflation requires an inner-interpreter result to
launder, and flat has no inner interpreter.

## 6. Upstream status (checked 2026-07-20)

Vendored tree is NethermindEth/EVMYulLean @ `066dc8b` (squashed subtree; pin
comment at `experiments/004_nested_evmyul/lakefile.lean:5`). Upstream default
branch `main`, HEAD `047f6307` (2025-09-23 — dormant ~10 months): the
catch-alls are **still present, byte-identical, at the same lines** (`:286`
and `:344` of upstream `EvmYul/EVM/Semantics.lean`). The only drift in the
file is a cosmetic type-index refactor (`Operation .EVM` vs `Operation`).
No upstream fix exists; an upstream report would be novel. Note the bug is
live upstream in *three* respects: fuel laundering, gas forfeiture
(`g' = 0` instead of refund), and the `accountMap := ∅` wipe reaching the
successor state.

## 7. Decision menu (trade-offs only — no recommendation-as-decision)

**(a) Status quo.** Keep the vendored tree untouched; the offset-cofinal
`ΘRuns` encoding stays the permanent adequacy surface, `k ≤ seedFuel w` stays
load-bearing, and this note plus the ThetaRuns post-mortem document the
residue. *For:* zero cost, never-edit-vendored rule intact, the cofinal
encoding is already proven correct and sufficient for everything exp004
currently claims; the absorbed path is *believed* unreachable under the
`fuelBound` seeding used by all headline theorems (the product seed is sized
so inner `Lambda` descents never bottom out). **Precision caveat (gate
review):** that unreachability is design intent, NOT a proved invariant —
`Θ_never_outOfFuel`'s CREATE cases are discharged by the unconditional
swallow lemmas themselves (`noOOF_step_create*`, used at
`NeverOutOfFuel.lean:4570-4571`), so the theorem holds *even if* the arm
fires inside a seeded run; no in-tree theorem rules that out. *Against:* the
model, taken as a definition, remains unfaithful off-envelope (wrong result
AND wiped world at insufficient fuel) — and per the caveat above, on-envelope
avoidance of the arm is itself unproven; and `Θ_fuel_mono` remains
unprovable — permanently forfeiting single-fuel introduction.

**(b) Minimal vendored patch** (two-line `| .error e => .error e`, both arms).
**Requires Eduardo's explicit authorization to break the never-edit-vendored
rule.** *For:* fixes laundering + gas forfeiture + state wipe at the root;
turns `Θ_fuel_mono` provable-in-principle; simplifies `create_result_gas_le` /
`create_spec` error branches; honest CALL/CREATE symmetry. *Against:* diverges
the vendored subtree (future upstream syncs conflict); triggers a moderate
rework of `noOOF_step_create*` and their consumers (§4 table); the big prize
still costs the ~1500-line mutual induction to actually collect; none of the
currently-committed headline theorems *need* the fix.

> **EXECUTED 2026-07-20 (option (b), under Eduardo's explicit authorization).**
> Both arms patched exactly as described: the pure tuple let-binding became an
> `Except`-valued `←` bind (three `.ok`-wrapped pure branches +
> `| .error e => .error e`), CREATE and CREATE2 byte-identical; no other
> vendored edits. Ripple repair landed in the same change, per the §4 table:
> `noOOF_step_create`/`create2` restated conditionally (pinned `Lambda`
> hypothesis at forwarded gas `L (gas − cost)`, child depth `Iₑ+1`, gated on
> the arm's `depth < 1024` guard), `Lambda_outOfFuel_of` sharpened to the
> concrete `exEnv` depth, `never_oof`'s CREATE cases discharged by the
> CALL-style descent (`fuelBound_succ` peel; `fuelHops = 8` covers the 4-hop
> create chain with slack — `fuelBound`/`fuelHops` themselves untouched),
> `create*_result_gas_le`/`_lt`, `step_ee`, and `create_spec` split spines
> reshaped for the new bind, and the absorption prose across
> NeverOutOfFuel/ThetaRuns/MessageBridge/XiTriple/ObservableTriple/Behaves/
> XLoop rewritten honestly (keystone: refuted → open-but-unproven; the
> MessageBridge caveat (A) survives in weakened form via `Lambda`'s own
> non-`OutOfFuel`-error absorption). Full exp004 `lake build` green, zero
> sorries. Commit: `0fda49f3` on branch `codex/sir-internal-functions`
> (reviewed, gated, and committed 2026-07-20; axiom-check on all repaired
> theorems: [propext, Classical.choice, Quot.sound] only).

**(c) Upstream issue/PR to NethermindEth/EVMYulLean.** *For:* the bug is real
upstream (semantic corruption on the absorbed path, not just a proof
inconvenience); a merged fix lets exp004 re-vendor cleanly, combining (b)'s
benefits without a local fork. *Against:* upstream is dormant (last commit
2025-09-23), so latency is unbounded; and an accepted fix still leaves the
local pin at `066dc8b` until a deliberate re-vendor (its own churn). Composable
with (a): report upstream now, stay on status quo until/unless it lands.

> **EXECUTED 2026-07-20, continuation (the prize + the draft).** The
> fuel-monotonicity keystone the fix was priced against is now PROVED:
> `FuelMono.Θ_fuel_mono_ok` / `Θ_fuel_mono_error` (new file
> `NestedEvmYul/FuelMono.lean`, ~740 lines), a six-layer
> (`step`-arms/`call`/`Θ`/`Ξ`/`Lambda`/`X`) strong induction on fuel with the
> semantic premise (result ≠ `.error .OutOfFuel`), NOT the `fuelBound`
> envelope — so it does not collapse into `never_oof`. The §4.3 stretch also
> landed: `ΘRuns.of_runTheta` is now UNCONDITIONAL (a two-line instantiation
> of the keystone) and `runΘ_complete'` dropped its numeric offset bound
> (only the `w.e ≤ 1024` depth cap remains, needed by seeded never-OOF).
> Post-mortem prose across ThetaRuns/XiTriple/Behaves/MessageBridge/
> ObservableTriple/CreateDemo rewritten from "open-but-unproven" to proved.
> Commit `0db198de` (+885/−153); full build green; vendored diff EMPTY (the
> two T1 arms remain the only vendored change); zero sorries; both keystones
> at [propext, Classical.choice, Quot.sound]. Implementation by codex
> (gpt-5.6-sol) via Smithers run `run-1784576427998`; reviewed and gated by
> Fable.
>
> **(c) draft produced (NOT sent — pending Eduardo):** proposed upstream
> report text for NethermindEth/EVMYulLean:
>
> > In `EvmYul/EVM/Semantics.lean`, the step-layer CREATE and CREATE2
> > branches match the inner `Lambda` result and currently use the catch-all
> > `| _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)` at
> > upstream lines 286 and 344. This absorbs `Lambda` errors — including
> > `.OutOfFuel` under recursion-fuel starvation — into an ordinary
> > failed-create tuple. The supposedly unreachable placeholder can therefore
> > become reachable when interpreter fuel is insufficient: execution
> > continues successfully, forwarded gas is forfeited through `g' = 0`, and
> > the successor state is derived from an `evmState'` whose `accountMap` is
> > empty, corrupting semantics on that path. The fix is to make the tuple
> > computation `Except`-valued and replace both catch-alls with
> > `| .error e => .error e`, wrapping the successful and ordinary-failure
> > tuples in `.ok`; this mirrors the existing `Lambda` and `Θ` discipline of
> > propagating `.OutOfFuel` rather than converting it into a semantic soft
> > failure. We applied and verified this minimal change in vendored commit
> > `0fda49f3`.
>
> Draft caveats: upstream coordinates verified against NethermindEth main at
> `047f6307` (2026-07-20); vendored pin remains `066dc8b`, lines may drift.
> Decision state: (b) executed (T1 `0fda49f3` + T2 `0db198de`); (c) drafted,
> send/hold is Eduardo's call; (a)/(d) moot.

---

*Verification method: direct read of the vendored `Semantics.lean` mutual
block (`step`/`X`/`Ξ`/`Lambda`/`Θ` at `:221`/`:494`/`:529`/`:566`/`:721`),
`RLP` in `Wheels.lean`, the exp004 proof files (`XLoop.lean`,
`ThetaRuns.lean`, `NeverOutOfFuel.lean`, `LambdaTriple.lean`), flat's
`Interpreter.lean`/`Drive.lean`/`Measure.lean`/`NeverOutOfFuel.lean`, and a
fetch of upstream `main`. Zero edits to any `.lean` file.*
