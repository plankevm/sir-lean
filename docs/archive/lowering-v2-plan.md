# Lowering v2: gasless IR, reflexive calls, observables export

> **Archived — partially superseded.** v2 was *completed* (see
> [experiment 001 results-v2.md](../../experiments/001_toy_external_call/docs/results-v2.md)).
> Its exported-statement *shape* (∃G₀ gas refinement, observables-only) survives
> verbatim and is still the design reference; its later execution phases are
> replaced by [planning/bytecode-first-plan.md](../planning/bytecode-first-plan.md).
> Read for the statement-shape rationale, not the roadmap.

Plan for the second iteration of the IR → bytecode lowering proof, superseding
the *statement* (not the machinery) of experiment 001. Three changes, in order
of importance:

1. **Reflexive external calls.** Drop the `CallOracle`/`CallOracleSound`
   machinery. The IR's `call` instruction executes arbitrary callee bytecode by
   invoking EVMYulLean's message-call function (`Θ`) directly — the *same*
   function application the lowered `CALL` opcode reaches. The call branch of
   the lowering proof then needs zero knowledge of what `Θ` does: both sides
   contain literally the same term.
2. **Gas leaves the IR semantics and the theorem statement.** The exported IR
   semantics is gas-free; the exported theorem is a refinement quantified as
   "∃ a gas bound G₀ such that for all gas G ≥ G₀ the bytecode run produces the
   IR's observables". Gas-exactness survives only as an internal proof artifact
   (a derived cost function). This makes the statement robust to gas
   optimizations in the lowering.
3. **Observables at the boundary.** The exported statement compares
   `Observables` (halt mode, return data, accounts/storage, logs/substate) —
   no `injectFrame`, no pc/stack/code, no gas, no fuel.

Plus one infrastructure decision: **vendor EVMYulLean's EVM core** into this
repo (we already maintain a fork with semantic-adjacent changes, the lemma
layer only makes sense against a pinned revision, and the Yul side is unused —
we lower directly to bytecode).

## 1. What the related projects actually do (surveyed 2026-06)

| Project | Call modeling at the high level | Gas in the high-level semantics/theorem |
|---|---|---|
| **Verifereum** (EVM semantics itself, HOL4) | Reflexive by construction: `CALL` pushes a new context onto a context stack inside the same `step` loop; result popped and merged (`step_call`/`proceed_call`/`pop_and_incorporate_context` in `spec/vfmExecutionScript.sml`). 63/64 rule explicit (`call_gas`). | Full gas model (it's the bytecode semantics). |
| **vyper-hol** (source semantics over Verifereum) | *Not* reflexive, but delegating: the Vyper-level semantics calls Verifereum's `run_call` on a freshly constructed single-context EVM state and merges the result back (`run_ext_call`, `make_ext_call_state` in `semantics/vyperInterpreterScript.sml`). The state translation at that boundary is exactly where their bridge cheat B5 (`evm_correspondence_to_call_result`) lives. | Source semantics is gas-agnostic; `vyper_call_correct` states `∃ gas_needed. gasLimit ≥ gas_needed ⇒ …`. |
| **Verity** | Calls are **not executed at all** in the source semantics (`evalExpr … (.externalCall …) = none`); call sites compile through "External Call Modules" carrying per-contract *interface assumptions* (documented in `AXIOMS.md`, checkable with `--deny-unchecked-dependencies`). The vendored EVMYulLean is never used to run a callee. | No gas anywhere ("Semantic correctness does not imply gas-safety", `TRUST_ASSUMPTIONS.md`). |

Takeaways:

* Our proposed design is **stronger than both comparators**: vyper-hol pays a
  state-translation cheat at the call boundary because its source state differs
  from the EVM state; our IR state already embeds `EVM.State`, so the `Θ`
  application on the two sides is the *same term on the same state* — the
  boundary that cost vyper-hol a cheat costs us a `rfl`-grade step.
* vyper-hol independently validates the `∃ gas bound` theorem shape.
* Verity is *weaker* on calls than commonly assumed; nothing to import from it
  here except the supported-fragment discipline (§6).

## 2. State design: gas joins the don't-care frame fields

In experiment 001, an IR state is an `EVM.State` whose `pc`, `stack`, and
`executionEnv.code` are don't-care, pinned by `injectFrame`. In v2,
**`gasAvailable` becomes the fourth don't-care field**: the IR semantics never
reads or charges it.

```
injectFrame evm pc stack code gas    -- now also overrides gasAvailable
```

The internal simulation invariant becomes: the bytecode state before
instruction *k* is `injectFrame s_k.evm pc_k [] code (G − cost of the prefix)`,
where the prefix cost is a **derived cost function**, not part of the IR
semantics (§4).

`fuel` stays in `Exec` for now: `Θ` is fuel-bounded, so the IR's call semantics
needs it. It is eliminated from the exported statement the same way gas is
(∃ F₀, ∀ F ≥ F₀ — for fuel this is plain monotonicity: more fuel only turns
`OutOfFuel` into the stable result).

## 3. Reflexive calls: design and proof obligations

### Semantics

The IR `call dst args` action:

1. evaluates operands (no gas accounting anymore — order ceases to matter
   semantically; keep right-to-left only if it simplifies reuse);
2. checks the static-mode condition (`¬perm ∧ value ≠ 0 → StaticModeViolation`)
   — this is gas-free and stays;
3. invokes `Θ` with: forwarded gas **exactly `g`** (+ the 2300 stipend when
   `value ≠ 0`), callee/value from operands, calldata = the in-region read from
   the IR's own memory, depth+1, fuel−2 — i.e. precisely the argument vector
   `EVM.call` builds, minus the `Ccallgas`/counter arithmetic;
4. merges the result exactly as `EVM.call` does: accounts/substate on success,
   rollback on failure, returnData set, out-region written, flag returned.
   (Leftover-gas refund is dropped — it only touches the don't-care counter.)

Implementation tactic: factor `EVM.call`'s body (in our vendored copy) into
`callCore (forwardedGas : UInt256) …` containing everything except the gas
arithmetic, so the IR semantics *calls the same function* the bytecode
semantics calls and the agreement lemma is

```
EVM.call fuel gasCost … s = (refund leftover) ∘ callCore (Ccallgas … s) … s
```

### Proof obligations replacing `CallOracleSound`

* **`EVM.call` frame/gas insensitivity** — `callCore` neither reads nor garbles
  `pc`/`stack`/`code`/`gasAvailable` beyond the documented merges. Previously
  half of the oracle assumption; now a proved lemma (mandatory, one-time).
  Since we vendor, we can also *refactor* `EVM.call` so this is nearly
  definitional.
* **Forwarded-gas agreement under adequacy** — at each call site, the bytecode
  forwards `min(g, ⌊63/64 · remaining⌋)`; the adequacy hypothesis (§4) gives
  `g ≤ ⌊63/64 · remaining⌋`, so both sides forward exactly `g`, hence apply
  `callCore` to identical arguments. After this rewrite the branch closes
  reflexively.

The theorem then has **no semantic assumptions left** — only representability
bounds (`hsize`, and a WF bound on gas operands, §4).

## 4. Gas as refinement: the cost function and the ∃∀ statement

### Why equality-on-gas must go

* The IR's gas schedule in 001 is *defined* as the lowering's cost — circular
  as a specification, and it pins the theorem to one fixed code sequence: any
  optimizing change to `lower` falsifies the statement.
* But gas cannot be simply erased either, because it is **semantically
  observable through calls**: a callee that runs out of gas returns flag 0 and
  the caller proceeds on a different branch of reality. Any sound gas-free
  statement must control the gas the callee receives.

### The resolution

The IR forwards **exactly the gas operand `g`** to the callee. On the bytecode
side, forwarded gas is `min(g, ⌊63/64 · remaining⌋)`, which equals `g` whenever
the caller has enough gas left. So for all sufficiently large initial gas `G`,
the callee receives exactly `g` on both sides and the entire execution is
**constant in `G`**. Exported shape (vyper-hol-validated):

```
theorem lowering_correct (program) (s : Exec) (hwf : WF program) (hsize : …) :
    ∃ G₀ F₀, ∀ G ≥ G₀, ∀ F ≥ F₀,
      observables (EVM.X F vj (inject s.evm 0 [] (lower program) G)) =
      observables (run program s F)        -- gas-free IR run
```

(Statement schematic; `run`'s fuel threading and the error cases to be pinned
in Phase C. For `G < G₀` the bytecode may `OutOfGass` — we promise nothing,
which is exactly the freedom a gas-optimizing compiler needs.)

### The internal cost function (reuse of 001)

`G₀` is witnessed constructively. Experiment 001's gas-exact `run` survives as
the **internal instrumented semantics**: it computes, for a given IR run, the
exact gas the lowered code consumes (memory-expansion costs are computable
from the IR states, which track `activeWords` identically). The internal layer
is:

1. 001-style equality theorem against the instrumented run (already proved;
   call branch redone reflexively per §3);
2. an erasure lemma: instrumented run ↔ gas-free run, given adequacy
   (`G ≥ cost of the run` and `g ≤ ⌊63/64 · (G − spent)⌋` at each call);
3. `G₀ :=` the instrumented run's total cost (plus the per-call slack), which
   satisfies adequacy by construction.

So nothing from 001 is wasted: `wordTouchCost`/`callTouchCost`/`Ccall` lemmas,
`Z_*`, the chunk lemmas — all become the cost-function correctness toolkit,
demoted from the spec to the proof.

### Honest edge cases (record in the spec doc)

* **Huge gas operands.** If `g` exceeds any achievable 63/64 cap (`g` near
  2²⁵⁶), no `G₀` exists. Excluded by a WF condition on programs (gas operands
  bounded — e.g. constants `< 2⁶³`, or whatever Plank's fragment guarantees).
  Fail-closed, Verity-style (§6).
* **No `GAS` opcode in the IR.** A gas-free IR cannot expose the counter; if
  Plank SIR needs `gas()`, that instruction lives outside this fragment until
  a cost-model layer exists.
* **Fuel.** `OutOfFuel` is an artifact exception; monotonicity in `F` gives the
  ∃∀ elimination. Verify (don't assume) that EVMYulLean propagates callee
  `OutOfFuel` as a hard error rather than flag 0 — if flag 0, fuel becomes
  observable like gas and gets the same ∃∀ treatment with a per-call bound.

## 5. Observables and statement hygiene

```
structure Observables where
  result    : HaltMode        -- success / which exception
  output    : ByteArray       -- return data
  accounts  : AccountMap      -- includes all storage
  substate  : Substate        -- logs, selfdestructs, accessed sets, refunds(?)
```

* Decide whether gas-refund counters inside `substate` are observable (they
  feed end-of-transaction gas accounting → probably *excluded*, same rationale
  as gas).
* `injectFrame` remains internal-only. Optionally harden by giving `Exec` a
  state type that genuinely lacks pc/stack/code/gasAvailable, with one
  embedding function into `EVM.State`; the IR semantics then *cannot* read the
  don't-care fields even by accident. Worth doing when the IR is next touched
  wholesale, not as a standalone refactor.
* Final memory is *not* observable at the STOP boundary (nothing reads it);
  locals/memory equality stays in the internal full-state lemma, which is
  strictly stronger and free to keep.

## 6. Later layer: locals map over memory, with a fail-closed WF predicate

Not part of v2's critical path, but the design is now unblocked; recorded here
because it interacts with the WF predicate introduced in §4.

* **Storage is a non-issue for this abstraction.** The locals map is a view of
  *memory* only. Storage lives in `accountMap`, equal on the nose on both
  sides; a reentrant callee clobbers it *identically* on both sides because
  both sides run the same `Θ` (reflexivity again). "A call may modify my
  storage" is a *program-verification* concern for a higher layer (where one
  adds no-reentrancy or interface assumptions), not a lowering concern.
* **Memory: the callee can only write the out-region.** A callee — even a
  reentrant call into the same contract — executes in fresh memory; the only
  caller memory written is `[outOffset, outOffset + outSize)`. The 001-era
  obstruction ("calls may clobber any memory") is precisely "outOffset is
  dynamic", which the compiler controls.
* **WF predicate, Verity-style.** Verity's `BridgedStmt` is an inductive
  whitelist over statements whose witnesses are carried in the artifacts
  themselves (function-table entries are subtypes `{ body // BridgedStmts body }`),
  so unsupported syntax *fails to prove*, never silently mishandles. Ours:
  `WF : Program → Prop` requiring (a) call out-regions statically disjoint
  from the locals region (e.g. constant `outOffset + outSize ≤ localBase`),
  (b) bounded gas operands (§4). Plank's allocator guarantees (a) by
  construction; the predicate makes the guarantee a checkable hypothesis.
* **The abstraction theorem.** Locals-map semantics ≃ memory-backed semantics
  under the coupling invariant `mem[localSlot x] = map x ∧ everything else
  equal`, by induction; the call case is preserved by out-region disjointness.
  Composes with `lowering_correct` to give a memory-layout-free exported
  statement.

## 7. Vendoring EVMYulLean

Decision: vendor the EVM core in-tree; stop tracking it as a fork checkout.

* **What to take:** `EvmYul/` EVM semantics + shared infrastructure (UInt256,
  state types, gas). Prune the Yul interpreter and Yul↔EVM common layer if it
  separates cleanly; if the shared `Operation` type resists separation, vendor
  whole and prune opportunistically.
* **What to keep alive:** the conformance-test harness (ethereum/tests
  GeneralStateTests). The claim "our vendored semantics is the real EVM" rests
  empirically on that suite; vendoring without it would silently convert an
  executable spec into an unvalidated model. Re-run after any local change.
* **Discipline:** record the upstream commit; keep a single `DIVERGENCES.md`
  (already-existing deltas: visibility of `Z`/`H`/`W`, list-based
  `ByteArray.get?`/`extract'`, pure `zeroes`, round-trip lemmas; new in v2:
  the `callCore` factoring of `EVM.call`). Hardfork updates become deliberate
  merges against the pinned ruleset Plank targets — acceptable.
* **Where the lemma layer goes:** in-tree next to the vendored code
  (`EVMLemmas` graduates from experiment-local to a library).

## 8. Phases

| Phase | Deliverable | Notes |
|---|---|---|
| **A. Vendor** | EVMYulLean EVM core in-tree, conformance harness running, `DIVERGENCES.md` | Mechanical; do first so B/C build against a stable target |
| **B. Reflexive calls** | 001's theorem re-proved with `Θ`/`callCore` instead of the oracle; `EVM.call` insensitivity lemma; **zero semantic assumptions** | Keeps gas-exact equality temporarily; redo `X_call`, `callStep_eval`; rest of 001 untouched |
| **C. Gas erasure** | Gas-free `run`; erasure lemma vs instrumented run; cost function + `G₀`; fuel ∃∀; exported ∃∀ observables theorem; `WF` (gas-operand bound) | The new statement Philip reads |
| **D. Statement hygiene** | `Observables`, `Simulates`-style wrapper, optionally frame-free `Exec` | Mostly cosmetic, do alongside C |
| **E. Locals-map layer** | `WF` out-region condition; coupling invariant; abstraction theorem; composed corollary | First genuinely higher-level IR |
| **F. Control flow → SIR** | `JUMP`/`JUMPI` with `D_J`, structured layer per agent-notes §1 | Unchanged from prior planning |

## 9. Open questions (for Philip / team)

1. Confirm the IR's call should forward **exactly `g`** (vs. modeling the
   63/64 min — which would drag the counter back into the IR). Forwarding `g`
   is what makes the gas-free statement possible; the price is the WF bound on
   gas operands and the ∃ G₀ shape.
2. Is the `∃ G₀` shape acceptable to consumers, or do they want a *computable*
   `G₀` exported (we can: the instrumented run computes it — worth exporting as
   a function even if the theorem only asserts existence)?
3. Substate refund counters: observable or not (§5)?
4. Does Plank SIR need `gas()`/`gasleft()`? If yes, plan a cost-model fragment
   early rather than bolting it on.
5. Vendoring sign-off: any reason to keep tracking upstream EVMYulLean (e.g.
   expected hardfork updates relevant to Plank's target ruleset)?
