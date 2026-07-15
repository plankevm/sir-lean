# exp005 (Track C, IR→EVM): "oracle" vs "observable" — comparison & recommendation

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

**For:** Eduardo (merge / keep-both / converge decision).
**Date:** 2026-06-25. **Method:** specs-first (datatypes, oracle/event structures, headline
theorem *statements* + hypotheses + axiom-cleanliness). Proof bodies were not reviewed.

**Topology first (the load-bearing fact).** The two directions live on **different branches**,
not side-by-side in one tree:

- **Direction A (oracle)** is on `main`. The oracle work is a single commit, `6f283ac`
  "exp005: gas + ext-call oracles — IR now gas-agnostic AND call-agnostic", on top of the
  merge-base `5ee984d`. Files: `LirLean/Gas.lean`, `LirLean/Call.lean`, plus oracle hooks in
  `SmallStep.lean`/`Match.lean`.
- **Direction B (V2)** is on `exp005-ir` (worktree `…-wt/ir-lowering`). 10 commits past the same
  merge-base, all under a fresh `LirLean/` subdir. **`Gas.lean` and `Call.lean` do not exist on
  this branch** — B never saw the oracle. B also carries a genuinely new exp003 lemma file,
  `BytecodeLayer/Hoare/GasMonotone.lean`, which is **absent from `main`**.

So this is not "A's files vs B's `` in one tree." It is two divergent branches that share only
the pre-oracle base (`IR.lean`, `Decode.lean`, `Layout.lean`, `Lowering.lean`, the v1 gas-aware
`SmallStep.lean`/`Match.lean`/`WorkedCall.lean`). Each branch kept that v1 base green and built its
own line on top.

---

## 1. Design philosophy

| | **A — oracle** (`main`) | **B — V2 / observable** (`exp005-ir`) |
|---|---|---|
| Gas | A *modeled cost*, abstracted behind `GasOracle`. IR threads a real `UInt64` gas counter (`IRState.gas`); each construct charges `oracle.{verylow,base,…}`. `evmOracle` instantiates the schedule defeq to EVM constants. | **Not modeled at all.** No counter, no charge, no `matCost`. Gas is an **observed value** the run supplies. |
| Gas introspection (`Expr.gas`) | Reads the live counter: `evalExpr … .gas := ofUInt64 st.gas`. | Reads the next **`gasRead` event** off a trace: `evalExpr st obs .gas := obs`. The only law on those values is **monotone non-increasing** (`Trace.gasMonotone`). |
| External calls | An *oracle effect*, `CallOracle` (post-storage / restored-gas / success-word), threaded by `IRState.applyCall`; `evmCallOracle` defines each field as a projection of exp003's `resumeAfterCall`. | An **event** (CompCert-style): `CallEvent` consumed from the transcript; the IR asserts *nothing* about `world'/success/returndata`. (Not yet built — `Event` currently has only `gasRead`; `call` is the next migration step.) |
| Core state | `IRState { locals, storage : Word→Word, gas : UInt64, callResult : Option Word }` (`SmallStep.lean:77`). | `IRState { locals, world : World }`, `World := Word→Word` (`Machine.lean:41,45`). No gas, no pc, no call-result slot. |
| Semantics | Small-step, gas-aware (`IRConf.running L pc st`), to line up one IR step ↔ one `Runs` segment. | **Big-step**, gas-free CFG driver `RunFrom`/`IRRun` threading a `Trace` (`Machine.lean:180,223`). |
| Boundary | `Match` structure, 6 clauses incl. `M1 pc_eq` and `M4 gas_eq` (`Match.lean:124`). | `Observable { worldDelta, result }` (`Machine.lean:162`). `M1`/`M4`/`M5` demoted to *internal* to the `Runs` witness; only `M3` (→`World`) and the halt result are IR-facing. |
| Prior art cited | vyper-hol (call as black box returning `CallResult`). | CompCert (calls as trace events), Verity (lower to structured target with no pc/gas), Dafny-EVM (gas separate from functional). |

One-line gist: **A says "gas/calls are real, but parameterized; pin them to EVM by `rfl`."
B says "gas/calls are not the IR's business; they are values the bytecode hands in, and the only
theorem is about observables (storage + halt)."**

---

## 2. Headline results

### A — oracle (`main`)

Three reflexivity theorems + a concrete worked-program discharge. All in `Match.lean`/`WorkedCall.lean`.

- **`gas_reflects_lowered`** (`Match.lean:188`). Under `Match`, the word the lowered `GAS` opcode
  pushes `= evalExpr (st.charge (gBase evmOracle)) .gas`. Hypothesis: a `Match prog L pc st fr`.
  Proof is `rw [h.gas_eq]; rfl` — the *whole* payload is M4 (`gas_eq`).
- **`call_reflects_lowered`** (`Match.lean:374`). Given `CallReturns callFr resumeFr`, at
  `evmCallOracle` the three projections coincide with the resumed frame's observables
  (post-storage = `storageAt resumeFr`, restored gas = `gasAvailable`, success word =
  `callSuccessFlag`). Hypothesis: a returning-CALL witness. `rfl`-clean.
- **`applyCall_reflects_lowered`** / **`bindCallResult_reflects_lowered`** (`Match.lean:392,412`) —
  the `applyCall` state lands on `resumeFr`'s storage+gas, the `callResult` slot is pinned to
  `callSuccessFlag`, and binding it to `resultTmp` puts that flag in `locals`.
- **`wc_preserves`** (`WorkedCall.lean:1688`) — the real end-to-end deliverable, **hypothesis-free
  except `50000 ≤ g.toNat`**: `messageCall (wcParams g) = .ok (toCallResult (endFrame (wcRetFrame g) halt))`
  for the worked program `workedCall` (one external CALL). `wc_preserves_twoCall` (`:1711`) is the
  two-call generalization but is a **shape lemma** (takes the two-call `Runs` assembly as hypotheses —
  `workedCall` has only one CALL).

Caveat worth flagging to Eduardo: the design doc §5 (`ir-design.md:343-356`) claims
`call_reflects_lowered` reflects *all three* effects "including the bound success flag," but the
theorem's own docstring (`Match.lean:352-358`) is more honest — the `resultTmp` binding is split into
the separate `applyCall`/`bindCallResult` lemmas, "not part of this reflexivity equation." The doc
slightly over-states; the Lean is correct. Minor.

### B — V2 (`exp005-ir`)

Two headline theorems, both `∃ G₀, ∀ g ≥ G₀, …` shaped, both `#print axioms`-guarded in-file.

- **`lower_preserves_obs`** (`Preserve.lean:586`). `∃ G₀, ∀ g ≥ G₀,
  IRRun protoIR w₀ [gasRead (protoObs g)] (protoObsResult w₀) ∧ LoweredRunHasObs g … `. No pc, no
  gas-equality in the statement; the only gas fact is the envelope `G₀ ≤ g`. The `gasRead` event is
  *realised* by the actual `GAS` opcode value; world agreement + completed-without-revert are the
  observable.
- **`lower_preserves_obs_mono`** (`Mono.lean:578`) — the milestone: same shape, **two** gas reads,
  whose correctness *uses* `Trace.gasMonotone`. The monotonicity is **discharged from the bytecode
  side** (`gReads_monotone`, exact `subCharges` + `omega`), not assumed. Underpinned by
  `Runs.gasAvailable_le` in the new `BytecodeLayer/Hoare/GasMonotone.lean` (`:271`), a general
  hypothesis-free lemma incl. the across-`.call` net-debit `CallReturns.gas_le`.

**Documented prototype cuts (B is a prototype, not parity):** the internal `Runs` witness is a
**hand-written PUSH1 `protoBytecode`/`guardBytecode`, not `lower prog`** (`Preserve.lean:86`,
`Mono.lean:229`) — wiring real `lower` in is deferred (it's what makes v1 `WorkedCall.lean` ~1700
lines). `returned w` maps to success+empty output (the word isn't observed). The STOP fall-through
arm and `RunFrom` determinism are not instantiated. **Calls-as-events is not built yet** (the §6
step-2 work, blocked on the §7.5 returndata decision).

### Axiom-cleanliness / `sorry`

Both directions are **`sorry`-free, `admit`-free, `native_decide`-free** across all reviewed files
(grep confirms only prose mentions of those words). B has explicit in-file `#print axioms` guards on
both headlines (`Preserve.lean:610`, `Mono.lean:603`); the design notes assert
`⊆ {propext, Classical.choice, Quot.sound}`. A's reflexivity lemmas are `rfl`/`rw`-only (so trivially
in the same set), and `ir-design.md:343` asserts the same for `call_reflects_lowered`. I did not
re-run the checker; the statements and proof shapes are consistent with the claims.

---

## 3. Shared vs divergent

**Shared base** (both branches, pre-oracle, untouched): `LirLean/IR.lean` (the grammar — `Expr`,
`Stmt`, `Term`, `CallSpec`, `Block`, `Program`), `Decode.lean`, `Layout.lean`/`pcOf` offset
arithmetic, `Lowering.lean` (`lower : Program → ByteArray`), and the **v1 gas-aware**
`SmallStep.lean` + `Match.lean` + `WorkedCall.lean`. Both rely on exp003's `Runs`/`messageCall_runs`
boundary API. B's `Machine.lean` re-derives a v2-local `blockAt`, `evalExpr`, `HaltResult` so it
imports only `IR.lean` (deliberately *not* the gas-aware `SmallStep.lean`).

**Divergent:** A adds `Gas.lean` + `Call.lean` + oracle hooks (on `main` only). B adds the entire
`` subdir + `BytecodeLayer/Hoare/GasMonotone.lean` (on `exp005-ir` only). **There is no file
overlap and no co-existence in any single tree today.** The v1 `Match` (with `M1`/`M4`) is the common
ancestor both build *away from* — A re-uses it (oracle hooks make `M4` a defeq-clean equality), B
*demotes* `M1`/`M4`/`M5` to internal witness bookkeeping.

---

## 4. Trade-offs

| Axis | A — oracle | B — V2 |
|---|---|---|
| Extensibility | New gas/call rules = new oracle fields + a defeq `evmOracle`/`evmCallOracle` proof. Couples the IR type to EVM-shaped projections (`CallOracle` mentions `CallResult`/`PendingCall`/`AccountAddress`). | New observed phenomena = a new `Event` constructor + a realisability clause. IR datatypes stay `Word`/`Tmp`-only. CompCert-style, very open. `ir-design-v2.md:289` flags `CallEvent` as a candidate for the shared `EVMSemantics` interface. |
| Proof burden | Reflexivity lemmas are cheap (`rfl`). But the *real* surface is `wc_preserves`, which carries `M1` pc arithmetic, `M4` gas threading, stack discipline — the ~1700-line `WorkedCall`. The generic `lower_preserves` over arbitrary `prog` is **future work** (admitted as such in `ir-design.md:411`). | Headline statement is dramatically lighter (no `M1`/`M4`/`M5`). But the heavy `Runs` witness is still needed *inside* — currently sidestepped with hand-written PUSH1 bytecode, **so the `lower`-decode cost is deferred, not eliminated.** Big-step `RunFrom` is simpler than small-step. |
| Faithfulness to EVM gas | **High and explicit.** IR gas = `gasAvailable` exactly (`M4`); the schedule is the real EVM schedule by `rfl`. You can *prove* per-opcode cost facts. | **Deliberately none.** Gas cost is unmodeled; only "GAS reads are monotone non-increasing" survives. Honest about being honest: a gas-dependent branch is evaluated against the *real observed* gas, so it can't lie — but it can't predict (no loop-termination-by-gas; `Mono.lean` confirms strict-decrease guards are *not* determinable). |
| CALL success flag / result | First-class: `callResult` slot + `bindCallResult`, pinned to `callSuccessFlag` (exp003's `x`). Fully worked through `Match`'s `M5` recompute-on-use discipline. | Carried as the `success` field of a `CallEvent` — **but the call event isn't built yet.** Returndata/revert is an open decision held for you (`ir-design-v2.md:259`, §7.5). |
| Fit with exp003/exp004 equivalence | Oracle projections are tied to exp003's `resumeAfterCall` (one engine). | `CallEvent`/event-trace is explicitly pitched as the shared boundary for *both* flat (exp003) and nested (exp004) — same `messageCall`-induced events (`ir-design-v2.md:289`). Closer to the cross-engine `SharedObservable` line on `main`. |

---

## 5. Recommendation

**Converge on B (the V2 / observable line) as the go-forward IR-preservation statement, and retire A's
oracle layer once B reaches `workedCall` parity — but do not delete A's reflexivity work; fold its
useful pieces in.** Reasoning:

1. **B matches your own stated driver.** `ir-design-v2.md:9` records your 2026-06-23 instruction
   verbatim: the IR should not be gas-aware or call-aware; calls are "whatever the bytecode does, not
   an oracle"; preservation should be observable-level and must not prove pc/gas preservation. A's
   oracle line is the thing that instruction was issued *against*. A was the prior trunk; B is the
   correction.
2. **B's theorem is the better product.** A compiler-correctness guarantee should be "observables
   preserved," not "gas counter equals `gasAvailable`." A's `M4` is exactly the low-level coupling B
   removes, and B keeps the honesty constraint (gas introspection is real, robust over the actual
   observed value; gas-freedom is earned via `Trace.gasMonotone`, which B *discharges* from the
   machine, not assumes).
3. **B is better positioned for cross-engine work** (exp003/exp004), which is the active track on
   `main` (`SharedObservable`). The event/transcript boundary is the natural shared interface.
4. **A's oracle isn't wasted.** The `rfl`-clean `evmCallOracle`/`evmOracle` projections and the
   `callSuccessFlag` plumbing are exactly the "realisability witness" content B will need when it
   builds the `call` event (B's `CallEvent` realised by a `Runs.call` node *is* A's `resumeAfterCall`
   projection, minus the IR-facing oracle type). Port that into B's call-event step rather than
   re-deriving it.

**What only you can decide (B is blocked on these — all in `ir-design-v2.md:259`):**

- §7.5 returndata/revert model — gates the `call`-event step (B's biggest remaining gap; A already
  models the success flag).
- §7.2 simulation direction (forward "IR ⇒ bytecode" vs converse) — B assumes forward.
- §7.1 `World` decoupling depth (EVM-native vs observable record + lens).
- Whether to keep A's oracle on `main` as a *parked alternative* during the transition, or excise it
  now. My lean: keep both branches green; **don't merge A's oracle commit further**, land B's ``
  onto a branch off `main`, and treat "wire real `lower` into B + build the call event (reusing A's
  projections)" as the next milestone. Converging to one (B) is the end state; until B hits
  `workedCall` parity, keep v1 `wc_preserves` as the reference both share.

**Risk to weigh:** B's headlines are still **prototype-grade** — hand-written witness bytecode, no
`lower` wiring, no call event, single concrete program (acyclic, determinism not proved). A's
`wc_preserves` is a *fully hypothesis-free, real-`lower`, with-CALL* deliverable. So today A has the
more complete proof and B has the better design. The recommendation bets that B's lighter statement
makes closing the remaining mechanical gaps cheaper than continuing to carry A's `M1`/`M4` burden
toward a generic `lower_preserves` — but that bet is unproven until B ports `workedCall`.
