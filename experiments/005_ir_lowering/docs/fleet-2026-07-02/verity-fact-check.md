All evidence gathered. Here is the report.

---

# Verity Fact-Check Report (exp005 design review — track: Verity comparison)

**Repo inspected:** `/Users/eduardo/workspace/evm-semantics/forks/verity` (read-only)

## 1. What the supplied `hNative` hypothesis actually asserts

The prior audit's citation is accurate. `Compiler/Proofs/EndToEnd.lean:128-147`, private theorem `compile_preserves_native_evmYulLean_of_nativeResultsMatchOn`, takes:

```lean
(hNative :
  nativeResultsMatchOn observableSlots
    (interpretIR irContract tx (FunctionBody.initialIRStateForTx model tx initialWorld))
    (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
      (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
      irContract tx ... observableSlots))
```

`nativeResultsMatchOn` is defined in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean:30898-30911`:

```lean
def nativeResultsMatchOn (observableSlots : List Nat) (ir : IRResult)
    (native : Except NativeLoweringError YulResult) : Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success ∧
      ir.returnValue = yul.returnValue ∧
      (∀ slot, slot ∈ observableSlots →
        ir.finalStorage (IRStorageSlot.ofNat slot) = yul.finalStorage (IRStorageSlot.ofNat slot)) ∧
      ir.events = yul.events
  | .error _ => False
```

So `hNative` asserts the **entire observable native execution result** — success flag, return value, storage on the declared observable slots, and events — matching IR interpretation. It is NOT an external-call correspondence and NOT gas-related. It is the whole Layer-3 (IR ↔ native EVMYulLean dispatcher execution) equivalence, assumed wholesale in the generic theorem.

Two qualifications the audit under-reported:
- The theorem carrying `hNative` is `private` and file-local; the public composition surface is documented at `EndToEnd.lean:24-29`.
- Verity DOES discharge it for one concrete contract: `simpleStorage_endToEnd_native_evmYulLean` (`EndToEnd.lean:41357-41367`) proves `nativeResultsMatchOn` outright for SimpleStorage with no run-match hypothesis — only dispatch-guard preconditions (`hselector`, `hNoWrap`, `hdispatchGuardSafe`). The gap is that this is per-contract, per-selector-case brute force (built from three per-case bridges, `:41337-41353`), not a generic statement-level framework.
- `TRUST_ASSUMPTIONS.md:64` confirms the generic closure gap verbatim: "the per-`BridgedStraightStmt` IR↔native observation-equivalence framework that would land truly unconditional S1–S8 … **has not been built yet** — that work is multi-week and tracked separately."

## 2. Does Verity model gas anywhere?

**Not in the verified semantics.** Three pieces of evidence:
- `TRUST_ASSUMPTIONS.md:61` ends flatly: "**Gas is not modeled.**" and `:65`: "**Implication**: Semantic correctness does not imply gas-safety."
- The IR interpreter (`Compiler/Proofs/IRGeneration/IRInterpreter.lean`) contains **zero** occurrences of "gas" (grep count 0). `IRResult`/`nativeResultsMatchOn` have no gas component.
- There IS a `Compiler/Gas/` directory, but it is an **unverified CLI static-analysis tool** (`Gas/StaticAnalysis.lean`, `Gas/Report.lean` — `lake exe gas-report`), computing loop-bounded upper-bound estimates with fallback constants (`unknownCallCost := 50000`, `unknownForwardedGas := 50000`, `GasConfig` at `StaticAnalysis.lean:8-15`). It never touches the proof stack. Crucially, **gas introspection (the GAS opcode as a program-visible value) is nowhere in their source language or IR** — their contracts cannot observe gas, so the problem exp005 solves does not even arise for them.

## 3. Is Eduardo right? What is the supplied run-match actually about?

**Eduardo is right that it is not about gas — but it is also not specifically about calls.** Both framings of the earlier agents were off:

- There is no log-feeding oracle structure anywhere in current Verity. `hNative` is not "run the bytecode to harvest values and feed them into IR semantics"; it is "assume the two independently-defined executions (IR interpreter vs. EVMYulLean native dispatcher) agree on the whole observable result." Verity's IR semantics is deterministic and closed — it needs no external inputs harvested from a run.
- The likely source of the audit agents' confusion: Verity **historically had** an oracle-routed path — `TRUST_ASSUMPTIONS.md:61`: "The legacy runtime-oracle stack and builtin comparison oracle have been removed as part of the EVMYulLean transition (DoD-5)"; `EndToEnd.lean:41468-41469`: "The historical Verity-backed public oracle-routed EndToEnd wrappers have been removed." So "Verity also used run-provided oracles" is true only of a **removed** legacy architecture, and even then those were builtin-comparison oracles, not gas or call oracles.

**Structural comparison to our StmtTies/TermTies debt:** yes, `hNative` is the same *species* of debt — a cross-layer run-correspondence supplied as a hypothesis rather than constructed — and Verity's own trust doc tracks it as such (honest, explicit, roadmapped), which matches our new policy of tracked debt over buried debt. It is **broader** than our seams, not narrower: it assumes the entire result equivalence, whereas our StmtTies/TermTies at least sit inside a proven simulation spine. Conversely, Verity has something we don't yet: one fully closed concrete instance (SimpleStorage) with the run-match hypothesis genuinely eliminated.

## 4. Verity's external-call surface vs. our V2 seams

Verity's external calls are handled by **exclusion and trust**, not by oracles:

- Language level: raw external calls are banned; every pattern goes through typed **External Call Modules** (`Compiler/ECM.lean`, `docs/EXTERNAL_CALL_MODULES.md`). Each ECM carries `compile : CompilationContext → List YulExpr → Except String (List YulStmt)` and a `proofStatus : proved | assumed | unchecked` — **defaulting to `.assumed`** (`ECM.lean:63`). `TRUST_ASSUMPTIONS.md:68-71`: "**Trust**: Each module's `compile` produces correct Yul." That is a trusted-codegen assumption, not a proof obligation about runtime call behavior.
- Proof level: `Expr.externalCall` is explicitly **outside the supported fragment** of the generic whole-contract theorem — `Compiler/Proofs/IRGeneration/SupportedSpec.lean:993-996`: `def exprTouchesUnsupportedForeignSurface : Expr → Bool | .externalCall _ _ => true`. `EndToEnd.lean:41499-41503`: `externalCallBind` bodies are admitted into the bridged fragment only when callees resolve in an explicit `BridgedFunctionTable`; "opaque ECM statements remain outside the safe-body wrapper."

Comparison: our V2 `CallOracle/CallReturns + hprec + CallsCode` seams are strictly stronger science. We *include* external calls in the verified statement and reduce their trust to "the recorded log values are what the callee returned" plus precondition seams. Verity either excludes calls from the theorem or trusts an unverified `compile` function per module. There is no Verity analogue of proving observable equality of a call-containing program modulo a call log.

## 5. Takeaway paragraph (safe to put in an experiment report)

> Verity's end-to-end surface and exp005's headline carry the same species of tracked debt — a cross-layer run-correspondence supplied as a hypothesis (Verity's `hNative : nativeResultsMatchOn …`, EndToEnd.lean:128; our StmtTies/TermTies) — but the content differs. Verity does not model gas at all ("Gas is not modeled", TRUST_ASSUMPTIONS.md:61) and its source language has no gas introspection, so the problem our gas oracle solves does not arise for them; external calls in Verity are either excluded from the verified fragment (SupportedSpec.lean:996) or trusted via ECM `compile` functions defaulting to `proofStatus := .assumed` (ECM.lean:63). No current Verity theorem feeds values harvested from a bytecode run back into IR semantics — their legacy "runtime-oracle stack" was removed (TRUST_ASSUMPTIONS.md:61). What our Phase-3 realisability closure would establish, and Verity has not: a *generic* theorem that for any lowered program, one recorded run of the bytecode constructs the tie witnesses (StmtTies/TermTies), yielding proven observable equality between bytecode execution and executable IR semantics for programs that *observe gas and perform external calls*, with the residual trust confined to named call-oracle seams. Verity's closest achievement is narrower on both axes: a per-contract, gas-free, external-call-free concrete closure (simpleStorage_endToEnd_native_evmYulLean, EndToEnd.lean:41357), with the generic per-statement closure explicitly "not built yet" (TRUST_ASSUMPTIONS.md:64). Credit where due: Verity has one hypothesis-free concrete instance, which is exactly the shape of milestone Phase 3 should also produce as its first checkpoint.

**Key file:line index:** `forks/verity/Compiler/Proofs/EndToEnd.lean:57-58, 78-92, 128-147, 41357-41367, 41397-41415, 41468-41469` · `forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean:30884-30911` · `forks/verity/TRUST_ASSUMPTIONS.md:59-71` · `forks/verity/Compiler/Proofs/IRGeneration/SupportedSpec.lean:993-996, 1169` · `forks/verity/Compiler/ECM.lean:63` · `forks/verity/Compiler/Gas/StaticAnalysis.lean:8-15` · `forks/verity/AXIOMS.md` (zero project axioms).