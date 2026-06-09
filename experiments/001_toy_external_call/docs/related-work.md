# Related work: Verity's lowering, and the Yul side of EVMYulLean

Findings from a survey of `forks/verity` and the Yul half of
`forks/EVMYulLean` (2026-06), assessed against this experiment's approach.

## What Verity does

* **Pipeline**: Lean EDSL (`verity_contract` macro) → `CompilationModel` →
  IR → **Yul source text** → pinned `solc 0.8.33` → bytecode. Their "IR"
  is already Yul-shaped (`IRExpr`/`IRStmt` are type aliases for
  `Yul.YulExpr`/`Yul.YulStmt`, `Compiler/IR.lean`).
* **What is proved**: the layers down to Yul. EDSL↔CompilationModel via
  per-contract bridge theorems; CompilationModel→IR via a generic
  `supported_function_correct` theorem; IR↔Yul for "safe-body" fragments,
  with the dispatch bridge as an explicit theorem *hypothesis*. Validated
  by executing the emitted Yul under EVMYulLean's Yul interpreter
  (`callDispatcher`) and comparing observables
  (`Compiler/Proofs/EndToEnd.lean`: `sourceResultMatchesNativeOn`).
* **What is trusted**: the Yul→bytecode step (`solc`) is *not* verified —
  Verity's chain stops at Yul. Their AXIOMS.md "zero axioms" claim is
  about Lean axioms; solc sits outside the formal boundary.
* **Gas**: not modeled at all ("semantic correctness does not imply
  gas-safety", TRUST_ASSUMPTIONS.md).
* **External calls**: External Call Modules — named interface assumptions
  per callee (ERC-20 transfer behaves per spec, etc.), fail-closed in CI.
  Analogous in role to our `CallOracleSound`, but at interface level
  rather than exact `EVM.call` agreement.
* **Relation shape**: not a step-indexed simulation — observable-result
  projection (success flag, return value, events, storage restricted to
  declared `observableSlots`) over whole-contract executions.

## The Yul side of EVMYulLean

* Full, production-grade Yul interpreter (statements, loops, user
  functions, switch/leave; `EvmYul/Yul/Interpreter.lean`), sharing the
  primop layer with the EVM side via `OperationType` dispatch.
* **Essentially no theorems**: 18 lemmas total, all structural
  size/termination facts (`SizeLemmas.lean`). No semantic lemmas, and **no
  formal connection between the Yul and EVM semantics** — they are two
  interpreters sharing infrastructure, with solc as the (unformalized)
  bridge.

## Consequences for this project

* **Targeting Yul would not have helped.** The Yul side has even less
  proof support than the EVM side, and lowering to Yul re-introduces solc
  as a trusted compiler — exactly the gap this experiment exists to close.
  Our IR→bytecode theorem against `EVM.X`, gas-exact and
  with errors aligned per opcode, is strictly below Verity's formal floor;
  the two efforts are complementary rather than overlapping.
* **Ideas worth importing as the IR scales**:
  * *Observable-result projection* for the eventual contract-level
    theorem (at the `Ξ`/`Θ` boundary): compare success/return
    data/logs/selected storage instead of whole states — our
    on-the-nose state equality is sustainable at the bytecode layer but
    will want projection once nondeterministic-ish context (block data,
    precompiles) enters.
  * *Generic supported-fragment theorems* over per-program proofs:
    Verity's elimination of per-contract axioms via one generic theorem is
    the same move as our `Z_generic`/chunk lemmas, applied a level up.
  * *Scoped interface assumptions* (their ECMs) as the eventual refinement
    of our call oracle: today `CallOracleSound` demands exact `EVM.call`
    agreement; contract-level reasoning will want per-callee behavioral
    interfaces layered on top of it.
