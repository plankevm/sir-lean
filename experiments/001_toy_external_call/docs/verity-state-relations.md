# How Verity relates its states across layers (deep-dive)

Distilled from a code-level survey (2026-06) of `forks/verity`, as a guide
for adding higher-level IR layers on top of our bytecode-level theorem.
File/line citations are in the survey transcript; key anchors repeated here.

## The three relations (there is no step simulation anywhere)

Verity's "prove the redefined state is equivalent to EVMYulLean" is
actually **three different relations at three boundaries**, all equalities
after an encoding/projection — none of them a step-indexed simulation:

1. **During execution, source↔IR**: `runtimeStateMatchesIR`
   (`Compiler/Proofs/IRGeneration/FunctionBody.lean:101`) — an **exact
   coupling invariant** threaded through per-statement preservation proofs.
   Every component is pinned: context fields by equality, **memory
   exactly** (`state.memory = fun o => (runtime.world.memory o).val`),
   calldata exactly, and storage through an encoding
   (`state.storage = fun s => IRStorageWord.ofNat (encodeStorageAt fields world s.toNat)`).
2. **At the function-result boundary, source↔IR**:
   `sourceResultMatchesIRResult` (`FunctionBody.lean:7588`) — memory is
   **dropped**; success, returnValue and events exact; storage equal after
   encoding, on *all* slots.
3. **At the native boundary, IR↔EVMYulLean**: `nativeResultsMatchOn`
   (`Backends/EvmYulLeanNativeHarness.lean`) — storage constrained **only
   on caller-declared `observableSlots`**; memory and gas unconstrained;
   success/returnValue/events exact. The state handoff is a one-way
   constructor `toSharedState` (`Backends/EvmYulLeanStateBridge.lean:775`)
   that builds a minimal single-account EVMYulLean state (nonce 0, gas 0,
   empty memory) and an inverse `extractStorage` that defaults absent
   slots to 0 (finite `RBMap` vs total function).

End-to-end is the composition (`Compiler/Proofs/EndToEnd.lean:78,96`).

**The pattern, named**: *encoding function + coupling invariant during
execution + projection at the boundary.* The invariant is strict while
you're proving statements (so composition is by rewriting, like our
`injectFrame` discipline); the *theorem statement* only keeps what a
caller can observe.

## Surprise: their "high-level" source state is less abstract than expected

`Verity.ContractState` (`Verity/Core.lean:71`) **does** model word-addressed
memory (`memory : Nat → Uint256`), calldata as a word list, msg context,
events. The genuine abstraction over the EVM is in **storage typing**:
separate `storage`, `storageAddr`, `storageMap`, `storageMap2`,
`storageArray` fields, flattened to slots by `encodeStorageAt` (mappings
via keccak-derived `solidityMappingSlot`). What their source state simply
*lacks*: gas (everywhere), a multi-account world (single account),
delegatecall, external-call return data (interface-assumed via ECMs).

So "higher-level" in Verity ≈ typed storage + structured control flow +
no gas — not "no memory".

## Control flow: fuel-indexed structural recursion, no pc, no Hoare logic

Source loops: `execForEachLoop` with an explicit iteration count; IR
loops: Yul-shaped `for_`/`if_`/`switch` run by a fuel-indexed interpreter
(`IRInterpreter.lean:859`). Proofs are structural induction over
statements with fuel as the measure. There are **no loop invariants, no
pc, no relational program logic** — the supported fragment is small
enough that proofs unfold the semantics directly.

## The supported-fragment machinery

* Inductive whitelists per layer: `BridgedExpr` → `BridgedStraightStmt` →
  `BridgedStmt` (`Backends/EvmYulLeanBridgePredicates.lean`), and at
  source level `BridgedSafeStmts` (~36 statement patterns,
  `Backends/EvmYulLeanBodyClosure.lean`). Anything outside the predicate
  is rejected at compile time (fail-closed), not reasoned about.
* ~25–36 builtin bridge lemmas, all `rfl`
  (`Backends/EvmYulLeanBridgeLemmas.lean`), e.g.
  `evalBuiltinCall_add_bridge` — their analogue of our per-opcode lemmas,
  one level up.
* Append/closure lemmas make bridged sequences compose, mirroring our
  chunk composition.

## What their theorems do NOT constrain (and the stated justifications)

gas (explicitly out of scope); storage outside `observableSlots`;
memory in any result; intermediate states; *why* a revert happened (only
that success flags agree); external-call return data (ECM interface
assumptions); delegatecall/proxies (excluded, fail-closed flag);
multi-account effects (single-account bridge). Caveat from the survey:
the 30k-line closure file was structure-checked, not audited case by
case; "36 lemmas" is approximate.

## What this means for our stack

Our bytecode theorem is *below* anything Verity has (they stop at Yul,
gas-free, observables only). Adding a higher-level IR on top of our toy
IR should copy the shape but can keep more:

1. **Relation shape per new layer**: encoding function
   (`encode : HighState → Exec`-components) + coupling invariant threaded
   per-statement + boundary projection. Our current `injectFrame` is the
   degenerate case where the encoding is the identity and the projection
   keeps everything.
2. **We can degrade gas gracefully instead of dropping it**: exact gas at
   the bytecode layer (done) → exact-or-upper-bound at the structured IR
   layer → unconstrained only if/where the source semantics genuinely
   underdetermines costs. This is a capability Verity never had.
3. **Storage typing is the first real abstraction to add** (typed fields
   + keccak slot derivation), since that's where Verity spent its
   encoding machinery.
4. **Adopt the fail-closed supported-fragment predicate** rather than
   universal statements over a syntax that includes unsupported constructs.
5. **Decide memory observability early** — Verity's late-stage pain.
   Either pin memory in the during-execution invariant and drop it at
   boundaries (their choice; cheap given our exact base), or carve
   observable regions explicitly.
6. **Control flow needs no pc in the IR**: structured/CFG semantics with
   fuel; the byte-level pc appears only in the lowering layer's layout map
   (`label → offset`), generalizing our `pre.length` bookkeeping.
