# Agent Responses (Plank EVM Semantics)

> **Archived — raw transcript.** Multi-agent investigation log. Its durable
> conclusions have been distilled into proper docs: the program-counter answer
> (§1) into [planning/sir-to-bytecode.md](../planning/sir-to-bytecode.md#where-the-program-counter-lives),
> and the Verity state-relation deep-dive (§4–§5) into
> [experiment 001 verity-state-relations.md](../../experiments/001_toy_external_call/docs/verity-state-relations.md).
> The docs-audit results (§3) drove the now-completed
> [review-followup-plan.md](./review-followup-plan.md). Kept for provenance.

## 1. Program Counter Question

Both sub-agents launched below. First, the program-counter question, which I can answer directly:

No — control flow doesn’t force a byte-level `pc` into the IR.  
There are two standard shapes, and both keep the IR `pc`-free:

- **Structured control flow** (`if`/`while`/blocks, Yul-style):  
  semantics by structural recursion (big-step, or small-step with a continuation/statement stack). No `pc` anywhere. This is what Verity inherits by making their IR literally Yul.
- **CFG of basic blocks** (likely what Plank SIR looks like):  
  the “position” is an abstract control point (`label`, `index within block`) rather than a byte offset. That is not a byte-level `pc`, it is just where you are in the syntax tree/graph.

The byte-level `pc` only appears in the simulation relation. We already have the degenerate version for straight-line code:

- `my.ofNat pre.length` bookkeeping through the chunk lemmas is a code-layout map.

With control flow, it generalizes to:

- `layout : Label → ByteOffset` (produced by the compiler),

and the invariant becomes:

- `EVM pc = layout(current label) + offset within chunk`.

The new proof obligations are:

- `JUMP`/`JUMPI` targets must land on `JUMPDEST`s (where threaded parameter `validJumps`/`D_J` is used),
- induction switches from structural-on-program to well-founded-on-fuel, since loops mean the program no longer shrinks.

So `pc` belongs in the relation, not in the IR language itself.

On higher-layer state constraints:

- Bytecode layer can use on-the-nose equality.
- Structured/control-flow layers typically use a coupling invariant (source locals/registers, source values/encodings).
- Contract boundary becomes observables (success/return data/logs/storage).

The first sub-agent is still responsible for extracting how Verity implements that middle layer.

---

## 2. Planned Investigations

### 2.1 Verity State-Abstraction Deep-Dive

Exact extraction of relations between source state, IR state, and EVMYulLean execution:

- abstraction function vs projection,
- cross-boundary handling of storage/memory/return values,
- why structured control flow avoids `pc`,
- statement-level invariant threaded through proofs (their analogue of `injectFrame`),
- what the end-to-end theorem constrains and what it omits.

Includes a concrete sketch of what a higher-level `IR → toy IR` layer could look like using their machinery.

### 2.2 Docs Audit

Cross-check repo docs against code in the four forks (`concept-comparison.md`, `lean-models.md`, `hol-models.md`, `evm-state-model.md`, `semantics-choice.md`, `verity-bridge.md`, …):

- validate each load-bearing claim,
- classify as accurate / misleading / incomplete / wrong / outdated,
- list essential omitted facts (e.g. zero execution theorems in EVMYulLean, Verity trusted `solc`, no formal Yul↔EVM bridge).

---

## 3. Docs Audit Results

The audit returned:

- facts were mostly correct at the quotation level,
- but incomplete and under-framed for planning/proof strategy.

### Scoring

- ~75% accurate
- ~60% complete
- ~50% current

### Substantive corrections

1. **`vyper-hol` proof status is conflated**  
   `vyper_call_correct` is proved, but depends on 7 bridge cheats and 56 pass-level cheats.  
   So “proved” means the theorem is formally present but relies on many explicitly cataloged assumptions (`PROOF_ROADMAP`).

2. **Verity is understated**  
   `compile_preserves_semantics` is fully proved; the bridge pattern in docs is in production use, not merely hypothetical.

3. **`verifereum` prog layer is underweighted**  
   It has a mature relational/Hoare-style framework, which is a major architectural advantage over EVMYulLean (which lacks that relational layer).

4. **Stale references**  
   Several EVMYulLean commit pins in docs (2025-09) are outdated relative to checked checkouts.

5. **Main gap is omission, not pure inaccuracy**  
   Missing proof-assurance framing included:

- EVMYulLean proves zero execution theorems.
- Verity stops at Yul with trusted `solc`, no gas model.
- No formal Yul↔EVM connection is established.
- This repo already has a complete IR→bytecode lowering proof against `EVM.X`.

### Suggested rewrite direction

Lead docs with a **proof-achievements / trust-assumptions matrix** rather than only state-model taxonomy.

---

## 4. Verity Demystification

Verity’s “nebulous equivalence” is effectively three relations, not one simulation:

### 4.1 Source ↔ IR during execution

`runtimeStateMatchesIR` is an equality-style coupling invariant for each statement:

- context fields equal,
- calldata equal,
- memory pinned exactly,
- storage related by `encodeStorageAt` (typed fields flattened to slots, bounds encoded into word carrier).

### 4.2 Source ↔ IR boundary

`sourceResultMatchesIRResult`:

- memory dropped at boundary,
- success / return value / events exact,
- storage equal over all slots via encoding.

### 4.3 IR ↔ EVMYulLean boundary

`nativeResultsMatchOn`:

- storage constrained only on caller-declared `observableSlots`,
- memory and gas unconstrained,
- `toSharedState` builds a minimal one-account native state (`nonce = 0`, `gas = 0`).

End-to-end theorem is composition of these two layers.

### Memory is not absent — it is constrained strategically

Verity `ContractState` does include:

- word-addressed memory (`Nat → Uint256`),
- calldata word lists,
- msg context.

Memory is exact in the middle-layer invariant, but abstractions appear elsewhere:

- typed storage (flattened fields and solidity-derived mapping slots),
- structured control flow (`for`/`if`/`switch`, fuel-based),
- no `pc`, no gas, no loop invariants, no Hoare logic,
- deliberate omissions: single-account world, no delegatecall, no external-return-data semantics beyond assumptions, no theorem proving revert reason beyond success mismatch.

### What this means for the next layer

For a higher-level IR above the toy IR, we can reuse this pattern:

- per-layer encoding function,
- coupling invariant per statement,
- boundary projection.

`injectFrame` is the degenerate case (identity encoding + keep-all projection).

Gas can be handled progressively:

- exact at bytecode layer,
- exact-or-upper-bound at structured layer,
- unconstrained where source underdetermines cost.

Storage typing is the first meaningful abstraction.

Two process lessons:

- use fail-closed supported-fragment predicates (e.g. whitelist patterns and reject unsupported syntax early),
- decide memory observability boundaries early.

### Audit honesty note

Their large closure file was only structure-checked, not fully case-audited; some “all 36 patterns are proven” claims rest on their own trust assumptions.

---

## 5. Follow-up: Verity Deep-Dive Consolidation

Demystification write-up (committed in `docs/verity-state-relations.md` in the experiment branch):

Verity does not prove a step-by-step simulation between source IR and EVMYulLean.  
The pattern is a three-part structure:

1. **Source ↔ IR (per statement):** `runtimeStateMatchesIR`  
   - exact-equality invariant threaded through statement lemmas,  
   - context fields equal, calldata equal, memory pinned exactly,  
   - storage related by `encodeStorageAt` (typed fields flattened into slots, then bounded into the word carrier).

2. **Source ↔ IR boundary (function result):** `sourceResultMatchesIRResult`  
   - memory is dropped,  
   - success/return value/events are exact,  
   - storage equal after encoding across all slots.

3. **IR ↔ EVMYulLean boundary:** `nativeResultsMatchOn`  
   - storage constrained only on caller-declared `observableSlots`,  
   - memory and gas unconstrained,  
   - one-way constructor `toSharedState` builds a minimal single-account native state (`nonce = 0`, `gas = 0`).

The end-to-end theorem is the composition of (2) and (3).

So the shape is:

- exact invariants while composing proofs (the role played by `injectFrame`),
- only observables at theorem boundaries.

Memory is not absent in Verity:

- `ContractState` contains word-addressed memory (`Nat → Uint256`), calldata word lists, and message context.
- memory is exact during execution.

What makes it “higher-level” is:

- typed storage modeling (`storage`, `storageAddr`, `storageMap`, `storageArray`) flattened via `solidityMappingSlot`,
- structured control flow (`for`/`if`/`switch`), fuel-indexed execution, no byte-level `pc`,
- no gas anywhere,
- no loop invariants and no Hoare logic; proofs unfold interpreter by fuel induction,
- deliberate omissions: single-account world, no delegatecall, external-call return data trusted by assumptions, and only success/reason compatibility (no full revert-reason theorem).

Implications for the next layer:

- Keep the same architecture on top of toy IR:
  - per-layer encoding function into the lower state,
  - per-statement coupling invariant,
  - projection at the boundary.
- `injectFrame` is the degenerate case (identity encoding + keep-everything projection).
- Gas can degrade gracefully:
  - exact at bytecode layer,
  - exact-or-upper-bound at structured layer,
  - unconstrained where the source genuinely underdetermines cost.
- Storage typing is the first meaningful abstraction (core of Verity’s encoding machinery).
- Process lessons:
  - use fail-closed supported-fragment predicates (e.g., `BridgedStmt` / `BridgedSafeStmts`) and prove a subset whitelist,
  - fix memory observability decisions early.

Honesty note: the large closure file was structure-checked but not fully audited statement-by-statement; claims about all 36 patterns being proven rely on documented trust assumptions.

Natural next steps are either:

- rewriting `concept-comparison.md` per the audit framing, or
- starting the `EVM.call` frame-insensitivity proof to discharge half of `CallOracleSound`.

---
