# Spec Comments Removed - 2026-07-09

This report preserves the architectural content that was previously carried by
comments in `LirLean/Spec/*.lean`. The Lean spec files are now comment-free, so
the points below are the review surface for why the definitions are shaped as
they are.

## Must Understand Checklist

- The IR state is intentionally small: locals plus the observable self-storage
  world. It has no gas counter, program counter, stack, memory, or call frame.
- Gas is observable input, not IR accounting. Gas reads consume a gas stream
  entry; gas-free theorems use an explicit `NoGasReads` scope.
- Calls and creates consume positional streams. Stream entries are world/result
  observations paired with success or deployed-address words, not functions of
  visible IR operands.
- `RunFrom` permits leftover streams at halt, while `RunFromLeft` exposes
  leftovers and `RunFromAll` requires exact whole-stream consumption.
- Lowering is fixed-layout bytecode emission: per-block `JUMPDEST`s, fixed-width
  `PUSH4` destinations, a two-pass offset table, and `lower = encode (emit ...)`.
- `defEnv` is the ordered carrier for materialisation; `defsOf` is its first-find
  allocation view; `matCache` is a total left fold over `defEnv`.
- Pure definitions rematerialise. Gas, `SLOAD`, `CALL`, and `CREATE` results
  spill through canonical memory slots derived from `slotOf`.
- Recorder streams are extracted from a Type-valued bytecode run log. This is why
  realised gas, `SLOAD`, call, and create streams are honest functions.
- The observer bridge projects bytecode frame results back to IR observables by
  reading the self-account storage lens and decoding output as stopped or
  returned-word.
- Seam predicates name live runtime/engine assumptions: self-presence, self
  preservation, reachable calls-code, precompile no-erase, and clean halt scope.
- Well-formedness is static program vocabulary. It is designed to make the
  lowering proof consume high-level facts rather than opcode-shaped premises.
- Budget derivations collapse many lower-level obligations into `codeFits` and
  `stackFits`, plus canonical spill-slot facts from `defsOf`.

## IR Vocabulary

`IR.lean` defines the source vocabulary used by experiment 005: EVM words,
SSA-style temporaries, labels, blocks, expressions, statements, terminators, and
programs. Expressions cover immediates, temporary reads, arithmetic/comparison,
observable storage reads, and gas introspection. Statements cover assignment,
storage writes, calls, and creates. Terminators cover halt, return, jump, and
branch.

The call payload deliberately models only the channels needed by the current
lowering proof: callee, forwarded gas, and an optional result temporary. The IR
does not model calldata or return-data values in this cut. Create payloads are
already shaped for `CREATE` and `CREATE2`: the salt is optional so the same IR
surface can describe both variants.

## Observable Semantics

`Semantics.lean` gives the IR an observable big-step semantics over a CFG. The
state is the local environment plus a self-storage world, and the final
observable is the final world plus a halt result. Halt results distinguish
stopped execution from returning a word.

The semantics uses independent streams for gas observations, call observations,
and create observations. A gas expression consumes one gas-stream word. A call
statement consumes one call-stream entry containing the next world, success bit,
and optional returned word. A create statement consumes one create-stream entry
containing the next world and deployed-address word. These streams are consumed
head-first by matching IR constructs and are independent of each other.

`RunFrom` drops unused stream suffixes at halt. `RunFromLeft` records the
leftover streams. `RunFromAll` requires no leftovers, closing the suffix-vacuity
gap when bytecode logs are turned into realised oracle streams.

## Lowering Layout And Materialisation

`Lowering.lean` separates policy, mechanism, and backend emission. The backend
emits bytes with a fixed shape: every block starts with `JUMPDEST`, jump
destinations are fixed-width `PUSH4` offsets, and the offset table is computed by
a two-pass layout scan. `lower` wraps emitted opcode bytes into the final
`ByteArray`.

Allocation is carried by `defEnv`, the ordered program-order list of
`(Tmp, Loc)` entries. `defsOf` is the first-find allocation view used by lowered
code. Pure expressions are rematerialised at use sites. Non-recomputable values,
including gas observations, storage reads, call results, and create results, are
spilled to canonical memory slots derived from `slotOf`.

`matCache` is the total byte-cache fold over `defEnv`. It replaces the older
fuel-bounded recomputation story: materialisation is structural over the ordered
definition environment, not bounded by a separate recomputation fuel.

## Recorder And Observer Bridge

`Recorder.lean` defines a Type-valued bytecode interpreter/logging layer. The
Type-valued form matters: Prop-only derivations cannot be projected into the
concrete oracle functions consumed by the IR semantics.

The recorder logs only top-level observations. Gas reads and `SLOAD` warmth
charges are recorded when the machine stack context shows the top-level point.
Call and create records are likewise gated to the top-level continuation so the
resulting streams match the IR semantics. The projections `realisedGas`,
`realisedSload`, `realisedCall`, and `realisedCreate` are therefore honest
functions of the recorded bytecode run.

The observer bridge maps bytecode frame results to IR observables by reading the
self-account storage lens and decoding frame output. Empty output is a stopped
halt; non-empty output is decoded as a returned word.

## Call And Create Entries

`CallEntry.lean` explains the stream entries produced from bytecode logs. The
realised call and create streams are coupled to bytecode resume projections:
`resumeAfterCall` and `resumeAfterCreate` determine the observed world and result
channels for each recorded event. These entries are positional records indexed by
the bytecode log, not input-to-output functions over the visible IR operands.

## Public Conformance Vocabulary

`Conformance.lean` names the public theorem surface. `entryState` pins the
initial IR world to the recipient-account storage lens from the bytecode call
parameters. `RunLog.clean` scopes runs whose call results are usable by the
spec-level theorem: a call is clean when it succeeds or retains nonzero gas,
excluding exception-shaped results that are outside the current theorem scope.

`Conforms` requires both observable channels to agree: final self-storage world
and halt result. `NoGasReads` is the companion predicate used to state gas-free
variants without pretending that gas-consuming bytecode is independent of gas.

## Seam Assumptions

`Seams.lean` keeps the live runtime boundary explicit. `SelfPresent` names the
entry-world account-presence fact that the IR world alone cannot witness.
`CallPreservesSelf` captures the preservation of the recipient account across
calls. `PrecompilesPreservePresence` covers the immediate-precompile branch that
must not erase account presence. `ReachableFrom` scopes reachable bytecode
frames, and `PrecompileAssumptions` packages the live assumptions: precompile
no-erase plus the fact that reachable calls target code accounts rather than
precompiles. `CleanHaltsNonException` names the clean-halt scope imported from
the engine layer.

The seam file is a register of assumptions, not a second call-stream semantics.
The call-stream kernel remains the first-class spec surface in the semantics and
recorder modules.

## Well-Formedness Predicates

`WellFormed.lean` defines static obligations over the source program. The
gas/call-aware `RunDefinableG` replaces older definability predicates that were
unsatisfiable for gas and call constructs. `DefsConsistent` prevents shadowing
mismatches between program cursors and the allocation view. `CFGClosed` carries
entry, target-presence, and in-bounds control-flow closure. `DefEnvOrdered`
states define-before-use over the ordered definition environment.

The invalidation and revalidation predicates express scoped recomputation
soundness. A statement may invalidate rematerialised expressions that depend on
changed storage or call/create effects, but each block must revalidate before
leaving. This keeps the materialisation cache sound without exposing proof
internals in public theorem statements.

`IRWellFormed` bundles the static facts consumed by the lowering theorem:
run-definability, definition consistency, CFG closure, ordered definitions,
per-block revalidation, spill-slot addressability, and sane call/create
operands. It is the source-program well-formedness surface; derived bytecode
adapters are built downstream.

## matCache And defEnv Invariants

The key invariant is the agreement between `defEnv`, `defsOf`, and `matCache`.
`defsOf` is first-find, while the cache fold is a left fold over the ordered
environment. `DefsConsistent` ensures entries for a temporary carry the canonical
allocation, so first-find allocation and last-written cache content agree for
the relevant source obligations.

`DefEnvOrdered` supplies the topological order used by first-index and
prefix-stability lemmas. `matCache_unfold` is the central internal fold law:
when a temporary is present in `defEnv`, its cached bytes match materialisation
of the canonical location under the cache prefix justified by earlier operands.

## Budget Derivations

`BudgetDerivations.lean` collapses bytecode-side bounds into two scalar source
budgets. `codeFits` proves the per-cursor program-counter and offset facts
needed by layout, closed CFG, and lowered-code well-formedness. `stackFits`
proves stack-room obligations by bounding materialisation and charge-depth
folds.

The spilled-slot facts are derived from `defsOf`: any allocation registered as a
slot points at the canonical `slotOf` address for that temporary. This removes
the need for a separate source marker exclusion predicate and keeps the
addressing proof tied directly to the lowering allocation policy.
