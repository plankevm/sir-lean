# Phase D port-hygiene outcome

Phase D completed as a behavior-preserving cleanup of the folded
`EVM/BytecodeLayer` surface. The work removed naming debt, compatibility and
namespace residue, stale documentation references, an unwanted aggregator
edge, and duplicated alignment proofs. The three flagship statements remain
unchanged from the pre-Phase-D baseline `ccf0d0d2`.

## D1 — naming and documentation hygiene

D1 passed after the following commits:

- `90d13254ef4a674a45c144552cd5397b4ab2d952` — renamed the IR halt result.
- `0f3cc0eb7b0da568944ff9777c22eff3cf3173e8` — renamed the EVM byte-window
  module from `MatDecLower` to `ByteWindow`.
- `1c8c55d3c76d8b015e94464bbccbd67f715da317` — removed recorder-entry version
  tags.
- `c5eb227d1fc79663901bf2e9096b94120672a38c` — renamed call reflection for its
  oracle role.
- `c22b95659f737b3c01d6908872f8330f987120d7` — named the modellability theorem
  by runs.
- `3e2b71abbc0948310af9bf3373d26245a3852f6c` — clarified the precompile-account
  lemma names.
- `03d8a43e0b8cdddec18d5436d9ac8a616bc98be6` — updated stale review prose that
  still presented the renamed items as unresolved debt.

Every rename was propagated across both packages. The retired names and the
EVM-side `MatDecLower` path have zero repository matches; the distinct IR-side
`Materialise/MatDecLower.lean` remains intentionally. All 212 changed Lean lines
normalize to exact lexical renames, and the three flagship statements are
byte-identical to `ccf0d0d2`.

## D2 — dead aliases and dangling references

D2 passed after three commits:

- `bc76ad814f58f54c9c8a5c98c0a6f8d4ede3d3f5` — removed the generic
  `BytecodeLayer.Exec.Trace` compatibility alias and pointed its sole forwarding
  consumer directly at `GasOracle`.
- `785d67ecd102e1604f444a5b1e2d7380648dc380` — removed the redundant `Lir`
  namespace open.
- `0d5fdc22d76730478c69e9ad26929dc841dbe6d4` — removed nonexistent `_attic`
  references and corrected the affected historical descriptions.

No live module was deleted. `MatDecLower` to `ByteWindow` remained a pure
rename, both consumers import `ByteWindow`, and EVM has no `LirLean` back-import.
Whole-repository sweeps found no remaining Phase D old names,
`BytecodeLayer.Exec.Trace` references, old EVM `MatDecLower` imports or links, or
`_attic` references. The flagship statement hashes still match `ccf0d0d2`; only
a helper proof-body reference changed earlier in Phase D.

## D3 — aggregator hygiene

Commit `a664f729bb0d45e038cc6695aded6ba4a7cd2b66` removed the draft
`BytecodeLayer.EVMSpec` import and its aggregator comment from
`EVM/BytecodeLayer.lean`. `EVMSpec.lean` remains in the repository.

## D4 — alignment-proof consolidation

Commit `ac3e9bdb2c248c41b35ef953e55f7b9690a603d7` introduced a
predicate-parameterized emission/alignment ladder and instantiated it for
`IsLoweringOp`, `NoCallCreateOp`, and `NoGasOp`. This removed duplicated
expression, materialization-fold, statement, and terminator proofs without
changing the flagship statements.

## Reverted or deferred work

No Phase D step was reverted or deferred. The temporary swap used while
completing witness checks was removed. No `.lake` or Smithers artifact is
tracked; the three pre-existing untracked `smithers.db` files remain local and
were not committed.

## Final green gate

Both build cones completed successfully:

```text
Build completed successfully (1101 jobs).
Build completed successfully (1106 jobs).
Build completed successfully (1165 jobs).
Build completed successfully (1190 jobs).
Build completed successfully (1198 jobs).
```

The flagship axiom output was exactly:

```text
'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Phase D implementation ends at
`ac3e9bdb2c248c41b35ef953e55f7b9690a603d7`, synchronized with
`origin/refactor/phase-d-hygiene` before this outcome document is added.
