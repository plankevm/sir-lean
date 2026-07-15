# Overnight polish outcome

Both behaviour-neutral cleanups landed on `refactor/overnight-polish`. The
statements of `Lir.lower_conforms`, `Lir.lower_conforms_exact`, and
`Lir.lower_conforms_gasfree` remained byte-identical throughout.

## Step outcomes and commits

### A1 — move the reachable-boundary adapter to Lir

PASS at `9d353de621008a179a34e81f757b84bdc17a041c`, committed and pushed as
`polish: place reachable boundary in Lir namespace`.

`Lir.AtReachableBoundary` now lives in namespace `Lir`. No
`BytecodeLayer.Interpreter.AtReachableBoundary` references remain, all live
consumers resolve through `Lir`, and `EVM/BytecodeLayer` contains no
Lir-specific declarations. The generic `modellable_of_runs` remains in
`BytecodeLayer.Interpreter`. A1 required no follow-up fix.

The A1 gate passed in both build cones. Each flagship reported exactly
`[propext, Classical.choice, Quot.sound]`, and the implementation endpoint was
clean, pushed, and synchronized with origin before A3 began.

### A3 — remove the vestigial SLOAD warmth stream

PASS at `2d687ced022c3750ddc3aceb48b5c63038dcd7bc`, committed and pushed as
`polish: drop vestigial sload warmth stream`.

`RunLog` now has exactly four fields: `observable`, `gas`, `calls`, and
`creates`. SLOAD values remain reflexive through `evalExpr`'s `st.world`
lookup; only the unused parallel warmth stream was removed. The tracked tree
has no remaining `sloads` references.

The documentation sweep landed at
`57c5b25353ed1f596906808ec961c857f0164ae3`, committed and pushed as
`polish: sweep removed sload log references`. It brought historical and live
descriptions of recorder state into line with the four-field model. Nothing
from A3 is deferred.

The A3 gate passed in both build cones. No forbidden Lean declarations or
tactics were introduced, and each flagship retained exactly the standard
axiom trio.

## Net line and field effect

Relative to the pre-A1 baseline `acacd76`, A1 and both A3 commits changed 29
files with 634 insertions and 957 deletions: **323 net lines removed**. A1 was
line-neutral (2 insertions and 2 deletions); the A3 implementation removed 318
net lines, and its documentation sweep removed another 5 net lines.

`RunLog` lost one field, changing from five fields to four. No replacement
field or second SLOAD record was added.

## Final green gate

Both build cones completed successfully:

```text
Build completed successfully (1101 jobs).
Build completed successfully (1106 jobs).
Build completed successfully (1165 jobs).
Build completed successfully (1184 jobs).
Build completed successfully (1201 jobs).
```

The flagship axiom output was exactly:

```text
'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The polished implementation endpoint is
`57c5b25353ed1f596906808ec961c857f0164ae3`, pushed to
`origin/refactor/overnight-polish` before this outcome document was added.
