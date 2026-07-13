# LirLean file-organization plan

Date: 2026-07-04. Status: **planned, execution DEFERRED** until the foundation-strengthening
workflow lands (moving files + updating every import collides head-on with a live deep
refactor — reorgs need a quiet tree). Execute + push the moment foundation is merged to `main`.

## Problem
`LirLean/` has **26 top-level `*.lean` files (13,122 lines)** in a flat pile — the byte/decode,
materialise, simulation, and assembly layers of the lowering-correctness proof, with no directory
structure. (The already-organized parts: `Spec/`, `Engine/`, `V2/`, `V2/Drive/`.)

## Proposed structure
Top-level `LirLean/` becomes just `Audit.lean` + these directories:

| Dir | Role | Files (moved from top-level) |
|---|---|---|
| `Spec/` *(exists)* | the definitions | IR, Semantics, Lowering, Recorder, Seams, Conformance |
| `Engine/` *(exists; slated for exp003)* | IR-agnostic EVM reasoning | AccountMap, StepWalk, Descent, DriveMono, Charges, MemAlgebra, CleanHalt, DriveRuns |
| `Decode/` **(new)** | byte layout + decode + control-flow validity | Layout, DecodeLower, DecodeAnchors, LowerDecode, BoundaryReach, JumpValid, NoCreateBytes, LoweringLemmas |
| `Materialise/` **(new)** | the spill/recompute value channel | MaterialiseRuns, MaterialiseGas, MaterialiseCleanHalt, MatDecLower, StashTail |
| `Sim/` **(new)** | v1 gas-aware simulation bricks + call/create oracles | SmallStep, Match, SimStmt, SimStmts, SimTerm, Call, Create |
| `Conformance/` **(new)** | assembled headline + direct support | LowerConforms, DefsSound, CleanHaltExtract, RecorderLemmas, Acyclic |
| `V2/` *(exists)* + `V2/Drive/` | the gas-free spine | (unchanged) |
| `Audit.lean` | axiom-guard net, imported last | (stays top-level) |

Net: 26 flat files → 1 file + 7 role-directories.

## Execution notes (when the tree is quiet)
1. `git mv` each file; update its module path in EVERY `import` across the repo (e.g.
   `import LirLean.LowerDecode` → `import LirLean.Decode.LowerDecode`) and in `LirLean.lean`.
2. `lake build` (default, green + sorry-free) + `lake build Nightly` after.
3. This touches nearly every file's import block — hence it must NOT overlap other in-flight work.

## Contents will shift before execution — re-confirm the mapping at execution time
- **Acyclic + LowerConforms** (the acyclic headline) are slated to be **dropped** (lead decision:
  the cyclic headline dominates), so `Conformance/` shrinks — possibly to nothing, folding into `V2/`.
- **Create.lean** becomes **live** (the CREATE2 feature), so it stays under `Sim/` (or a `Create/`).
- **BytecodeLayer/Hoare/** is separately slated to **graduate to exp003** (`docs/target-architecture-2026-07-02.md`).
So run the reorg AFTER foundation + the acyclic-drop, when the final file set is settled.
