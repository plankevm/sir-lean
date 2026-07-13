import Lake
open Lake DSL

-- Experiment 005 — high-level IR → EVM bytecode, lowering preserved (Track C).
-- We require exp003's `bytecode_layer` package (vendored EVM + the `Runs`
-- reasoning layer); transitively this brings in the `evm` package (`Evm`
-- library) and Mathlib. The lowering target is `Evm.decode`-compatible bytecode;
-- external calls discharge against exp003's `messageCall_runs` / `Runs` API.
-- See docs/ir-design.md for the extend-vs-fresh decision (fresh: `LirLean`).
require bytecode_layer from "../003_bytecode_layer"

package «ir_lowering» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «LirLean» where
  -- Root-based target (NOT the submodule glob): only modules transitively imported by the
  -- `LirLean` root build. The byte-coupled *leaf examples* (`WorkedCall`, `WorkedCallParity`, and
  -- the old `Decode` example module — distinct from the current `Decode/` directory) — superseded
  -- worked examples whose byte layout is stale under the Phase-C sload spill (re-derivation
  -- deferred) — have been ARCHIVED under `_attic/` (no longer in-tree as `LirLean` modules). The
  -- default-build cyclic headline `lower_conforms_cyclic` (+ `_cyclic'`, `CfgSim/`) and the
  -- whole spine remain in the cone and built. See docs/uniform-spill-alloc-plan.md (Phase C).
  roots := #[`LirLean]

-- NON-DEFAULT realisability integration lib. It holds the closed flagships and transitively
-- rebuilds the full exp003 + EVM proof cone without importing that cost into the default root.
-- Build with `lake build WIP`.
lean_lib «WIP» where
  roots := #[`LirLean.Realisability.RealisabilitySpec, `LirLean.Realisability.Producer]
