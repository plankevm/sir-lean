import Lake
open Lake DSL

-- Experiment 005 — high-level IR → EVM bytecode, lowering preserved (Track C).
-- We require exp003's `bytecode_layer` package (vendored EVMLean + the `Runs`
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
  -- default-build cyclic headline `lower_conforms_cyclic` (+ `_cyclic'`, `Assembly/`) and the
  -- whole spine remain in the cone and built. See docs/uniform-spill-alloc-plan.md (Phase C).
  roots := #[`LirLean]

-- NON-DEFAULT work-in-progress lib: the Phase-3 realisability spec skeleton (sorry-carrying BY
-- DESIGN — every sorry there is tracked debt; see the module header docstring). Deliberately
-- NOT a default target and NOT imported by the `LirLean` root, so the default build stays
-- sorry-free. Build with `lake build WIP`.
lean_lib «WIP» where
  roots := #[`LirLean.V2.Realisability.RealisabilitySpec]
