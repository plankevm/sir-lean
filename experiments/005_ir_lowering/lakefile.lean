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
  -- `LirLean` root build. This EXCLUDES the byte-coupled *leaf examples* `LirLean.Decode`,
  -- `LirLean.WorkedCall`, `LirLean.V2.WorkedCallParity` — superseded worked examples whose byte
  -- layout is stale under the Phase-C sload spill (re-derivation deferred). The four headlines
  -- (`lower_conforms`/`lower_conforms_acyclic_cfg`/`lower_conforms_cyclic`/`_cyclic'`) and the
  -- whole spine remain in the cone and built. See docs/uniform-spill-alloc-plan.md (Phase C).
  roots := #[`LirLean]
