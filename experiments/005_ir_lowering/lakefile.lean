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
  globs := #[.andSubmodules `LirLean]
