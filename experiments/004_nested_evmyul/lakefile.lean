import Lake
open Lake DSL

-- Experiment 004: nested EVM core over EVMYulLean («evmyul» package, library `EvmYul`),
-- vendored in-tree at ./EVMYulLean (squashed subtree of NethermindEth/EVMYulLean @ 066dc8b).
-- The Yul subsystem is stripped to the minimum the τ-polymorphic shared semantics need.
-- Genuinely-nested mutual Θ/Ξ semantics; flat-vs-nested bake-off against exp003. See PLAN.md.
require evmyul from "EVMYulLean"

package «nested_evmyul» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «NestedEvmYul» where
  globs := #[.andSubmodules `NestedEvmYul]
