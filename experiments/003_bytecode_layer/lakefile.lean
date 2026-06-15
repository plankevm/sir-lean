import Lake
open Lake DSL

-- Experiment 003: bytecode layer over the real leanevm («evm» package, library `Evm`).
-- Reflexive CALL modeling; observables at the messageCall boundary. See docs/design.md.
require evm from "../../forks/leanevm"

package «bytecode_layer» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «BytecodeLayer» where
  globs := #[.andSubmodules `BytecodeLayer]
