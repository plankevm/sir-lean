import Lake
open Lake DSL

-- Experiment 003: bytecode layer over EVMLean («evm» package, library `Evm`),
-- vendored in-tree at ./EVMLean (squashed subtree of philogy/leanevm @ 9cefe5b).
-- Reflexive CALL modeling; observables at the messageCall boundary. See docs/design.md.
require evm from "EVMLean"

package «bytecode_layer» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «BytecodeLayer» where
  globs := #[.andSubmodules `BytecodeLayer]
