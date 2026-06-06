import Lake
open Lake DSL

require evmyul from "../../forks/EVMYulLean"

package «toy_external_call» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «ToyExternalCall» where
  globs := #[.andSubmodules `ToyExternalCall]
