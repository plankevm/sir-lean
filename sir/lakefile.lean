import Lake
open Lake DSL

require evm from "../EVM"

package "sir" where
  version := v!"0.1.0"
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Sir» where
  roots := #[`Sir]

lean_exe "sir" where
  root := `Main
