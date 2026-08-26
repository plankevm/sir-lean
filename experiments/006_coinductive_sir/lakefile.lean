import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
require evm from "../../EVM"

package "CoinductiveSir" where
  version := v!"0.1.0"

@[default_target]
lean_lib «CoinductiveSir»
