import Lake
open Lake DSL

-- Experiment 004: nested EVM core over EVMYulLean («evmyul» package, library `EvmYul`),
-- vendored in-tree at ./EVMYulLean (squashed subtree of NethermindEth/EVMYulLean @ 066dc8b).
-- Monomorphized to EVM-only (B0): the `OperationType` polymorphism and the whole Yul
-- subsystem are removed; the shared semantics are now plain EVM.
-- Genuinely-nested mutual Θ/Ξ semantics; flat-vs-nested bake-off against exp003. See PLAN.md.
require evmyul from "EVMYulLean"

package «nested_evmyul» where
  -- `-s` raises the per-thread stack to 1 GB: the FFI-backed precompile gas lemmas
  -- (`NestedEvmYul.PrecompileGas` — `Ξ_BN_MUL`/`SNARKV`/… have kernel-heavy `String`-pattern
  -- bodies) overflow the default worker-thread stack during kernel typechecking under
  -- `lake build` (`(kernel) deep recursion detected`), though they check fine on the main
  -- thread (`lake env lean`).
  moreLeanArgs := #["-DautoImplicit=false", "-s", "1048576"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «NestedEvmYul» where
  -- Root module plus every submodule under `NestedEvmYul/` (B2 added
  -- `NestedEvmYul/NeverOutOfFuel.lean`).
  globs := #[.andSubmodules `NestedEvmYul]
