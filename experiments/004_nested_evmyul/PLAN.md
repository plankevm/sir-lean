# Track B — local plan (Nested EVM core over EVMYulLean, Yul stripped)

Worktree: `../evm-semantics-wt/nested-evmyul` · Branch: `exp004-nested` · Base: `exp003-fuel-layer-cleanup`
Master index: repo-root `currentplan.md`.

## Goal
Build the EVM reasoning core on the **genuinely nested** semantics
(NethermindEth/EVMYulLean's mutual `Θ/Ξ`), as a flat-vs-nested bake-off against
exp003. Deliver: external-call core logic, fuel↔gas (never-`OutOfFuel` when fuel ≥
gas-bound), and an observables-only surface for IRs — with **multiple** calls
composing naturally (the thing flat makes hard).

## Source facts (validated 2026-06-22)
- Upstream dev checkout: `forks/EVMYulLean` (gitignored). `EvmYul` lib ≈700K,
  `EvmYul/Yul/` ≈200K, `EthereumTests` empty. Package `«evmyul»`, libs `EvmYul` +
  `Conform`. Crypto FFI (sha256/keccak) in the lakefile.
- Nested core: `EvmYul/EVM/Semantics.lean` — mutual `call`/`Θ`/`X`/`Ξ`/`Lambda`/`Υ`,
  fuel-passing. `Ξ` builds a fresh child machine, runs `X`, returns a result tuple;
  `Θ` consumes it. (Contrast exp003's flat `drive`+`Pending`.)
- **Yul strip:** only `EvmYul/Semantics.lean` (the shared one) imports `EvmYul.Yul`.
  Removing `EvmYul/Yul/` requires fixing that single import.

## Milestones
- [x] **B0** Monomorphize EVMYulLean to EVM-only: remove the `OperationType = Yul |
  EVM` polymorphism entirely, specialize all `τ`-indexed types to their EVM
  instances, delete the whole Yul subsystem. (Done 2026-06-22; see log.)
- [ ] **B1** Squashed subtree vendor of EVMYulLean → `EVMYulLean/` here; strip
  `EvmYul/Yul/` + Yul-only code; fix the `EvmYul/Semantics.lean` import; keep the
  EVM library (+`Conform` dep) green via `lake build`; trim heavy/irrelevant pieces.
  Add a lakefile for exp004 requiring the vendored `evmyul`.
- [ ] **B2** Never-`OutOfFuel` on nested `Ξ/Θ`: fuel ≥ gas-derived bound ⇒ no
  `OutOfFuel` (nested analogue of exp003's `messageCall_never_outOfFuel`).
- [ ] **B3** Nested external-call core: `{P} Ξ(child) {Q}` triple + call-site/frame
  rule; show ≥2 calls compose naturally.
- [ ] **B4** Observables-only, fuel/frame-free surface for IRs.

## Agent brief (durable — re-spawn from this verbatim)
> Work ONLY in `/Users/eduardo/workspace/evm-semantics-wt/nested-evmyul`, branch
> `exp004-nested`, dir `experiments/004_nested_evmyul`. Do **Milestone B1 only**
> this run, then stop and report. Vendor with:
> `git subtree add --prefix=experiments/004_nested_evmyul/EVMYulLean /Users/eduardo/workspace/evm-semantics/forks/EVMYulLean <HEAD-sha> --squash`
> (resolve `<HEAD-sha>` via `git -C /Users/eduardo/workspace/evm-semantics/forks/EVMYulLean rev-parse HEAD`.
> The dev checkout lives ONLY in the main repo tree (gitignored, absent from this
> worktree), so use the ABSOLUTE path as subtree source; requires a clean tree,
> so commit the PLAN.md first). Then strip `EvmYul/Yul/` and Yul-only files, fix the
> `EvmYul/Semantics.lean` import, and get `lake build` green for the EVM library.
> If the EVM library genuinely needs a Yul fragment, keep the minimum and note it.
> Append dated progress to this PLAN.md after each step; commit frequently on this
> branch; do not touch other tracks. Report the final build status + what was stripped.

## Progress log
- 2026-06-22: Track seeded. Awaiting B1 agent.
- 2026-06-22 (B1): Vendored EVMYulLean as a squashed subtree at
  `experiments/004_nested_evmyul/EVMYulLean` from
  `/Users/eduardo/workspace/evm-semantics/forks/EVMYulLean` @ `066dc8b` (816K vendored).
  - **Yul strip.** The shared `Semantics.lean` is `τ`-polymorphic
    (`OperationType = Yul | EVM`); its `step`/`dispatch*` machinery has `.Yul` arms
    that call the Yul primop interpreter, and the core EVM state types `Account`/
    `ExecutionEnv` carry `Yul.Ast.contractCode τ` (`= ByteArray` for `.EVM`). So a
    minimal Yul fragment is genuinely required by the EVM path. Kept (minimum):
    `EvmYul/Yul/{Ast,State,StateOps,Exception,Wheels,PrimOps}.lean` — this is the
    transitive closure the shared semantics + EVM state types pull in; none of them
    import the deleted modules. Deleted (Yul-only): `EvmYul/Yul/{Interpreter,
    MachineState,SizeLemmas,YulNotation}.lean` and `EvmYul/Yul/YulSemanticsTests/`.
  - `EvmYul/Semantics.lean` import was left UNCHANGED: its Yul imports
    (`Yul.{State,Ast,Exception,PrimOps,StateOps}`) all point at kept modules, so
    nothing to fix there. The umbrella `EvmYul.lean` and `lakefile.lean` were edited:
    dropped the deleted-module imports + the `yulSemanticsTests` exe.
  - Added `experiments/004_nested_evmyul/{lakefile.lean,NestedEvmYul.lean,
    lean-toolchain}` requiring the vendored `evmyul` (mirrors exp003's
    `require evm from "EVMLean"`). Toolchain pinned to the vendored `v4.22.0`.
  - **Build status: GREEN.** `lake update` pulled the mathlib v4.22.0 cache
    (no scratch mathlib build needed). `lake build evmyul/EvmYul` → 1033/1033, 0
    errors — and this includes the crypto FFI extern_lib (sha-256 + SHA3IUF +
    ffi.c compiled via `cc`): **no FFI/native blocker in this environment.**
    `lake build` (exp004 default target `NestedEvmYul`, which `import`s
    `EvmYul.EVM.Semantics`) → green, confirming the lakefile `require evmyul`
    wiring end-to-end. B1 complete.
- 2026-06-22 (B0): **Monomorphized EVMYulLean to EVM-only.** The `OperationType =
  Yul | EVM` polymorphism is gone — `inductive OperationType` deleted, the `τ`
  parameter stripped from every type and function it threaded through.
  - **Types specialized.** `contractCode τ` → `ByteArray` (its `.EVM` instance),
    inlined directly into `Account`/`PersistentAccountState`/`ExecutionEnv`/
    `ToExecute` (which no longer import `Yul.Ast`). The `(τ : OperationType)`
    parameter dropped from `Account`, `PersistentAccountState`, `ExecutionEnv`,
    `State`, `SharedState`, `AccountMap`, `PersistentAccountMap`, `ToExecute`,
    `Operation` (and its `SAOp/CBLOp/KOp/EOp/BOp/SMSFOp/LOp/SOp` sub-ops). All
    `… .EVM` type applications across the EVM side + Conform were stripped.
  - **Shared `Semantics.lean` rewritten.** The `Transformer τ`/`dispatch*`
    indirection (which matched on `τ` to pick EVM-vs-Yul interpreters) collapsed to
    direct `EVM.*` calls; `step`'s signature lost `{τ}` and `Operation τ → … →
    Operation`, and ALL `.Yul` match arms (STOP/MLOAD/RETURN/REVERT/SELFDESTRUCT/
    POP/EXTCODESIZE/RETURNDATACOPY + the `.Yul, _` fallback) were deleted. The
    `match τ, op` became `match op`.
  - **Yul deleted.** Entire `EvmYul/Yul/` removed (`Ast`, `Exception`, `PrimOps`,
    `State`, `StateOps`, `Wheels` — the modules B1 had kept). After the refactor no
    file imports `EvmYul.Yul.*`, verified by grep. Umbrella `EvmYul.lean` dropped
    the six Yul imports; `EVMYulLean/lakefile.lean` comment updated.
  - **Proofs/lemmas adapted:** none. The vendored EVM library carries no proofs that
    broke — the refactor was purely on `def`s/`structure`s/`abbrev`s. Conform (the
    conformance harness) only ever used `.EVM` instances, so the same `.EVM`-strip
    fixed it; all its modules + `Conform.Main` build.
  - **Build: GREEN.** exp004 target (`lake build NestedEvmYul.lean`, transitively the
    full `EvmYul` lib incl. nested `EvmYul.EVM.Semantics` Θ/Ξ/X) → green; vendored
    `EvmYul` default lib → green; all `Conform.*` modules → green. (`lake build
    Conform` as a lib still fails on a *pre-existing* missing `Conform.lean` root —
    not introduced here; the modules themselves compile.)
  - **Axioms:** `#print axioms` on `EvmYul.step`, `EvmYul.EVM.Ξ`, `EvmYul.EVM.Θ` all
    report only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom
    axiom. `grep` confirms zero `sorry`/`admit`/`axiom` in source.
