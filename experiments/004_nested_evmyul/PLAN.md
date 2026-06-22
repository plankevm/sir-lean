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
- [~] **B2** Never-`OutOfFuel` on nested `Ξ/Θ`: fuel ≥ gas-derived bound ⇒ no
  `OutOfFuel` (nested analogue of exp003's `messageCall_never_outOfFuel`).
  PARTIAL — cornerstone (per-step gas positivity) fully proved; measure assembly
  remains. See B2 log below.
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
- 2026-06-22 (B2, PARTIAL): Nested never-`OutOfFuel` — cornerstone proved, measure
  assembly documented. All in `NestedEvmYul/NeverOutOfFuel.lean`; bare `lake build`
  GREEN; `#print axioms` on every theorem reports only `[propext, Quot.sound]`
  (+ `Classical.choice` for the `Θ_zero`/`Ξ_zero` base cases) — **no `sorryAx`, no
  custom axiom, zero `sorry`/`admit`/`axiom` in source.**
  - **Lakefile + wiring.** Restored the default-target glob to
    `globs := #[.andSubmodules \`NestedEvmYul]`; root `NestedEvmYul.lean` now
    `import`s `NestedEvmYul.NeverOutOfFuel`. New module is in the default build.
  - **Fuel bound.** `def seedFuel (g : ℕ) : ℕ := 4 * (g + 1)` — gas-derived,
    analogue of exp003's flat `seedFuel gas`. Rationale: each `X` loop iteration
    burns ≥1 gas; the per-instruction fuel-hop count across `X`/`step`/`call`/`Θ`/`Ξ`
    is ≤4; child gas is carved from the parent (`Ccallgas ≤ parent gas`); depth ≤1024.
    Any larger multiple also works.
  - **Fuel-`0` base cases (PROVED, all `rfl`).** `X_zero`, `step_zero`, `call_zero`,
    `Ξ_zero`, `Θ_zero` — these are the ONLY direct emitters of `.error .OutOfFuel`
    in the five mutual layers (everything else propagates), pinning exactly where the
    bound must bite.
  - **Per-step gas positivity = CORNERSTONE (PROVED).** `C'_pos_of_runnable :
    runnable w → 1 ≤ C' s w`, where `runnable w := w ∉ {STOP, RETURN, REVERT,
    SELFDESTRUCT, INVALID}`. Covers ALL ~140 opcodes via one `cases w`-sweep:
    constant-cost groups (`Wbase/Wverylow/Wlow/Wmid/Whigh`) collapse under a
    `decide`-evaluated membership cascade; special arms use helper positivity lemmas
    `Caccess_pos`, `Csstore_pos`, `Csload_pos`, `Cselfdestruct_pos`, `Ccall_pos` (all
    PROVED — each dominated by a positive gas constant, `Gwarmaccess=100`, …).
    KEY SEMANTIC FACTS this rests on: the only `C'=0` opcodes are `Wzero =
    {STOP, RETURN, REVERT}` (all *halt* the `X` loop via `H`) and `INVALID` (whose
    `step` returns `.error .InvalidInstruction` — a non-`OutOfFuel` halt). So every
    opcode that *continues* the loop strictly burns gas ⇒ gas is a sound decreasing
    measure.
  - **REMAINING obligations for the headline `Θ_never_outOfFuel` (documented in the
    file, NOT faked):**
    1. **Gas-decrement chain** `C'_pos_of_runnable → Z → step → X`: prove a
       successful `Z validJumps w s = .ok (s', cost₂)` yields `1 ≤ cost₂` (= `C'` of
       `Z`'s post-`cost₁` state — started as `Z_cost₂_pos` but the `Except` `do`-block
       inversion is fiddly: `simp [Bind.bind, Except.bind]` leaves nested
       `match .ok/.error` that `split` doesn't fully peel; needs a targeted
       `Except.bind` inversion lemma), then that `step f cost₂ instr s` on the default
       (non-call/create/halt) arm yields a state with `gasAvailable` reduced by
       `cost₂` (i.e. `EvmYul.step` preserves gas except the `- gasCost` debit; a
       per-opcode `replaceStackAndIncrPC`-preserves-gas sweep).
    2. **`X` measure descent.** With (1): one non-halting `X (f+1)` iteration goes to
       a state with strictly less gas, so `X` needs ≤ `gas+1` fuel for its own loop
       (a `Nat`-strong-induction on gas, or a `termination_by gas` measure lemma).
    3. **Cross-layer gas/depth conservation.** `call`/`Θ`/`Ξ` forward `Ccallgas ≤ g`
       to the child and bump depth (`e+1`), capped at 1024; the child's fuel need
       (`seedFuel childGas`) plus the 3 descent hops stays under the parent's budget.
       This is the genuinely-nested analogue of exp003's flat `gasFundsDescent`
       (there the trampoline made it a `totalGas` sum over a pending stack; here it is
       a direct parent→child inequality threaded through the `Θ`/`Ξ` arms of `call`).
    4. **Final mutual induction** on `fuel` over `X`/`Ξ`/`Θ`/`call`/`step`
       simultaneously, concluding `seedFuel g ≤ fuel → layer … ≠ .error .OutOfFuel`.
       Spine mirrors exp003 but the recursion is genuinely mutual (no trampoline), so
       it is a `Nat.rec`/well-founded mutual induction rather than a stack measure.
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
