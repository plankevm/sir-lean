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
  PARTIAL — cornerstone + gas-decrement chain (`Z→step→X`) + `X` measure descent +
  cross-layer gas/depth conservation (item 3) + 4/5 layer propagation skeletons
  (`Ξ`/`Θ`-Code/`call`/`Lambda`) proved (B2d). **B2e: step skeleton + X inner
  loop-induction + precompiled `Θ`-arm + END-TO-END LEAF FRAME (`Θ_leaf_noOOF`,
  unconditional for non-nesting calls) now closed.** REMAINING for the fully nested
  headline: extend the per-iteration gas descent to CALL/CREATE iterations + the final
  mutual `fuel` induction threaded with a **super-linear depth-aware bound**
  `B (k+1) gas = (gas+1)·(B k gas + c) + 2` (the linear `4*(g+1)` AND the linear
  product `(1025−depth)·4·(gas+1)` are both insufficient — corrected in B2e). See
  B2e/B2d logs below.
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
- 2026-06-23 (B2e — step skeleton + X inner induction + precompiled arm + END-TO-END
  LEAF FRAME). Bare `lake build` GREEN; `#print axioms` on every new theorem reports
  only `[propext, (Classical.choice,) Quot.sound]` — no `sorryAx`, no custom axiom;
  zero `sorry`/`admit`/`axiom`/`native_decide` in source. All in
  `NestedEvmYul/NeverOutOfFuel.lean`.
  - **`step` skeleton — DONE** (`noOOF_step`). `step (f+1) … ≠ OutOfFuel` given each
    `call f …` is not OutOfFuel. CALL/CALLCODE/DELEGATECALL/STATICCALL → `call f` via a
    generic `noOOF_call_arm_body` (defeq coercion to the call-bind body, one lemma for
    all four); CREATE/CREATE2 are **unconditional** (they swallow `Lambda`'s error into
    a tuple — `dsimp only [step]` + `repeat' split at h`); the default arm → the new
    `noOOF_EvmYul_step` (the shared interpreter never OutOfFuels — full per-arm sweep
    mirroring `gas_EvmYul_step`, with `noOOF_*` combinator + inline helpers). 
  - **`X` inner loop-induction — DONE** (`X_loop_noncallcreate`). The genuinely-hard
    piece: GAS is the bottoming-out measure (every non-halting iter burns ≥1 via
    `X_iter_gas_lt`; `Z` never raises gas via the new `Z_ok_state`+`gas_sub_le`), so
    once `fuel > gas+1` the loop halts before fuel runs out. Induction on `fuel`,
    extracting `f = f'+1` so the per-instruction `step f'+1` is never the fuel-0
    OutOfFuel. Closed for a frame whose code never decodes to a CREATE/CALL opcode.
    Also added `Z_never_outOfFuel` and `X_outOfFuel_of` (the X propagation skeleton).
  - **Precompiled `Θ`-arm — DONE** (`Θ_precompiled_never_outOfFuel`). The brief's
    warning was real: `simp only [Θ]` deep-recurses on the enormous `.Precompiled` eq
    lemmas, and a naive `split` emits unprovable `pc = n → False` side-goals. Bespoke
    reduction: `dsimp only [Θ]` + keep-`hc`-in-scope `split at hc` (no revert) +
    `repeat' first | nomatch hc | split at hc`.
  - **END-TO-END LEAF FRAME — DONE, UNCONDITIONAL** (`Θ_leaf_noOOF`, `Ξ_leaf_noOOF`,
    `X_leaf_noOOF`). For a single **non-nesting** message call (Code with no CREATE/CALL
    opcode), `Θ (fuel+1) … ≠ OutOfFuel` whenever `gas + 2 < fuel`, with **no** hypotheses
    on sub-layers. Chain: `noOOF_step_default → X_loop_noncallcreate → X_leaf_noOOF →
    Ξ_outOfFuel_of_gas (gas-aware: X only runs on the fresh child at gas g) →
    Ξ_leaf_noOOF → Θ_outOfFuel_of → Θ_leaf_noOOF`. This is a complete, axiom-clean
    never-OutOfFuel headline for the non-nested fragment — the genuine bake-off
    deliverable for straight-line + intra-frame control flow.
  - **Headline `Θ_never_outOfFuel` (fully nested) — NOT yet closed; gap is precise.**
    The only missing piece is the **mutual descent** (a frame whose X-loop runs a
    CALL/CREATE). Two sub-obligations, both documented in-file (closing `/-! ## Status
    … -/`) and NOT faked:
    1. **Call-iteration gas descent.** `X_iter_gas_lt` is stated `¬ isCallCreate w`;
       extend it to call/create iterations (they also net-burn `≥ Cextra ≥ 1` since the
       child returns `g' ≤ Cgascap = cost₂ − Cextra`, from `Cgascap_le_gas` /
       `Ccallgas_le_gas_of_cover`). Effort comparable to `gas_EVM_step_default`.
    2. **Mutual `fuel` induction + depth-aware bound.** Strong induction on `fuel` over
       all six layers; the proved skeletons are the `fuel+1` steps; the IH discharges
       each descent.
  - **KEY CORRECTION to the prior `seedFuel` finding.** The depth-aware bound is
    **super-linear** in gas across depth, NOT the linear product `(1025−depth)·4·(gas+1)`
    the B2d note suggested. Reason: a frame's X-loop runs up to `gas` iterations and
    *each* may spawn a child needing its *own full* `B(childgas, depth+1)`, so
    `B gas depth ≥ gas·(c + B gas (depth+1))` ⇒ ~`(gas+1)^(1025−depth)`. The cleanest
    sound `B` is by recursion on the depth-countdown `k = 1025−depth`:
    `B 0 gas = gas+2`, `B (k+1) gas = (gas+1)·(B k gas + c) + 2` (recurrence holds
    definitionally; assembly arithmetic is a few `omega`/unfold). (The gas-telescoping
    route gives a linear `B = c·gas + c·1024` but needs the harder invariant.) The
    original `seedFuel = 4·(g+1)` and the linear product are both insufficient.
- 2026-06-22 (B2d, item 3 DONE + 4 propagation skeletons): Cross-layer gas/depth
  conservation closed, and four of the five recursive layers now have their
  inductive-step (`fuel+1`) OutOfFuel-propagation skeleton **fully proved**. Bare
  `lake build` GREEN; `#print axioms` on every new theorem reports only
  `[propext, (Classical.choice,) Quot.sound]` — no `sorryAx`, no custom axiom; zero
  `sorry`/`admit`/`axiom`/`native_decide` in source. All in
  `NestedEvmYul/NeverOutOfFuel.lean`.
  - **Item 3 (child gas ≤ parent gas) — DONE.**
    - `Cgascap_le_cap` (`Cgascap ≤ g`, the call's gas-stack cap, both branches).
    - `Ccallgas_le_gas_of_cover`: the gas a `CALL`-family frame forwards to its
      child (`Ccallgas = Cgascap (+ Gcallstipend when val≠0)`) is `≤` the parent's
      available gas **in the branch where the parent covers `Cextra`** — because the
      stipend `2300` is dominated by `Cxfer = Gcallvalue = 9000`, which the parent
      pays as part of `Cextra` exactly when `val ≠ 0`. (Proved by casing on the
      `Fin` value of `val`, which simultaneously decides the `Ccallgas` `⟨0⟩`-match
      and the `Cxfer` `!=`-guard; the `bne`/`Cxfer` evaluate by `rfl` per arm.)
    - `call_depth_bound`: the `call→Θ` recursion is gated by `Iₑ < 1024`, so the
      child depth `e = Iₑ+1 ≤ 1024`.
  - **Item 4 — propagation skeletons (4/5 layers DONE), final assembly NOT closed.**
    Each layer emits `.error .OutOfFuel` **directly** only at its `fuel = 0` arm
    (the proved base cases); at `fuel+1` it only *propagates*. Proved skeletons
    reduce `layer (fuel+1) … ≠ OutOfFuel` to the sub-layer it calls:
    - `Ξ_outOfFuel_of`: `Ξ(f+1)` ⇐ `X f` (the success post-processing never errors).
    - `Θ_outOfFuel_of`: `Θ(fuel+1)` on a **`Code`** call ⇐ `Ξ fuel` (the explicit
      `if e == .OutOfFuel then throw .OutOfFuel` re-throw; other `Ξ`-errors swallowed
      into `pure`).
    - `call_outOfFuel_of`: `call(f+1)` ⇐ `Θ f` (the balance/depth `if`-branch; the
      `else` and post-call assembly are pure `.ok`).
    - `Lambda_outOfFuel_of`: `Lambda(f+1)` (CREATE/CREATE2) ⇐ `Ξ f` (same re-throw
      shape as `Θ`'s Code arm; the leading `L_A` address lift only ever errors as
      `.StackUnderflow`).
    Tactic notes: `unfold Θ` fails (do-block equation-lemma gen), but
    `simp only [Θ, bind, Except.bind]` works for the `Code` arm; the `Ξ`/`Θ`/`Lambda`
    error arms use `by_cases err = OutOfFuel` + a `cases err` BEq-`false` lemma
    (`ExecutionException` has only derived `BEq`, no `LawfulBEq`). The local
    `MonadLift Option (Except …)` sends `none → .error .StackUnderflow`.
  - **REMAINING for the headline `Θ_never_outOfFuel` (documented in-file + here, NOT
    faked):**
    1. **`step` skeleton.** `step(f+1) cost (some (w,a)) s` ⇐ `call f` (CALL family,
       have `call_outOfFuel_of`) + `Lambda f` (CREATE family, have
       `Lambda_outOfFuel_of`) + `EvmYul.step` (default arm, never `OutOfFuel`: the
       shared interpreter mentions OutOfFuel **nowhere** (`grep` = 0), but a Lean
       proof still needs the per-arm sweep like `gas_EvmYul_step`, or to be
       parameterized over that clearly-true base fact). The routing itself is the
       `cases w` defeq-coercion from `gas_EVM_step_default`.
    2. **`X`-loop bound (the genuinely hard INNER induction).** `X(f+1)` halts (`.ok`)
       or recurses `X f` on a *gas-strictly-smaller* state (`X_iter_gas_lt`, PROVED).
       Concluding `X fuel … ≠ OutOfFuel` needs an inner induction on the loop-
       iteration count, bounded by gas (each non-halting iter burns ≥1 gas), nested
       inside the outer fuel induction: `fuel ≥ gas+1` covers a single frame's loop.
    3. **Precompiled `Θ`-arm** (non-recursive; never `OutOfFuel` — every numeric arm
       and the `_ => default = .ok default` fallthrough are `.ok`). Term-size-heavy:
       the `Θ.eq` lemmas for `.Precompiled` are enormous, and the literal-pattern
       `match pc with | 1 … | 10 …` makes `split` emit unprovable `pc = n → False`
       exhaustiveness side-goals. Needs a bespoke reduction, not `split`.
    4. **Final mutual `fuel` induction** (strong induction on `fuel` over the six-
       layer mutual statement). The skeletons above are the per-layer `fuel+1` steps;
       the IH at `fuel` discharges each hand-off PROVIDED the fuel bound is threaded.
  - **KEY DESIGN FINDING — `seedFuel` must be DEPTH-AWARE.** The current
    `seedFuel g = 4*(g+1)` is **insufficient** for the nested case. Reason: along a
    single root-to-leaf fuel path, gas is only **non-increasing** across a descent
    (child gas ≤ parent gas, item 3 — but NOT strictly smaller per descent), while
    fuel must also cover the `~4` hops × up-to-`1024` descents. Two sound fixes:
    (a) **depth-aware product bound** `B(gas,depth) = (1025 - depth) * 4*(gas+1)`
        (a frame at depth `e ≤ 1024` needs `≤ 4*(gas+1)` for its own X-loop+hops plus
        its child's `B(·,e+1)`; avoids gas-telescoping by bounding by the *product*
        `gas × remaining-depth`); or
    (b) prove **gas-telescoping** (`childgas ≤ parentgas − (parent's iters so far)`,
        so `Σ frame-iters ≤ root gas`) and use `B = 4*(gas) + 4*1024`. (a) is the
        lower-effort route. Either way the headline's `hfuel` hypothesis must be
        restated against the depth-aware bound (or the depth pinned at the top frame).
- 2026-06-22 (B2c, PARTIAL→measure assembly): The `Z→step→X` gas-decrement chain
  and the `X` measure descent are now **fully proved** (no `sorry`/`axiom`); bare
  `lake build` GREEN; `#print axioms` on every new theorem reports only
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom.
  All in `NestedEvmYul/NeverOutOfFuel.lean`.
  - **Item 1 (gas-decrement chain) — DONE.**
    - `gas_EvmYul_step`: the shared per-opcode interpreter `EvmYul.step` preserves
      `gasAvailable` on `.ok`. Proved by a per-opcode sweep over the grouped
      `Operation`: ~20 combinator gas lemmas (`gas_execBinOp`, `gas_binaryStateOp`,
      `gas_ternaryCopyOp`, the log ops, …) and ~12 inline-arm lemmas
      (`gas_dup`/`gas_swap`/`gas_inl_pop`/`gas_inl_mload`/`gas_inl_jump`/`…`/
      `gas_inl_selfdestruct`), each applied to a concrete arm **by definitional
      unfolding** (`exact gas_X _ _ _ h` — the `EvmYul.step <concrete-op>` reduces by
      defeq during unification). KEY: `simp only [EvmYul.step]` on the 140-arm `match`
      *times out* (`isDefEq` heartbeats), so the proof never re-elaborates the whole
      `match` — concrete-op defeq is the trick. The `CREATE`/`CALL` family is excluded
      (`¬ isCallCreate`): the shared step routes them to `_ => default = .ok default`,
      which is **not** gas-preserving, and the nested `EVM.step` special-cases them
      earlier so they never reach here. The big `SELFDESTRUCT` arm (nested EIP-6780
      `if`/account-map `match`es) is closed by peeling to each `replaceStackAndIncrPC`
      leaf (gas-free `accountMap`/`substate` rebuild).
    - `gas_EVM_step_default`: `EVM.step (f+1) cost (some (w,a)) s` on the default arm
      (`¬ isCallCreate w`) yields `s'.gasAvailable = s.gasAvailable - ofNat cost`.
    - `Z_ok_cost_le_gas`: `Z … = .ok (s', c) → c ≤ s'.gasAvailable.toNat ∧ c = C' s' w`.
      The `Except` `do`-inversion the prior run got stuck on is done by `generalize`-ing
      the heavy `memoryExpansionCost`/`C'` discriminants opaque, then `by_cases` +
      `rw [if_pos/if_neg]` on the two gas guards (avoiding `split`/`split_ifs`'
      discriminant-simp, which blows up on those terms), and peeling the remaining
      small validity `if`s.
  - **Item 2 (`X` measure descent) — DONE.** `X_iter_gas_lt`: a non-halting `X (f+1)`
    iteration (`Z` ok with cost `cost₂`, `step` ok on a non-call/create `w`, `H = none`)
    lands in a state with `s₂.gasAvailable.toNat < s₁.gasAvailable.toNat`. Assembled
    from `H_none_not_halt` + `step_invalid_error` (⇒ `runnable w`),
    `C'_pos_of_runnable` (`1 ≤ cost₂`), `Z_ok_cost_le_gas` (`cost₂ ≤ s₁.gas`),
    `gas_EVM_step_default` (the debit), and `gas_sub_lt` (`UInt256` subtraction of a
    positive non-underflowing cost strictly drops `.toNat` — proved via `Fin.sub_def`).
  - **Item 3 (child gas ≤ parent gas) — DOWN-PAYMENT.** `Cgascap_le_gas` +`L_le`: the
    gas a frame forwards (`Cgascap`) is `≤ μ.gasAvailable.toNat` (or capped at `g`).
    REMAINING: thread this through the `call`/`Θ`/`Ξ` arms — the `Ccallgas` top-up by
    `Gcallstipend`, the `depth e+1 ≤ 1024` cap, and the parent→child gas inequality
    across the descent (the genuinely-nested analogue of exp003's flat
    `gasFundsDescent`).
  - **Item 4 (final mutual induction) — NOT STARTED (documented).** The headline
    `Θ_never_outOfFuel` needs a MUTUAL well-founded induction over the five layers
    `X`/`Ξ`/`Θ`/`call`/`step` simultaneously (NOT a pending-stack measure — the nested
    recursion is genuinely mutual). Two viable spines:
    (a) `Nat.rec` on `fuel` with the five-layer mutual never-`OutOfFuel` statement
        (each layer's `0` case is the proved `X_zero`/…/`Θ_zero`; the `f+1` case uses
        `X_iter_gas_lt` for the `X` loop and the item-3 child-gas inequality to bound
        the child's fuel need by the parent's budget);
    (b) well-founded recursion on the lexicographic measure `(gas, depth)`.
    The precise remaining obligation: a lemma `gas+depth ≤ budget → layer … ≠
    .error .OutOfFuel`, proved by that mutual induction. The headline statement is
    written as a documented goal in the file (a doc comment, NOT a `sorry`ed theorem).
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
