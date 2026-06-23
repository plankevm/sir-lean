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
- 2026-06-23 (G1 — precompiled `Θ`-gas arm DONE). `lake build NestedEvmYul.NeverOutOfFuel`
  GREEN; `#print axioms` on every new theorem ⊆ `[propext, Classical.choice, Quot.sound]`
  (`Θ_gas_le_precompiled` + `expmod_gas_le` use `Classical.choice`; the rest only
  `[propext, Quot.sound]`); zero `sorry`/`admit`/`axiom`/`native_decide` in the additions.
  - **The 10 per-contract `Ξ_*` gas bricks + the generic `gas_branch_le`** are PROVED. Each
    `Ξ_*` returns leftover gas `if g.toNat < gᵣ then ⟨0⟩ else g − .ofNat gᵣ` (the fallible
    ones — BN_ADD/BN_MUL/SNARKV/BLAKE2_F/PointEval — wrap the else in a `match` whose
    `.error` arm is also `⟨0⟩`); both `≤ g`. Simple shape (ECREC/SHA256/RIP160/ID/EXPMOD):
    `unfold; simp only []; rw [apply_ite (·.2.2.1)]; exact gas_branch_le _ _` — the
    `apply_ite` push avoids `split` grabbing EXPMOD's inner `adjusted_exp_length` `if`s (the
    B2h obstacle). Match shape: `by_cases` outer guard + `generalize` the result + `cases`.
  - **`Θ_gas_le_precompiled`** assembles them into the `.Precompiled pc` arm of Θ-gas-mono
    (non-recursive — NO child hypothesis). `simp only [Θ,…]` + `split at h` on the 10-way `pc`
    match + per-arm `injection; subst; exact *_gas_le` (fallthrough → `Nat.zero_le`).
  - **MODULE SPLIT + lakefile `-s` (IMPORTANT for A1).** The FFI-backed precompiles
    (`BN_MUL`/`SNARKV`/… have kernel-heavy `String`-pattern bodies via `totallySafePerformIO`)
    overflow the default *worker-thread* stack during kernel typechecking under `lake build`
    (`(kernel) deep recursion detected`) — yet check fine on the main thread (`lake env lean`).
    FIX: (a) the 10 bricks + `gas_branch_le` + `gas_sub_le` moved to siblings
    `NestedEvmYul/GasArith.lean` (owns `gas_sub_le`+`gas_branch_le`+a `match_proj_le` helper)
    and `NestedEvmYul/PrecompileGas.lean` (the 10 bricks), imported by `NeverOutOfFuel`;
    (b) lakefile `moreLeanArgs += ["-s","1048576"]` (1 GB thread stack). `gas_sub_le` now lives
    ONLY in `GasArith` (removed from `NeverOutOfFuel`; resolves via import). If A1 ever adds
    more FFI-precompile reasoning, keep it in `PrecompileGas` / preserve the `-s` flag.
  - **B2i plan check:** nothing here contradicts the LINEAR-PRODUCT bound. The precompile arm
    is purely a gas-monotonicity leaf (`leftover ≤ g`), orthogonal to the depth recurrence.
- 2026-06-23 (B2i — HEADLINE-CLOSE PLAN; decision: close full CALL+CREATE headline).
  **KEY DESIGN CORRECTION — the bound is LINEAR-PRODUCT, not super-linear.** B2e/B2f/B2g/B2h
  recorded the fuel bound as super-linear `B(g,d) ≈ (g+1)^(1025−d)`, on the premise that "a
  frame's X-loop runs up to `g` iterations and *each* spawns a child needing its own full
  `B(childgas,d+1)`" (so children's budgets accumulate). **That premise is wrong.** Reading
  `X` (`EvmYul/EVM/Semantics.lean:494`): `X (f+1)` runs `step f` then continues `X f` — BOTH
  use the literal `f`. Fuel is NOT in `State`; it is a pass-by-value structural counter. So
  after a child returns, the parent loop continues at exactly `f`, **independent of how much
  fuel the child subtree burned.** The `g` children a frame spawns therefore do NOT accumulate
  budgets; iteration `i` runs at fuel `F−i`, and the binding constraint is the single worst
  (last) iteration, not the sum. Recurrence is ADDITIVE: `F ≥ g + c + B(g,d+1)` with child gas
  ≤ parent gas (item 3) and `B` monotone in gas ⇒ closed form
      **`B(g,d) = (1025 − d) · (g + c)`** — linear in gas, with a depth FACTOR.
  Descent hop-chain confirmed `c ≈ 5`: `X(F)`→`step f`→`call (f-1)`→`Θ (f-2)`→`Ξ (f-3)`→child
  `X (f-4)` (`call (f+1)`→`Θ f` at `Semantics.lean:141`; `Θ`→`Ξ`/`Lambda`→`X`).
  **Bake-off implication:** nested costs a depth *factor* (+ ~6 brick iterations + two mutual
  inductions), NOT a super-linear blowup — still linear in gas. The EXPERIMENT-REPORT
  "Sharpening" super-linear claim must be corrected — but ONLY after the proof confirms the
  product bound actually closes (earn it, don't assert it).
  **ARCHITECTURE — ONE combined mutual induction on fuel.** The never-OOF strict descent
  (`call_result_gas_lt`) needs child gas-monotonicity, so fold both obligations into one strong
  induction on `fuel`: `P n := gasMono(n) ∧ neverOOF-under-B(n)` over step/call/Θ/Ξ/Lambda/X;
  the IH at `< n` supplies BOTH child gas-mono and child never-OOF.
  **Remaining work items (4):**
  - **G1** (brick, delegated): precompiled `Θ` arm of `Θ_gas_le` (`.Precompiled`, non-recursive;
    `gas_branch_le` + per-contract sweep, ~120 lines — recipe in the B2h entry below).
  - **N1** (brick, delegated): strict gas-descent on CALL/CREATE iterations — generalize
    `X_iter_gas_lt` to drop `¬isCallCreate`, via the already-proved `call_result_gas_lt` /
    `create*_result_gas_lt` (as CONDITIONAL bricks: child gas-mono stays a hypothesis the A1
    induction later discharges). Bottoms out the X-loop on every iteration.
  - **N2** (design, HELD by orchestrator): define `B(g,d) = (1025−d)·(g+c)`, prove its one-step
    recurrence + gas-monotonicity; part of A1's design.
  - **A1** (assembly, HELD by orchestrator — integration risk where the product bound is
    TESTED): the combined mutual induction tying G1+N1+N2; instantiate the headline at the
    initial depth (verify the 1024-vs-1025 off-by-one).
  G1+N1 dispatched to ONE background agent (sequential, same file → no concurrent-build race);
  N2+A1 held for orchestrator design + steer.
- 2026-06-23 (B2h — gas-monotonicity per-layer reductions; sub-task 1 of the headline
  assembly). `lake build NestedEvmYul.NeverOutOfFuel` GREEN; `#print axioms` on every new
  theorem ⊆ `[propext, Classical.choice, Quot.sound]` (`ofNat_le_of_le` only `[propext]`);
  zero `sorry`/`admit`/`axiom`/`native_decide` in source (grep-verified). All in
  `NestedEvmYul/NeverOutOfFuel.lean`.
  **The fully-nested headline `Θ_never_outOfFuel` is NOT closed this run.** What IS done:
  the entire gas-monotonicity per-layer reduction chain (the harder of the two mutual
  inductions' prerequisites — discharges `call_result_gas_le`/`create*`'s child hyps).
  - **CALL-family `step` gas-monotonicity (the B2f "tedious but mechanical" arg-matching,
    now PROVED):** `step_call_gas_le`, `step_callcode_gas_le`, `step_delegatecall_gas_le`,
    `step_staticcall_gas_le`. Each reduces `step (f+1) (C' s w) (w,_) s`'s CALL arm to
    `call f` and applies `call_result_gas_le`. Arg-matching: `pop7_stack_index` /
    `pop6_stack_index` (new) expose `μᵢ = s[i]!`; `accountAddr_roundtrip` (new) handles the
    `CALLCODE`/`DELEGATECALL` recipient round-trip `ofUInt256 (ofNat codeOwner) = codeOwner`
    (addresses are 160-bit, fit in UInt256 without truncation); `Ccallgas_le_Ccall` closes.
    `pop_of_liftM` (new) inverts the local `MonadLift Option (Except …)` stack-pop lift.
    KEY fuel bookkeeping: `step (f+1)` → `call f` = `call ((f-1)+1)`, so the child hyp is at
    `Θ (f-1)`; CREATE's `step (f+1)` → `Lambda f` (child hyp at `Lambda f`). Asymmetric but
    both `< f+1` — fine for strong induction.
  - **`step_gas_le`** — UNIFIED per-instruction bound dispatching all 7 arms (default →
    `step_default_gas_le` unconditional; CREATE/2 → `create*_result_gas_le`; CALL family →
    the four lemmas above). This is the `hstep` the X loop needs.
  - **`X_loop_gas_le'`** — strengthening of `X_loop_gas_le` whose per-step `hstep` may assume
    `cost = C' s' w` (`Z_ok_cost_le_gas.2` supplies it in the loop) — REQUIRED because the
    CALL/CREATE arms of `step_gas_le` need `cost = C'` for the `Ccallgas ≤ Ccall` matching.
  - **`Θ_gas_le_code`** — `Θ (n+1) (.Code code) g` leftover `≤ g`, given child `Ξ n` mono.
    Three result sources (swallowed-error `g'=⟨0⟩` / revert / success) all handled.
  - **`Ξ_gas_le`** — `Ξ (n+1) g` leftover `≤ g`, given child `X n` mono on the fresh child
    state (gas exactly `g`). `xiResultGas` (new) projects the Ξ/Θ leftover gas.
  - **`Lambda_gas_le`** — `Lambda (n+1) g` leftover `≤ g`, given child `Ξ n` mono. Success
    `g' = .ofNat (if F then 0 else gStarStar − codeDeposit)` bounded via `ite_zero_sub_le` +
    `ofNat_le_of_le` (both new). Handles the `L_A` lift + nested `liftM` reductions.
  - **REMAINING (precise, NOT faked; also in-file `## Status` REMAINING section):**
    1. **Gas-mono mutual induction — ASSEMBLY only.** Strong induction on `fuel` tying the
       above reductions into `gas_mono n : Θ_gas_le n ∧ Ξ_gas_le n ∧ X_gas_le n ∧
       Lambda_gas_le n ∧ step_gas_le n`, feeding the IH at `< n` to each child hyp. ONE
       brick missing: the **precompiled `Θ` arm** of `Θ_gas_le` (`.Precompiled pc`,
       non-recursive). Each of the 10 `Ξ_*` returns gas `⟨0⟩` or `g − .ofNat gᵣ` (≤ g via
       `gas_sub_le`); per-contract sweep. Scratch-verified for `Ξ_BN_ADD` (`unfold; by_cases
       g.toNat < 150; cases inner BN_ADD match`) and `Ξ_ID`. The OBSTACLE found: a uniform
       `unfold Ξ_X; split` does NOT fire cleanly — the big `let gᵣ` block makes `split`
       grab an inner `if` (e.g. EXPMOD's `adjusted_exp_length`) instead of the outer
       `g.toNat < gᵣ`, and `simp only []` over-unfolds gᵣ. FIX (to apply next): a generic
       `gas_branch_le : (if (g.toNat < gr) then (⟨0⟩:UInt256) else g − .ofNat gr).toNat ≤
       g.toNat` lemma + per-contract `unfold; exact gas_branch_le …` once the projection is
       reduced (or `conv` to the `.2.2.1` slot, avoiding gᵣ unfolding). `sub_word_le` is the
       else-branch closer. ~120 lines for all 10.
    2. **Never-`OutOfFuel` mutual induction with the depth-aware bound `B`.** NOT STARTED.
       `B 0 g = g+2`, `B (k+1) g = (g+1)*(B k g + c) + 2`, `k = 1025 − depth`. The
       propagation skeletons (`*_outOfFuel_of`) are the `fuel+1` steps; the STRICT bricks
       `call_result_gas_lt`/`create*_result_gas_lt` bottom out the X loop on CALL/CREATE
       iterations (generalising `X_loop_noncallcreate` to drop `hnc`, the strict cousin of
       `X_loop_gas_le'`); the IH at smaller fuel + larger depth discharges each descent once
       `B` is threaded. Instantiate the headline at the initial depth (verify 1024 vs 1025).
- 2026-06-23 (B2g — CREATE/CREATE2/`Lambda` gas-descent bricks; CREATE-side analog of
  B2f's CALL descent). `lake build NestedEvmYul.NeverOutOfFuel` GREEN; `#print axioms`
  on every new theorem ⊆ `[propext, Classical.choice, Quot.sound]`; zero
  `sorry`/`admit`/`axiom`/`native_decide` (grep-verified). All in
  `NestedEvmYul/NeverOutOfFuel.lean`.
  **VERDICT: CREATE IS TRACTABLE — ready for the mutual assembly.** The CREATE gas is
  monotone in exactly the expected way; no structural surprise blocks the bricks.
  - **Exact CREATE/CREATE2 gas shape (read from the vendored `EVM.step` arms).** Gas is
    first debited (`evmState.gasAvailable := evmState.gasAvailable - .ofNat gasCost`;
    call this debited word `gd`), then the child `Lambda f … (forwarded =
    .ofNat (L gd.toNat)) …` runs returning leftover `g'`, and the result state has
        `gasAvailable := .ofNat <| gd.toNat - L (gd.toNat) + g'.toNat`
    where `L n = n - n/64` (EVM.L, the 63/64 create cap; `L_le` already proved). This is
    a **`Nat`-shaped expression wrapped by a single `.ofNat`**, NOT CALL's wrapping
    `UInt256` sum — the paraphrase in B2f's report was correct. The forwarded gas is
    exactly `.ofNat (L gd.toNat)`, so the `Lambda`-mono brick is `g'.toNat ≤ L gd.toNat`.
    KEY SIMPLIFICATION found in the code: the inner branch's `evmState'` has its
    `gasAvailable` *overwritten* by the final `{ evmState' with … gasAvailable := … }`,
    so the result gas depends ONLY on `g'`, not on which of the three branches ran.
  - **`g'` across the three `(a, evmState', g', z, o)` branches** (all ≤ `L gd.toNat`):
    nonce-overflow → `g' = .ofNat (L gd.toNat)`; else (insufficient funds / depth=1024 /
    init-code > 49152) → same; `Lambda` branch → `g'` = `Lambda`'s 4th `.ok` component
    (reduced to the single child hypothesis), else `⟨0⟩`.
  - **Bricks PROVED (axiom-clean):**
    - `create_gas_arith` / `create_gas_arith_lt` — the `Nat` no-wrap core: from
      `g' ≤ L gd` and `gd ≤ G` (resp. `gd < G`, `G < size`) conclude
      `(.ofNat (gd − L gd + g')).toNat ≤ G` (resp. `< G`). The single `.ofNat` does not
      wrap because `gd − L gd + g' ≤ gd ≤ G < size`. (CREATE analog of `gas_add_sub_le/lt`.)
    - `create_result_gas_le` / `create_result_gas_lt` — a successful
      `step (f+1) gasCost (some (.CREATE, _)) ev` lands at gas `≤` (resp. `<`) `ev.gas`,
      GIVEN `gasCost ≤ ev.gas.toNat` (no-wrap debit), `1 ≤ gasCost` (strict only;
      supplied by `Gcreate = 32000`), and the child-`Lambda` mono hypothesis `hΛ`. The
      strict drop comes from the DEBIT (`gd < ev.gas`), not from `g' < L` (equality
      `g' = L` is allowed). Every branch (nonce-overflow / Lambda-ok / Lambda-fail /
      else) + the `OutOfGass` guard arm handled.
    - `create2_result_gas_le` / `create2_result_gas_lt` — identical over the `pop4` arm
      (CREATE2 differs only by popping the salt `μ₃` and computing `ζ`; gas accounting
      byte-for-byte the same).
    - `C'_create_pos` / `C'_create2_pos` — `C' s .CREATE/.CREATE2 ≥ Gcreate = 32000 ≥ 1`
      (discharges the strict `hpos`).
    - `pop3_stack_index` / `pop4_stack_index` — CREATE/CREATE2 arg-matching (pop 3 / 4),
      the create analog of `pop7_stack_index`; cheap, so included.
  - **What's reduced, not yet assembled:** the `hΛ` hypothesis (child `Lambda → Ξ → X`
    gas-monotonicity) is discharged by the same mutual induction that discharges B2f's
    `hΘ`. The CREATE bricks plug into that induction exactly like the CALL bricks. No
    new obstruction; the headline can keep BOTH CALL and CREATE in scope.
- 2026-06-23 (B2f — gas-monotonicity / CALL-descent bricks). Bare `lake build` GREEN;
  `#print axioms` on every new theorem reports only `[propext, (Classical.choice,)
  Quot.sound]`; zero `sorry`/`admit`/`axiom`/`native_decide` in source. All in
  `NestedEvmYul/NeverOutOfFuel.lean`. The CALL-iteration gas descent (prior
  sub-obligation 1) is now fully reduced to the child-`Θ` gas-monotonicity hypothesis,
  with every supporting brick PROVED:
  - **`Ccallgas_le_Ccall` / `Ccallgas_lt_Ccall`** — forwarded gas `≤`/`<` call total
    cost `Ccall = Cgascap + Cextra` (strict since `Cextra ≥ Caccess ≥ 1` for val=0 and
    `Cextra ≥ Cxfer = 9000 > 2300 = Gcallstipend` for val≠0).
  - **`gas_add_sub_le` / `gas_add_sub_lt`** — the UInt256 NO-WRAP core: the call-result
    gas `(ev.gas − ofNat cost) + g'` is a *wrapping* UInt256 sum; its `.toNat` is
    `≤`/`<` `ev.gas.toNat` given `g'.toNat ≤`/`< cost`. (This is the wraparound
    subtlety the prior notes had not surfaced — now resolved.)
  - **`call_result_gas_le` / `call_result_gas_lt`** — a successful `call (f+1) cost … ev`
    lands at gas `≤`/`<` `ev.gas`, given (i) `cost ≤ ev.gas`, (ii) `Ccallgas(call-args)
    ≤`/`< cost`, (iii) the child `Θ` returns `g'.toNat ≤ gg.toNat` (the gas-monotonicity
    hypothesis the mutual IH supplies). Both `g'` sources (child-`Θ` cover branch and
    `.ofNat callgas` else branch) handled.
  - **`Z_ok_code_pc`** — `Z` preserves `pc`/`code` (only debits gas), so the loop's
    decoded opcode is the opcode at the post-`Z` step-state.
  - **`X_loop_gas_le`** — the `X` loop never RAISES gas (`resultGas r ≤ s.gas`) given a
    per-instruction `hstep` (now phrased with the decoded-opcode equation so leaf frames
    recover non-call/create from `hnc`).
  - **`step_default_gas_le` + `X_leaf_gas_le`** — leaf-frame gas-monotonicity is
    UNCONDITIONAL (default-arm `hstep` via the strict cousin of `gas_EVM_step_default`).
  - **`pop7_stack_index`** — CALL-arm arg-matching: `pop7 s = some (tl,a,b,c,…) ⇒
    s[0]!=a ∧ s[1]!=b ∧ s[2]!=c`, reconciling the `Ccallgas` `call` forwards (from
    `pop7`) with the `Ccall` that `C'` charges (from `μₛ[i]!`).
  - **REMAINING for the headline (2 mutual inductions, precise & not faked; in-file
    `/-! ## Status … -/`):**
    1. **Gas-monotonicity mutual induction** (strong induction on `fuel` over
       step/call/Θ/Ξ/X/Lambda) — discharges `call_result_gas_le`'s `hΘ` and
       `X_loop_gas_le`'s `hstep`. Two sub-tasks inside: (a) CALL-arm arg-matching
       assembly — combine `pop7_stack_index` with "Z leaves stack untouched" to show
       `Ccallgas(call-args) ≤ Ccall(C'-args) = cost`; (b) CREATE/`Lambda` gas accounting
       — CREATE result gas is `.ofNat (ev.gas − L(ev.gas) + g')` (a *different* shape
       than CALL's UInt256 sum), `g' ≤ L(ev.gas)` from the child `Lambda → Ξ`; a `Nat`
       lemma (`L_le` already proved) closes it.
    2. **Never-OutOfFuel mutual induction with the depth-aware `B`** — the propagation
       skeletons (B2d/B2e) are the `fuel+1` steps; sub-task (1)'s `call_result_gas_lt`
       supplies the *strict* gas descent that bottoms out the `X` loop on CALL/CREATE
       iterations (generalising `X_loop_noncallcreate` to drop `hnc`); the IH at smaller
       fuel + larger depth discharges each descent once `B` is threaded. Bound:
       `B 0 gas = gas+2`, `B (k+1) gas = (gas+1)*(B k gas + c) + 2`, `k = 1025 − depth`
       (super-linear; the linear/linear-product seeds are insufficient).
    The CALL path is now essentially mechanical (all arithmetic + no-wrap + arg-match
    bricks proved); the unexamined-in-proof residue is the CREATE/Lambda gas shape and
    the actual mutual-induction wiring. Stopped here per the design-sensitivity guidance
    rather than risk a broken half-assembly.
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
