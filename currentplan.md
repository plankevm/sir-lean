# Current Plan — three-track parallel orchestration

**This is the master index. If you are a freshly-spawned Claude with no context,
READ THIS FIRST, then read the local `PLAN.md` of whichever track you are
resuming. Then verify reality against git (branches, worktrees, `lake build`)
before asserting any status below as fact — these checkboxes are intent, the
build is truth.**

Last updated: 2026-06-22. Owner: Eduardo. Base branch: `exp003-fuel-layer-cleanup`
(holds exp003 + the vendored `EVMLean` subtree; this file lives here and is
inherited by every track's worktree).

---

## The shape of the work

Three tracks run in parallel, each in its **own git worktree on its own branch**
off the base branch. Worktrees (not a shared checkout) so three background agents
can commit concurrently without racing the git index. Each branch merges back
into the base when its milestones are green. The base branch is the integration
trunk.

| Track | Goal | Worktree | Branch | Local plan |
|---|---|---|---|---|
| **A** | Calls as a `Runs` constructor; multi-call composition | `../evm-semantics-wt/runs-call` | `exp003-runs-call` | `experiments/003_bytecode_layer/PLAN.md` |
| **B** | Nested EVM core over EVMYulLean (Yul stripped); fuel↔gas; IR-facing surface | `../evm-semantics-wt/nested-evmyul` | `exp004-nested` | `experiments/004_nested_evmyul/PLAN.md` |
| **C** | High-level IR (storage arith + calls + branching) → EVM bytecode, lowering preserved | `../evm-semantics-wt/ir-lowering` | `exp005-ir` | `experiments/005_ir_lowering/PLAN.md` |

Paths are relative to the repo root `/Users/eduardo/workspace/evm-semantics`.

---

## Why these three, and how they interlock

The driving questions (the "why" behind the milestones):

1. **Multiple external calls.** exp003's sequencing rule (`messageCall_call_runs`)
   is *one frame → one call → one frame that halts*. It composes only with things
   that **eventually halt**, so we cannot yet reason about **intermediary** calls
   (a program that calls, continues, calls again, …). This is the headline defect.
   **Track A** attacks it by making `call` a constructor of `Runs` (so a multi-call
   program is one `Runs` value built by `.trans`). **Track C** is the real consumer
   /test: lowering a multi-call IR program will *prove or disprove* that A's rule
   composes. If A is insufficient, C's requirements drive A's redesign.
2. **Gas introspection.** Can we reason about `GAS`/gas-dependent branches, or at
   least prove introspection "doesn't interfere too much"? This **requires branching
   in the IR** — primarily explored in **Track C** (the IR must have branches), with
   the honesty constraint from project memory: keep theorems TRUE under gas
   introspection, earn gas-freedom as a *proved* result, never assume it.
3. **Fuel↔gas.** "Instantiate fuel ≥ (a function of) gas ⇒ never `OutOfFuel`," so
   IRs never see fuel/frames. Flat side (exp003) already has the unconditional
   `messageCall_never_outOfFuel`. **Track B** must re-establish this on the *nested*
   `Ξ/Θ` semantics.
4. **A higher-level semantics surface for IRs.** Both A (derived-nested over flat)
   and B (genuinely nested) aim to expose observables-only, fuel/frame-free results
   that the next IRs (Track C and beyond) consume. A and B are a deliberate
   **flat-vs-nested bake-off** for which foundation best serves IR reasoning.

Background (validated 2026-06-22, see `experiments/003_bytecode_layer/docs/verifereum-nested-call.md`):
philogy/`leanevm` (= vendored `EVMLean`, exp003's base) is **flat** (one `drive`
trampoline over a shared `List Pending`); NethermindEth/`EVMYulLean` is **nested**
(mutual `Θ/Ξ`, Yellow-Paper-faithful). Nested gives the classical procedure-call +
frame rules by construction; flat makes us earn each as a theorem. Track A recovers
nesting *as a theorem over flat*; Track B *adopts* the already-nested semantics.

---

## Milestones (intent — verify against build)

### Track A — `Runs.call` + multi-call composition  (worktree `runs-call`)
- [ ] **A1** Add a `call` constructor to `Runs` (bundles `CallReturns`). Decide the
  index: drop the now-vestigial `Nat` (fuel premises already gone) in favour of the
  non-`OutOfFuel`-reconciliation invariant. Reuse `drive_descend_eq`,
  `drive_fuel_mono`, `drive_eq_of_both_ne_oof` (all exist in exp003).
- [ ] **A2** Collapse the two boundary bridges (`messageCall_runs` +
  `messageCall_call_runs`) into one `messageCall_runs`; the old keystone becomes a
  use of it on a `Runs` containing `.call` nodes.
- [ ] **A3** Prove **multi-call composition**: a program with ≥2 external calls and
  code between them, reasoned about without each call having to halt the program.
  THE test of whether the constructor fixes the intermediary-call defect.
- [ ] **A4** Verdict + report: does this supersede `messageCall_call_runs`? Feed
  the composition API to Track C. Keep green, axiom-clean, no `sorry`.

### Track B — Nested EVM core over EVMYulLean  (worktree `nested-evmyul`)
- [x] **B1** DONE (`exp004-nested` @ `20ad4c1`, green 1033 jobs). Vendored
  EVMYulLean @ `066dc8b` (816K). **Finding: a clean Yul-ectomy is impossible** — the
  nested semantics is `τ`-polymorphic over `OperationType = Yul | EVM` and EVM state
  types carry `Yul.Ast.contractCode`, so the EVM path needs a minimal Yul fragment
  (`Yul/{Ast,State,StateOps,Exception,Wheels,PrimOps}` kept; `Yul/{Interpreter,
  MachineState,SizeLemmas,YulNotation}`+tests deleted). exp004 lakefile requires
  `evmyul from "EVMYulLean"`; toolchain v4.22.0; crypto FFI built fine.
- [ ] **B2** Fuel↔gas: never-`OutOfFuel` on nested `Ξ/Θ` when fuel ≥ gas-derived
  bound (the nested analogue of `messageCall_never_outOfFuel`).
- [ ] **B3** Nested external-call core: a `{P} Ξ(child) {Q}` triple + call-site/frame
  rule; demonstrate **multiple** calls compose naturally (contrast with A's effort).
- [ ] **B4** Expose an observables-only, fuel/frame-free semantics surface for IRs.

### Track C — IR + lowering + preservation  (worktree `ir-lowering`)
- [x] **C1** DONE (`exp005-ir` @ `505c83b`, green 1105 jobs). Fresh `LirLean` IR
  (NOT extending `SirLean`: UInt32, no CALL, no gas, dead SSA weight). First-class
  `sload/sstore/add/lt`, `Stmt.call`, `Term.branch`, `Expr.gas`. `docs/ir-design.md`
  + `sorry`-free compiling two-pass lowering skeleton.
- [ ] **C2** Lowering IR → EVM bytecode.
- [ ] **C3** Prove lowering preserves semantics, using exp003's reasoning layer
  (the `Runs`/boundary-bridge machinery — coordinate with Track A's API).
- [ ] **C4** Evaluate whether exp003's sequencing suffices for **multi-call** IR
  programs. If not, file the concrete requirement against Track A (this is the
  feedback edge A↔C).

---

## Dependencies & integration

- **A ↔ C** is the live feedback loop: C consumes A's sequencing API; C's multi-call
  lowering is A's acceptance test. C can start *now* (IR design + single-call
  lowering) without waiting on A3.
- **B** is independent; it informs the long-term foundation choice (flat-derived
  nesting vs. genuine nesting). Bake-off, not a blocker.
- **Gas introspection** (Q2) is explored in C once branches exist.
- Merge order when green: A into base first (it improves exp003's reusable layer),
  then C rebases onto it; B merges whenever B-milestones land.

---

## Resume protocol (for a context-cleared main Claude)

1. Read this file.
2. `git worktree list` and `git branch` — confirm the three worktrees/branches
   exist. If a worktree is missing, recreate: `git worktree add <path> <branch>`
   (branches persist even if worktrees are pruned).
3. For each track, read its local `PLAN.md` **progress log** (agents append there as
   they work) and run `lake build` in that worktree to see real status.
4. Re-spawn the per-track background agents from the briefs captured in each local
   `PLAN.md` ("Agent brief" section). Do NOT rely on old agent IDs — they are
   ephemeral; the briefs are the durable spawn instructions.
5. Update the checkboxes here only after the build confirms a milestone.

**Durability rules for agents (enforced in every brief):** append a dated entry to
your local `PLAN.md` progress log after each meaningful step; commit frequently on
your own branch with clear messages; never touch another track's files; if blocked,
write the blocker into PLAN.md before stopping.

## Orchestration log
- 2026-06-22: Plan created. exp003 vendored EVMLean + cleanup already committed on
  base. Three worktrees + branches created (`exp003-runs-call`, `exp004-nested`,
  `exp005-ir`), each with a committed local `PLAN.md`.
- 2026-06-22: **M1 background agents launched for all three tracks** (bounded: each
  does only its M1, appends to its PLAN.md progress log, commits on its branch,
  then stops + reports). On resume: do NOT look for these agents (ephemeral); read
  each PLAN.md log + `lake build`, then re-spawn from the PLAN.md "Agent brief".
- 2026-06-22: **B1 + C1 DONE, both green & committed** (B `20ad4c1`, C `505c83b`;
  the C agent finished its work but failed to commit — main loop committed it, closing
  the gap). Track A (`Runs.call`) still running. **KEY CROSS-TRACK FINDING (C, the C4
  question, surfaced early): exp003's call sequencing CANNOT express ≥2-call programs**
  — a CALL is `Signal.needsCall`, not a `StepsTo`/`Runs` link, so `Runs.trans` can't
  glue it; the bridge is hard-wired to exactly one `CallReturns`. ⇒ **Track A's
  `Runs.call` constructor is the confirmed critical path**; C's single-call lowering
  (C2) can proceed now, but multi-call (C3/C4) is blocked on A1–A3.
