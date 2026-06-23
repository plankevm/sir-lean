# HANDOFF — good morning, Eduardo

**Written:** 2026-06-23 night (before you slept). **Kept current by the overnight loop.**
This is your resume surface. For the full chronological record see `currentplan.md`
(orchestration log + the "2026-06-23 (NIGHT)" overnight protocol).

---

## TL;DR state

- **Track A** (flat reasoning layer): DONE, merged to base, reported. No overnight work.
- **Track C** (IR→bytecode lowering): v1 `wc_preserves` DONE (hypothesis-free, axiom-clean),
  merged, report refreshed. A **v2 redesign is planned** (gas/pc-free IR, calls-as-events,
  observable preservation, monotone gas oracle) — `docs/ir-design-v2.md` on `exp005-ir`.
- **Track B** (nested EVM never-OutOfFuel): non-nesting leaf headline CLOSED; all CALL+CREATE
  gas-descent bricks proved; the **fully-nested headline `Θ_never_outOfFuel` was in its final
  assembly run (B2h) when you slept** (4 prior partials).

## Currently running (live)

| Agent | Track | Goal |
|---|---|---|
| **C-v2 monotonicity** | C / `exp005-ir` | First two-read example validating the monotone gas-oracle law (§3.4) |

*(Track B is HELD — no agent running; awaiting your steer, see Open decisions.)*

## Overnight results (newest first — loop appends as things land)

- **✅ C-v2 call-free prototype DONE & verified** (`exp005-ir`, build green 1132,
  axiom-clean, v1 untouched). `LirLean/V2/{Machine,Preserve}.lean`: gas-free IR machine +
  `gasRead` event + observable `lower_preserves_obs` (pc-free, gas-equality-free). **The v2
  shape is validated.** Surfaced open decisions for you (see "Open decisions" below).
  → Launched the **two-read monotonicity** milestone; **HELD** the call-event step pending
  your §7.5 returndata decision.
- **⏸️ B2h DONE & verified — 5th PARTIAL, headline still open; Track B HELD** (`exp004-nested`,
  build green, axiom-clean, tree clean). Proved the gas-monotonicity per-layer reductions
  (the novel structural work). Remaining to the headline: the gas-mono assembly fixpoint + a
  precompiled-`Θ` brick, and the never-OOF mutual induction (super-linear `B`) which is **NOT
  STARTED**. Per the overnight rule I did **not** launch a 6th grind — **needs your steer**
  (see Open decisions). The 5-iteration struggle is itself a bake-off finding (see report).

## Decision rules the loop is following

1. **Verify everything** (build green + `#print axioms` clean + grep `sorry`/`native_decide`)
   — never trust agent self-reports.
2. **C-v2 prototype positive** → launch step-2 (call-events + first two-read monotonicity
   example). **Friction** → document + hold (don't build on a flawed base).
3. **B2h closes headline** → merge B→base, mark B2 ✅, spawn Track B review report, refresh
   master report. **B2h partial (5th)** → verify + document the gap, **STOP** (no 6th
   autonomous grind — needs your steer).
4. No speculative refactors. No exp005-ir→base merge while the C-v2 prototype is mid-commit.

## Open decisions awaiting YOU (review in the morning)

- **🔴 Track B (TOP decision — B2h returned the 5th partial; track is held).** The nested
  headline `Θ_never_outOfFuel` is still open and the never-OOF mutual induction is *not even
  started*. Pick one:
  (a) **accept** the axiom-clean leaf headline + the large gas-descent/monotonicity brick
  library as Track B's deliverable, and treat the asymmetry (flat = easy/unconditional/linear;
  nested = 5 iterations and counting) as the bake-off verdict → move B to B3/Phase-2;
  (b) **scope** the headline to CALL-only (drops CREATE; precompile brick still needed);
  (c) **keep grinding** (6th+ iteration — diminishing returns, design-sensitive);
  (d) **try a cleaner measure** for the two mutual inductions before more grinding.
  My read: (a) is the honest high-value call — the *difficulty itself* is the result — but
  it's your bake-off to call. (See `currentplan.md` Track-B entry + the report's "Sharpening".)
- **C-v2 open decisions** (`ir-design-v2.md §7`): `World` decoupling depth, simulation
  direction, calldata/value generality, revert-as-observable. Defaults chosen; override any.
- **Gas monotonicity** (`ir-design-v2.md §3.4`): confirm promoting the monotone-oracle law
  into the first concrete two-read example, once the prototype validates the event shape.

## Where to look

- `EXPERIMENT-REPORT.md` (repo root) — results synthesis, entry point.
- `experiments/005_ir_lowering/docs/` on `exp005-ir` — `ir-design-v2.md`,
  `gas-introspection-prior-art.md`, refreshed `track-c-review.md`.
- `currentplan.md` — full orchestration log.

## How to resume me

Re-read this file + `currentplan.md`, then `git log --oneline` across the worktrees
(`git worktree list`) to see what landed. **A 45-min cron heartbeat `f3ba5aed` is running**
to keep the loop alive — if it's still active when you're back, tell me to `CronDelete
f3ba5aed` (or it auto-expires in 7 days; it's session-only and dies if Claude exits).
