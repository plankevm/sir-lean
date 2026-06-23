# HANDOFF — good morning, Eduardo

**Written overnight 2026-06-23; loop WOUND DOWN at the end (clean stop, nothing running).**
Full chronological record: `currentplan.md` (orchestration log). This is your resume surface.

---

## TL;DR — what happened overnight

Both proof/prototype tracks ran to clean, verified stopping points; **both are now blocked on
a decision only you can make**, so I wound down (deleted the heartbeat, no speculative work).

- **Track C (v2 redesign): 3 milestones landed, all axiom-clean, all verified by me.**
  The gas-free / observable / events / monotone-gas-oracle design is **validated end-to-end
  for the call-free fragment**, and §3.4's last open obligation ("gas monotonicity holds
  across calls") is now a **real hypothesis-free proof**. The next step (external-call events
  / general theorem) is **blocked on your returndata-model decision** (§7.5).
- **Track B (nested never-OutOfFuel): 5th partial — held for your steer.** Lots of sound
  brick-work landed, but the headline is still open and its final mutual induction isn't
  started. The *difficulty itself* is now a concrete bake-off finding.
- **Track A:** untouched (done + merged + reported).

## Nothing is running now

The 45-min heartbeat `f3ba5aed` has been **deleted** (wind-down). No background agents active.
Everything is committed; all worktrees clean (except your pre-existing scratch files on base).

## Overnight results (newest first — all VERIFIED by me, not self-reported)

- **✅ General `Runs`-level gas-monotonicity lemma — PROVED, hypothesis-free, axiom-clean**
  (`6adebb5`/`7af50a3`; `BytecodeLayer/Hoare/GasMonotone.lean`, on the `Spec.lean` surface).
  `Runs.gasAvailable_le` (gas never increases across any `Runs`, incl. `.call` nodes — the
  63/64 net-debit is `CallReturns.gas_le`, no side-condition). Confirmed
  `[propext, Classical.choice, Quot.sound]` myself. **This closes §3.4's "holds across calls"
  as a real proof.** Decision-free runway for Track C is now exhausted ⇒ wound down.
- **✅ C-v2 two-read monotonicity milestone** (`exp005-ir`, green 1133, axiom-clean).
  `LirLean/V2/Mono.lean`: the monotone-oracle law on a sticky-gas-guard; bytecode *discharges*
  monotonicity from exact gas accounting (no new gas theory). Law works as designed.
- **✅ C-v2 call-free prototype** (green 1132, axiom-clean, v1 untouched).
  `LirLean/V2/{Machine,Preserve}.lean`: gas-free IR machine + `gasRead` event + observable
  `lower_preserves_obs` (pc-free, gas-equality-free). The v2 shape is validated.
- **⏸️ B2h — 5th PARTIAL, Track B HELD** (`exp004-nested`, green, axiom-clean, tree clean).
  Proved the gas-monotonicity per-layer reductions. Remaining to headline: gas-mono assembly
  fixpoint + a precompiled-`Θ` brick, **and the never-OOF mutual induction (super-linear `B`)
  which is NOT STARTED.** No 6th grind launched (per rule).

## 🔴 Decisions awaiting YOU (in priority order)

1. **Track B — the bake-off call (top).** Headline still open after 5 iterations; the never-OOF
   mutual induction isn't started. Options:
   (a) **accept** the axiom-clean leaf headline + the brick library as B's deliverable and
   treat the asymmetry (flat: easy, unconditional, linear bound — nested: 5 iterations and
   counting, super-linear bound, two mutual inductions) as the **bake-off verdict** → move B
   to B3/Phase-2;
   (b) **scope** to CALL-only (drops CREATE);
   (c) **keep grinding** (diminishing returns);
   (d) **try a cleaner measure** first.
   *My read: (a). The difficulty IS the result.* (See report "Sharpening" + `currentplan.md`.)
2. **Track C — the returndata-model decision (`ir-design-v2.md §7.5`).** Unblocks the
   call-event step. (a) Drop the word from `IRHalt.returned` (match the empty-window lowering)
   or make the lowering RETURN it? (b) When revert enters, align `IRHalt`/`Observable.result`
   with the EVM `Outcome`. *Default I'd take for a first cut: value-free, empty
   calldata/returndata (mirrors v1 `workedCall`), revert deferred — then I can launch the
   call-event step + wiring `lower` into the witness.*
3. **Track C — smaller `§7` items:** `World` decoupling depth, simulation direction,
   `evalExpr` gas-trace threading. Defaults chosen in the doc; override any.

## What I deliberately did NOT do (and why)

- No 6th Track-B grind (4→5 partials; design-sensitive; needs your steer).
- Did not launch the "wire `lower` into the v2 witness" step — decision-free but grindy, and
  better done *together with* the call-event step once you've settled returndata (§7.5), so it
  comes out coherent rather than redone.
- No speculative refactors; no `exp005-ir`→base merge (kept C work on its branch; merge when
  v2 stabilizes — see below).

## To resume me in the morning

Re-read this file + `currentplan.md` orchestration log; `git worktree list` then
`git log --oneline` per worktree to see the commits. Then just tell me your calls on the
decisions above and I'll spin the next agents back up. (The heartbeat is already deleted —
nothing to clean up.)

## Where to look

- `EXPERIMENT-REPORT.md` (repo root) — results synthesis + the flat-vs-nested "Sharpening".
- `experiments/005_ir_lowering/docs/` on `exp005-ir` — `ir-design-v2.md` (the v2 plan, now with
  step-1/1b DONE + §3.4 fully proved), `gas-introspection-prior-art.md`, `track-c-review.md`.
- New Lean: `LirLean/V2/{Machine,Preserve,Mono}.lean` + `BytecodeLayer/Hoare/GasMonotone.lean`
  (all on `exp005-ir`).
- `currentplan.md` — full orchestration log + overnight protocol.
