# Experiment 003 — handoff

Read `results.md` first. This file is the to-do list for the next run.

## Where the ladder stopped

```
A  Observables           ✅  CallResult.observe / Observables          (BytecodeLayer/Observables.lean)
B  run vocabulary        ✅  drive_step / drive_halt / two_le_seedFuel (BytecodeLayer/Drive.lean)
   step characterization ✅  stepFrame_stop / stepFrame_push1          (BytecodeLayer/Step.lean)
C  sequencing            ✅  exercised in capstone-1′ (PUSH1;STOP)      (BytecodeLayer/Capstone1.lean)
capstone-1               ✅  messageCall_stop_observe
capstone-1′              ✅  messageCall_pushStop_observe (gas floor 3≤gas, no ∃G₀)
─────────────────────────────────────────────────────────────────────
B′ descents              ❌  blocked — see "Obstruction 2"
C′ CALL rule             ❌  blocked — see "Obstruction 2"
D  fuel-sufficiency      —   not attempted (vacuous for M1; needed only with descents)
capstone-2 (∃G₀)         ❌  not reached
axiom purity             ❌  impossible without a foundation fix — see "Obstruction 1"
```

## Obstruction 1 — foundation `bv_decide` axiom (blocks axiom purity everywhere)

`Evm.messageCall`, `Evm.drive`, `Evm.beginCall`, `Evm.stepFrame`, `Evm.endFrame`
all already depend on `Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7`.
Source: `forks/leanevm/Evm/UInt256.lean:459` (`blt_iff_toBitVec_lt` proved by
`bv_decide`), used to build `Decidable (· < ·)`/`Decidable (· ≤ ·)` for
`UInt256` (lines 478–483), used throughout the semantics.

**Next step (to unblock):** reprove the `bv_decide` lemmas in
`Evm/UInt256.lean` (`blt_iff_toBitVec_lt` and siblings at lines 271, 276, 312,
424, 430, 436, 441, 464) without `bv_decide`/`ofReduceBool`. Plan that was
validated to the goal-shape stage:
1. Prove a generic `append_ult : (hi₁ ++ lo₁).ult (hi₂ ++ lo₂) =
   hi₁.ult hi₂ || (hi₁ == hi₂ && lo₁.ult lo₂)` for `BitVec`, via
   `BitVec.toNat_append` + `BitVec.ult ↔ decide (·.toNat < ·.toNat)` + `omega`.
   The one missing sub-lemma is the `Nat` bridge `a <<< n ||| b = a*2^n + b`
   for `b < 2^n` (mathlib name not found by `exact?`; prove from
   `Nat.lor`/`testBit` or `Nat.shiftLeft_add`).
2. Fold `append_ult` seven times to reduce `blt` (lexicographic over 8 limbs) to
   the 256-bit `ult`. The file already has axiom-free `toNat_add`/`toNat_mul`
   etc. as models for the style.
3. Re-run `#print axioms` on a downstream theorem to confirm the axiom is gone.

This is a self-contained UInt256 task; once done, **all of experiment 003 (and
any other leanevm proof) becomes axiom-clean for free.**

## Obstruction 2 — `callArm`/`createArm` are `private` (blocks M2)

`forks/leanevm/Evm/Semantics/System.lean:12,73` declare `callArm`/`createArm`
`private`. After `stepFrame` on `CALL` reduces through `dispatch`/`systemOp`/
`Stack.pop7`, the goal contains the inaccessible `Evm.callArm✝`; it cannot be
unfolded from the experiment.

**Next step (to unblock M2):**
1. Upstream change in leanevm: drop `private` on `callArm`/`createArm` (or add
   public `@[simp]` equation lemmas for the `.needsCall`/`.next`-on-fail
   branches). Re-run `lake exe conform 8` to confirm no regression.
2. Then build, in this package:
   - `stepFrame_call_needsCall` — CALL with a 7-element stack, `value = 0`,
     `depth < 1024`, enough gas ⇒ `.needsCall childParams pending`, exhibiting
     `childParams.codeSource = toExecute accounts codeAddress` (the **reflexive**
     child — model it as the real `messageCall`, never an oracle).
   - a `drive` descent lemma (the `.needsCall` arm of `drive`, analogous to
     `drive_step`/`drive_halt`).
   - `resumeAfterCall` characterisation: push `1` on child success, `0` on
     child OOG, advance pc.
   - capstone-2: caller = `PUSH1×7 ; CALL ; STOP` (or a stack-preloaded internal
     frame to avoid 7 PUSH lemmas), callee = `STOP` account. State the `∃G₀`:
     at modest `g` the `callGasCap` (`allButOneSixtyFourth`) binds, the callee
     OOGs, flag `0` is stored, caller STOPs — observables differ from the
     full-gas run, no `OutOfGas` at top level.
3. The 7-PUSH caller is the proof-cost risk. A `stepFrame_push1`-style lemma
   already exists; either iterate it 7× (mechanical) or prove the capstone about
   an internal frame whose stack is pre-loaded (internal lemmas may be
   low-level), then connect via the PUSH lemmas separately.

## Reusable patterns confirmed this run (carry forward)

- `decode <bytes> <pc> = some (op, imm)` **by `rfl`, as a named lemma**; inline
  it and `simp` won't fire under `getD`.
- Reduce `stepFrame` with: `unfold stepFrame; simp only [hdec];
  dsimp only [Option.getD]; rw [if_neg (by decide)]` (INVALID guard) `;
  rw [if_neg <overflow>]; dsimp only [dispatch, …]; unfold Evm.charge;
  rw [if_neg <gas>]; rfl`.
- Advance `drive` with `conv_lhs => unfold drive; dsimp only; rw [hstep]`
  (`drive_step`) — `conv_lhs` is essential or `unfold` rewrites the RHS too.
- Peel seeded fuel: `rw [show seedFuel p.gas = (… - k) + k by have := two_le_seedFuel …; omega]`.
- Stack-size side goals over a `(…push v)` of a `default.stack` record: discharge
  with `le_of_eq_of_le (by rfl) (by omega)` — `decide` fails (free vars in the
  surrounding record), but the `.size` is defeq to a literal.
- `set_option … in` must go **before** the `/-- … -/` docstring, not between it
  and the `theorem`.

## Build

`cd experiments/003_bytecode_layer && lake build` → green (1107 jobs).
`lakefile.lean` globs `.andSubmodules \`BytecodeLayer`.
