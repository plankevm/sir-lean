# Experiment 003 — handoff

Read `results.md` first. Both milestones (M1 call-free spine, M2 external calls)
are **proven, green, and axiom-clean** (`[propext, Classical.choice, Quot.sound]`
on every export). The two foundation obstructions the earlier run reported were
resolved upstream in leanevm (`9cefe5b`). This file records the final ladder and
what a *next* experiment can build on.

## Where the ladder reached (all ✅)

```
A  Observables           ✅  CallResult.observe / .storageAt            (BytecodeLayer/Observables.lean)
B  run vocabulary        ✅  drive_step / drive_halt / two_le_seedFuel  (BytecodeLayer/Drive.lean)
B′ generalized run       ✅  driveG_step / _halt_callDeliver / _needsCall_code (BytecodeLayer/DriveGen.lean)
   step characterization ✅  stepFrame_stop/_push1/_push/_sstore/_sstore_oog   (BytecodeLayer/Step.lean)
C  sequencing            ✅  messageCall_seq_storageAt + toNat_subCharges (BytecodeLayer/Capstone3.lean)
C′ CALL rule             ✅  stepFrame_call (reflexive callChildParams)  (BytecodeLayer/Call.lean)
capstone-1               ✅  messageCall_stop_observe                    (BytecodeLayer/Capstone1.lean)
capstone-1′              ✅  messageCall_pushStop_observe (gas floor 3)
capstone (SSTORE)        ✅  messageCall_sstore_storageAt (floor 22106)
capstone (SEQUENCE)      ✅  messageCall_seq_storageAt (floor 44212)
─────────────────────────────────────────────────────────────────────
capstone-2 (∃G₀ CALL)    ✅  messageCall_call_storageAt                  (BytecodeLayer/CapstoneCall.lean)
∃G₀ counterexample       ✅  call_counterexample (g = 24000 ⇒ cell = 0)
reflexivity witness      ✅  messageCall_child_reflexive
axiom purity             ✅  every export = [propext, Classical.choice, Quot.sound]
```

`D` fuel-sufficiency was never needed as a separate brick: leanevm seeds enough
fuel from gas, and each capstone peels exactly the units it consumes from
`seedFuel g` via `two_le_seedFuel` + the `seedFuel g = (… - k) + k` rewrite, so
fuel is discharged once per proof and never appears in a statement.

## The two obstructions — RESOLVED (record of the fix)

Both were `forks/leanevm` foundation issues, fixed by one endorsed upstream
commit `9cefe5b` ("Remove bv_decide axiom from the execution path; expose
callArm/createArm"), conformance unchanged (2859/2859):

1. **`bv_decide` axiom** — `blt_iff_toBitVec_lt` (`Evm/UInt256.lean`) reproved by
   reducing both sides to `Nat` (`BitVec.lt_def` + `toNat_limbs`) and an
   8-limb-lexicographic `omega`, keeping `blt`/`toBitVec`/the `Decidable` instances
   and the fast runtime path unchanged. `#print axioms Evm.messageCall` is now
   standard. (Spec lemmas off the execution path still use `bv_decide` — harmless.)
2. **`private callArm`/`createArm`** (`Evm/Semantics/System.lean`) made
   non-`private`, so `stepFrame_call` can `unfold callArm`.

If a future leanevm bump regresses either, re-applying the same two changes
upstream restores axiom purity and M2 reducibility.

## Reusable patterns confirmed this run (carry forward)

- `decode <bytes> <pc> = some (op, imm)` **by `rfl`, as a named lemma**; inline it
  and `simp` won't fire under `getD`. The pc argument must be written **exactly as
  `incrPC` produces it** (e.g. `(0:UInt32) + UInt8.toUInt32 2 + …`), not reduced.
- Reduce `stepFrame` with: `unfold stepFrame; simp only [hdec];
  dsimp only [Option.getD]; rw [if_neg (by decide)]` (INVALID guard)
  `; rw [if_neg <overflow>]; dsimp only [dispatch, …]; unfold Evm.charge;
  rw [if_neg <gas>]; rfl`. For CALL also unfold `callArm`, kill the
  mem-expansion (`Cₘ a - Cₘ a = 0`), and discharge `callGasCap + callExtraCost ≤
  gasAvailable` then the depth/balance guard (`⟨UInt256.zero_le _, hdepth⟩`).
- Advance top-level `drive` with `drive_step`/`drive_halt`; advance a *suspended*
  run (parent on the pending stack) with `driveG_step`/`driveG_halt_callDeliver`/
  `driveG_needsCall_code`. The `conv_lhs => unfold drive` guard against rewriting
  the RHS is baked into the lemmas.
- Peel seeded fuel: `rw [show seedFuel g = (seedFuel g - k) + k by
  have := two_le_seedFuel g; unfold seedFuel; omega]` (k = total fuel the run
  consumes).
- **Gas threading for sequences**: `subCharges g cs` + `toNat_subCharges` reads the
  running `gasAvailable` after charges `cs` as `g.toNat - cs.sum` (given the sum
  fits), so every step's gas/stipend side-goal is a one-line `omega` against a
  fixed prefix sum — avoids the quadratic blow-up of nested `toNat_sub_ofNat`.
- The **63/64 cap** lives in `callGasCap`/`allButOneSixtyFourth`; bound it with
  `childGas_lb`/`childGas_ub` and let `omega` finish. `callExtraCost … = 2600` and
  `sstoreChargeOf … = 22100` reduce by `decide` once the world fields are pinned.
- Stack-size side goals over a `(…push v)` of a `default.stack`: discharge by
  reducing `.size` to a literal `Nat` and `omega` (free vars block `decide`).
- `set_option … in` must go **before** the `/-- … -/` docstring.
- Some call proofs need a large `maxHeartbeats` (e.g. `messageCall_call_storageAt`
  uses `800000000`). This is reduction depth, not a soundness concession.

## Where a next experiment could go

The bytecode reasoning layer is now demonstrated end-to-end against the real
`messageCall`, including the hard case (external calls with the `∃G₀` gas story),
all axiom-clean. Natural next rungs, each demand-driven:

- **Non-zero `value` / non-empty memory windows** in CALL (the value-free,
  zero-memory restriction in `stepFrame_call` was deliberate to isolate the 63/64
  content; lifting it adds the value-transfer balance arithmetic and
  mem-expansion charge).
- **`RETURN`/`REVERT` output**, so `CallResult.output` carries non-empty bytes and
  the caller can read returndata.
- **Nested calls / depth**, exercising `driveG_*` with a deeper pending stack.
- **A source IR → bytecode lowering** with these capstones as the target-side
  obligations (the original bytecode-first goal); the export shape (observables at
  the messageCall boundary, fuel/frame-free) is exactly what a lowering soundness
  theorem should land in.

## Build

`cd experiments/003_bytecode_layer && lake build` → green (1111 jobs; two cosmetic
unused-simp-arg linter warnings). `lakefile.lean` globs `.andSubmodules
`BytecodeLayer`.
