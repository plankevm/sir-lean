import BytecodeLayer.Exec.Modellable
import BytecodeLayer.Exec.Invariants
import LirLean.Decode.BoundaryReach

/-!
# `ModellableStep` over lowered code

`runs_of_drive_ok` (`BytecodeLayer/Hoare/DriveRuns.lean`) reconstructs a halting `Runs fr₀ last` from a clean
`drive` outcome, under the **modellability** side condition
`∀ fr', Runs fr₀ fr' → ModellableStep fr'` — every reachable frame issues a *code* CALL or a halt:
no CREATE node, no precompile-CALL node (`Runs` models neither). `cleanHalts_of_runWithLog`
(`DriveSim.lean`) used to consume that universal as a **raw supplied hypothesis**.

This module replaces it with a **proved producing lemma**. The work splits along the two clauses
of `ModellableStep`:

* **Clause 1 — CREATE resumes successfully (`CreateResolves`).** The former "no CREATE at all"
  clause is **RETIRED**: `emitStmt .create` now emits a real `CREATE2` byte and CREATE is
  **modelled** by `Runs.create` (`runs_of_drive_ok`'s `.needsCreate` arm builds a `CreateReturns`
  node). What remains is the honest R4 residual `CreateResolves` — a `.needsCreate` whose init
  child terminates resumes successfully (the 63/64 retention guard, `Create.lean:200`, passing).
  This is NOT structural for `lower prog` (the guard can `throw .OutOfGas` on a `UInt64` overflow
  of the retained gas), so it is a genuine runtime side condition, vacuous for create-free
  programs. The OOG resume-fault delivers an exception halt through the drive stack — a control
  flow `Runs` does not resume — so `CreateResolves` rules it out on every reachable create frame.

* **Clause 2 — no precompile-CALL.** `beginCall cp = .inr _` holds **iff** `cp.codeSource =
  .Precompiled _`, and in a `.needsCall` produced by `callArm`, `cp.codeSource =
  toExecute accounts codeAddress` where `codeAddress = AccountAddress.ofUInt256 toAddress` is the
  CALL **target taken off the stack at runtime**. `toExecute … = .Precompiled _` iff the target
  address is a precompile (`1..10`). So clause 2 is **genuinely runtime-dependent**: a `lower prog`
  whose IR `Stmt.call` materialises a precompile address as its callee *would* produce a
  precompile-CALL. This is NOT a structural property of the lowering — it is a side condition on
  the program's reachable call targets, captured by the residual `CallsCode` and proven through
  `beginCall_isCode_of_codeSource_ne_precompiled`.

So the producing lemma `lower_modellable` consumes only the two honest residuals: `CreateResolves`
(no reachable CREATE OOG-faults on resume) and `CallsCode` (no reachable precompile-CALL).
`cleanHalts_of_runWithLog` then takes those in place of the raw `ModellableStep` universal —
satisfiable, precisely-scoped hypotheses (each *vacuously* true for any IR program with no
creates / no calls respectively, and for any program whose creates are ordinary and whose call
targets are ordinary contract accounts). See the module-level note in `DriveSim.lean`.

No `sorry`/`axiom`/`native_decide`. -/

namespace BytecodeLayer.Interpreter

open Evm
/-- **`AtReachableBoundary prog fr`** — the structural-reachability premise: `fr` runs
`lower prog` and its current pc is an instruction boundary reachable from the program start,
strictly before the program end and within the `UInt32` address space. This is *exactly* the
"reachable pc is a `lower prog` instruction boundary" invariant the no-CREATE clause needs
(`docs/uniform-spill-alloc-plan.md`); it is the residual whole-run reachability fact, strictly
weaker than the raw `NotCreate` it discharges (`notCreate_of_atReachableBoundary`). -/
def AtReachableBoundary (prog : Lir.Program) (fr : Frame) : Prop :=
  ∃ boundary : Nat,
    fr.exec.executionEnv.code = Lir.lower prog
    ∧ fr.exec.pc = UInt32.ofNat boundary
    ∧ Evm.ReachesBoundary (Lir.lower prog) 0 boundary
    ∧ boundary < (Lir.flatBytes prog).length
    ∧ boundary < 2 ^ 32


end BytecodeLayer.Interpreter

-- Build-enforced axiom-cleanliness guards for the `ModellableStep` producing chain: the create-
-- resolves residual (`CreateResolves`), the precompile-CALL characterization
-- (`beginCall_isCode_of_codeSource_ne_precompiled`), the per-frame reduction (`modellableStep_of`)
-- and the producing lemma (`lower_modellable`) all depend only on `[propext, Classical.choice,
-- Quot.sound]`.
