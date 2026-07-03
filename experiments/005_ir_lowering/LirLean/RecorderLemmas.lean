import LirLean.Spec.Recorder

/-!
# LirLean v2 — recorder lemmas (extracted from `Spec/Recorder.lean`)

The proof companions of the recording interpreter (`LirLean/Spec/Recorder.lean`,
the former `V2/RunLog.lean`): the SLOAD/CALL value-level bridges
(`sloadRecord_eq_sloadCost` / `realisedCall_eq_evmV2`) and the adequacy chain
(`driveLog_drive` → `runWithLog_drive` → `runWithLog_messageCall`). Extracted so
`Spec/Recorder.lean` stays a definitions-only spec-core file (Wave 3,
`docs/fleet-2026-07-02/reorg-legibility.md` §5 Step 3); the former direct importers
of `LirLean.V2.RunLog` (`SimTerm.lean`, `V2/Drive/SelfPresent.lean`) import this
module instead, so every downstream consumer reaches the lemmas exactly as before.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

/-- **The SLOAD value-level bridge** (parallel to `gasReadOf_gasFrame_eq_obs`). At an
SLOAD frame `g` whose stack-head is the bound key (`g.exec.stack.head? = some key`), the
recorded warmth-charge `sloadWarmthOf g` is exactly the value `SloadRealises` demands at
that frame: `sloadCost (accessedStorageKeys.contains (self, key))`. `simp`-clean (it is
`sloadWarmthOf`'s `some`-branch unfolded). So once the (deferred) alignment selects that
the SLOAD cursor's recorded charge is this site's `sloadWarmthOf`, the `sloadChg k =
sloadCost …` conjunct of `SloadRealises` is discharged at the cursor frame. -/
theorem sloadRecord_eq_sloadCost (g : Frame) {key : Word}
    (hkey : g.exec.stack.head? = some key) :
    sloadWarmthOf g
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key)) := by
  simp only [sloadWarmthOf, hkey]

/-- **`realisedCall` faithfulness.** When the log recorded a CALL (`log.calls = rec ::
_`), the realised call oracle *is* `evmV2CallOracle` at that record's `(result, pending)`
— the `resumeAfterCall` projection of `LirLean/V2/CallRealises.lean`. `rfl`-clean, so
`callRealises_bridge` ties its `(world', success)` bundle to the lowered CALL's
observable by construction (the call-side realisability). -/
theorem realisedCall_eq_evmV2 {log : RunLog} {rec : CallRecord} {tl : List CallRecord}
    (self : AccountAddress) (hc : log.calls = rec :: tl) :
    realisedCall log self = evmV2CallOracle rec.result rec.pending self := by
  simp only [realisedCall, callOracleOf, hc]

/-! ## Result adequacy: `driveLog` agrees with `drive`

`driveLog` mirrors `drive` branch-for-branch, so its result projection is exactly
`drive`'s result — the recording does not change *what* the machine computes, only
*what it remembers*. By induction on fuel, each branch reducing both sides one step
to a recursive call the IH closes (the recording splices are erased by `.map (·.1)`). -/

/-- **Result adequacy of `driveLog`.** The recording interpreter computes the same
result as `drive`: erasing the log (`Except.map (·.1)`) recovers `drive`'s output,
for *any* accumulator. Induction on fuel, one branch per `drive`/`driveLog`
transition — the two are definitionally the same control flow, the splices only
touch the (erased) accumulator. -/
theorem driveLog_drive :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord),
      (driveLog f stack state gasAcc sloadAcc callAcc).map (·.1) = drive f stack state := by
  intro f
  induction f with
  | zero => intro stack state gasAcc sloadAcc callAcc; rfl
  | succ n ih =>
    intro stack state gasAcc sloadAcc callAcc
    unfold driveLog drive
    -- Case on each scrutinee with `cases h : …` (substitutes *both* sides at once, so
    -- LHS and RHS never desync). Every branch reduces both sides to a recursive call
    -- the IH closes, or to the `.ok` leaf (`rfl`). The recording splices (the gas `if`,
    -- `recordCall`) only touch the erased accumulator, dropped by `Except.map (·.1)`.
    cases state with
    | inr result =>
      dsimp only
      cases stack with
      | nil => rfl
      | cons pending rest =>
        dsimp only
        cases h : pending.resume result with
        | ok parent => dsimp only [h]; exact ih rest (.inl parent) _ _ _
        | error e => dsimp only [h]; exact ih rest (.inr (endFrame pending.frame (.exception e))) _ _ _
    | inl current =>
      dsimp only
      cases h : stepFrame current with
      | next exec =>
        dsimp only [h]
        -- the nested recording `if`s (gas / sload / else) all reduce to the same recursive
        -- `driveLog` call modulo the (erased) accumulators; split every arm, close by `ih`.
        split <;> [skip; split] <;> exact ih stack (.inl { current with exec := exec }) _ _ _
      | halted halt => dsimp only [h]; exact ih stack (.inr (endFrame current halt)) _ _ _
      | needsCall params pending =>
        dsimp only [h]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; exact ih (.call pending :: stack) (.inl child) _ _ _
        | inr result => dsimp only [hbc]; exact ih (.call pending :: stack) (.inr (.call result)) _ _ _
      | needsCreate params pending =>
        dsimp only [h]
        exact ih (.create pending :: stack) (.inl (beginCreate params)) _ _ _

/-! ## Adequacy: `runWithLog` agrees with the verified semantics (`drive`/`messageCall`)

The recording interpreter's `observable` is exactly the value the **verified** engine
computes. Lifting `driveLog_drive` (result adequacy of the parallel recorder) through
`runWithLog`'s entry: a successful `runWithLog params fuel` pins both `drive fuel`'s and
`messageCall`'s output (the latter at the same fuel — `runWithLog` takes the fuel
explicitly rather than `seedFuel`; the two coincide once `fuel = seedFuel params.gas`,
see `runWithLog_messageCall`). This is the `Type`-interpreter↔relation bridge the
lessons doc calls *adequacy* — extract from the function, reason with the relation. -/

/-- **Adequacy of `runWithLog` against `drive`.** A successful recording run pins
`drive`'s result to the recorded `observable`: the recording does not change *what* the
verified engine computes. Directly from `driveLog_drive`. -/
theorem runWithLog_drive {params : CallParams} {fuel : ℕ} {log : RunLog}
    (h : runWithLog params fuel = some log) :
    ∃ frame, beginCall params = .inl frame
      ∧ drive fuel [] (.inl frame) = .ok log.observable := by
  unfold runWithLog at h
  cases hbc : beginCall params with
  | inr result => rw [hbc] at h; simp at h
  | inl frame =>
    rw [hbc] at h; dsimp only at h
    cases hdl : driveLog fuel [] (.inl frame) [] [] [] with
    | error e => rw [hdl] at h; simp at h
    | ok triple =>
      obtain ⟨r, gas, sloads, calls⟩ := triple
      rw [hdl] at h; simp only [Option.some.injEq] at h
      subst h
      refine ⟨frame, rfl, ?_⟩
      -- `drive fuel [] frame = (driveLog …).map (·.1) = (.ok (r,…)).map (·.1) = .ok r = observable`
      have hd := driveLog_drive fuel [] (.inl frame) [] [] []
      rw [hdl] at hd
      simpa only [Except.map] using hd.symm

/-- **Adequacy of `runWithLog` against `messageCall`.** When run at the seed fuel
`seedFuel params.gas` (the budget `messageCall` itself uses), a successful recording run
pins the verified top-level boundary `messageCall params` to the recorded `observable`'s
call result. The honest tie between the instrumented interpreter and the exported
semantics. -/
theorem runWithLog_messageCall {params : CallParams} {log : RunLog}
    (h : runWithLog params (seedFuel params.gas) = some log) :
    messageCall params = .ok log.observable.toCallResult := by
  obtain ⟨frame, hbc, hd⟩ := runWithLog_drive h
  rw [messageCall_eq_drive params frame hbc, hd]
  rfl

-- Build-enforced axiom-cleanliness guards: the recording interpreter's result
-- adequacy depends only on `[propext, Classical.choice, Quot.sound]`.
#print axioms driveLog_drive
#print axioms sloadRecord_eq_sloadCost
#print axioms realisedCall_eq_evmV2
#print axioms runWithLog_drive
#print axioms runWithLog_messageCall
#print axioms observe

end Lir.V2
