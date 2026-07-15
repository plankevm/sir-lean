import BytecodeLayer.Exec.Recorder

/-!
# Recorder lemmas

Value-level projection facts for recorded GAS, SLOAD, CALL, and CREATE events,
plus the adequacy chain from `driveLog` to `drive`.
-/

namespace BytecodeLayer.Exec.Recorder

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

/-- The `Word` a `GAS` opcode at (post-charge) frame `fr` reports: `ofUInt64` of the
frame's `gasAvailable`. -/
def gasReadOf (fr : Frame) : Word := UInt256.ofUInt64 fr.exec.gasAvailable

/-- The GAS-frames are threaded by `Runs` in program order: each is reachable from the
previous. -/
def FramesRun : List Frame → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Runs a b ∧ FramesRun (b :: rest)

/-- At an SLOAD frame whose stack head is `key`, the recorded warmth charge is
the EVM SLOAD cost for that key. -/
theorem sloadRecord_eq_sloadCost (g : Frame) {key : Word}
    (hkey : g.exec.stack.head? = some key) :
    sloadWarmthOf g
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key)) := by
  simp only [sloadWarmthOf, hkey]

/-- A nonempty recorded CALL list maps to its projected head followed by the
remaining projected stream. -/
theorem realisedCall_cons {log : RunLog} {rec : CallRecord} {tl : List CallRecord}
    (self : AccountAddress) (hc : log.calls = rec :: tl) :
    realisedCall log self
      = evmCallEntry rec.result rec.pending self :: callStreamOf tl self := by
  simp only [realisedCall, callStreamOf, hc, List.map_cons]

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
      (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord)
      (createAcc : List CreateRecord),
      (driveLog f stack state gasAcc sloadAcc callAcc createAcc).map (·.1) = drive f stack state := by
  intro f
  induction f with
  | zero => intro stack state gasAcc sloadAcc callAcc createAcc; rfl
  | succ n ih =>
    intro stack state gasAcc sloadAcc callAcc createAcc
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
        | ok parent => dsimp only [h]; exact ih rest (.inl parent) _ _ _ _
        | error e => dsimp only [h]; exact ih rest (.inr (endFrame pending.frame (.exception e))) _ _ _ _
    | inl current =>
      dsimp only
      cases h : stepFrame current with
      | next exec =>
        dsimp only [h]
        -- the nested recording `if`s (gas / sload / create2 / call / else) all reduce to the same
        -- recursive `driveLog` call modulo the (erased) accumulators; split every arm, close by `ih`.
        split <;> [skip; split <;> [skip; split <;> [skip; split]]] <;>
          exact ih stack (.inl { current with exec := exec }) _ _ _ _
      | halted halt => dsimp only [h]; exact ih stack (.inr (endFrame current halt)) _ _ _ _
      | needsCall params pending =>
        dsimp only [h]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; exact ih (.call pending :: stack) (.inl child) _ _ _ _
        | inr result => dsimp only [hbc]; exact ih (.call pending :: stack) (.inr (.call result)) _ _ _ _
      | needsCreate params pending =>
        dsimp only [h]
        exact ih (.create pending :: stack) (.inl (beginCreate params)) _ _ _ _

/-! ## Adequacy of `runWithLog` -/

/-- A successful recording run pins `drive`'s result to the recorded observable. -/
theorem runWithLog_drive {params : CallParams} {fuel : ℕ} {log : RunLog}
    (h : runWithLog params fuel = some log) :
    ∃ frame, beginCall params = .inl frame
      ∧ drive fuel [] (.inl frame) = .ok log.observable := by
  unfold runWithLog at h
  cases hbc : beginCall params with
  | inr result => rw [hbc] at h; simp at h
  | inl frame =>
    rw [hbc] at h; dsimp only at h
    cases hdl : driveLog fuel [] (.inl frame) [] [] [] [] with
    | error e => rw [hdl] at h; simp at h
    | ok triple =>
      obtain ⟨r, gas, sloads, calls, creates⟩ := triple
      rw [hdl] at h; simp only [Option.some.injEq] at h
      subst h
      refine ⟨frame, rfl, ?_⟩
      -- `drive fuel [] frame = (driveLog …).map (·.1) = (.ok (r,…)).map (·.1) = .ok r = observable`
      have hd := driveLog_drive fuel [] (.inl frame) [] [] [] []
      rw [hdl] at hd
      simpa only [Except.map] using hd.symm

/-- A nonempty recorded CREATE list maps to its projected head followed by the
remaining projected stream. -/
theorem realisedCreate_cons {log : RunLog} {rec : CreateRecord} {tl : List CreateRecord}
    (self : AccountAddress) (hc : log.creates = rec :: tl) :
    realisedCreate log self
      = evmCreateEntry rec.result rec.pending self :: createStreamOf tl self := by
  simp only [realisedCreate, createStreamOf, hc, List.map_cons]
