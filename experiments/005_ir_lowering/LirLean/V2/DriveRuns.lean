import BytecodeLayer.Hoare.CallSequence

/-!
# `drive → Runs`: reconstruct a halting `Runs` from a clean-terminating top-level `drive`

The cyclic-CFG forward simulation (`V2/DriveSim.lean`) conditions on the entry frame's
`CleanHalts fr₀` — `∃ last halt, Runs fr₀ last ∧ stepFrame last = .halted halt`. The honest
scope hypothesis it is *derived* from is the **clean-halt outcome** of the recording interpreter:
`runWithLog params (seedFuel params.gas) = some log`, which (`runWithLog_drive`) pins
`drive (seedFuel params.gas) [] (running fr₀) = .ok log.observable`.

The existing direction (`CallSequence.lean`) is `Runs → drive` (`Runs.drive_reconcile`,
`messageCall_runs`). This module proves the **reverse**: a top-level `drive` that terminates
cleanly (`.ok`) **with no CREATE reached** reconstructs a halting `Runs` to the result's halt
frame. `Runs` carries returning external CALLs as black-box `CallReturns` nodes but has **no**
CREATE counterpart, so the reconstruction carries a `NoCreate` side condition (the IR lowering
emits no CREATE, so it is benign for the IR scope — discharged structurally for `lower prog`).

## The construction

* **`drive_descend_lt`** — the *bounded* CALL-boundary descent: a child sub-run that drains to
  `.ok res` resumes the parent at a fuel **strictly below** the parent's (`< f`). This is the
  bound `drive_descend_eq` leaves existential; it is what makes the reverse recursion well-founded
  (the resumed run is at strictly less fuel, so strong induction on fuel applies).
* **`NoCreate`** — the frame never issues a CREATE that begins as a frame on any reachable
  configuration of its run. Phrased as a property of the `drive` configuration; the only place it
  is consumed is the `.needsCreate` arm, which `Runs` cannot model.
* **`runs_of_drive_ok`** — the reverse construction. By strong induction on the top-level fuel,
  case on `stepFrame fr`: `.halted` is the base (`Runs.refl`); `.next` prepends a `Runs.step`;
  `.needsCall` (child = Code) extracts the child's black-box terminating sub-run, builds the
  `CallReturns` node, and recurses at the strictly-smaller resumed fuel (`drive_descend_lt`);
  `.needsCreate` is excluded by `NoCreate`.

No `sorry`/`axiom`/`native_decide`. Imports only the exp003 bytecode layer.
-/

namespace BytecodeLayer.Interpreter

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare

/-! ## The bounded descent equation -/

/-- **Bounded stack-append framing.** As `drive_append_framing`, but the residual fuel `j` is
**strictly below** the input fuel `f` whenever the bottom stack is non-empty: the splice consumes
at least the one fuel unit that delivers the drained child's `.inr res` to the bottom segment. By
induction on `f` following `drive`'s recursion — the terminal `.inr`/empty-`top` arm returns the
leftover fuel `n` with `n + 1 = f`, so `n < f`. -/
theorem drive_append_framing_lt :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∀ (bot : List Pending),
        ∃ j, j + 1 ≤ f ∧ drive f (top ++ bot) st = drive (j + 1) bot (finished res) := by
  intro f
  induction f with
  | zero => intro top st res h bot; simp [drive] at h
  | succ n ih =>
    intro top st res h bot
    unfold drive at h ⊢
    cases st with
    | inr result =>
      cases top with
      | nil =>
        dsimp only at h ⊢
        cases h
        exact ⟨n, by omega, rfl⟩
      | cons pending rest =>
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih rest (.inl parent) res h bot
          exact ⟨j, by omega, hj⟩
        | error e =>
          rw [hres] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih rest (.inr (endFrame pending.frame (.exception e))) res h bot
          exact ⟨j, by omega, hj⟩
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h; dsimp only at h ⊢
        obtain ⟨j, hjlt, hj⟩ := ih top (.inl { current with exec := exec }) res h bot
        exact ⟨j, by omega, hj⟩
      | halted halt =>
        rw [hstep] at h; dsimp only at h ⊢
        obtain ⟨j, hjlt, hj⟩ := ih top (.inr (endFrame current halt)) res h bot
        exact ⟨j, by omega, hj⟩
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih (.call pending :: top) (.inl child) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩
        | inr result =>
          rw [hbc] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih (.call pending :: top) (.inr (.call result)) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        cases hbcr : beginCreate params with
        | ok child =>
          rw [hbcr] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih (.create pending :: top) (.inl child) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩
        | error e =>
          rw [hbcr] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih (.create pending :: top) (.inr (.create _)) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩

/-- **Bounded CALL-boundary descent.** As `drive_descend_eq`, but the resumed-parent run is at a
fuel `j` **strictly below** the parent's descent fuel `f`. The strict bound (from the non-empty
bottom segment `.call pd :: ps` in `drive_append_framing_lt`) is what makes the reverse `drive →
Runs` recursion well-founded: the resumed run recurses at `j < f`. -/
theorem drive_descend_lt (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCall) (ps : List Pending)
    (h : drive f [] (running child) = .ok res) :
    ∃ j, j < f ∧ drive f (.call pd :: ps) (running child)
      = drive j ps (running (resumeAfterCall res.toCallResult pd)) := by
  obtain ⟨j, hjlt, hj⟩ := drive_append_framing_lt f [] (.inl child) res h (.call pd :: ps)
  rw [List.nil_append] at hj
  -- peel the single `.call` resume of `drive (j+1) (.call pd :: ps) (.inr res)`.
  refine ⟨j, by omega, ?_⟩
  rw [hj]
  conv_lhs => unfold drive
  dsimp only [Pending.resume]

/-! ## The `NoCreate` side condition

`Runs` models opcode steps (`Runs.step`) and returning external CALLs (`Runs.call`/`CallReturns`)
but has **no** CREATE node. So the reverse construction holds only when no CREATE that begins as a
frame is reached. We phrase the side condition as the **per-frame** fact that no frame reachable
on the (already-built) `Runs` prefix issues a CREATE step, threaded as the recursion descends.
For a single-contract IR run (`lower prog` emits CALL but never CREATE) it is discharged
structurally; here it is the honest scope marker on the reverse direction. -/

/-- **A frame's step is `Runs`-modellable.** `stepFrame fr` is either a non-halting step
(`.next`), a halt (`.halted`), or a **code** CALL that begins as a frame (`.needsCall cp _` with
`beginCall cp = .inl _`). It is never a `.needsCreate`, and never a `.needsCall` resolving to a
precompile/immediate (`.inr`). These are exactly the configurations `Runs` models (`Runs.step` /
`Runs.refl` / `Runs.call`); CREATE and precompile-CALL have no `Runs` node. The IR lowering
(`lower prog`) only ever issues code CALLs, so this is discharged structurally for the IR scope. -/
def ModellableStep (fr : Frame) : Prop :=
  (∀ cp pending, stepFrame fr ≠ .needsCreate cp pending)
  ∧ (∀ cp pending result, stepFrame fr = .needsCall cp pending → beginCall cp ≠ .inr result)

/-- **`drive` only errors with `OutOfFuel`.** Every `.error` outcome of `drive` is
`.OutOfFuel`: a halting frame produces a `.ok (endFrame …)` result (exceptions are folded into the
`FrameResult` via `endFrame`, not raised), so the sole `.error` leaf is the `fuel = 0` budget
exhaustion. By induction on fuel following `drive`'s recursion. -/
theorem drive_error_oof :
    ∀ (f : ℕ) (stack : List Pending) (st : Frame ⊕ FrameResult) (e : ExecutionException),
      drive f stack st = .error e → e = .OutOfFuel := by
  intro f
  induction f with
  | zero => intro stack st e h; simp only [drive] at h; exact (Except.error.injEq _ _ |>.mp h).symm
  | succ n ih =>
    intro stack st e h
    unfold drive at h
    cases st with
    | inr result =>
      cases stack with
      | nil => simp at h
      | cons pending rest =>
        dsimp only at h
        cases hres : pending.resume result with
        | ok parent => rw [hres] at h; dsimp only at h; exact ih rest (.inl parent) e h
        | error ex =>
          rw [hres] at h; dsimp only at h
          exact ih rest (.inr (endFrame pending.frame (.exception ex))) e h
    | inl current =>
      dsimp only at h
      cases hstep : stepFrame current with
      | next exec => rw [hstep] at h; dsimp only at h; exact ih stack (.inl { current with exec := exec }) e h
      | halted halt => rw [hstep] at h; dsimp only at h; exact ih stack (.inr (endFrame current halt)) e h
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h
        cases hbc : beginCall params with
        | inl child => rw [hbc] at h; dsimp only at h; exact ih (.call pending :: stack) (.inl child) e h
        | inr result => rw [hbc] at h; dsimp only at h; exact ih (.call pending :: stack) (.inr (.call result)) e h
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h
        cases hbcr : beginCreate params with
        | ok child => rw [hbcr] at h; dsimp only at h; exact ih (.create pending :: stack) (.inl child) e h
        | error ex => rw [hbcr] at h; dsimp only at h; exact ih (.create pending :: stack) (.inr (.create _)) e h

/-! ## Child-run extraction

A child CALL's standalone run terminates at *its own* seed fuel (`messageCall_never_outOfFuel`),
so it has a definite result there — the datum `CallReturns` records. -/

/-- **A code child terminates standalone.** When a CALL begins as a code child
(`beginCall cp = .inl child`), the child's standalone seed-fuel run never runs out of fuel
(`messageCall_never_outOfFuel`), so it returns a definite `.ok childRes`. -/
theorem child_terminates {cp : CallParams} {child : Frame}
    (hbc : beginCall cp = .inl child) :
    ∃ childRes, drive (seedFuel cp.gas) [] (running child) = .ok childRes := by
  have hne : drive (seedFuel cp.gas) [] (running child) ≠ .error .OutOfFuel := by
    intro hcontra
    apply messageCall_never_outOfFuel cp
    rw [messageCall_eq_drive cp child hbc, hcontra]; rfl
  cases hd : drive (seedFuel cp.gas) [] (running child) with
  | error e =>
    rw [drive_error_oof _ _ _ e hd] at hd; exact absurd hd hne
  | ok childRes => exact ⟨childRes, rfl⟩

/-- **Standalone OOF propagates to the framed run.** If the standalone child run runs out of fuel
at fuel `f` (`drive f [] (running child) = .error .OutOfFuel`), then so does the framed run with an
inert bottom stack appended (`drive f bot (running child)`). The bottom segment is inert until the
child drains to `[]`, so the child consumes the same fuel either way; running out standalone means
running out framed. By induction on `f` mirroring `drive`'s recursion (the `.inr`/empty-`top`
terminal arm cannot fire — it returns `.ok`, not `OutOfFuel`). -/
theorem framed_oof_of_standalone_oof :
    ∀ (f : ℕ) (st : Frame ⊕ FrameResult) (top bot : List Pending),
      drive f top st = .error .OutOfFuel →
      drive f (top ++ bot) st = .error .OutOfFuel := by
  intro f
  induction f with
  | zero => intro st top bot _; rfl
  | succ n ih =>
    intro st top bot h
    unfold drive at h ⊢
    cases st with
    | inr result =>
      cases top with
      | nil => dsimp only at h; exact absurd h (by nofun)
      | cons pending rest =>
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent => simp only [hres] at h ⊢; exact ih (.inl parent) rest bot h
        | error e =>
          simp only [hres] at h ⊢
          exact ih (.inr (endFrame pending.frame (.exception e))) rest bot h
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec => simp only [hstep] at h ⊢; exact ih (.inl { current with exec := exec }) top bot h
      | halted halt => simp only [hstep] at h ⊢; exact ih (.inr (endFrame current halt)) top bot h
      | needsCall params pending =>
        simp only [hstep] at h ⊢
        cases hbc : beginCall params with
        | inl child =>
          simp only [hbc] at h ⊢
          have := ih (.inl child) (.call pending :: top) bot h
          rwa [List.cons_append] at this
        | inr result =>
          simp only [hbc] at h ⊢
          have := ih (.inr (.call result)) (.call pending :: top) bot h
          rwa [List.cons_append] at this
      | needsCreate params pending =>
        simp only [hstep] at h ⊢
        cases hbcr : beginCreate params with
        | ok child =>
          simp only [hbcr] at h ⊢
          have := ih (.inl child) (.create pending :: top) bot h
          rwa [List.cons_append] at this
        | error e =>
          simp only [hbcr] at h ⊢
          have := ih (.inr (.create _)) (.create pending :: top) bot h
          rwa [List.cons_append] at this

/-- **Framed non-OOF gives standalone non-OOF.** Contrapositive of
`framed_oof_of_standalone_oof` at `top := []`: a framed child run that does not run out of fuel
witnesses that the standalone child run does not either (it drained the child within budget). -/
theorem child_ne_oof_of_framed (f : ℕ) (child : Frame) (pending : PendingCall) (ps : List Pending)
    (h : drive f (.call pending :: ps) (running child) ≠ .error .OutOfFuel) :
    drive f [] (running child) ≠ .error .OutOfFuel := by
  intro hcontra
  exact h (by have := framed_oof_of_standalone_oof f (running child) [] (.call pending :: ps) hcontra
              rwa [List.nil_append] at this)

/-! ## The reverse construction `runs_of_drive_ok`

The reverse `drive → Runs`. Two reduction facts are proved inline (no top-level `.halted` /
`.inr`-nil reduction lemma exists in `Drive.lean`): the halting step delivers its `endFrame`
result through the empty stack, and the advancing step is `drive_step`. The CALL case uses the
**bounded** descent `drive_descend_lt` and the standalone child run `child_terminates`, reconciled
to the framed fuel by `drive_fuel_mono`. -/

/-- **`drive → Runs` (reverse construction).** A top-level `drive` that terminates cleanly
(`drive f [] (running fr) = .ok res`) with every `Runs`-reachable frame `ModellableStep`
reconstructs a halting `Runs fr last`: a frame `last` reached from `fr` by opcode steps and
returning external CALLs that **halts**, with `res = endFrame last halt`. By strong induction on
`f`, case on `stepFrame fr`:

* `.halted halt` — base: `last = fr` (`Runs.refl`), `res = endFrame fr halt`;
* `.next exec'` — prepend a `Runs.step`, recurse at `f-1` on the advanced frame;
* `.needsCall cp pending` (code child) — extract the child's standalone terminating run
  (`child_terminates`), build the `CallReturns` node, recurse at the **strictly-smaller** resumed
  fuel (`drive_descend_lt`); the framed/standalone child fuels reconcile by `drive_fuel_mono`;
* `.needsCreate …` / precompile CALL — excluded by `ModellableStep` (no `Runs` node). -/
theorem runs_of_drive_ok :
    ∀ (f : ℕ) (fr : Frame) (res : FrameResult),
      drive f [] (running fr) = .ok res →
      (∀ fr', Runs fr fr' → ModellableStep fr') →
      ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
        ∧ res = endFrame last halt := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro fr res hdrive hmodel
    cases f with
    | zero => simp [drive] at hdrive
    | succ n =>
      cases hstep : stepFrame fr with
      | halted halt =>
        -- base: `fr` halts; `res = endFrame fr halt`. Peel the halting step then the empty-stack
        -- delivery (`drive` unfolds twice).
        have hd1 : drive (n + 1) [] (running fr)
            = drive n [] (finished (endFrame fr halt)) := by
          conv_lhs => unfold drive
          dsimp only [running]; rw [hstep]
        rw [hd1] at hdrive
        cases n with
        | zero => simp [drive] at hdrive
        | succ m =>
          have hd2 : drive (m + 1) [] (finished (endFrame fr halt))
              = .ok (endFrame fr halt) := by
            conv_lhs => unfold drive
          rw [hd2] at hdrive
          have : res = endFrame fr halt := (Except.ok.injEq _ _).mp hdrive.symm
          exact ⟨fr, halt, Runs.refl fr, hstep, this⟩
      | next exec =>
        -- step: advance `fr → fr'`, recurse at `n`.
        set fr' : Frame := { fr with exec := exec } with hfr'
        have hsteps : StepsTo fr fr' := ⟨hstep, rfl⟩
        rw [drive_step n fr exec hstep] at hdrive
        obtain ⟨last, halt, hruns, hhalt, hres⟩ :=
          ih n (by omega) fr' res hdrive
            (fun fr'' hr => hmodel fr'' (Runs.step hsteps hr))
        exact ⟨last, halt, Runs.step hsteps hruns, hhalt, hres⟩
      | needsCall cp pending =>
        -- CALL: must begin as a code child (precompile excluded by `ModellableStep`).
        cases hbc : beginCall cp with
        | inr immediate =>
          exact absurd hbc (hmodel fr (Runs.refl fr) |>.2 cp pending immediate hstep)
        | inl child =>
          obtain ⟨childRes, hchild_seed⟩ := child_terminates hbc
          -- the framed descent at fuel `n` resumes the parent at a strictly-smaller fuel.
          rw [driveG_needsCall_code n [] fr cp pending child hstep hbc] at hdrive
          -- the child standalone terminates at fuel `n` too (the framed run drained it), with the
          -- same result as at `seedFuel` (`drive_fuel_mono`, both non-`OutOfFuel`).
          have hchild_n : drive n [] (running child) = .ok childRes := by
            have hframed_ne : drive n (.call pending :: []) (running child)
                ≠ .error .OutOfFuel := by rw [hdrive]; nofun
            -- standalone child at fuel `n` is non-`OutOfFuel` (else the framed run would be too).
            have hstand_ne : drive n [] (running child) ≠ .error .OutOfFuel :=
              child_ne_oof_of_framed n child pending [] hframed_ne
            cases hsn : drive n [] (running child) with
            | error e =>
              rw [drive_error_oof _ _ _ e hsn] at hsn; exact absurd hsn hstand_ne
            | ok cres =>
              -- reconcile `cres` (fuel `n`) with `childRes` (fuel `seedFuel`) via mono.
              have hcres : drive (max n (seedFuel cp.gas)) [] (running child) = .ok cres :=
                (drive_fuel_mono (le_max_left _ _) [] (running child) (by rw [hsn]; nofun)).trans hsn
              have hother : drive (max n (seedFuel cp.gas)) [] (running child) = .ok childRes :=
                (drive_fuel_mono (le_max_right _ _) [] (running child)
                  (by rw [hchild_seed]; nofun)).trans hchild_seed
              rw [hcres] at hother
              exact hother
          -- the bounded descent: the framed run equals the resumed run at fuel `j < n`.
          obtain ⟨j, hjlt, hj⟩ := drive_descend_lt n child childRes pending [] hchild_n
          rw [hj] at hdrive
          -- the `CallReturns` node for this CALL.
          set resumeFr := resumeAfterCall childRes.toCallResult pending with hresume
          have hcall : CallReturns fr resumeFr :=
            ⟨cp, pending, child, childRes, hstep, hbc, hchild_seed, hresume⟩
          -- recurse from the resumed frame at the strictly-smaller fuel `j < n < n+1`.
          obtain ⟨last, halt, hruns, hhalt, hres⟩ :=
            ih j (by omega) resumeFr res hdrive
              (fun fr'' hr => hmodel fr'' (Runs.call hcall hr))
          exact ⟨last, halt, Runs.call hcall hruns, hhalt, hres⟩
      | needsCreate cp pending =>
        exact absurd hstep (hmodel fr (Runs.refl fr) |>.1 cp pending)

end BytecodeLayer.Interpreter

-- Build-enforced axiom-cleanliness guards for the `drive → Runs` reverse construction.
#print axioms BytecodeLayer.Interpreter.drive_append_framing_lt
#print axioms BytecodeLayer.Interpreter.drive_descend_lt
#print axioms BytecodeLayer.Interpreter.drive_error_oof
#print axioms BytecodeLayer.Interpreter.framed_oof_of_standalone_oof
#print axioms BytecodeLayer.Interpreter.runs_of_drive_ok
