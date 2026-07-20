import BytecodeLayer.Hoare.CallSequence

/-!
# Reconstruct a halting `Runs` from a clean-terminating top-level `drive`

`CleanHalts fr₀` means `∃ last halt, Runs fr₀ last ∧ stepFrame last = .halted halt`. It can be
derived from the **clean-halt outcome** of the recording interpreter:
`runWithLog params (seedFuel params.gas) = some log`, which (`runWithLog_drive`) pins
`drive (seedFuel params.gas) [] (running fr₀) = .ok log.observable`.

The forward direction is `Runs → drive` (`Runs.drive_reconcile`, `messageCall_runs`). This module
proves the **reverse**: a top-level `drive` that terminates
cleanly (`.ok`) reconstructs a halting `Runs` to the result's halt frame. `Runs` carries
returning external CALLs as black-box `CallReturns` nodes AND returning CREATEs as `CreateReturns`
nodes (`Runs.create`), so both descents are modelled. The reconstruction carries only the honest
`ModellableStep` residuals: every reachable CREATE resumes successfully (no 63/64 OOG-fault) and
every reachable CALL targets code (no precompile) — the two configurations `Runs` cannot resume.

## The construction

* **`drive_descend_lt` / `drive_descend_create_lt`** (upstream,
  `Semantics/Interpreter/DescentEq.lean`) — the *bounded* CALL/CREATE-boundary descents: a child
  sub-run that drains to `.ok res` resumes the parent at a fuel **strictly below** the parent's
  (`< f`). This is the bound the `_eq` forms leave existential; it is what makes the reverse
  recursion well-founded (the resumed run is at strictly less fuel, so strong induction on fuel
  applies). The CREATE twin is conditioned on the successful resume witness (`ModellableStep`
  clause 1).
* **`runs_of_drive_ok`** — the reverse construction. By strong induction on the top-level fuel,
  case on `stepFrame fr`: `.halted` is the base (`Runs.refl`); `.next` prepends a `Runs.step`;
  `.needsCall` (child = Code) extracts the child's black-box terminating sub-run, builds the
  `CallReturns` node, and recurses at the strictly-smaller resumed fuel (`drive_descend_lt`);
  `.needsCreate` extracts the total `beginCreate` child's sub-run, resolves the resume, builds the
  `CreateReturns` node, and recurses (`drive_descend_create_lt`).

No `sorry`/`axiom`/`native_decide`. Imports only the bytecode layer.
-/

namespace BytecodeLayer.Interpreter

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare

/-! ## The `ModellableStep` side condition

`Runs` models opcode steps (`Runs.step`), returning external CALLs (`Runs.call`/`CallReturns`)
AND returning CREATEs (`Runs.create`/`CreateReturns`). The two configurations it cannot resume are
a precompile CALL (`.inr`) and a CREATE that OOG-faults on resume (the 63/64 guard throwing). So
the reverse construction carries the per-frame `ModellableStep` residual — every reachable CREATE
resumes successfully, every reachable CALL targets code — threaded as the recursion descends. Both
are honest runtime side conditions (vacuous for create-free / call-free programs). -/

/-- **A frame's step is `Runs`-modellable.** `stepFrame fr` is either a non-halting step
(`.next`), a halt (`.halted`), a **code** CALL that begins as a frame (`.needsCall cp _` with
`beginCall cp = .inl _`), or a **CREATE whose init child returns and *successfully* resumes** (the
63/64 retention guard passing) — the four configurations `Runs` models (`Runs.step` / `Runs.refl` /
`Runs.call` / `Runs.create`).

Two per-frame clauses:

* **clause 1 (create-resolves) — the honest create-resolves residual.** A `.needsCreate cp pending`
  whose init
  child terminates (`drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes`) resumes
  successfully (`resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr`). This is NOT a
  structural property of `lower prog` — the 63/64 guard (`EVM/Evm/Semantics/Create.lean:200`) can
  `throw .OutOfGas`
  on a `UInt64` overflow of the retained gas, so it is the genuine "enough gas retained" side
  condition CALL never needed. Vacuous for any create-free program; satisfiable for
  empty-init CREATEs at ordinary gas (the guard fires only on arithmetic overflow). The OOG
  resume-fault delivers an exception halt through the drive stack — a control flow `Runs` does not
  *resume* — so it is out of scope of the `Runs.create` node by construction; this clause rules it
  out on every reachable create frame.
* **clause 2 (code-CALL) — the precompile residual.** A `.needsCall` never begins as a
  precompile/immediate (`.inr`); those have no `Runs` node either.

The former "no CREATE at all" clause (`stepFrame fr ≠ .needsCreate …`) is **RETIRED** — CREATE is
now modelled by `Runs.create`, not excluded (`runs_of_drive_ok`'s `.needsCreate` arm below). -/
def ModellableStep (fr : Frame) : Prop :=
  (∀ cp pending childRes, stepFrame fr = .needsCreate cp pending →
      drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes →
      ∃ resumeFr, resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr)
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
        exact ih (.create pending :: stack) (.inl (beginCreate params)) e h

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

/-- **A create init child terminates standalone.** `beginCreate cp` is a total frame whose
gas is `cp.gas` (`beginCreate_gas`), so its standalone seed-fuel run's measure `μ` is bounded by
`seedFuel cp.gas` — hence it never runs out of fuel (`mu_bound gasFundsDescent_holds`) and returns
a definite `.ok childRes`. The CREATE twin of `child_terminates` (which used
`messageCall_never_outOfFuel`); here the same `mu_bound` machinery applies directly to the total
`beginCreate cp` frame. -/
theorem create_child_terminates (cp : CreateParams) :
    ∃ childRes, drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes := by
  have hg : (beginCreate cp).exec.gasAvailable = cp.gas := BytecodeLayer.System.beginCreate_gas
  have hμ : μ [] (.inl (beginCreate cp)) ≤ seedFuel cp.gas := by
    simp only [μ, tagBit, totalGas, activeGas, List.map_nil, List.sum_nil, List.length_nil]
    unfold seedFuel; rw [hg]; omega
  have hb : drive (seedFuel cp.gas) [] (.inl (beginCreate cp)) ≠ .error .OutOfFuel :=
    mu_bound gasFundsDescent_holds (seedFuel cp.gas) [] (.inl (beginCreate cp)) hμ
  cases hd : drive (seedFuel cp.gas) [] (running (beginCreate cp)) with
  | error e => rw [drive_error_oof _ _ _ e hd] at hd; exact absurd hd hb
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
        have := ih (.inl (beginCreate params)) (.create pending :: top) bot h
        rwa [List.cons_append] at this

/-- **Framed non-OOF gives standalone non-OOF.** Contrapositive of
`framed_oof_of_standalone_oof` at `top := []`, generic in the suspended `Pending` (`.call` or
`.create`): a framed child run that does not run out of fuel witnesses that the standalone child
run does not either (it drained the child within budget). -/
theorem child_ne_oof_of_framed (f : ℕ) (child : Frame) (p : Pending) (ps : List Pending)
    (h : drive f (p :: ps) (running child) ≠ .error .OutOfFuel) :
    drive f [] (running child) ≠ .error .OutOfFuel := by
  intro hcontra
  exact h (by have := framed_oof_of_standalone_oof f (running child) [] (p :: ps) hcontra
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
* `.needsCreate cp pending` (returning create) — extract the init child's standalone terminating
  run, resolve the resume (`ModellableStep` clause 1), build the `Runs.create` node, recurse at the
  **strictly-smaller** resumed fuel (`drive_descend_create_lt`);
* precompile CALL / OOG-faulting create resume — excluded by `ModellableStep` (no `Runs` node). -/
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
          -- same result as at `seedFuel` (`drive_ok_agree`).
          have hchild_n : drive n [] (running child) = .ok childRes := by
            have hframed_ne : drive n (.call pending :: []) (running child)
                ≠ .error .OutOfFuel := by rw [hdrive]; nofun
            -- standalone child at fuel `n` is non-`OutOfFuel` (else the framed run would be too).
            exact drive_ok_agree [] (running child)
              (child_ne_oof_of_framed n child (.call pending) [] hframed_ne) hchild_seed
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
        -- CREATE: `beginCreate` is total, so the descent is unconditional. The init child's
        -- standalone run terminates (`create_child_terminates`), the resume resolves
        -- (`ModellableStep` clause 1 — the honest create-resolves residual), and a `Runs.create`
        -- node is built,
        -- recursing at the strictly-smaller resumed fuel (`drive_descend_create_lt`). Mirrors the
        -- `.needsCall` code arm.
        obtain ⟨childRes, hchild_seed⟩ := create_child_terminates cp
        rw [driveG_needsCreate n [] fr cp pending hstep] at hdrive
        -- the child standalone terminates at fuel `n` too (the framed run drained it), with the
        -- same result as at `seedFuel` (`drive_ok_agree`).
        have hchild_n : drive n [] (running (beginCreate cp)) = .ok childRes := by
          have hframed_ne : drive n (.create pending :: []) (running (beginCreate cp))
              ≠ .error .OutOfFuel := by rw [hdrive]; nofun
          exact drive_ok_agree [] (running (beginCreate cp))
            (child_ne_oof_of_framed n (beginCreate cp) (.create pending) [] hframed_ne) hchild_seed
        -- the resume resolves successfully (honest create-resolves residual, `ModellableStep.1`).
        obtain ⟨resumeFr, hok⟩ :=
          (hmodel fr (Runs.refl fr)).1 cp pending childRes hstep hchild_seed
        -- the bounded create descent: the framed run equals the resumed run at fuel `j < n`.
        obtain ⟨j, hjlt, hj⟩ :=
          drive_descend_create_lt n (beginCreate cp) childRes pending [] resumeFr hchild_n hok
        rw [hj] at hdrive
        -- the `CreateReturns` node for this CREATE.
        have hc : CreateReturns fr resumeFr := ⟨cp, pending, childRes, hstep, hchild_seed, hok⟩
        -- recurse from the resumed frame at the strictly-smaller fuel `j < n < n+1`.
        obtain ⟨last, halt, hruns, hhalt, hres⟩ :=
          ih j (by omega) resumeFr res hdrive
            (fun fr'' hr => hmodel fr'' (Runs.create hc hr))
        exact ⟨last, halt, Runs.create hc hruns, hhalt, hres⟩

end BytecodeLayer.Interpreter

-- Build-enforced axiom-cleanliness guards for the `drive → Runs` reverse construction.
