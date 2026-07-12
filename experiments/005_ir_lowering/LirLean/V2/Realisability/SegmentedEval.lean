import LirLean.V2.Realisability.WitnessParams

/-!
# LirLean v2 — Realisability spec, SEGMENTED KERNEL EVALUATION (the R12a leaf machinery)

The generic step-composition machinery for discharging the two R12a `Bool` leaves
(`exCheck = true`, `entryCallsCodeOk exParams 4096 = true`) **in-kernel** — the
segmented-evaluation route identified in `WitnessParams.lean`'s module header after the
plain `decide +kernel` attempt was measured infeasible (the v4.30 kernel OOMs on the CALL
resume's state duplication: the parent frame's account/substate fields are deep
UNEVALUATED thunks at the resume, and the kernel's pointer-keyed whnf cache cannot share
their instantiated copies).

The route: both leaf evaluators (`driveLog`, `callsCodeOk`) consume exactly ONE fuel per
recursion step, so each run is a linear chain of machine configurations. We

1. reify one recursion step as a PURE transition function on configurations
   (`nextLog : LogConfig → LogConfig ⊕ LogResult`, `nextCC : Frame → Frame ⊕ Bool`) with
   an unfolding lemma equating one fuel-step of the evaluator to one transition
   (`driveLog_succ_eq`, `callsCodeOk_succ_eq`);
2. iterate it (`stepsLog`, `stepsCC`) with a fuel-shift composition lemma
   (`driveLog_shift`, `callsCodeOk_shift`): `k` transitions ending at `c'` turn
   `driveLog (k + fuel) c` into `driveLog fuel c'`;
3. close each segment `stepsLog K cᵢ = .inl cᵢ₊₁` by kernel evaluation from a LITERAL
   start `cᵢ` (`WitnessSegments.lean`, generated) — every restart resets the laziness, so
   the duplicated state at the CALL resume is a pointer-shared LITERAL, which the kernel
   cache CAN share;
4. finish with the terminal lemmas (`driveLog_final`, `callsCodeOk_final`).

Everything here is generic over the configuration (no witness literals); it is
sorry-free and belongs to the same WIP cone as `WitnessParams.lean`.
-/

set_option maxHeartbeats 1000000

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

/-! ## §1 — the `driveLog` step function -/

/-- One `driveLog` machine configuration: the pending stack, the running-or-delivering
state, and the four record accumulators — exactly `driveLog`'s non-fuel arguments. -/
structure LogConfig where
  stack : List Pending
  state : Frame ⊕ FrameResult
  gasAcc : List Word
  sloadAcc : List Nat
  callAcc : List CallRecord
  createAcc : List CreateRecord

/-- `driveLog`'s success payload. -/
abbrev LogResult :=
  FrameResult × List Word × List Nat × List CallRecord × List CreateRecord

/-- Apply `driveLog` to a configuration (fuel split off). -/
def driveLogC (fuel : ℕ) (c : LogConfig) :
    Except ExecutionException LogResult :=
  driveLog fuel c.stack c.state c.gasAcc c.sloadAcc c.callAcc c.createAcc

/-- **One `driveLog` transition** — the body of one recursion step of `driveLog`,
branch-for-branch, as a pure function: `.inr` is the `.ok` terminal (empty stack, a
delivered result), `.inl` is the next configuration. `driveLog`'s only other exit,
`.error .OutOfFuel`, is the fuel-0 case, which lives in the evaluator, not the step. -/
def nextLog (c : LogConfig) : LogConfig ⊕ LogResult :=
  match c.state with
    | .inr result =>
      match c.stack with
        | [] => .inr (result, c.gasAcc, c.sloadAcc, c.callAcc, c.createAcc)
        | pending :: rest =>
          match pending.resume result with
            | .ok parent =>
              .inl { stack := rest, state := .inl parent
                     gasAcc := c.gasAcc, sloadAcc := c.sloadAcc
                     callAcc := if rest.isEmpty then recordCall pending result c.callAcc
                                else c.callAcc
                     createAcc := if rest.isEmpty then recordCreate pending result c.createAcc
                                  else c.createAcc }
            | .error e =>
              .inl { stack := rest, state := .inr (endFrame pending.frame (.exception e))
                     gasAcc := c.gasAcc, sloadAcc := c.sloadAcc
                     callAcc := if rest.isEmpty then recordCall pending result c.callAcc
                                else c.callAcc
                     createAcc := if rest.isEmpty then recordCreate pending result c.createAcc
                                  else c.createAcc }
    | .inl current =>
      match stepFrame current with
        | .next exec =>
          if isGasOp current && c.stack.isEmpty then
            .inl { c with state := .inl { current with exec := exec }
                          gasAcc := c.gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable] }
          else if isSloadOp current && c.stack.isEmpty then
            .inl { c with state := .inl { current with exec := exec }
                          sloadAcc := c.sloadAcc ++ [sloadWarmthOf current] }
          else if isCreate2Op current && c.stack.isEmpty then
            .inl { c with state := .inl { current with exec := exec }
                          createAcc := c.createAcc ++ [softFailCreateRecord current] }
          else if isCallOp current && c.stack.isEmpty then
            .inl { c with state := .inl { current with exec := exec }
                          callAcc := c.callAcc ++ [softFailCallRecord current] }
          else
            .inl { c with state := .inl { current with exec := exec } }
        | .halted halt => .inl { c with state := .inr (endFrame current halt) }
        | .needsCall params pending =>
          match beginCall params with
            | .inl child => .inl { c with stack := .call pending :: c.stack
                                          state := .inl child }
            | .inr result => .inl { c with stack := .call pending :: c.stack
                                           state := .inr (.call result) }
        | .needsCreate params pending =>
          .inl { c with stack := .create pending :: c.stack
                        state := .inl (beginCreate params) }

/-- The unfolding lemma: one fuel-step of `driveLog` IS one `nextLog` transition. -/
theorem driveLogC_succ_eq (fuel : ℕ) (c : LogConfig) :
    driveLogC (fuel + 1) c =
      match nextLog c with
        | .inr res => .ok res
        | .inl c' => driveLogC fuel c' := by
  obtain ⟨stack, state, gasAcc, sloadAcc, callAcc, createAcc⟩ := c
  cases state with
  | inr result =>
    cases stack with
    | nil => rfl
    | cons pending rest =>
      show driveLog (fuel + 1) (pending :: rest) (.inr result) _ _ _ _ = _
      rw [driveLog, nextLog]
      dsimp only []
      cases hres : pending.resume result <;> (dsimp only []; rfl)
  | inl current =>
    show driveLog (fuel + 1) stack (.inl current) _ _ _ _ = _
    rw [driveLog, nextLog]
    dsimp only []
    cases hstep : stepFrame current with
    | next exec =>
      dsimp only []
      by_cases h1 : (isGasOp current && stack.isEmpty) = true
      · rw [if_pos h1, if_pos h1]; rfl
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : (isSloadOp current && stack.isEmpty) = true
        · rw [if_pos h2, if_pos h2]; rfl
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : (isCreate2Op current && stack.isEmpty) = true
          · rw [if_pos h3, if_pos h3]; rfl
          · rw [if_neg h3, if_neg h3]
            by_cases h4 : (isCallOp current && stack.isEmpty) = true
            · rw [if_pos h4, if_pos h4]; rfl
            · rw [if_neg h4, if_neg h4]; rfl
    | halted halt => rfl
    | needsCall params pending =>
      dsimp only []
      cases hbeg : beginCall params <;> rfl
    | needsCreate params pending => rfl

/-- Iterate `nextLog` for `k` transitions (a reached terminal absorbs). -/
def stepsLog : ℕ → LogConfig → LogConfig ⊕ LogResult
  | 0, c => .inl c
  | k + 1, c =>
    match nextLog c with
      | .inl c' => stepsLog k c'
      | .inr res => .inr res

/-- **The fuel-shift composition lemma**: `k` transitions ending at configuration `c'`
turn `driveLog (k + fuel)` from `c` into `driveLog fuel` from `c'` — the segment-gluing
step. -/
theorem driveLogC_shift {k : ℕ} {c c' : LogConfig} (h : stepsLog k c = .inl c')
    (fuel : ℕ) : driveLogC (k + fuel) c = driveLogC fuel c' := by
  induction k generalizing c with
  | zero =>
    unfold stepsLog at h
    injection h with h
    subst h
    rw [Nat.zero_add]
  | succ k ih =>
    unfold stepsLog at h
    have harith : k + 1 + fuel = k + fuel + 1 := by omega
    rw [harith, driveLogC_succ_eq]
    cases hn : nextLog c with
    | inl c₁ =>
      rw [hn] at h
      dsimp only [] at h ⊢
      exact ih h
    | inr res =>
      rw [hn] at h
      dsimp only [] at h
      cases h

/-- **The terminal-segment lemma**: `k` transitions reaching the terminal result `res`
close `driveLog` at ANY fuel `≥ k + 1`. Stated at `k + fuel + 1` so the arithmetic is
literal-friendly. -/
theorem driveLogC_final {k : ℕ} {c : LogConfig} {res : LogResult}
    (h : stepsLog k c = .inr res) (fuel : ℕ) :
    driveLogC (k + fuel + 1) c = .ok res := by
  induction k generalizing c with
  | zero =>
    unfold stepsLog at h
    cases h
  | succ k ih =>
    unfold stepsLog at h
    have harith : k + 1 + fuel + 1 = (k + fuel + 1) + 1 := by omega
    rw [harith, driveLogC_succ_eq]
    cases hn : nextLog c with
    | inl c₁ =>
      rw [hn] at h
      dsimp only [] at h ⊢
      exact ih h
    | inr res' =>
      rw [hn] at h
      dsimp only [] at h ⊢
      injection h with h
      rw [h]

/-! ## §2 — the `callsCodeOk` step function -/

/-- **One `callsCodeOk` transition**: `.inl` is the next top-level frame on the checker's
replay chain, `.inr` a decided verdict. Branch-for-branch `callsCodeOk`'s body (the
`.needsCall` guard-`&&`-continuation shape splits into the `.inr false` short-circuit and
the guarded continuation). -/
def nextCC (fr : Frame) : Frame ⊕ Bool :=
  match stepFrame fr with
    | .next exec => .inl { fr with exec := exec }
    | .halted _ => .inr true
    | .needsCall cp pending =>
      match cp.codeSource with
        | .Precompiled _ => .inr false
        | .Code _ =>
          match beginCall cp with
            | .inl child =>
              match drive (seedFuel cp.gas) [] (running child) with
                | .ok childRes => .inl (resumeAfterCall childRes.toCallResult pending)
                | .error _ => .inr true
            | .inr _ => .inr true
    | .needsCreate cp pending =>
      match drive (seedFuel cp.gas) [] (running (beginCreate cp)) with
        | .ok childRes =>
          match resumeAfterCreate childRes.toCreateResult pending with
            | .ok resumeFr => .inl resumeFr
            | .error _ => .inr false
        | .error _ => .inr true

set_option maxHeartbeats 1000000 in
/-- The unfolding lemma: one fuel-step of `callsCodeOk` IS one `nextCC` transition. -/
theorem callsCodeOk_succ_eq (fuel : ℕ) (fr : Frame) :
    callsCodeOk (fuel + 1) fr =
      match nextCC fr with
        | .inr b => b
        | .inl fr' => callsCodeOk fuel fr' := by
  rw [callsCodeOk.eq_def, nextCC]
  dsimp only []
  cases hstep : stepFrame fr with
  | next exec => rfl
  | halted halt => rfl
  | needsCall cp pending =>
    dsimp only []
    cases hcs : cp.codeSource with
    | Precompiled p => rfl
    | Code code =>
      dsimp only []
      cases hbeg : beginCall cp with
      | inl child =>
        dsimp only []
        cases hdrive : drive (seedFuel cp.gas) [] (running child) <;> rfl
      | inr result => rfl
  | needsCreate cp pending =>
    dsimp only []
    cases hdrive : drive (seedFuel cp.gas) [] (running (beginCreate cp)) with
    | ok childRes =>
      dsimp only []
      cases hres : resumeAfterCreate childRes.toCreateResult pending <;> rfl
    | error e => rfl

/-- Iterate `nextCC` for `k` transitions (a reached verdict absorbs). -/
def stepsCC : ℕ → Frame → Frame ⊕ Bool
  | 0, fr => .inl fr
  | k + 1, fr =>
    match nextCC fr with
      | .inl fr' => stepsCC k fr'
      | .inr b => .inr b

/-- The fuel-shift composition lemma for the checker. -/
theorem callsCodeOk_shift {k : ℕ} {fr fr' : Frame} (h : stepsCC k fr = .inl fr')
    (fuel : ℕ) : callsCodeOk (k + fuel) fr = callsCodeOk fuel fr' := by
  induction k generalizing fr with
  | zero =>
    unfold stepsCC at h
    injection h with h
    subst h
    rw [Nat.zero_add]
  | succ k ih =>
    unfold stepsCC at h
    have harith : k + 1 + fuel = k + fuel + 1 := by omega
    rw [harith, callsCodeOk_succ_eq]
    cases hn : nextCC fr with
    | inl fr₁ =>
      rw [hn] at h
      dsimp only [] at h ⊢
      exact ih h
    | inr b =>
      rw [hn] at h
      dsimp only [] at h
      cases h

/-- The terminal-segment lemma for the checker: `k` transitions reaching verdict `b`
decide `callsCodeOk` at any fuel `≥ k + 1`. -/
theorem callsCodeOk_final {k : ℕ} {fr : Frame} {b : Bool}
    (h : stepsCC k fr = .inr b) (fuel : ℕ) :
    callsCodeOk (k + fuel + 1) fr = b := by
  induction k generalizing fr with
  | zero =>
    unfold stepsCC at h
    cases h
  | succ k ih =>
    unfold stepsCC at h
    have harith : k + 1 + fuel + 1 = (k + fuel + 1) + 1 := by omega
    rw [harith, callsCodeOk_succ_eq]
    cases hn : nextCC fr with
    | inl fr₁ =>
      rw [hn] at h
      dsimp only [] at h ⊢
      exact ih h
    | inr b' =>
      rw [hn] at h
      dsimp only [] at h ⊢
      injection h

end Lir.V2
