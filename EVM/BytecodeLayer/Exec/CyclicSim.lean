import BytecodeLayer.Exec.RecorderLemmas
import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Hoare.Descent
import BytecodeLayer.Hoare.DriveRuns

namespace BytecodeLayer.Exec.CyclicSim

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.System
open BytecodeLayer.Exec.Recorder

/-- An invariant preserved by ordinary steps and completed CALL/CREATE descents
is preserved by a whole cyclic execution path. -/
theorem invariant_of_runs {Inv : Frame → Prop}
    (step : ∀ {fr fr'}, StepsTo fr fr' → Inv fr → Inv fr')
    (call : ∀ {fr fr'}, CallReturns fr fr' → Inv fr → Inv fr')
    (create : ∀ {fr fr'}, CreateReturns fr fr' → Inv fr → Inv fr')
    {fr fr' : Frame} (run : Runs fr fr') :
    Inv fr → Inv fr' := by
  induction run with
  | refl _ => exact id
  | step edge _ ih => exact fun hfr => ih (step edge hfr)
  | call edge _ ih => exact fun hfr => ih (call edge hfr)
  | create edge _ ih => exact fun hfr => ih (create edge hfr)

/-- A run from a frame that halts immediately can only be reflexive. -/
theorem runs_halt_eq {fr fr' : Frame} {h : FrameHalt}
    (hh : stepFrame fr = .halted h) (hr : Runs fr fr') : fr = fr' := by
  cases hr with
  | refl _ => rfl
  | step hstep _ => rw [hstep.1] at hh; exact absurd hh (by nofun)
  | call hcall _ =>
      obtain ⟨_, _, _, _, hstep, _⟩ := hcall
      rw [hstep] at hh; exact absurd hh (by nofun)
  | create hc _ =>
      obtain ⟨_, _, _, hstep, _⟩ := hc
      rw [hstep] at hh; exact absurd hh (by nofun)

/-- Every edge in a run returns to a frame of the starting frame's kind. -/
theorem runs_kind {fr fr' : Frame} (h : Runs fr fr') : fr'.kind = fr.kind := by
  induction h with
  | refl _ => rfl
  | step hs _ ih => rw [ih, hs.kind_eq]
  | call hc _ ih =>
      obtain ⟨cp, pending, child, childRes, hstep, _, _, hresume⟩ := hc
      rw [ih, hresume]
      exact (Evm.stepFrame_needsCall_inv hstep).2.1
  | create hc _ ih =>
      obtain ⟨cp, pending, childRes, hstep, _, hresume⟩ := hc
      rw [ih, resumeAfterCreate_kind childRes pending _ hresume]
      exact (Evm.stepFrame_needsCreate_inv hstep).2.1

private theorem recordCall_append (pending : Pending) (result : FrameResult)
    (c0 : List CallRecord) :
    recordCall pending result c0 = c0 ++ recordCall pending result [] := by
  cases pending with
  | call pd => simp [recordCall]
  | create _ => simp [recordCall]

private theorem recordCreate_append (pending : Pending) (result : FrameResult)
    (d0 : List CreateRecord) :
    recordCreate pending result d0 = d0 ++ recordCreate pending result [] := by
  cases pending with
  | call _ => simp [recordCreate]
  | create pd => simp [recordCreate]

private theorem driveLog_acc_hom :
    ∀ (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (g0 : List Word) (c0 : List CallRecord) (d0 : List CreateRecord),
      driveLog fuel stack state g0 c0 d0
        = (driveLog fuel stack state [] [] []).map
            (fun x => (x.1, g0 ++ x.2.1, c0 ++ x.2.2.1, d0 ++ x.2.2.2)) := by
  intro fuel
  induction fuel with
  | zero => intro stack state g0 c0 d0; rfl
  | succ n ih =>
    intro stack state g0 c0 d0
    unfold driveLog
    cases state with
    | inr result =>
      dsimp only
      cases stack with
      | nil => simp [Except.map]
      | cons pending rest =>
        dsimp only
        cases hres : pending.resume result with
        | ok parent =>
          dsimp only [hres]
          split_ifs with hre
          · rw [ih rest (.inl parent) g0 (recordCall pending result c0)
                  (recordCreate pending result d0),
                ih rest (.inl parent) [] (recordCall pending result [])
                  (recordCreate pending result [])]
            cases hb : driveLog n rest (.inl parent) [] [] [] with
            | error e => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0,
                recordCreate_append pending result d0, List.append_assoc]
          · rw [ih rest (.inl parent) g0 c0 d0]
        | error e =>
          dsimp only [hres]
          split_ifs with hre
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0
                  (recordCall pending result c0) (recordCreate pending result d0),
                ih rest (.inr (endFrame pending.frame (.exception e))) []
                  (recordCall pending result []) (recordCreate pending result [])]
            cases hb : driveLog n rest (.inr (endFrame pending.frame (.exception e))) [] [] [] with
            | error e' => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0,
                recordCreate_append pending result d0, List.append_assoc]
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 c0 d0]
    | inl current =>
      dsimp only
      cases hstep : stepFrame current with
      | next exec =>
        dsimp only [hstep]
        split_ifs with hc1 hc2 hc3
        · rw [ih stack (.inl { current with exec := exec })
                (g0 ++ [UInt256.ofUInt64 exec.gasAvailable]) c0 d0,
              ih stack (.inl { current with exec := exec })
                ([] ++ [UInt256.ofUInt64 exec.gasAvailable]) [] []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 c0
                (d0 ++ [softFailCreateRecord current]),
              ih stack (.inl { current with exec := exec }) [] []
                ([] ++ [softFailCreateRecord current])]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0
                (c0 ++ [softFailCallRecord current]) d0,
              ih stack (.inl { current with exec := exec }) []
                ([] ++ [softFailCallRecord current]) []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 c0 d0]
      | halted halt =>
        dsimp only [hstep]
        rw [ih stack (.inr (endFrame current halt)) g0 c0 d0]
      | needsCall params pending =>
        dsimp only [hstep]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; rw [ih (.call pending :: stack) (.inl child) g0 c0 d0]
        | inr result =>
          dsimp only [hbc]; rw [ih (.call pending :: stack) (.inr (.call result)) g0 c0 d0]
      | needsCreate params pending =>
        dsimp only [hstep]
        rw [ih (.create pending :: stack) (.inl (beginCreate params)) g0 c0 d0]

private theorem isGasOp_false_of_isCreate2Op {fr : Frame} (h : isCreate2Op fr = true) :
    isGasOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.System .CREATE2 := by simpa [isCreate2Op] using h
  simp only [isGasOp, h']
  decide

private theorem isGasOp_false_of_isCallOp {fr : Frame} (h : isCallOp fr = true) :
    isGasOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.System .CALL := by simpa [isCallOp] using h
  simp only [isGasOp, h']
  decide

private theorem isCreate2Op_false_of_isCallOp {fr : Frame} (h : isCallOp fr = true) :
    isCreate2Op fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.System .CALL := by simpa [isCallOp] using h
  simp only [isCreate2Op, h']
  decide

theorem recorderCoupled_entry {params : CallParams} {log : RunLog} {fr₀ : Frame}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀) :
    RecorderCoupled log fr₀ log.gas log.calls log.creates := by
  unfold runWithLog at hrun
  rw [hbegin] at hrun
  dsimp only at hrun
  cases hdl : driveLog (seedFuel params.gas) [] (.inl fr₀) [] [] [] with
  | error e => rw [hdl] at hrun; simp at hrun
  | ok tuple =>
    obtain ⟨r, gas, calls, creates⟩ := tuple
    rw [hdl] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact ⟨⟨seedFuel params.gas, hdl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

theorem recorderCoupled_step_gas {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {g : Word} {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr (g :: gS) cS dS)
    (hgas : isGasOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS cS dS
    ∧ g = UInt256.ofUInt64 exec.gasAvailable := by
  obtain ⟨⟨f, hf⟩, hgp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, g :: gS, cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgc hcd
      injection hcd with hc hd
      injection hgc with hgeq hgSeq
      subst hobs; subst hgSeq; subst hc; subst hd
      refine ⟨⟨⟨m, hX⟩, ?_, hcpp, hdp⟩, hgeq.symm⟩
      obtain ⟨pre, hpre⟩ := hgp
      exact ⟨pre ++ [g], by rw [hpre, List.append_assoc, List.singleton_append]⟩

theorem gasSuffix_nonempty {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hgas : isGasOp fr = true) (hstep : stepFrame fr = .next exec) :
    ∃ g gS', gS = g :: gS' := by
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with _ hf4
      injection hf4 with hgc _
      exact ⟨_, _, hgc.symm⟩

theorem recorderCoupled_step_other {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hng : isGasOp fr = false)
    (hnc : isCreate2Op fr = false)
    (hncall : isCallOp fr = false)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS cS dS := by
  obtain ⟨⟨f, hf⟩, hgp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hnc, hncall, List.isEmpty_nil, Bool.false_and,
      Bool.and_false] at hf
    exact ⟨⟨m, hf⟩, hgp, hcpp, hdp⟩

private theorem driveLog_frame_nonempty (bot : List Pending) (hbot : bot.isEmpty = false)
    (g0 : List Word) (c0 : List CallRecord) (d0 : List CreateRecord) :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∃ j, driveLog f (top ++ bot) st g0 c0 d0
          = driveLog (j + 1) bot (.inr res) g0 c0 d0 := by
  have hbne : ∀ (t : List Pending), (t ++ bot).isEmpty = false := by
    intro t; cases t with
    | nil => exact hbot
    | cons _ _ => rfl
  intro f
  induction f with
  | zero => intro top st res h; simp [drive] at h
  | succ n ih =>
    intro top st res h
    unfold drive at h
    unfold driveLog
    cases st with
    | inr result =>
      cases top with
      | nil =>
        dsimp only at h ⊢
        cases h
        exact ⟨n, rfl⟩
      | cons pending rest =>
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h
          simp only [hres]
          split_ifs with he
          · rw [hbne rest] at he; simp at he
          · exact ih rest (.inl parent) res h
        | error e =>
          rw [hres] at h; dsimp only at h
          simp only [hres]
          split_ifs with he
          · rw [hbne rest] at he; simp at he
          · exact ih rest (.inr (endFrame pending.frame (.exception e))) res h
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        split_ifs with hc1 hc2 hc3
        · rw [hbne top] at hc1; simp at hc1
        · rw [hbne top] at hc2; simp at hc2
        · rw [hbne top] at hc3; simp at hc3
        · exact ih top (.inl { current with exec := exec }) res h
      | halted halt =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        exact ih top (.inr (endFrame current halt)) res h
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h
          dsimp only
          rw [← List.cons_append]
          exact ih (.call pending :: top) (.inl child) res h
        | inr result =>
          rw [hbc] at h; dsimp only at h
          dsimp only
          rw [← List.cons_append]
          exact ih (.call pending :: top) (.inr (.call result)) res h
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        rw [← List.cons_append]
        exact ih (.create pending :: top) (.inl (beginCreate params)) res h

theorem callSuffix_nonempty {log : RunLog} {fr : Frame} {cp : CallParams}
    {pending : PendingCall} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .needsCall cp pending) :
    ∃ rec cS', cS = rec :: cS' := by
  obtain ⟨⟨fuel', hrestart⟩, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    unfold driveLog at hrestart
    simp only [hstep] at hrestart
    cases hbc : beginCall cp with
    | inl child =>
      simp only [hbc] at hrestart
      have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
        have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] []
        rw [hrestart] at hd
        simpa only [Except.map] using hd.symm
      have hstand_ne : drive m [] (.inl child) ≠ .error .OutOfFuel := by
        intro hoof
        have := framed_oof_of_standalone_oof m (.inl child) [] (.call pending :: []) hoof
        rw [List.nil_append, hdrive] at this
        simp at this
      cases hstand : drive m [] (.inl child) with
      | error e =>
        rw [drive_error_oof _ _ _ e hstand] at hstand
        exact absurd hstand hstand_ne
      | ok childRes =>
        obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
          m [] (.inl child) childRes hstand
        rw [List.nil_append] at hframe
        rw [hframe] at hrestart
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
          List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) []
          [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
        cases htail : driveLog j []
            (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          exact ⟨_, _, (congrArg (fun x => x.2.2.1) htuple).symm⟩
    | inr result =>
      simp only [hbc] at hrestart
      have hdrive : drive m (.call pending :: []) (.inr (.call result))
          = .ok log.observable := by
        have hd := driveLog_drive m (.call pending :: []) (.inr (.call result)) [] [] []
        rw [hrestart] at hd
        simpa only [Except.map] using hd.symm
      have hstand_ne : drive m [] (.inr (.call result)) ≠ .error .OutOfFuel := by
        intro hoof
        have := framed_oof_of_standalone_oof m (.inr (.call result)) []
          (.call pending :: []) hoof
        rw [List.nil_append, hdrive] at this
        simp at this
      cases hstand : drive m [] (.inr (.call result)) with
      | error e =>
        rw [drive_error_oof _ _ _ e hstand] at hstand
        exact absurd hstand hstand_ne
      | ok childRes =>
        obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
          m [] (.inr (.call result)) childRes hstand
        rw [List.nil_append] at hframe
        rw [hframe] at hrestart
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
          List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) []
          [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
        cases htail : driveLog j []
            (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          exact ⟨_, _, (congrArg (fun x => x.2.2.1) htuple).symm⟩

theorem createSuffix_nonempty {log : RunLog} {fr : Frame} {cp : CreateParams}
    {pending : PendingCreate} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .needsCreate cp pending) :
    ∃ rec dS', dS = rec :: dS' := by
  obtain ⟨⟨fuel', hrestart⟩, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    unfold driveLog at hrestart
    simp only [hstep] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hstand_ne : drive m [] (.inl (beginCreate cp)) ≠ .error .OutOfFuel := by
      intro hoof
      have := framed_oof_of_standalone_oof m (.inl (beginCreate cp)) []
        (.create pending :: []) hoof
      rw [List.nil_append, hdrive] at this
      simp at this
    cases hstand : drive m [] (.inl (beginCreate cp)) with
    | error e =>
      rw [drive_error_oof _ _ _ e hstand] at hstand
      exact absurd hstand hstand_ne
    | ok childRes =>
      obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] []
        m [] (.inl (beginCreate cp)) childRes hstand
      rw [List.nil_append] at hframe
      rw [hframe] at hrestart
      cases hresume : resumeAfterCreate childRes.toCreateResult pending with
      | error e =>
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, hresume, List.isEmpty_nil, if_true, recordCall,
          recordCreate, List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inr (endFrame (Pending.create pending).frame (.exception e))) [] []
          [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
        cases htail : driveLog j []
            (.inr (endFrame (Pending.create pending).frame (.exception e))) [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          exact ⟨_, _, (congrArg (fun x => x.2.2.2) htuple).symm⟩
      | ok resumeFr =>
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, hresume, List.isEmpty_nil, if_true, recordCall,
          recordCreate, List.nil_append] at hrestart
        rw [driveLog_acc_hom j [] (.inl resumeFr) [] []
          [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
        cases htail : driveLog j [] (.inl resumeFr) [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          exact ⟨_, _, (congrArg (fun x => x.2.2.2) htuple).symm⟩

theorem recorderCoupled_call {log : RunLog} {fr resumeFr : Frame}
    {gS : List Word} {rec : CallRecord} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS (rec :: cS) dS)
    (hcr : CallReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS cS dS := by
  obtain ⟨cp, pending, child, childRes, hstep, hcode, hchild, hresume⟩ := hcr
  have hcode' : beginCall cp = .inl child := hcode
  obtain ⟨⟨fuel', hrestart⟩, hgp, hcpp, hdp⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    -- Unfold the restart's first (CALL) step: `fr` descends into `child` on `[.call pending]`.
    have hdescent : driveLog (m + 1) [] (.inl fr) [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode']
    rw [hdescent] at hrestart
    -- The child terminates within fuel `m` (the framed restart succeeded).
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.call pending :: []) (running child) ≠ .error .OutOfFuel := by
      rw [hdrive]; simp
    have hchildm_ne : drive m [] (running child) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m child (.call pending) [] hne
    -- Reconcile the framed child result with `hcr`'s black-box `childRes` (`drive_ok_agree`).
    have hchildm : drive m [] (running child) = .ok childRes :=
      drive_ok_agree [] (running child) hchildm_ne hchild
    -- Frame the recorder: the inline child records nothing; the outer delivery records `[outerRec]`.
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    -- Reduce the outer CALL delivery (`rest = []`): record `[outerRec]`, resume at `resumeFr`.
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl resumeFr) []
            [{ result := childRes.toCallResult, pending := pending }] [] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    -- Peel the single seeded record via the accumulator homomorphism.
    rw [driveLog_acc_hom j [] (.inl resumeFr) []
      [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
    cases hb : driveLog j [] (.inl resumeFr) [] [] [] with
    | error e => rw [hb] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', cS'', dS''⟩ := val
      rw [hb] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'', [] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, rec :: cS, dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with hobs heq3
      injection heq3 with hgeq heq4
      injection heq4 with hseq heq5
      injection hseq with _ hcs
      subst hobs; subst hgeq; subst hcs; subst heq5
      refine ⟨⟨j, hb⟩, hgp, ?_, hdp⟩
      obtain ⟨pre, hpre⟩ := hcpp
      exact ⟨pre ++ [rec], by rw [hpre]; simp [List.append_assoc]⟩

theorem recorderCoupled_create {log : RunLog} {fr resumeFr : Frame}
    {gS : List Word} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS (rec :: dS))
    (hcr : CreateReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS cS dS := by
  obtain ⟨cp, pending, childRes, hstep, hchild, hresume⟩ := hcr
  obtain ⟨⟨fuel', hrestart⟩, hgp, hcpp, hdp⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl fr) [] [] []
        = driveLog m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep]
    rw [hdescent] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.create pending :: []) (running (beginCreate cp))
        ≠ .error .OutOfFuel := by rw [hdrive]; simp
    have hchildm_ne : drive m [] (running (beginCreate cp)) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m (beginCreate cp) (.create pending) [] hne
    have hchildm : drive m [] (running (beginCreate cp)) = .ok childRes :=
      drive_ok_agree [] (running (beginCreate cp)) hchildm_ne hchild
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] []
      m [] (.inl (beginCreate cp)) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.create pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl resumeFr) [] []
            [{ result := childRes.toCreateResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] []
      [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
    cases hb : driveLog j [] (.inl resumeFr) [] [] [] with
    | error e => rw [hb] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', cS'', dS''⟩ := val
      rw [hb] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ cS'',
          [{ result := childRes.toCreateResult, pending := pending }] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, cS, rec :: dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with hobs heq3
      injection heq3 with hgeq heq4
      injection heq4 with hseq heq5
      injection heq5 with hcEq hcons
      subst hobs; subst hgeq; subst hseq; subst hcons
      refine ⟨⟨j, hb⟩, hgp, hcpp, ?_⟩
      obtain ⟨pre, hpre⟩ := hdp
      exact ⟨pre ++ [rec], by rw [hpre]; simp [List.append_assoc]⟩

theorem recorderCoupled_create_extract {log : RunLog} {createFr : Frame}
    {cp : CreateParams} {pending : PendingCreate}
    {gS : List Word} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log createFr gS cS (rec :: dS))
    (hstep : stepFrame createFr = .needsCreate cp pending)
    (hresolve : CreateResolves createFr) :
    ∃ (childRes : FrameResult) (resumeFr : Frame),
        CreateReturns createFr resumeFr
      ∧ rec = { result := childRes.toCreateResult, pending := pending }
      ∧ resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr
      ∧ RecorderCoupled log resumeFr gS cS dS := by
  obtain ⟨childRes, hchild⟩ := create_child_terminates cp
  obtain ⟨resumeFr, hresume⟩ := hresolve cp pending childRes hstep hchild
  have hcr : CreateReturns createFr resumeFr :=
    ⟨cp, pending, childRes, hstep, hchild, hresume⟩
  refine ⟨childRes, resumeFr, hcr, ?_, hresume, recorderCoupled_create hcp hcr⟩
  obtain ⟨⟨fuel', hrestart⟩, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl createFr) [] [] []
        = driveLog m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep]
    rw [hdescent] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.create pending :: []) (running (beginCreate cp))
        ≠ .error .OutOfFuel := by rw [hdrive]; simp
    have hchildm_ne : drive m [] (running (beginCreate cp)) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m (beginCreate cp) (.create pending) [] hne
    have hchildm : drive m [] (running (beginCreate cp)) = .ok childRes :=
      drive_ok_agree [] (running (beginCreate cp)) hchildm_ne hchild
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] []
      m [] (.inl (beginCreate cp)) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.create pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl resumeFr) [] []
            [{ result := childRes.toCreateResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] []
      [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
    cases hbok : driveLog j [] (.inl resumeFr) [] [] [] with
    | error e => rw [hbok] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', cS'', dS''⟩ := val
      rw [hbok] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ cS'',
          [{ result := childRes.toCreateResult, pending := pending }] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, cS, rec :: dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with _ heq3
      injection heq3 with _ heq4
      injection heq4 with _ heq5
      injection heq5 with hrecEq _
      exact hrecEq.symm

theorem create2Suffix_nonempty_of_next {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hc2 : isCreate2Op fr = true)
    (hstep : stepFrame fr = .next exec) :
    ∃ rec dS', dS = rec :: dS' := by
  have hng : isGasOp fr = false := isGasOp_false_of_isCreate2Op hc2
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hc2, List.isEmpty_nil, Bool.and_true,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] []
      [softFailCreateRecord fr]] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      simp only [Except.map, List.nil_append, List.singleton_append] at hf
      injection hf with htuple
      exact ⟨softFailCreateRecord fr, dS',
        (congrArg (fun x => x.2.2.2) htuple).symm⟩

theorem callSuffix_nonempty_of_next {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hcall : isCallOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    ∃ rec cS', cS = rec :: cS' := by
  have hng : isGasOp fr = false := isGasOp_false_of_isCallOp hcall
  have hnc : isCreate2Op fr = false := isCreate2Op_false_of_isCallOp hcall
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hnc, hcall, List.isEmpty_nil, Bool.and_true,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) []
      [softFailCallRecord fr] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      simp only [Except.map, List.nil_append, List.singleton_append] at hf
      injection hf with htuple
      exact ⟨softFailCallRecord fr, cS',
        (congrArg (fun x => x.2.2.1) htuple).symm⟩

theorem recorderCoupled_call_softfail {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {rec : CallRecord} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS (rec :: cS) dS)
    (hcall : isCallOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS cS dS
    ∧ rec = softFailCallRecord fr := by
  have hng : isGasOp fr = false := isGasOp_false_of_isCallOp hcall
  have hnc : isCreate2Op fr = false := isCreate2Op_false_of_isCallOp hcall
  obtain ⟨⟨f, hf⟩, hgp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hnc, hcall, List.isEmpty_nil, Bool.and_true,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) []
      [softFailCallRecord fr] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', softFailCallRecord fr :: cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, rec :: cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgSeq hf5
      injection hf5 with hcEq hdEq
      injection hcEq with hreq hcSeq
      subst hobs; subst hgSeq; subst hcSeq; subst hdEq
      refine ⟨⟨⟨m, hX⟩, hgp, ?_, hdp⟩, hreq.symm⟩
      obtain ⟨pre, hpre⟩ := hcpp
      exact ⟨pre ++ [rec], by rw [hpre, List.append_assoc, List.singleton_append]⟩

theorem recorderCoupled_create_softfail {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS (rec :: dS))
    (hc2 : isCreate2Op fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS cS dS
    ∧ rec = softFailCreateRecord fr := by
  have hng : isGasOp fr = false := isGasOp_false_of_isCreate2Op hc2
  obtain ⟨⟨f, hf⟩, hgp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hc2, List.isEmpty_nil, Bool.and_true,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] []
      [softFailCreateRecord fr]] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', cS', softFailCreateRecord fr :: dS')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, cS, rec :: dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgSeq hf5
      injection hf5 with hcEq hdEq
      injection hdEq with hreq hdSeq
      subst hobs; subst hgSeq; subst hcEq; subst hdSeq
      refine ⟨⟨⟨m, hX⟩, hgp, hcpp, ?_⟩, hreq.symm⟩
      obtain ⟨pre, hpre⟩ := hdp
      exact ⟨pre ++ [rec], by rw [hpre, List.append_assoc, List.singleton_append]⟩

private theorem recorderCoupled_halted_inv {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h) :
    gS = [] ∧ cS = [] ∧ dS = [] ∧ log.observable = endFrame fr h := by
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep] at hf
    -- `hf : driveLog m [] (.inr (endFrame fr h)) [] [] [] = .ok (log.observable, …)`.
    cases m with
    | zero => simp [driveLog] at hf
    | succ k =>
      unfold driveLog at hf
      simp only [Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨hobs, hg, hc, hd⟩ := hf
      exact ⟨hg.symm, hc.symm, hd.symm, hobs.symm⟩

theorem recorderCoupled_halted_suffixes_nil {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h) :
    gS = [] ∧ cS = [] ∧ dS = [] := by
  obtain ⟨hg, hc, hd, _⟩ := recorderCoupled_halted_inv hcp hstep
  exact ⟨hg, hc, hd⟩

theorem creates_nil_of_stepFrame_halted {log : RunLog} {fr : Frame} {halt : Evm.FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted halt) :
    dS = [] :=
  (recorderCoupled_halted_suffixes_nil hcp hstep).2.2

theorem calls_nil_of_stepFrame_halted {log : RunLog} {fr : Frame} {halt : Evm.FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted halt) :
    cS = [] :=
  (recorderCoupled_halted_suffixes_nil hcp hstep).2.1

theorem recorderCoupled_call_extract {log : RunLog} {callFr : Frame}
    {cp : CallParams} {pending : PendingCall} {child : Frame}
    {gS : List Word} {rec : CallRecord} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log callFr gS (rec :: cS) dS)
    (hstep : stepFrame callFr = .needsCall cp pending)
    (hcode : beginCall cp = .inl child) :
    ∃ childRes : FrameResult,
        CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending)
      ∧ rec = { result := childRes.toCallResult, pending := pending }
      ∧ RecorderCoupled log (Evm.resumeAfterCall childRes.toCallResult pending) gS cS dS := by
  obtain ⟨childRes, hchild_seed⟩ := child_terminates hcode
  have hcr : CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending) :=
    ⟨cp, pending, child, childRes, hstep, hcode, hchild_seed, rfl⟩
  refine ⟨childRes, hcr, ?_, recorderCoupled_call hcp hcr⟩
  -- The record identity: peel the restart equation (as `recorderCoupled_call`, but keep the head).
  obtain ⟨⟨fuel', hrestart⟩, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl callFr) [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode]
    rw [hdescent] at hrestart
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.call pending :: []) (running child) ≠ .error .OutOfFuel := by
      rw [hdrive]; simp
    have hchildm_ne : drive m [] (running child) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m child (.call pending) [] hne
    have hchildm : drive m [] (running child) = .ok childRes :=
      drive_ok_agree [] (running child) hchildm_ne hchild_seed
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) []
            [{ result := childRes.toCallResult, pending := pending }] [] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) []
      [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
    cases hbok : driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] []
      with
    | error e => rw [hbok] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', cS'', dS''⟩ := val
      rw [hbok] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'', [] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, rec :: cS, dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with _ heq3
      injection heq3 with _ heq4
      injection heq4 with hcons _
      injection hcons with hrecEq _
      exact hrecEq.symm

theorem recorderCoupled_stepsTo_other {log : RunLog} {fr fr' : Frame}
    {gS : List Word} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hng : isGasOp fr = false)
    (hnc : isCreate2Op fr = false)
    (hncall : isCallOp fr = false)
    (hstep : StepsTo fr fr') :
    RecorderCoupled log fr' gS cS dS := by
  obtain ⟨hs, hfr'⟩ := hstep
  rw [hfr']
  exact recorderCoupled_step_other hcp hng hnc hncall hs

theorem recorderCoupled_halted_observable {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h) :
    log.observable = endFrame fr h :=
  (recorderCoupled_halted_inv hcp hstep).2.2.2

theorem recorderCoupled_halted_leftovers_nil {log : RunLog} {self : AccountAddress}
    {fr : Frame} {h : FrameHalt}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    {Tleft : GasOracle} {Cleft : CallStream} {Dleft : CreateStream}
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstep : stepFrame fr = .halted h)
    (hT : Tleft = gS) (hC : Cleft = callStreamOf cS self)
    (hD : Dleft = createStreamOf dS self) :
    Tleft = [] ∧ Cleft = [] ∧ Dleft = [] := by
  obtain ⟨hg, hc, hd⟩ := recorderCoupled_halted_suffixes_nil hcp hstep
  subst hg; subst hc; subst hd
  exact ⟨hT, by simp [hC, callStreamOf], by simp [hD, createStreamOf]⟩

end BytecodeLayer.Exec.CyclicSim
