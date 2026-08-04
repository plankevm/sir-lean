import Sir.Proofs.Decode
import Sir.Spec.WellFormed

namespace Sir

variable {program : Program} {ctx : CallContext}

@[elab_as_elim]
theorem Steps.inductionOn {program : Program} {ctx : CallContext}
    {motive : (s : MachineState) → (t : Trace) → (e : MachineState) →
      Steps program ctx s t e → Prop}
    (refl : ∀ s, motive s [] s .refl)
    (tail : ∀ {s mid s' : MachineState} {t₁ t₂ : Trace}
      (start : Steps program ctx s t₁ mid) (next : SmallStep program ctx mid t₂ s'),
      motive s t₁ mid start → motive s (t₁ ++ t₂) s' (start.tail next))
    {s : MachineState} {t : Trace} {e : MachineState}
    (h : Steps program ctx s t e) : motive s t e h := by
  refine Steps.rec (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun a ta b hh => motive a ta b hh)
      (motive_3 := fun _ _ _ _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?refl ?tail ?_ ?_ h
  case refl => intro a; exact refl a
  case tail => intro a m b ta tb start next ih _; exact tail start next ih
  all_goals intros; trivial

theorem Steps.single {program : Program} {ctx : CallContext}
    {s s' : MachineState} {t : Trace}
    (step : SmallStep program ctx s t s') : Steps program ctx s t s' :=
  Steps.tail Steps.refl step

theorem Steps.trans {program : Program} {ctx : CallContext}
    {s mid s' : MachineState} {t₁ t₂ : Trace}
    (h₁ : Steps program ctx s t₁ mid) (h₂ : Steps program ctx mid t₂ s') :
    Steps program ctx s (t₁ ++ t₂) s' := by
  induction h₂ using Steps.inductionOn with
  | refl => simpa using h₁
  | tail start next ih => simpa [List.append_assoc] using Steps.tail (ih h₁) next

theorem Steps.head {program : Program} {ctx : CallContext}
    {s mid s' : MachineState} {t₁ t₂ : Trace}
    (step : SmallStep program ctx s t₁ mid) (rest : Steps program ctx mid t₂ s') :
    Steps program ctx s (t₁ ++ t₂) s' :=
  Steps.trans (Steps.single step) rest
def Stuck (program : Program) (ctx : CallContext) (s : MachineState) : Prop :=
  ∀ t s', ¬ SmallStep program ctx s t s'

theorem stuck_of_returned
    {state : MachineState} {rs : Array Word} (hctrl : state.control = .returned rs) :
    Stuck program ctx state := by
  intro t s' hstep
  cases hstep <;> simp_all [Program.decodeStmt, Program.terminatorAt]

theorem stuck_of_halted
    {state : MachineState} (hctrl : state.control = .halted) :
    Stuck program ctx state := by
  intro t s' hstep
  cases hstep <;> simp_all [Program.decodeStmt, Program.terminatorAt]

theorem Steps.head_decomp
    {s e : MachineState} {t : Trace} (h : Steps program ctx s t e) :
    (s = e ∧ t = []) ∨
      ∃ mid t₁ t₂, SmallStep program ctx s t₁ mid ∧ Steps program ctx mid t₂ e ∧
        t = t₁ ++ t₂ := by
  induction h using Steps.inductionOn with
  | refl => exact .inl ⟨rfl, rfl⟩
  | tail start next ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨mid, u₁, u₂, step, rest, rfl⟩
    · exact .inr ⟨_, _, [], next, .refl, by simp⟩
    · exact .inr ⟨mid, u₁, u₂ ++ _, step, rest.tail next, by simp⟩

theorem Steps.eq_of_stuck
    {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e) (hs : Stuck program ctx s) : e = s ∧ t = [] := by
  rcases h.head_decomp with ⟨rfl, rfl⟩ | ⟨mid, t₁, t₂, step, -, -⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd step (hs t₁ mid)

private theorem eval_jump_control
    {s s' : MachineState} {target : BlockId}
    (h : (eval_jump program target).run s = .ok ((), s')) :
    ∃ cursor targetBlock, s.control = .running cursor ∧
      program.block? { cursor with block := target } = some targetBlock ∧
      s'.control = .running
        { cursor with block := target, position := targetBlock.startPosition } := by
  cases hctrl : s.control with
  | returned rs =>
    simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
      getThe, MonadStateOf.get, hctrl, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hsrc : program.block? cursor with
    | none =>
      simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
        getThe, MonadStateOf.get, hctrl, hsrc, Function.comp, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some sourceBlock =>
      cases htgt : program.block? { cursor with block := target } with
      | none =>
        simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hsrc, htgt, Function.comp, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
      | some targetBlock =>
        refine ⟨cursor, targetBlock, rfl, htgt, ?_⟩
        cases htr : Locals.transfer sourceBlock.outputs targetBlock.inputs s.locals with
        | error e =>
          simp [eval_jump, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, pure, Except.pure, modify, modifyGet,
            MonadStateOf.modifyGet] at h
        | ok res =>
          obtain ⟨⟨⟩, locals'⟩ := res
          simp only [eval_jump, StateT.run, bind, StateT.bind, Except.bind, StateT.get,
            get, getThe, MonadStateOf.get, hctrl, hsrc, htgt, liftM, monadLift,
            MonadLift.monadLift, htr, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
            true_and] at h
          rw [← h]

theorem eval_terminator_iret_inv
    {s s' : MachineState}
    (h : (eval_terminator program .iret).run s = .ok ((), s')) :
    ∃ cursor block rs, s.control = .running cursor ∧
      program.block? cursor = some block ∧
      block.outputs.mapM (s.locals.lookup ·) = .ok rs ∧
      s' = { s with control := .returned rs } := by
  cases hctrl : s.control with
  | returned old =>
    simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | halted =>
    simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
      get, getThe, MonadStateOf.get, hctrl, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, pure, Except.pure] at h
  | running cursor =>
    cases hblock : program.block? cursor with
    | none =>
      simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
        get, getThe, MonadStateOf.get, hctrl, hblock, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, Except.pure] at h
    | some block =>
      cases hrs : block.outputs.mapM (s.locals.lookup ·) with
      | error e =>
        simp [eval_terminator, StateT.run, bind, Except.bind, StateT.bind, StateT.get,
          get, getThe, MonadStateOf.get, hctrl, hblock, hrs, liftM, monadLift,
          MonadLift.monadLift, StateT.lift, pure, Except.pure] at h
      | ok rs =>
        refine ⟨cursor, block, rs, rfl, hblock, hrs, ?_⟩
        simp only [eval_terminator, StateT.run, bind, StateT.bind, StateT.get, get,
          getThe, MonadStateOf.get, hctrl, hblock, liftM, monadLift,
          MonadLift.monadLift, hrs, StateT.lift, Except.bind, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq, true_and] at h
        exact h.symm

theorem SmallStep.preserves_function
    {cursor : ProgramCursor} {s s' : MachineState} {t : Trace}
    (h : SmallStep program ctx s t s')
    (hctrl : s.control = .running cursor) :
    s'.control = .halted ∨ (∃ rs, s'.control = .returned rs) ∨
      ∃ cursor', s'.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  cases h with
  | assign hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | sstore hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | gas hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | call hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mallocUninit hstmt halloc heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mstore32 hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | mload32 hstmt heval =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | icall hstmt hargs hcallee hbind =>
    obtain ⟨pos, rfl⟩ := Program.decodeStmt_next_block hctrl hstmt
    exact .inr (.inr ⟨_, rfl, rfl⟩)
  | icallHalted hstmt hargs hcallee => exact .inl rfl
  | terminator hterm heval =>
    rename_i term
    have hsrc := Program.terminatorAt_inv hctrl hterm
    cases term with
    | halt =>
      have hh : (eval_terminator program .halt).run s =
          .ok ((), { s with control := .halted }) := rfl
      rw [hh] at heval
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj heval)
      exact .inl rfl
    | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
      obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
      exact .inr (.inr ⟨_, hctrl', rfl⟩)
    | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
      cases hcond : s.locals.lookup condition with
      | error e =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        simp at heval
      | ok w =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        by_cases hw : w = 0
        · rw [if_pos hw] at heval
          obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
          obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
          exact .inr (.inr ⟨_, hctrl', rfl⟩)
        · rw [if_neg hw] at heval
          obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
          obtain rfl := MachineControl.running.inj (hsource.symm.trans hctrl)
          exact .inr (.inr ⟨_, hctrl', rfl⟩)
    | iret =>
      obtain ⟨cursor, block, rs, hs, hb, hrs, rfl⟩ := eval_terminator_iret_inv heval
      exact .inr (.inl ⟨rs, rfl⟩)

theorem Steps.preserves_function_proof
    {cursor : ProgramCursor} {s e : MachineState} {t : Trace}
    (h : Steps program ctx s t e)
    (hctrl : s.control = .running cursor) :
    e.control = .halted ∨ (∃ rs, e.control = .returned rs) ∨
      ∃ cursor', e.control = .running cursor' ∧ cursor'.fn = cursor.fn := by
  induction h using Steps.inductionOn with
  | refl => exact .inr (.inr ⟨cursor, hctrl, rfl⟩)
  | tail start next ih =>
    rcases ih hctrl with hmid | ⟨rs, hmid⟩ | ⟨cursor', hctrl', hfn⟩
    · exact absurd next (stuck_of_halted hmid _ _)
    · exact absurd next (stuck_of_returned hmid _ _)
    · rcases next.preserves_function hctrl' with hhalt | hreturned | ⟨cursor'', hctrl'', hfn'⟩
      · exact .inl hhalt
      · exact .inr (.inl hreturned)
      · exact .inr (.inr ⟨cursor'', hctrl'', hfn'.trans hfn⟩)

theorem SmallStep.returned_inv
    {s s' : MachineState} {t : Trace} {rs : Array Word}
    (h : SmallStep program ctx s t s') (hret : s'.control = .returned rs) :
    ∃ cursor block, s.control = .running cursor ∧
      program.block? cursor = some block ∧ block.terminator = .iret ∧
      block.outputs.mapM (s.locals.lookup ·) = .ok rs := by
  cases h with
  | assign hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | sstore hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | gas hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | call hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mallocUninit hstmt halloc heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mstore32 hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | mload32 hstmt heval =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | icall hstmt hargs hcallee hbind =>
    obtain ⟨cursor, rfl⟩ := Program.decodeStmt_next_running hstmt
    cases hret
  | icallHalted hstmt hargs hcallee => cases hret
  | terminator hterm heval =>
    rename_i term
    cases term with
    | halt =>
      simp only [eval_terminator] at heval
      obtain rfl := (Prod.mk.inj (Except.ok.inj heval)).2
      cases hret
    | jump target =>
      simp only [eval_terminator] at heval
      obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
      rw [hctrl'] at hret
      cases hret
    | branch condition thenTarget elseTarget =>
      simp only [eval_terminator] at heval
      cases hcond : s.locals.lookup condition with
      | error e =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        simp at heval
      | ok w =>
        simp only [StateT.run, bind, StateT.bind, Locals.lookupM, liftM, monadLift,
          MonadLift.monadLift, StateT.get, Except.bind, StateT.lift, pure,
          Except.pure, hcond] at heval
        obtain ⟨sourceCursor, targetBlock, hsource, htgt, hctrl'⟩ := eval_jump_control heval
        rw [hctrl'] at hret
        cases hret
    | iret =>
      obtain ⟨cursor, block, actual, hctrl, hblock, houtputs, rfl⟩ :=
        eval_terminator_iret_inv heval
      obtain rfl := MachineControl.returned.inj hret
      cases hpos : cursor.position with
      | statement index => simp [Program.terminatorAt, hctrl, hpos] at hterm
      | terminator =>
        have hblockTerm : block.terminator = .iret := by
          simpa [Program.terminatorAt, hctrl, hpos, hblock] using hterm
        exact ⟨cursor, block, hctrl, hblock, hblockTerm, houtputs⟩

end Sir
