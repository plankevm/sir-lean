import Sir.Proofs.Steps

namespace Sir

variable {program : Program} {ctx : CallContext}

theorem eval_call_ok
    (call : Call) (result : CallResult) (s : MachineState) (callee gas : Word)
    (hcallee : s.locals.lookup call.callee = .ok callee)
    (hgas : s.locals.lookup call.gas = .ok gas) :
    (eval_call call result).run s =
      .ok ({ input := { target := .ofUInt256 callee, gas := gas, world := s.globals.world }
             result := result },
        { s with
          locals := s.locals.assign call.result (Evm.UInt256.fromBool result.success)
          globals := { s.globals with returnData := result.output, world := result.world' } }) := by
  simp only [eval_call, StateT.run, hcallee, hgas, bind, Except.bind]

theorem eval_call_record_result
    {call : Call} {result : CallResult} {s state' : MachineState} {record : CallRecord}
    (h : (eval_call call result).run s = .ok (record, state')) :
    record.result = result := by
  cases hcallee : s.locals.lookup call.callee <;>
    cases hgas : s.locals.lookup call.gas <;>
    simp only [eval_call, StateT.run, hcallee, hgas, bind, Except.bind] at h
  all_goals try contradiction
  injection h with hrecord
  exact (congrArg CallRecord.result (Prod.mk.inj hrecord).1).symm

theorem eval_call_record_input
    {call : Call} {result : CallResult} {s state' : MachineState} {record : CallRecord}
    (h : (eval_call call result).run s = .ok (record, state')) :
    ∃ callee gas,
      s.locals.lookup call.callee = .ok callee ∧
      s.locals.lookup call.gas = .ok gas ∧
      record.input = { target := .ofUInt256 callee, gas := gas, world := s.globals.world } := by
  cases hcallee : s.locals.lookup call.callee <;>
    cases hgas : s.locals.lookup call.gas <;>
    simp only [eval_call, StateT.run, hcallee, hgas, bind, Except.bind] at h
  all_goals try contradiction
  injection h with hrecord
  exact ⟨_, _, rfl, rfl, (congrArg CallRecord.input (Prod.mk.inj hrecord).1).symm⟩

theorem smallStep_assign_det
    {state s₁ s₂ : MachineState} {result : VarId} {expr : Expr}
    (h₁ : eval_assign ctx state result expr = .ok s₁)
    (h₂ : eval_assign ctx state result expr = .ok s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Except.ok.inj h₂

theorem smallStep_sstore_det
    {state s₁ s₂ : MachineState} {key value : VarId}
    (h₁ : eval_sstore ctx state key value = .ok s₁)
    (h₂ : eval_sstore ctx state key value = .ok s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Except.ok.inj h₂

theorem smallStep_gas_det
    {result : VarId} {g₁ g₂ : Word} {state s₁ s₂ : MachineState}
    (ht : ([Event.gas g₁] : Trace) = [.gas g₂])
    (h₁ : (eval_gas result g₁).run state = .ok ((), s₁))
    (h₂ : (eval_gas result g₂).run state = .ok ((), s₂)) : s₁ = s₂ := by
  have hg : g₁ = g₂ := Event.gas.inj (List.cons.inj ht).1
  subst hg
  rw [h₁] at h₂
  exact (Prod.mk.inj (Except.ok.inj h₂)).2

theorem smallStep_call_det
    {call : Call} {r₁ r₂ : CallResult} {rec₁ rec₂ : CallRecord}
    {state s₁ s₂ : MachineState}
    (ht : ([Event.call rec₁] : Trace) = [.call rec₂])
    (h₁ : (eval_call call r₁).run state = .ok (rec₁, s₁))
    (h₂ : (eval_call call r₂).run state = .ok (rec₂, s₂)) : s₁ = s₂ := by
  have hrec : rec₁ = rec₂ := Event.call.inj (List.cons.inj ht).1
  have hresult : r₁ = r₂ := by
    calc
      r₁ = rec₁.result := (eval_call_record_result h₁).symm
      _ = rec₂.result := congrArg CallRecord.result hrec
      _ = r₂ := eval_call_record_result h₂
  subst hresult
  subst hrec
  rw [h₁] at h₂
  exact (Prod.mk.inj (Except.ok.inj h₂)).2

theorem smallStep_mstore32_det
    {offset value : VarId} {state s₁ s₂ : MachineState}
    (h₁ : (eval_mstore32 offset value).run state = .ok ((), s₁))
    (h₂ : (eval_mstore32 offset value).run state = .ok ((), s₂)) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact (Prod.mk.inj (Except.ok.inj h₂)).2

theorem smallStep_terminator_det
    {term : Terminator} {state s₁ s₂ : MachineState}
    (h₁ : (eval_terminator program term).run state = .ok ((), s₁))
    (h₂ : (eval_terminator program term).run state = .ok ((), s₂)) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact (Prod.mk.inj (Except.ok.inj h₂)).2

theorem smallStep_call_constructor_det
    {state state₁ state₂ : MachineState}
    {next₁ next₂ : MachineControl} {call₁ call₂ : Call}
    {result₁ result₂ : CallResult} {record₁ record₂ : CallRecord}
    (hstmt₁ : program.decodeStmt state.control = some (next₁, .call call₁))
    (heval₁ : (eval_call call₁ result₁).run state = .ok (record₁, state₁))
    (hstmt₂ : program.decodeStmt state.control = some (next₂, .call call₂))
    (heval₂ : (eval_call call₂ result₂).run state = .ok (record₂, state₂))
    (ht : ([Event.call record₁] : Trace) = [.call record₂]) :
    { state₁ with control := next₁ } = { state₂ with control := next₂ } := by
  have hdecoded : (next₁, Stmt.call call₁) = (next₂, Stmt.call call₂) :=
    Option.some.inj (hstmt₁.symm.trans hstmt₂)
  have hnext : next₁ = next₂ := congrArg Prod.fst hdecoded
  have hcall : call₁ = call₂ := Stmt.call.inj (congrArg Prod.snd hdecoded)
  subst hnext
  subst hcall
  have hstate : state₁ = state₂ := smallStep_call_det ht heval₁ heval₂
  subst hstate
  rfl

end Sir
