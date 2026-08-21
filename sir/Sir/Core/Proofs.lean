import Sir.Core.Spec
import Sir.Core.Proofs.Bump

namespace Sir

namespace Trace.QueryDivergence

theorem extend {trace₁ trace₂ : Trace} (suffix₁ suffix₂ : Trace)
    (h : Trace.QueryDivergence trace₁ trace₂) :
    Trace.QueryDivergence (trace₁ ++ suffix₁) (trace₂ ++ suffix₂) := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, hquery⟩ := h
  exact ⟨pre, event₁, rest₁ ++ suffix₁, event₂, rest₂ ++ suffix₂,
    by simp, by simp, hne, hquery⟩

theorem appendLeft {trace₁ trace₂ : Trace} (pre : Trace)
    (h : Trace.QueryDivergence trace₁ trace₂) :
    Trace.QueryDivergence (pre ++ trace₁) (pre ++ trace₂) := by
  obtain ⟨common, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, hquery⟩ := h
  exact ⟨pre ++ common, event₁, rest₁, event₂, rest₂,
    by simp, by simp, hne, hquery⟩

theorem singleton {event₁ event₂ : Event} (hne : event₁ ≠ event₂)
    (hquery : event₁.query = event₂.query) :
    QueryDivergence [event₁] [event₂] := by
  exact ⟨[], event₁, [], event₂, [], rfl, rfl, hne, hquery⟩

end Trace.QueryDivergence

namespace FunctionOutcome

theorem toControl_inj {outcome₁ outcome₂ : FunctionOutcome}
    (h : outcome₁.toControl = outcome₂.toControl) : outcome₁ = outcome₂ := by
  cases outcome₁ <;> cases outcome₂ <;> simp_all [toControl]

end FunctionOutcome

namespace Globals

theorem storeStorage_dialogue (globals : Globals) (context : CallContext)
    (key value : Word) :
    globals.storeStorage context key value = globals.storeStorage context key value := rfl

theorem gas_dialogue (answer₁ answer₂ : Word) :
    answer₁ = answer₂ ∨ Trace.QueryDivergence [.gas answer₁] [.gas answer₂] := by
  by_cases h : answer₁ = answer₂
  · exact .inl h
  · exact .inr (Trace.QueryDivergence.singleton (fun heq => h (Event.gas.inj heq)) rfl)

theorem call_dialogue (globals : Globals) (target gas : Word)
    (answer₁ answer₂ : CallResult) :
    (answer₁ = answer₂ ∧ globals.applyCall answer₁ = globals.applyCall answer₂) ∨
      Trace.QueryDivergence
        [.call { input := globals.callInput target gas, result := answer₁ }]
        [.call { input := globals.callInput target gas, result := answer₂ }] := by
  by_cases h : answer₁ = answer₂
  · subst answer₂
    exact .inl ⟨rfl, rfl⟩
  · exact .inr (Trace.QueryDivergence.singleton
      (fun heq => h (congrArg CallRecord.result (Event.call.inj heq))) rfl)

theorem pushAlloc_dialogue (globals : Globals) {allocation₁ allocation₂ : Allocation}
    (h : allocation₁ = allocation₂) :
    globals.pushAlloc allocation₁ = globals.pushAlloc allocation₂ := by
  cases h
  rfl

theorem writeWord32_dialogue (globals : Globals) (offset value : Word) :
    globals.writeWord32 offset value = globals.writeWord32 offset value := rfl

theorem readWord32_dialogue (globals : Globals) (offset : Word)
    (assumed₁ assumed₂ : Vector UInt8 32)
    (h : globals.readWord32 offset assumed₁ = globals.readWord32 offset assumed₂) :
    globals.readWord32 offset assumed₁ = globals.readWord32 offset assumed₂ := h

end Globals

end Sir
