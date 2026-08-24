import Sir.Core.Spec
import Sir.Core.Proofs.Bump

namespace Sir

namespace Trace

theorem getElem?_append_cons (pre : Trace) (event : Event) (rest : Trace) :
    (pre ++ event :: rest)[pre.length]? = some event := by
  simp

end Trace

namespace Trace.QueryDivergence

theorem ne {trace₁ trace₂ : Trace}
    (h : Trace.QueryDivergence trace₁ trace₂) : trace₁ ≠ trace₂ := by
  obtain ⟨pre, event₁, rest₁, event₂, rest₂, rfl, rfl, hne, -⟩ := h
  intro heq
  exact hne (List.cons.inj (List.append_cancel_left heq)).1

theorem query_eq {trace₁ trace₂ : Trace}
    (hdiv : Trace.QueryDivergence trace₁ trace₂)
    {pre : Trace} {event₁ event₂ : Event} {rest₁ rest₂ : Trace}
    (h₁ : trace₁ = pre ++ event₁ :: rest₁) (h₂ : trace₂ = pre ++ event₂ :: rest₂) :
    event₁.query = event₂.query := by
  obtain ⟨common, a, ra, b, rb, hpa, hpb, hne, hq⟩ := hdiv
  have gA1 : trace₁[pre.length]? = some event₁ := by rw [h₁]; exact getElem?_append_cons ..
  have gA2 : trace₁[common.length]? = some a := by rw [hpa]; exact getElem?_append_cons ..
  have gB1 : trace₂[pre.length]? = some event₂ := by rw [h₂]; exact getElem?_append_cons ..
  have gB2 : trace₂[common.length]? = some b := by rw [hpb]; exact getElem?_append_cons ..
  rcases Nat.lt_trichotomy pre.length common.length with hlt | hlen | hgt
  · have c₁ : trace₁[pre.length]? = common[pre.length]? := by
      rw [hpa]; exact List.getElem?_append_left hlt
    have c₂ : trace₂[pre.length]? = common[pre.length]? := by
      rw [hpb]; exact List.getElem?_append_left hlt
    obtain rfl : event₁ = event₂ :=
      Option.some.inj ((c₁.symm.trans gA1).symm.trans (c₂.symm.trans gB1))
    rfl
  · obtain rfl : event₁ = a := Option.some.inj ((hlen ▸ gA1).symm.trans gA2)
    obtain rfl : event₂ = b := Option.some.inj ((hlen ▸ gB1).symm.trans gB2)
    exact hq
  · have c₁ : trace₁[common.length]? = pre[common.length]? := by
      rw [h₁]; exact List.getElem?_append_left hgt
    have c₂ : trace₂[common.length]? = pre[common.length]? := by
      rw [h₂]; exact List.getElem?_append_left hgt
    exact absurd
      (Option.some.inj ((c₁.symm.trans gA2).symm.trans (c₂.symm.trans gB2))) hne

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
