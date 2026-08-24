import Sir.Stack.Proofs.Readiness

namespace Sir.Stack

variable {program : Program} {ctx : CallContext}

theorem Proofs.Program.WellFormed.progress_reachable_nonIcall_bump
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : State}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  refine Proofs.Program.WellFormed.progress_reachable_nonIcall hwf hrun hcontrol ?_ hstore
  constructor
  · intro next size hinstr hfetch
    exact ⟨state.globals.memory.bumpAlloc size.toNat,
      state.globals.memory.isValidNewAlloc_bumpAlloc size.toNat
        (hspace.1 next size hinstr hfetch),
      state.globals.memory.bumpAlloc_size size.toNat,
      state.globals.memory.bumpAlloc_bytes size.toNat⟩
  · intro next size hinstr hfetch
    exact ⟨state.globals.memory.bumpAlloc size.toNat,
      state.globals.memory.isValidNewAlloc_bumpAlloc size.toNat
        (hspace.2 next size hinstr hfetch),
      state.globals.memory.bumpAlloc_size size.toNat⟩

theorem Proofs.Program.WellFormed.progress (hwf : program.WellFormed) {state : State}
    (ready : program.ReadyState ctx state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  obtain ⟨⟨function, globals, args, runTrace, hrun⟩, hcontrol,
    hallocation | hspace, hstore⟩ := ready
  · exact Proofs.Program.WellFormed.progress_reachable_nonIcall
      hwf hrun hcontrol hallocation hstore
  · exact Proofs.Program.WellFormed.progress_reachable_nonIcall_bump
      hwf hrun hcontrol hspace hstore

end Sir.Stack
