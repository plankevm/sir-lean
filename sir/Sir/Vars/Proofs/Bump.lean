import Sir.Vars.Proofs.Readiness

namespace Sir

variable {program : Vars.Program} {ctx : CallContext}

theorem Vars.Proofs.Program.WellFormed.progress_reachable_nonIcall_bump
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : Vars.State}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', Vars.SmallStep program ctx state trace state' := by
  refine Vars.Proofs.Program.WellFormed.progress_reachable_nonIcall hwf hrun hcontrol ?_ hstore
  constructor
  · intro nextControl result size word hstmt hword
    exact ⟨state.globals.memory.bumpAlloc word.toNat,
      state.globals.memory.isValidNewAlloc_bumpAlloc word.toNat
        (hspace.1 nextControl result size word hstmt hword),
      state.globals.memory.bumpAlloc_size word.toNat,
      state.globals.memory.bumpAlloc_bytes word.toNat⟩
  · intro nextControl result size word hstmt hword
    exact ⟨state.globals.memory.bumpAlloc word.toNat,
      state.globals.memory.isValidNewAlloc_bumpAlloc word.toNat
        (hspace.2 nextControl result size word hstmt hword),
      state.globals.memory.bumpAlloc_size word.toNat⟩

theorem Vars.Proofs.Program.WellFormed.progress
    (hwf : program.WellFormed) {state : Vars.State}
    (ready : program.ReadyState ctx state) :
    ∃ trace state', Vars.SmallStep program ctx state trace state' := by
  obtain ⟨⟨function, globals, args, runTrace, hrun⟩, hcontrol,
    hfreshAllocation | hspace, hstore⟩ := ready
  · exact Vars.Proofs.Program.WellFormed.progress_reachable_nonIcall
      hwf hrun hcontrol hfreshAllocation hstore
  · exact Vars.Proofs.Program.WellFormed.progress_reachable_nonIcall_bump
      hwf hrun hcontrol hspace hstore

end Sir

