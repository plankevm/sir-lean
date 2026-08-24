import Sir.Stack.Proofs.Statics

namespace Sir.Stack

variable {program : Program} {ctx : CallContext}

theorem Proofs.progress_current
    {state : State} (hready : program.CurrentReady ctx state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  rcases hready with
    ⟨next, instruction, hinstr, hnonIcall, hfire⟩ | ⟨terminator, environment, finalControl, hterm, heval⟩
  · rcases hfire with
        ⟨globals, environment, heval⟩ |
        ⟨answer, environment, hop, hpush⟩ |
        ⟨target, gasLimit, environment, hop, hfetch, hpush⟩ |
        ⟨size, allocation, environment, hop, hfetch, hallow, hzero, hpush⟩ |
        ⟨size, allocation, environment, hop, hfetch, hallow, hpush⟩ |
        ⟨offset, value, environment, hop, hfetch, hbound, hpush⟩ |
        ⟨offset, assumed, environment, hop, hfetch, hpush⟩
    · exact ⟨[], _, .evaluate hinstr heval⟩
    · subst hop
      exact ⟨[.gas answer], _, .gas hinstr hpush⟩
    · subst hop
      let answer : CallResult :=
        { world' := state.globals.world, success := true, output := ByteArray.empty }
      exact ⟨[.call { input := state.globals.callInput target gasLimit, result := answer }],
        _, .call (answer := answer) hinstr hfetch hpush⟩
    · subst hop
      exact ⟨[], _, .malloc hinstr hfetch hallow hzero hpush⟩
    · subst hop
      exact ⟨[], _, .mallocUninit hinstr hfetch hallow hpush⟩
    · subst hop
      exact ⟨[], _, .mstore32 hinstr hfetch hbound hpush⟩
    · subst hop
      exact ⟨[], _, .mload32 (assumed := assumed) hinstr hfetch hpush⟩
  · exact ⟨[], _, .control hterm heval⟩

theorem Proofs.Program.WellFormed.progress
    (_hwf : program.WellFormed) {state : State}
    (ready : program.ReadyState ctx state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  obtain ⟨_, hcurrent, _, _⟩ := ready
  exact Proofs.progress_current hcurrent

end Sir.Stack
