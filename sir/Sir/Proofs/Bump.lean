import Sir.Proofs.Memory
import Sir.Proofs.Readiness

namespace Sir

namespace MemoryState

def ZeroAboveWatermark (m : MemoryState) : Prop :=
  ∀ address, m.watermark ≤ address → m.readByte address = 0

theorem zeroAboveWatermark_empty : MemoryState.empty.ZeroAboveWatermark := by
  intro address _
  rfl

private theorem le_foldl_max (l : List Allocation) (init : Nat) :
    init ≤ l.foldl (fun watermark allocation => max watermark allocation.endExclusive) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl init
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left init head.endExclusive) (ih _)

private theorem mem_le_foldl_max (l : List Allocation) (init : Nat) :
    ∀ a ∈ l,
      a.endExclusive ≤
        l.foldl (fun watermark allocation => max watermark allocation.endExclusive) init := by
  induction l generalizing init with
  | nil => intro a ha; cases ha
  | cons head tail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.le_trans (Nat.le_max_right init a.endExclusive) (le_foldl_max tail _)
      · exact ih _ a ha

theorem endExclusive_le_watermark (m : MemoryState) {a : Allocation}
    (ha : a ∈ m.provisioned) : a.endExclusive ≤ m.watermark := by
  rw [watermark, ← Array.foldl_toList]
  exact mem_le_foldl_max m.provisioned.toList 0 a (Array.mem_def.mp ha)

theorem watermark_push (m : MemoryState) (a : Allocation) :
    (m.push a).watermark = max m.watermark a.endExclusive := by
  simp [MemoryState.watermark, MemoryState.push]

theorem zeroAboveWatermark_push {m : MemoryState} (a : Allocation)
    (h : m.ZeroAboveWatermark) : (m.push a).ZeroAboveWatermark := by
  intro address haddress
  rw [watermark_push] at haddress
  change (m.push a).store address = 0
  rw [store_push]
  exact h address (Nat.le_trans (Nat.le_max_left _ _) haddress)

theorem zeroAboveWatermark_writeBytes {m : MemoryState} {offset : Word}
    {bytes : ByteArray} (h : m.ZeroAboveWatermark)
    (hin : m.InBounds offset.toNat bytes.size) :
    (m.writeBytes offset bytes).ZeroAboveWatermark := by
  intro address haddress
  have hwatermark : (m.writeBytes offset bytes).watermark = m.watermark := by
    simp only [MemoryState.watermark, provisioned_writeBytes]
  rw [hwatermark] at haddress
  obtain ⟨a, ha, _, hend⟩ := hin
  have hwriteEnd : offset.toNat + bytes.size ≤ m.watermark :=
    Nat.le_trans hend (m.endExclusive_le_watermark ha)
  rw [readByte_writeBytes, if_neg]
  · exact h address haddress
  · intro hrange
    omega

theorem bumpAllocation_size (m : MemoryState) (size : Nat) :
    (m.bumpAllocation size).size = size := by
  rfl

theorem isValidNewAlloc_bumpAllocation (m : MemoryState) (size : Nat)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    m.IsValidNewAlloc (m.bumpAllocation size) := by
  have hbound : Evm.UInt256.size = 2 ^ 256 := rfl
  have hstart : (m.bumpAllocation size).start = m.watermark % 2 ^ 256 := by
    simp [bumpAllocation, Allocation.start, Evm.UInt256.toNat_ofNat]
  have hend : (m.bumpAllocation size).endExclusive = m.watermark % 2 ^ 256 + size := by
    rw [Allocation.endExclusive, hstart, bumpAllocation_size]
  rw [hbound] at hspace
  rcases Nat.lt_or_ge m.watermark (2 ^ 256) with hlt | hge
  · have hmod : m.watermark % 2 ^ 256 = m.watermark := Nat.mod_eq_of_lt hlt
    refine ⟨by rw [hend, hmod, hbound]; exact hspace, ?_⟩
    intro a' ha'
    exact Or.inr (by rw [hstart, hmod]; exact m.endExclusive_le_watermark ha')
  · have hwatermark : m.watermark = 2 ^ 256 := Nat.le_antisymm (by omega) hge
    have hsize : size = 0 := by omega
    have hend' : (m.bumpAllocation size).endExclusive = 0 := by
      rw [hend, hwatermark, hsize, Nat.mod_self]
    exact ⟨by rw [hend']; exact Nat.zero_le _,
      fun a' _ => Or.inl (by rw [hend']; exact Nat.zero_le _)⟩

theorem readBytes_push_bumpAllocation (m : MemoryState) (size : Nat)
    (hzero : m.ZeroAboveWatermark)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    (m.push (m.bumpAllocation size)).readBytes (m.bumpAllocation size).offset size =
      ⟨Array.replicate size 0⟩ := by
  have hbound : Evm.UInt256.size = 2 ^ 256 := rfl
  rw [hbound] at hspace
  rcases Nat.lt_or_ge m.watermark (2 ^ 256) with hlt | hge
  · have hoffsetMod :
        (m.bumpAllocation size).offset.toNat = m.watermark % 2 ^ 256 := by
      simp [MemoryState.bumpAllocation, Evm.UInt256.toNat_ofNat]
    have hoffset : (m.bumpAllocation size).offset.toNat = m.watermark := by
      rw [hoffsetMod, Nat.mod_eq_of_lt hlt]
    have hreads :
        (List.range size).map
            (fun index =>
              (m.push (m.bumpAllocation size)).readByte
                ((m.bumpAllocation size).offset.toNat + index)) =
          List.replicate size 0 := by
      have hall : ∀ index ∈ List.range size,
          (m.push (m.bumpAllocation size)).readByte
            ((m.bumpAllocation size).offset.toNat + index) = 0 := by
        intro index _
        change (m.push (m.bumpAllocation size)).store
          ((m.bumpAllocation size).offset.toNat + index) = 0
        rw [store_push]
        exact hzero _ (by rw [hoffset]; omega)
      simpa using List.map_eq_replicate_iff.mpr hall
    unfold MemoryState.readBytes
    apply ByteArray.ext
    simp only [List.data_toByteArray]
    rw [← List.toArray_replicate]
    exact congrArg List.toArray hreads
  · have hsize : size = 0 := by omega
    subst size
    unfold MemoryState.readBytes
    apply ByteArray.ext
    simp

end MemoryState

namespace Generic.MemoryPolicy

theorem bump_deterministic_proof : bump.Deterministic := by
  intro memory size allocation₁ allocation₂ h₁ h₂
  rw [h₁.2, h₂.2]

theorem bump_sound_proof : bump.Sound := by
  intro memory size allocation h
  rw [h.2]
  exact ⟨memory.isValidNewAlloc_bumpAllocation size h.1,
    memory.bumpAllocation_size size⟩

theorem bump_satisfiable_proof : bump.Satisfiable := by
  intro memory size hspace
  exact ⟨memory.bumpAllocation size, hspace, rfl⟩

theorem permissive_not_deterministic_proof : ¬ permissive.Deterministic := by
  intro hdet
  have h₁ : permissive.Allows MemoryState.empty 0 { offset := 1, size := 0 } := by
    refine ⟨⟨?_, by simp [MemoryState.empty]⟩, rfl⟩
    decide
  have h₂ : permissive.Allows MemoryState.empty 0 { offset := 2, size := 0 } := by
    refine ⟨⟨?_, by simp [MemoryState.empty]⟩, rfl⟩
    decide
  have heq := hdet MemoryState.empty 0 { offset := 1, size := 0 }
    { offset := 2, size := 0 } h₁ h₂
  cases heq

theorem permissive_sound_proof : permissive.Sound := by
  intro _ _ _ h
  exact h

theorem permissive_satisfiable_proof : permissive.Satisfiable := by
  intro memory size hspace
  exact ⟨memory.bumpAllocation size,
    memory.isValidNewAlloc_bumpAllocation size hspace,
    memory.bumpAllocation_size size⟩

end Generic.MemoryPolicy

variable {program : Program} {policy : Generic.MemoryPolicy} {ctx : CallContext}

theorem Program.WellFormed.progress_reachable_nonIcall_of_satisfiable_proof
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hsound : policy.Sound) (hsatisfiable : policy.Satisfiable)
    (hrun : program.RunsFunction policy ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program policy ctx state trace state' := by
  refine hwf.progress_reachable_nonIcall_proof hrun hcontrol ?_ hstore
  intro nextControl result size word hdecode hword
  obtain ⟨allocation, hallows⟩ := hsatisfiable state.globals.memory word.toNat
    (hspace nextControl result size word hdecode hword)
  exact ⟨allocation, hallows, hsound state.globals.memory word.toNat allocation hallows⟩

theorem Program.WellFormed.progress_reachable_nonIcall_bump_proof
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hrun : program.RunsFunction Generic.MemoryPolicy.bump ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program Generic.MemoryPolicy.bump ctx state trace state' :=
  hwf.progress_reachable_nonIcall_of_satisfiable_proof
    Generic.MemoryPolicy.bump_sound_proof Generic.MemoryPolicy.bump_satisfiable_proof
    hrun hcontrol hspace hstore

end Sir
