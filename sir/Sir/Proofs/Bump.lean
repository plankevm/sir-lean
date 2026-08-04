import Sir.Proofs.Memory
import Sir.Proofs.Readiness

namespace Sir

namespace MemoryState

def bumpAlloc (m : MemoryState) (size : Nat) : Allocation :=
  { offset := .ofNat m.watermark, size }

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

theorem bumpAlloc_size (m : MemoryState) (size : Nat) :
    (m.bumpAlloc size).size = size := by
  rfl

theorem isValidNewAlloc_bumpAlloc (m : MemoryState) (size : Nat)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    m.IsValidNewAlloc (m.bumpAlloc size) := by
  have hbound : Evm.UInt256.size = 2 ^ 256 := rfl
  have hstart : (m.bumpAlloc size).start = m.watermark % 2 ^ 256 := by
    simp [bumpAlloc, Allocation.start, Evm.UInt256.toNat_ofNat]
  have hend : (m.bumpAlloc size).endExclusive = m.watermark % 2 ^ 256 + size := by
    rw [Allocation.endExclusive, hstart, bumpAlloc_size]
  rw [hbound] at hspace
  rcases Nat.lt_or_ge m.watermark (2 ^ 256) with hlt | hge
  · have hmod : m.watermark % 2 ^ 256 = m.watermark := Nat.mod_eq_of_lt hlt
    refine ⟨by rw [hend, hmod, hbound]; exact hspace, ?_⟩
    intro a' ha'
    exact Or.inr (by rw [hstart, hmod]; exact m.endExclusive_le_watermark ha')
  · have hwatermark : m.watermark = 2 ^ 256 := Nat.le_antisymm (by omega) hge
    have hsize : size = 0 := by omega
    have hend' : (m.bumpAlloc size).endExclusive = 0 := by
      rw [hend, hwatermark, hsize, Nat.mod_self]
    exact ⟨by rw [hend']; exact Nat.zero_le _,
      fun a' _ => Or.inl (by rw [hend']; exact Nat.zero_le _)⟩

theorem readBytes_push_bumpAlloc (m : MemoryState) (size : Nat)
    (hzero : m.ZeroAboveWatermark)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    (m.push (m.bumpAlloc size)).readBytes (m.bumpAlloc size).offset size =
      ⟨Array.replicate size 0⟩ := by
  have hbound : Evm.UInt256.size = 2 ^ 256 := rfl
  rw [hbound] at hspace
  rcases Nat.lt_or_ge m.watermark (2 ^ 256) with hlt | hge
  · have hoffsetMod :
        (m.bumpAlloc size).offset.toNat = m.watermark % 2 ^ 256 := by
      simp [MemoryState.bumpAlloc, Evm.UInt256.toNat_ofNat]
    have hoffset : (m.bumpAlloc size).offset.toNat = m.watermark := by
      rw [hoffsetMod, Nat.mod_eq_of_lt hlt]
    have hreads :
        (List.range size).map
            (fun index =>
              (m.push (m.bumpAlloc size)).readByte
                ((m.bumpAlloc size).offset.toNat + index)) =
          List.replicate size 0 := by
      have hall : ∀ index ∈ List.range size,
          (m.push (m.bumpAlloc size)).readByte
            ((m.bumpAlloc size).offset.toNat + index) = 0 := by
        intro index _
        change (m.push (m.bumpAlloc size)).store
          ((m.bumpAlloc size).offset.toNat + index) = 0
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

variable {program : Program} {ctx : CallContext}

theorem Program.WellFormed.progress_reachable_nonIcall_bump_proof
    (hwf : program.WellFormed) {function : FunctionId} {globals : Globals}
    {args : Array Word} {runTrace : Trace} {state : MachineState}
    (hrun : program.RunsFunction ctx function globals args runTrace state)
    (hcontrol : program.NonIcallControl state)
    (hspace : program.BumpFits state)
    (hstore : program.StoreInBounds state) :
    ∃ trace state', SmallStep program ctx state trace state' := by
  refine hwf.progress_reachable_nonIcall_proof hrun hcontrol ?_ hstore
  intro nextControl result size word hdecode hword
  exact ⟨state.globals.memory.bumpAlloc word.toNat,
    state.globals.memory.isValidNewAlloc_bumpAlloc word.toNat
      (hspace nextControl result size word hdecode hword),
    state.globals.memory.bumpAlloc_size word.toNat⟩

end Sir
