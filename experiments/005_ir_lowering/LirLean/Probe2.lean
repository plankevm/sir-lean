import Evm
open Evm
example (a : UInt64) (h : UInt256.ofUInt64 a = 0) : a.toNat = 0 := by
  have h0 := congrArg (fun w => w.l0.toNat) h
  have h1 := congrArg (fun w => w.l1.toNat) h
  simp only [UInt256.ofUInt64] at h0 h1
  have e0 : (0:UInt256).l0.toNat = 0 := rfl
  have e1 : (0:UInt256).l1.toNat = 0 := rfl
  rw [e0] at h0; rw [e1] at h1
  rw [UInt64.toUInt32_toNat] at h0
  rw [UInt64.toUInt32_toNat] at h1
  have lt64 : a.toNat < 2^64 := a.toNat_lt
  -- h1 still has (a >>> 32).toNat; reduce it
  have hsr : (a >>> 32).toNat = a.toNat / 2^32 := by
    simp [UInt64.toNat_ushiftRight?]
  sorry
