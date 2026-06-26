import Evm

/-!
# `LirLean.MemAlgebra` — memory-channel crux lemmas

This file establishes the crux lemmas needed to add a *memory value channel*
to the bytecode-lowering correctness proof (MSTORE the CALL success flag to a
per-tmp slot, MLOAD it back on use).

The EVM memory model lives in the exp003 package
(`EVMLean/Evm/Machine/MachineStateOps.lean`): `mstore` calls `writeWord` →
`writeBytes` → `ByteArray.write`; `mload` calls `lookupMemory` →
`ByteArray.readWithPadding` → `fromByteArrayBigEndian`.

## Verdict — all three crux lemmas PROVED, axiom-clean

* **CALL preserves caller memory** (`resumeAfterCall_mload`). The lowered CALL
  uses zero-size input *and* return windows; that makes `writeBytes … 0` a no-op
  on memory and `MachineState.M … 0` a no-op on `activeWords`, so an `MLOAD` at
  any fixed slot is preserved across `resumeAfterCall`.

* **MSTORE/MLOAD read-back** (`mload_after_mstore`):
  `((m.mstore addr val).mload addr).1 = val`. Both side-conditions —
  `addr.toNat + 32 ≤ m.memory.size` (slot pre-allocated, in-bounds) and
  `addr.toNat + 63 < 2 ^ 64` (realistic offset; without it `addr.toUInt64`
  truncates, `lookupMemory`'s `activeWords` guard fires and the read returns
  `0 ≠ val`, so the lemma is genuinely false) — are met by a freshly allocated
  tmp slot.

* **Disjointness** (`mstore_mload_disjoint`): an `MSTORE` at `[addr, addr+32)`
  is invisible to an `MLOAD` at a non-overlapping, in-bounds window.

The earlier "opaque-FFI wall" is gone: `ffi.ByteArray.zeroes` now has a provable
pure body (`Array.replicate`), so `size`/`getElem`/`toList` of `zeroes`,
`UInt256.toByteArray`'s exact 32-byte width, the big-endian
`fromBytes'`/`toBytes'` round-trip, and the `UInt256` `ofNat`/`toNat`/`toUInt64`
reassemblies are all theorems. The `#print axioms` guards at the bottom pin every
crux result to `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no FFI
axiom.
-/

open Evm

namespace LirLean.MemAlgebra

/-! ## Lemma 3 — CALL with a zero-size window preserves caller memory reads -/

/-- `mload .1` (i.e. `lookupMemory`) depends on the machine state only through
its `memory` and `activeWords` fields. -/
theorem mload_congr {m m' : MachineState} (slot : UInt256)
    (hmem : m.memory = m'.memory) (haw : m.activeWords = m'.activeWords) :
    (m.mload slot).1 = (m'.mload slot).1 := by
  unfold MachineState.mload MachineState.lookupMemory
  simp [hmem, haw]

/-- `resumeAfterCall` with a zero-size **return** window leaves the caller
frame's memory bytes untouched (`writeBytes _ _ _ _ 0 = self`). -/
theorem resumeAfterCall_memory {result : CallResult} {pd : PendingCall}
    (hout : pd.outSize = 0) :
    (resumeAfterCall result pd).exec.toMachineState.memory
      = pd.frame.exec.toMachineState.memory := by
  unfold resumeAfterCall ExecutionState.replaceStackAndIncrPC
  simp only [hout]
  unfold writeBytes ByteArray.write
  simp

/-- `resumeAfterCall` with zero-size **input and return** windows leaves the
caller frame's `activeWords` untouched (`M s f 0 = s` applied twice). -/
theorem resumeAfterCall_activeWords {result : CallResult} {pd : PendingCall}
    (hin : pd.inSize = 0) (hout : pd.outSize = 0) :
    (resumeAfterCall result pd).exec.toMachineState.activeWords
      = pd.frame.exec.toMachineState.activeWords := by
  unfold resumeAfterCall ExecutionState.replaceStackAndIncrPC
  simp only [hin, hout]
  unfold MachineState.M
  simp

/-- **CALL preserves caller memory.** The lowered CALL uses zero-size input and
return windows (`in_off = in_size = out_off = out_size = 0`, see
`LirLean/Lowering.lean:144`); under those hypotheses an `MLOAD` at any fixed slot
reads the same word before and after the call's resume. The zero-size return
window is exactly what makes the memory bytes survive (`writeBytes … 0`), and the
zero-size input window keeps `activeWords` (hence the `lookupMemory` bounds
guard) unchanged. -/
theorem resumeAfterCall_mload {result : CallResult} {pd : PendingCall}
    (hin : pd.inSize = 0) (hout : pd.outSize = 0) (slot : UInt256) :
    ((resumeAfterCall result pd).exec.toMachineState.mload slot).1
      = (pd.frame.exec.toMachineState.mload slot).1 :=
  mload_congr slot
    (resumeAfterCall_memory hout)
    (resumeAfterCall_activeWords hin hout)

/-! ## Read-back groundwork — `ffi.ByteArray.zeroes` is now a provable pure body -/

/-- `ffi.ByteArray.zeroes n` has `size = n.toNat`. -/
theorem zeroes_size (n : USize) : (ffi.ByteArray.zeroes n).size = n.toNat := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- Every byte of `ffi.ByteArray.zeroes n` is `0`. -/
theorem zeroes_getElem (n : USize) (i : Nat) (h : i < (ffi.ByteArray.zeroes n).size) :
    (ffi.ByteArray.zeroes n)[i] = 0 := by
  simp [ffi.ByteArray.zeroes, ByteArray.getElem_eq_data_getElem]

/-- `ByteArray.toList` agrees with `.data.toList`. -/
theorem toList_eq_data_toList (b : ByteArray) : b.toList = b.data.toList := by
  rw [ByteArray.toList]
  suffices h : ∀ i r, ByteArray.toList.loop b i r = r.reverse ++ (b.data.toList.drop i) by
    simpa using h 0 []
  intro i r
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hlt ih =>
    rw [ih]
    have hsz : i < b.size := hlt
    have hi : i < b.data.toList.length := by
      rw [Array.length_toList]; exact hsz
    have hget : b.get! i = b.data.toList[i]'hi := by
      obtain ⟨arr⟩ := b
      have harr : i < arr.size := hsz
      simp only [ByteArray.get!]
      rw [getElem!_pos arr i harr]
      rfl
    rw [hget, List.reverse_cons, List.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hi]
    simp
  | case2 i r hge =>
    have hsz : b.size ≤ i := Nat.le_of_not_lt hge
    have : b.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact hsz
    simp [List.drop_eq_nil_of_le this]

/-- `toList` of `ffi.ByteArray.zeroes n` is `List.replicate n.toNat 0`. -/
theorem zeroes_toList (n : USize) :
    (ffi.ByteArray.zeroes n).toList = List.replicate n.toNat 0 := by
  rw [toList_eq_data_toList]
  simp [ffi.ByteArray.zeroes, Array.toList_replicate]

/-! ## Decoder round-trip — `fromBytes'`/`toBytes'` over `Nat` -/

open Evm (fromBytes' toBytesBigEndian fromBytesBigEndian fromByteArrayBigEndian)

/-- `fromBytes'` (little-endian) ignores trailing (most-significant) zero bytes. -/
theorem fromBytes'_append_zeroes (l : List UInt8) (k : Nat) :
    fromBytes' (l ++ List.replicate k 0) = fromBytes' l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ, List.nil_append, fromBytes']; simpa using ih
  | cons b bs ih =>
    simp only [List.cons_append, fromBytes', ih]

/- The library encoder `Evm.toBytesBigEndian` is `List.reverse ∘ Evm.toBytes'`, but
`Evm.toBytes'` is `private`. `open private … in` re-exposes it (under the local name
`toBytes'`) so we can run `fun_induction`/equation lemmas on it. -/
open private toBytes' in Evm.toBytesBigEndian

/-- `toBytes' 0 = []` (well-founded recursion needs the equation lemma to unfold). -/
theorem toBytes'_nil : toBytes' 0 = [] := by rw [toBytes'.eq_def]

/-- The fundamental little-endian round-trip: decoding the byte expansion of `n`
returns `n`. `toBytes'` peels the low byte `n % 256` and recurses on `n / 256`. -/
theorem fromBytes'_toBytes' (n : Nat) : fromBytes' (toBytes' n) = n := by
  fun_induction toBytes' n
  · rfl
  · rename_i m _byte _hwf ih
    simp only [fromBytes']
    rw [ih]
    show (UInt8.ofNat ((m + 1) % UInt8.size)).toFin.val + 2 ^ 8 * ((m + 1) / UInt8.size) = m + 1
    have hval : (UInt8.ofNat ((m + 1) % UInt8.size)).toFin.val
        = ((m + 1) % UInt8.size) % 2 ^ 8 := UInt8.toNat_ofNat'
    rw [hval]
    have hsz : UInt8.size = 2 ^ 8 := rfl
    rw [hsz, Nat.mod_mod]
    omega

/-- The byte expansion of `n` fits in `k` bytes once `n < 2 ^ (8k)`. -/
theorem toBytes'_length_le (n k : Nat) (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at h; subst h
    simp [toBytes'_nil]
  | succ k ih =>
    fun_cases toBytes' n
    · simp
    · rename_i m _byte _hwf
      simp only [List.length_cons]
      have hdiv : (m + 1) / UInt8.size < 2 ^ (8 * k) := by
        have hsz : UInt8.size = 2 ^ 8 := rfl
        rw [hsz]
        apply Nat.div_lt_of_lt_mul
        calc m + 1 < 2 ^ (8 * (k + 1)) := h
          _ = 2 ^ 8 * 2 ^ (8 * k) := by rw [← pow_add]; ring_nf
      have hle := ih _ hdiv
      simp only [Nat.succ_eq_add_one] at hle ⊢
      omega

/-! ## `UInt256` ↔ `Nat` round-trips (`ofNat`/`toNat`, `toUInt64`) -/

/-- `(UInt256.ofNat n).toNat = n % 2 ^ 256` — the eight 32-bit windows of `n`
reassemble its low 256 bits. -/
theorem toNat_ofNat (n : Nat) : (UInt256.ofNat n).toNat = n % 2 ^ 256 := by
  rw [UInt256.toNat_limbs]
  simp only [UInt256.ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2:Nat)^256 = 2^32 * 2^224 by rw [← pow_add],
      show (2:Nat)^224 = 2^32 * 2^192 by rw [← pow_add],
      show (2:Nat)^192 = 2^32 * 2^160 by rw [← pow_add],
      show (2:Nat)^160 = 2^32 * 2^128 by rw [← pow_add],
      show (2:Nat)^128 = 2^32 * 2^96  by rw [← pow_add],
      show (2:Nat)^96  = 2^32 * 2^64  by rw [← pow_add],
      show (2:Nat)^64  = 2^32 * 2^32  by rw [← pow_add]]
  rw [Nat.mod_mul, Nat.mod_mul, Nat.mod_mul, Nat.mod_mul, Nat.mod_mul, Nat.mod_mul, Nat.mod_mul]
  simp only [show ∀ m, (UInt32.ofNat m).toNat = m % 2^32 from fun m => UInt32.toNat_ofNat',
    Nat.div_div_eq_div_mul, ← pow_add]
  ring

theorem toNat_lt (val : UInt256) : val.toNat < 2 ^ 256 := by
  rw [UInt256.toNat_eq_toBitVec_toNat]; exact val.toBitVec.isLt

/-- `UInt256.ofNat ∘ toNat = id`: `ofNat` recovers any word from its `toNat`. -/
theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply UInt256.toNat_inj
  rw [toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt a)]

/-- `UInt256.toUInt64` is truncation to the low 64 bits. -/
theorem toUInt64_toNat (a : UInt256) : a.toUInt64.toNat = a.toNat % 2 ^ 64 := by
  rw [UInt256.toUInt64, UInt256.toNat_limbs]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show (32:UInt64).toNat = 32 from rfl]
  have q0 : a.l0.toNat < 2^32 := a.l0.toBitVec.isLt
  have q1 : a.l1.toNat < 2^32 := a.l1.toBitVec.isLt
  have hsh : a.l1.toNat <<< 32 % 2^64 = a.l1.toNat * 2^32 := by
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have : a.l1.toNat * 2^32 < 2^32 * 2^32 :=
      Nat.mul_lt_mul_of_lt_of_le q1 (le_refl _) (by norm_num)
    omega
  rw [hsh]
  have hor : a.l0.toNat ||| a.l1.toNat * 2^32 = a.l0.toNat + a.l1.toNat * 2^32 := by
    rw [Nat.or_comm, mul_comm a.l1.toNat, ← Nat.two_pow_add_eq_or_of_lt q0]; ring
  rw [hor]
  have key : a.l0.toNat + a.l1.toNat * 2 ^ 32 + a.l2.toNat * 2 ^ 64 + a.l3.toNat * 2 ^ 96 +
      a.l4.toNat * 2 ^ 128 + a.l5.toNat * 2 ^ 160 + a.l6.toNat * 2 ^ 192 + a.l7.toNat * 2 ^ 224
      = (a.l0.toNat + a.l1.toNat * 2^32)
        + 2^64 * (a.l2.toNat + a.l3.toNat*2^32 + a.l4.toNat*2^64 + a.l5.toNat*2^96
                  + a.l6.toNat*2^128 + a.l7.toNat*2^160) := by ring
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have : a.l1.toNat * 2^32 < 2^32 * 2^32 :=
    Nat.mul_lt_mul_of_lt_of_le q1 (le_refl _) (by norm_num)
  omega

/-! ## Decoding `UInt256.toByteArray` -/

/-- `ffi.ByteArray.zeroes n` (as `.data.toList`) is `List.replicate n.toNat 0`. -/
theorem zeroes_data_toList (n : USize) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n.toNat 0 := by
  simp [ffi.ByteArray.zeroes, Array.toList_replicate]

/-- `ffi.ByteArray.zeroes 0` is empty. -/
theorem zeroes_zero : ffi.ByteArray.zeroes 0 = ByteArray.empty := by
  apply ByteArray.size_eq_zero_iff.mp
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- `(BE n).data.toList` is the big-endian byte list of `n`. -/
theorem BE_data_toList (n : Nat) : (BE n).data.toList = (toBytes' n).reverse := by
  simp [BE, Function.comp, List.data_toByteArray, Evm.toBytesBigEndian]

/-- The big-endian encoder padded to 32 bytes (`UInt256.toByteArray`) decodes back
to `val.toNat`. The leading zero pad is invisible to the little-endian `fromBytes'`
after the final `reverse`, and the unpadded core is the `toBytes'`/`fromBytes'`
round-trip. -/
theorem fromByteArray_toByteArray (val : UInt256) :
    fromByteArrayBigEndian val.toByteArray = val.toNat := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  simp only [Function.comp]
  rw [UInt256.toByteArray, toList_eq_data_toList]
  simp only [ByteArray.data_append, Array.toList_append, zeroes_data_toList, BE_data_toList,
    List.reverse_append, List.reverse_replicate]
  rw [fromBytes'_append_zeroes, List.reverse_reverse, fromBytes'_toBytes']

/-! ## `UInt256.toByteArray` is exactly 32 bytes -/

/-- `(BE n).size ≤ 32` for any 256-bit value `n` (`n < 2 ^ 256`). -/
theorem BE_size_le (n : Nat) (h : n < 2 ^ 256) : (BE n).size ≤ 32 := by
  have hsz : (BE n).size = (toBytes' n).length := by
    simp [BE, Function.comp, List.size_toByteArray, Evm.toBytesBigEndian]
  rw [hsz]
  exact toBytes'_length_le n 32 (by simpa using h)

/-- The pad-length `USize` `⟨32 - s⟩` used by `toByteArray` has `toNat = 32 - s`
(the `BitVec` subtraction equals the `Nat` one because `s ≤ 32 < 2 ^ numBits`). -/
theorem usize_mk_sub_toNat (s : Nat) (hs : s ≤ 32) :
    ({ toBitVec := (32 : BitVec System.Platform.numBits) - (s : BitVec System.Platform.numBits) }
      : USize).toNat = 32 - s := by
  show ((32 : BitVec System.Platform.numBits) - (s : BitVec System.Platform.numBits)).toNat = 32 - s
  have hbig : (2:Nat)^32 ≤ 2 ^ System.Platform.numBits := by
    apply Nat.pow_le_pow_right (by norm_num); cases System.Platform.numBits_eq <;> omega
  rw [BitVec.toNat_sub,
      show ((s : BitVec System.Platform.numBits)) = BitVec.ofNat _ s by
        simp [Nat.cast, NatCast.natCast],
      show ((32 : BitVec System.Platform.numBits)) = BitVec.ofNat _ 32 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show s < 2 ^ System.Platform.numBits by omega),
      Nat.mod_eq_of_lt (show 32 < 2 ^ System.Platform.numBits by omega),
      show 2 ^ System.Platform.numBits - s + 32 = 2 ^ System.Platform.numBits + (32 - s) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- `UInt256.toByteArray val` is exactly 32 bytes. -/
theorem toByteArray_size (val : UInt256) : val.toByteArray.size = 32 := by
  rw [UInt256.toByteArray, ByteArray.size_append, zeroes_size]
  have hle : (BE val.toNat).size ≤ 32 := BE_size_le _ (toNat_lt val)
  rw [usize_mk_sub_toNat _ hle]
  omega

/-! ## MSTORE write reduction (pre-allocated slot)

When the 32-byte window `[addr, addr+32)` already lies inside memory
(`addr + 32 ≤ memory.size` — the realistic case after slot allocation), the
nested `min`/padding branches of `ByteArray.write` all collapse and `writeWord`
is a single in-place `copySlice`. -/

/-- `writeWord` leaves `activeWords` untouched (it only rewrites `memory`). -/
theorem writeWord_activeWords (m : MachineState) (addr val : UInt256) :
    (m.writeWord addr val).activeWords = m.activeWords := rfl

/-- `writeWord` into a pre-allocated window is a plain `copySlice`. -/
theorem writeWord_memory (m : MachineState) (addr val : UInt256)
    (h : addr.toNat + 32 ≤ m.memory.size) :
    (m.writeWord addr val).memory
      = val.toByteArray.copySlice 0 m.memory addr.toNat 32 := by
  show (Evm.writeBytes val.toByteArray 0 m addr.toNat 32).memory = _
  unfold Evm.writeBytes
  show ByteArray.write val.toByteArray 0 m.memory addr.toNat 32 = _
  unfold ByteArray.write
  rw [if_neg (by norm_num), if_neg (by rw [toByteArray_size]; omega), toByteArray_size]
  rw [show min m.memory.size (addr.toNat + 32) = addr.toNat + 32 by omega,
      show addr.toNat - m.memory.size = 0 by omega]
  norm_num
  rw [show (OfNat.ofNat 0 : USize) = (0 : USize) from rfl, zeroes_zero,
    ByteArray.append_empty, ByteArray.append_empty]

/-- The `copySlice` result still has the caller's memory size. -/
theorem copySlice_size (mem : ByteArray) (addr : Nat) (val : UInt256)
    (h : addr + 32 ≤ mem.size) :
    (val.toByteArray.copySlice 0 mem addr 32).size = mem.size := by
  rw [ByteArray.copySlice_eq_append]
  have hsz : val.toByteArray.size = 32 := toByteArray_size val
  have hd : val.toByteArray.data.size = 32 := by rw [← ByteArray.size]; exact hsz
  have hmd : mem.data.size = mem.size := ByteArray.size_data ..
  simp only [ByteArray.size_append, ByteArray.size_extract, hd, hmd,
    show min 32 (32 - 0) = 32 from rfl, show (0:Nat) + 32 = 32 from rfl]
  omega

/-- Reading the just-written window back out of the `copySlice` yields the stored
bytes verbatim. -/
theorem copySlice_extract (mem : ByteArray) (addr : Nat) (val : UInt256)
    (h : addr + 32 ≤ mem.size) :
    (val.toByteArray.copySlice 0 mem addr 32).extract addr (addr + 32) = val.toByteArray := by
  rw [ByteArray.copySlice_eq_append]
  have hsz : val.toByteArray.size = 32 := toByteArray_size val
  have hd : val.toByteArray.data.size = 32 := by rw [← ByteArray.size]; exact hsz
  rw [show (0:Nat) + 32 = 32 from rfl, hd, show min 32 (32 - 0) = 32 from rfl]
  rw [show val.toByteArray.extract 0 32 = val.toByteArray by
        conv_rhs => rw [← ByteArray.extract_zero_size (b := val.toByteArray), hsz]]
  set A := mem.extract 0 addr with hA
  have hAsz : A.size = addr := by rw [hA, ByteArray.size_extract]; omega
  have h1 : addr - (A ++ val.toByteArray).size = 0 := by
    rw [ByteArray.size_append, hAsz, hsz]; omega
  have h2 : addr + 32 - (A ++ val.toByteArray).size = 0 := by
    rw [ByteArray.size_append, hAsz, hsz]; omega
  rw [ByteArray.extract_append, h1, h2,
      ByteArray.extract_same, ByteArray.append_empty, ← hAsz,
      ByteArray.extract_append_eq_right (by rw [hAsz]) (by rw [hsz])]

/-- `readWithPadding` of the written memory at the written window returns the stored
word's byte encoding (no padding, since the window is full-width). -/
theorem readWithPadding_written (mem : ByteArray) (addr : Nat) (val : UInt256)
    (h : addr + 32 ≤ mem.size) :
    (val.toByteArray.copySlice 0 mem addr 32).readWithPadding addr 32 = val.toByteArray := by
  set W := val.toByteArray.copySlice 0 mem addr 32 with hW
  have hWsz : W.size = mem.size := copySlice_size mem addr val h
  unfold ByteArray.readWithPadding
  rw [if_neg (by norm_num)]
  unfold ByteArray.readWithoutPadding
  rw [if_neg (by rw [hWsz]; omega), show min 32 W.size = 32 by rw [hWsz]; omega,
      copySlice_extract mem addr val h]
  simp only []
  have hpad : ffi.ByteArray.zeroes
      { toBitVec := ((32 : Nat) - (32 : Nat) : BitVec System.Platform.numBits) } = ByteArray.empty := by
    rw [show ((32 : Nat) - (32 : Nat) : BitVec System.Platform.numBits) = 0 by simp]
    exact zeroes_zero
  rw [toByteArray_size, hpad, ByteArray.append_empty]

/-! ## `activeWords` bookkeeping (`M`) -/

/-- `M` at `l = 32` (its non-zero branch). -/
theorem M_32 (s f : UInt64) : MachineState.M s f 32 = max s ((f + 32 + 31) / 32) := rfl

/-- The `UInt64` `max` dominates its right argument: `x.toNat ≤ (max s x).toNat`. -/
theorem umax_ge (s x : UInt64) : x.toNat ≤ (max s x).toNat := by
  show x.toNat ≤ (if s ≤ x then x else s).toNat
  split
  · exact le_refl _
  · rename_i hns
    rw [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hns
    omega

/-- The `UInt64` `max` dominates its left argument: `s.toNat ≤ (max s x).toNat`. -/
theorem umax_ge_left (s x : UInt64) : s.toNat ≤ (max s x).toNat := by
  show s.toNat ≤ (if s ≤ x then x else s).toNat
  split
  · rename_i h; rwa [UInt64.le_iff_toNat_le] at h
  · exact le_refl _

/-- After an `MSTORE` at `addr`, the new `activeWords` covers `addr` — i.e. the
`lookupMemory` upper-bound guard `addr.toNat < activeWords.toNat * 32` holds —
provided `addr` is a realistic (sub-`2 ^ 64`) memory offset. -/
theorem activeWords_covers (s : UInt64) (addr : UInt256) (haddr : addr.toNat + 63 < 2 ^ 64) :
    addr.toNat < (MachineState.M s addr.toUInt64 32).toNat * 32 := by
  rw [M_32]
  set x : UInt64 := (addr.toUInt64 + 32 + 31) / 32 with hx
  have hmono : x.toNat ≤ (max s x).toNat := umax_ge s x
  have hau : addr.toUInt64.toNat = addr.toNat := by
    rw [toUInt64_toNat, Nat.mod_eq_of_lt (by omega)]
  have hxval : x.toNat = (addr.toNat + 63) / 32 := by
    rw [hx, UInt64.toNat_div]
    simp only [UInt64.toNat_add, hau, show (32:UInt64).toNat = 32 from rfl,
      show (31:UInt64).toNat = 31 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have : addr.toNat < x.toNat * 32 := by rw [hxval]; omega
  omega

/-! ## Lemma 1 — MSTORE/MLOAD read-back (the memory value channel crux)

`((m.mstore addr val).mload addr).1 = val`, under two realisability side-conditions
that the lowering always supplies for a freshly allocated tmp slot:
* `addr.toNat + 32 ≤ m.memory.size` — the 32-byte slot is in-bounds (pre-allocated);
* `addr.toNat + 63 < 2 ^ 64` — `addr` is a real (non-astronomical) memory offset, so
  the `UInt64` `activeWords` bookkeeping does not truncate.
Without the second the lemma is genuinely false: for `addr.toNat ≥ 2 ^ 64`,
`addr.toUInt64` truncates and `lookupMemory`'s guard fires, returning `0 ≠ val`. -/
theorem mload_after_mstore (m : MachineState) (addr val : UInt256)
    (hmem : addr.toNat + 32 ≤ m.memory.size) (haddr : addr.toNat + 63 < 2 ^ 64) :
    ((m.mstore addr val).mload addr).1 = val := by
  show ((m.mstore addr val).lookupMemory addr) = val
  unfold MachineState.mstore
  unfold MachineState.lookupMemory
  have hmemEq : (m.writeWord addr val).memory
      = val.toByteArray.copySlice 0 m.memory addr.toNat 32 := writeWord_memory m addr val hmem
  -- the stored state: memory is the copySlice, activeWords is `M … addr 32`
  simp only [hmemEq]
  have hsize : (val.toByteArray.copySlice 0 m.memory addr.toNat 32).size = m.memory.size :=
    copySlice_size m.memory addr.toNat val hmem
  rw [writeWord_activeWords]
  rw [if_neg ?guard]
  case guard =>
    rw [not_or]
    refine ⟨by rw [hsize]; omega, ?_⟩
    have := activeWords_covers m.activeWords addr haddr
    omega
  rw [readWithPadding_written m.memory addr.toNat val hmem,
      fromByteArray_toByteArray, ofNat_toNat]

/-! ## Lemma 2 — disjointness

An `MSTORE` at a 32-byte window `[addr, addr+32)` is invisible to an `MLOAD` at a
non-overlapping window `[addr', addr'+32)`. We prove the byte-level core first
(the written `copySlice` agrees with the original memory off the write window),
then lift it through `readWithPadding`/`lookupMemory`. Side-conditions: both
windows are in-bounds of the (size-preserving) memory, and `addr'` is a realistic
offset — exactly the realisability premises of Lemma 1, plus the read offset. -/

/- The written `copySlice` agrees with the original memory on any window disjoint
from `[addr, addr+32)`. -/
set_option maxHeartbeats 800000 in
theorem copySlice_extract_disjoint (mem : ByteArray) (addr addr' : Nat) (val : UInt256)
    (hw : addr + 32 ≤ mem.size) (hr : addr' + 32 ≤ mem.size)
    (hdis : addr + 32 ≤ addr' ∨ addr' + 32 ≤ addr) :
    (val.toByteArray.copySlice 0 mem addr 32).extract addr' (addr' + 32)
      = mem.extract addr' (addr' + 32) := by
  have hsz : val.toByteArray.size = 32 := toByteArray_size val
  have hd : val.toByteArray.data.size = 32 := by rw [← ByteArray.size]; exact hsz
  have hmd : mem.data.size = mem.size := ByteArray.size_data ..
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_copySlice]
  apply Array.ext
  · simp only [Array.size_extract, Array.size_append, hd, hmd]; omega
  · intro i hi1 _
    have hilt : i < 32 := by simp only [Array.size_extract] at hi1; omega
    rw [Array.getElem_extract, Array.getElem_extract]
    have hAa : (mem.data.extract 0 addr).size = addr := by rw [Array.size_extract, hmd]; omega
    have hBa : (val.toByteArray.data.extract 0 (0 + 32)).size = 32 := by
      rw [Array.size_extract, hd]; omega
    rcases hdis with hge | hle
    · rw [Array.getElem_append_right
            (xs := mem.data.extract 0 addr ++ val.toByteArray.data.extract 0 (0 + 32))
            (by rw [Array.size_append, hAa, hBa]; omega),
          Array.getElem_extract]
      congr 1
      rw [Array.size_append, hAa, hBa,
        show min 32 (val.toByteArray.data.size - 0) = 32 by rw [hd]; decide]
      omega
    · rw [Array.getElem_append_left (by rw [Array.size_append, hAa, hBa]; omega),
        Array.getElem_append_left (by rw [hAa]; omega), Array.getElem_extract]
      congr 1
      omega

/-- `readWithPadding` at an in-bounds full window is exactly the corresponding
`extract` (no padding). -/
theorem readWithPadding_inbounds (mem : ByteArray) (addr' : Nat) (hr : addr' + 32 ≤ mem.size) :
    mem.readWithPadding addr' 32 = mem.extract addr' (addr' + 32) := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by norm_num)]
  unfold ByteArray.readWithoutPadding
  rw [if_neg (by omega), show min 32 mem.size = 32 by omega]
  have hesz : (mem.extract addr' (addr' + 32)).size = 32 := by
    rw [ByteArray.size_extract]; omega
  have hpad : ffi.ByteArray.zeroes
      { toBitVec := ((32 : Nat) - (mem.extract addr' (addr' + 32)).size
        : BitVec System.Platform.numBits) } = ByteArray.empty := by
    rw [hesz, show (((32 : Nat) : BitVec System.Platform.numBits)
          - ((32 : Nat) : BitVec System.Platform.numBits)) = 0 by simp]
    exact zeroes_zero
  simp only []
  rw [hpad, ByteArray.append_empty]

/-- **Disjointness.** An `MSTORE` at `[addr, addr+32)` does not disturb an `MLOAD`
at a non-overlapping in-bounds window `[addr', addr'+32)`. Premises (all met by a
freshly allocated, in-bounds tmp slot): the write window is in-bounds
(`addr.toNat + 32 ≤ m.memory.size`); the read window is in-bounds
(`addr'.toNat + 32 ≤ m.memory.size`); the read offset is already active
(`addr'.toNat < m.activeWords.toNat * 32`); and the windows are disjoint. -/
theorem mstore_mload_disjoint (m : MachineState) (addr addr' val : UInt256)
    (hwmem : addr.toNat + 32 ≤ m.memory.size)
    (hrmem : addr'.toNat + 32 ≤ m.memory.size)
    (hract : addr'.toNat < m.activeWords.toNat * 32)
    (hdis : addr.toNat + 32 ≤ addr'.toNat ∨ addr'.toNat + 32 ≤ addr.toNat) :
    ((m.mstore addr val).mload addr').1 = (m.mload addr').1 := by
  show ((m.mstore addr val).lookupMemory addr') = (m.lookupMemory addr')
  unfold MachineState.mstore MachineState.lookupMemory
  have hmemEq : (m.writeWord addr val).memory
      = val.toByteArray.copySlice 0 m.memory addr.toNat 32 := writeWord_memory m addr val hwmem
  simp only [hmemEq, writeWord_activeWords]
  have hsize : (val.toByteArray.copySlice 0 m.memory addr.toNat 32).size = m.memory.size :=
    copySlice_size m.memory addr.toNat val hwmem
  -- both guards are false (write preserves size, only grows activeWords)
  have hactGe : m.activeWords.toNat ≤ (MachineState.M m.activeWords addr.toUInt64 32).toNat := by
    rw [M_32]; exact umax_ge_left _ _
  rw [if_neg (by rw [not_or]; exact ⟨by rw [hsize]; omega, by omega⟩),
      if_neg (by rw [not_or]; exact ⟨by omega, by omega⟩)]
  rw [readWithPadding_inbounds _ _ (by rw [hsize]; omega),
      readWithPadding_inbounds _ _ hrmem,
      copySlice_extract_disjoint m.memory addr.toNat addr'.toNat val hwmem hrmem hdis]

/-! ## Axiom-cleanliness guard

The three crux results must rest only on the standard `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`, no project axiom, in particular no `ffi`-axiom — the
de-opaqued `ffi.ByteArray.zeroes` body is what makes this possible). -/
/-- info: 'LirLean.MemAlgebra.resumeAfterCall_mload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resumeAfterCall_mload

/-- info: 'LirLean.MemAlgebra.mload_after_mstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mload_after_mstore

/-- info: 'LirLean.MemAlgebra.mstore_mload_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mstore_mload_disjoint

end LirLean.MemAlgebra
