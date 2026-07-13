import LirLean.Decode.DecodeAnchors
import LirLean.Materialise.MaterialiseRuns

/-!
# LirLean — `PUSH32` round-trip + byte-window bricks (decode-side helpers)

The lowering-independent byte facts the fold decode channel reuses:

* **`uInt256_wordBytesBE`** — the `PUSH32` immediate round-trip:
  `uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ = w`. A genuine 256-bit fact (the byte
  decomposition `wordBytesBE` reverses to little-endian, `fromBytes'` reads it back), proved
  bottom-up through `u256_toNat_ofNat` / `u256_shiftRight_toNat` / the 32-digit base-256
  reconstruction. This is what turns a "decode = PUSH32 carrying *the window's*
  `uInt256OfByteArray`" anchor into "decode = PUSH32 carrying `w`" — the `.imm` clause of
  the cache-keyed decode bundle `MatDecC` (`Materialise/MatFoldChannel.lean`).

* **`extract_toList_eq`** (+ `ofNat_add'`) — the immediate-window read `decode` performs
  for a PUSH, as a pointwise list fact, and the `UInt32` cursor-collapse helper.

The cache-keyed decode bundle and its segment bridge (`MatDecC` / `matDecC_of_seg`) live in
`Materialise/MatFoldChannel.lean` and consume these bricks through
`decode_lower_{push,nonpush}` (`Decode/DecodeLower.lean`).

No `sorry`, no `axiom`, no `native_decide`. Nothing here touches `Spec/Semantics.lean` /
`Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm

set_option maxRecDepth 8192

/-! ## The `PUSH32` immediate round-trip (`uInt256OfByteArray ∘ wordBytesBE = id`) -/

/-- `(UInt256.ofNat m).toNat = m % 2^256` — the `toNat`/`ofNat` round-trip, via the limb
decomposition (`toNat_limbs`) and `omega`. -/
theorem u256_toNat_ofNat (m : ℕ) : (UInt256.ofNat m).toNat = m % 2 ^ 256 := by
  rw [UInt256.toNat_limbs]
  unfold UInt256.ofNat
  simp only [show ∀ k : ℕ, (UInt32.ofNat k).toNat = k % 2 ^ 32 from fun k => by simp]
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- `UInt256.ofNat w.toNat = w` (the value round-trips through `toNat`; `w.toNat < 2^256`). -/
theorem u256_ofNat_toNat (w : Word) : UInt256.ofNat w.toNat = w := by
  apply UInt256.toNat_inj
  rw [u256_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by rw [UInt256.toNat_eq_toBitVec_toNat]; exact (UInt256.toBitVec w).isLt)

/-- `(w >>> s).toNat = w.toNat / 2^s` for a shift `s < 256` (the `BitVec`-backed
`UInt256.shiftRight`, un-`ofBitVec`'d). -/
theorem u256_shiftRight_toNat (w : Word) (s : ℕ) (hs : s < 256) :
    (w >>> UInt256.ofNat s).toNat = w.toNat / 2 ^ s := by
  show (UInt256.shiftRight w (UInt256.ofNat s)).toNat = _
  unfold UInt256.shiftRight
  rw [u256_toNat_ofNat, Nat.mod_eq_of_lt (by calc s < 256 := hs
                                              _ < 2 ^ 256 := by norm_num)]
  rw [if_neg (by omega), UInt256.toNat_eq_toBitVec_toNat, UInt256.toBitVec_ofBitVec,
    BitVec.toNat_ushiftRight, ← UInt256.toNat_eq_toBitVec_toNat, Nat.shiftRight_eq_div_pow]

/-- `(UInt8.ofNat k).toFin.val = k % 256` (the byte truncation `fromBytes'` reads). -/
theorem u8_ofNat_toFin (k : ℕ) : (UInt8.ofNat k).toFin.val = k % 256 := rfl

/-- `fromBytes'` of the **reversed** big-endian word bytes is the word's `Nat` value: the
`wordBytesBE w` digits, reversed to little-endian, reconstruct `w.toNat` in base 256. -/
theorem fromBytes_wordBytesBE (w : Word) :
    fromBytes' (wordBytesBE w).reverse = w.toNat := by
  unfold wordBytesBE
  simp only [show (List.range 32) = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
      22,23,24,25,26,27,28,29,30,31] from by decide]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  simp only [fromBytes', u8_ofNat_toFin]
  rw [show ((31-31)*8) = 0 from rfl, show ((31-30)*8) = 8 from rfl, show ((31-29)*8) = 16 from rfl,
      show ((31-28)*8) = 24 from rfl, show ((31-27)*8) = 32 from rfl, show ((31-26)*8) = 40 from rfl,
      show ((31-25)*8) = 48 from rfl, show ((31-24)*8) = 56 from rfl, show ((31-23)*8) = 64 from rfl,
      show ((31-22)*8) = 72 from rfl, show ((31-21)*8) = 80 from rfl, show ((31-20)*8) = 88 from rfl,
      show ((31-19)*8) = 96 from rfl, show ((31-18)*8) = 104 from rfl, show ((31-17)*8) = 112 from rfl,
      show ((31-16)*8) = 120 from rfl, show ((31-15)*8) = 128 from rfl, show ((31-14)*8) = 136 from rfl,
      show ((31-13)*8) = 144 from rfl, show ((31-12)*8) = 152 from rfl, show ((31-11)*8) = 160 from rfl,
      show ((31-10)*8) = 168 from rfl, show ((31-9)*8) = 176 from rfl, show ((31-8)*8) = 184 from rfl,
      show ((31-7)*8) = 192 from rfl, show ((31-6)*8) = 200 from rfl, show ((31-5)*8) = 208 from rfl,
      show ((31-4)*8) = 216 from rfl, show ((31-3)*8) = 224 from rfl, show ((31-2)*8) = 232 from rfl,
      show ((31-1)*8) = 240 from rfl, show ((31-0)*8) = 248 from rfl]
  rw [u256_shiftRight_toNat w 0 (by norm_num), u256_shiftRight_toNat w 8 (by norm_num),
      u256_shiftRight_toNat w 16 (by norm_num), u256_shiftRight_toNat w 24 (by norm_num),
      u256_shiftRight_toNat w 32 (by norm_num), u256_shiftRight_toNat w 40 (by norm_num),
      u256_shiftRight_toNat w 48 (by norm_num), u256_shiftRight_toNat w 56 (by norm_num),
      u256_shiftRight_toNat w 64 (by norm_num), u256_shiftRight_toNat w 72 (by norm_num),
      u256_shiftRight_toNat w 80 (by norm_num), u256_shiftRight_toNat w 88 (by norm_num),
      u256_shiftRight_toNat w 96 (by norm_num), u256_shiftRight_toNat w 104 (by norm_num),
      u256_shiftRight_toNat w 112 (by norm_num), u256_shiftRight_toNat w 120 (by norm_num),
      u256_shiftRight_toNat w 128 (by norm_num), u256_shiftRight_toNat w 136 (by norm_num),
      u256_shiftRight_toNat w 144 (by norm_num), u256_shiftRight_toNat w 152 (by norm_num),
      u256_shiftRight_toNat w 160 (by norm_num), u256_shiftRight_toNat w 168 (by norm_num),
      u256_shiftRight_toNat w 176 (by norm_num), u256_shiftRight_toNat w 184 (by norm_num),
      u256_shiftRight_toNat w 192 (by norm_num), u256_shiftRight_toNat w 200 (by norm_num),
      u256_shiftRight_toNat w 208 (by norm_num), u256_shiftRight_toNat w 216 (by norm_num),
      u256_shiftRight_toNat w 224 (by norm_num), u256_shiftRight_toNat w 232 (by norm_num),
      u256_shiftRight_toNat w 240 (by norm_num), u256_shiftRight_toNat w 248 (by norm_num)]
  have hlt : w.toNat < 2 ^ 256 := by
    rw [UInt256.toNat_eq_toBitVec_toNat]; exact (UInt256.toBitVec w).isLt
  set N := w.toNat
  omega

/-- **The `PUSH32` immediate round-trip.** `uInt256OfByteArray` of the 32 big-endian bytes
`wordBytesBE w` emits is `w`; the literal cursor decodes as `PUSH32` carrying `w`, not merely
"carrying the window's value". -/
theorem uInt256_wordBytesBE (w : Word) :
    uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ = w := by
  unfold uInt256OfByteArray
  rw [fromBytes_wordBytesBE, u256_ofNat_toNat]

/-! ## Byte-window bricks (the immediate-window read + cursor collapse) -/

/-- `((l.toArray).extract s (s+n)).toList = seg` when `l` matches `seg` (length `n`) pointwise
over `[s, s+n)` — the immediate-window read `decode` performs for a PUSH. -/
theorem extract_toList_eq (l : List UInt8) (s n : ℕ) (seg : List UInt8)
    (hlen : seg.length = n)
    (hseg : ∀ j, j < n → l[s + j]? = seg[j]?) :
    (l.toArray.extract s (s + n)).toList = seg := by
  rw [Array.toList_extract]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [List.length_eq_zero_iff.mp (by omega : seg.length = 0)]; simp
  have hlge : s + n ≤ l.length := by
    have heq := hseg (n - 1) (by omega)
    have hsome : seg[n - 1]? ≠ none := by rw [List.getElem?_eq_getElem (by omega)]; simp
    rw [← heq] at hsome
    have : s + (n - 1) < l.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hsome; exact hsome rfl
    omega
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.toList_toArray, hlen]; omega
  · intro j hj1 _
    rw [List.getElem_take, List.getElem_drop]
    have hjn : j < n := by
      simp only [List.length_take, List.length_drop, List.toList_toArray] at hj1; omega
    have hh := hseg j hjn
    rw [List.getElem?_eq_getElem (show s + j < l.length by omega),
        List.getElem?_eq_getElem (show j < seg.length by omega)] at hh
    exact Option.some.inj hh

theorem ofNat_add' (a b : ℕ) : UInt32.ofNat a + UInt32.ofNat b = UInt32.ofNat (a + b) := by
  rw [UInt32.ofNat_add]

end Lir
