import LirLean.Decode.DecodeAnchors
import LirLean.Materialise.MaterialiseRuns

/-!
# LirLean — generic `MatDec` reconstruction over `lower prog` (Layer **A→B1 bridge**)

`DecodeAnchors.lean` (Layer A) turns a flat byte fact into a `decode (lower prog) …` fact.
`MaterialiseRuns.lean` (Layer B1) consumes the *structured* decode bundle `MatDec` — one
decode clause per opcode `materialiseExpr` emits, anchored at the running pc. This module
assembles the anchors into the whole `MatDec` bundle, **generically over `lower prog`**, by
induction on `materialiseExpr`'s structure. It discharges B1's carried `MatDec` hypothesis
(and the per-opcode terminator decodes) at the static cursors, so the lower layers see no
free decode hypothesis.

## The two pieces

* **`uInt256_wordBytesBE`** — the `PUSH32` immediate round-trip:
  `uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ = w`. A genuine 256-bit fact (the byte
  decomposition `wordBytesBE` reverses to little-endian, `fromBytes'` reads it back), proved
  bottom-up through `u256_toNat_ofNat` / `u256_shiftRight_toNat` / the 32-digit base-256
  reconstruction. This is what turns A2's "decode = PUSH32 carrying *the window's*
  `uInt256OfByteArray`" into "decode = PUSH32 carrying `w`", exactly `MatDec`'s `.imm` clause.

* **`MatSeg` + `matDec_of_seg`** — the structural bridge. `MatSeg prog base defs fuel e` says
  the bytes of `materialiseExpr defs fuel e` sit at `flatBytes prog` offsets `[base, base+len)`.
  Each `materialiseExpr` constructor lays its sub-expressions and consuming opcode out
  contiguously (`add a b = mat b ++ mat a ++ [ADD]`, …), so a parent segment splits into the
  sub-segments — `matDec_of_seg` recurses on them and discharges each leaf decode (PUSH32 /
  ADD / LT / SLOAD / GAS) from the segment byte via `decode_lower_{push,nonpush}`. The pc
  anchors (`UInt32.ofNat base + UInt32.ofNat (sub-length)`) collapse to `UInt32.ofNat (base +
  …)` by `UInt32.ofNat_add`, matching `MatDec`'s running-pc shape exactly.

`matDec_of_lower` then specialises `matDec_of_seg` to a *statement cursor*: the materialise
bytes of an `emitStmt`'s operand are a sub-segment of the statement's flat bytes
(`flatBytes_at_pcOf_offset`), so `MatSeg` holds at `pcOf prog L pc + offset`.

No `sorry`, no `axiom`, no `native_decide`. Nothing here touches `Spec/Semantics.lean` /
`V2/Law.lean` (the frame-free spine).
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
`wordBytesBE w` emits is `w` — exactly what `MatDec`'s `.imm w` clause needs (decode at the
literal cursor is `PUSH32` carrying `w`, not merely "carrying the window's value"). -/
theorem uInt256_wordBytesBE (w : Word) :
    uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ = w := by
  unfold uInt256OfByteArray
  rw [fromBytes_wordBytesBE, u256_ofNat_toNat]

/-! ## The byte-segment bridge (`MatSeg` + `matDec_of_seg`)

`MatSeg prog base defs fuel e` is the local hypothesis that the bytes of
`materialiseExpr defs fuel e` sit in `flatBytes prog` at offsets `[base, base+len)`.
`matDec_of_seg` turns it into the full `MatDec` bundle, by induction on `materialiseExpr`'s
recursion — each constructor's sub-segments split off the parent (`seg_prefix`/`seg_suffix`)
and each leaf decode (`PUSH32` / `ADD` / `LT` / `SLOAD` / `GAS`) is read off the segment byte. -/

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

/-- **`.imm` leaf decode from a segment.** When `emitImm w`'s bytes sit at `base`, decode at
`base` is `PUSH32` carrying `w` (the byte is `PUSH32`, the 32-byte window round-trips via
`uInt256_wordBytesBE`). -/
theorem imm_leaf_decode (prog : Program) (base : ℕ) (w : Word)
    (hbound : base + 33 ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm w).length → (flatBytes prog)[base + j]? = (emitImm w)[j]?) :
    decode (lower prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (w, 32)) := by
  have hemit : (emitImm w).length = 33 := emitImm_length w
  have hbyte : (flatBytes prog)[base]? = some Byte.push32 := by
    have := hseg 0 (by omega); simpa [emitImm] using this
  have hwin : ((flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)).toList = wordBytesBE w := by
    apply extract_toList_eq (flatBytes prog) (base + 1) 32 (wordBytesBE w) (by simp [wordBytesBE])
    intro j hj
    have := hseg (1 + j) (by rw [hemit]; omega)
    rw [show base + (1 + j) = base + 1 + j from by ring] at this
    rw [this, show (1 + j) = j + 1 from by ring]
    simp [emitImm, List.getElem?_cons_succ]
  have himm : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)⟩ = w := by
    have hh : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)⟩
        = uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ := by
      unfold uInt256OfByteArray
      congr 2
      show ((flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)).toList.reverse = _
      rw [hwin]
    rw [hh, uInt256_wordBytesBE]
  have hp : Evm.pushArgWidth (Evm.parseInstr Byte.push32) = (32 : UInt8) := by decide
  have h32 : (32 : UInt8).toNat = 32 := by decide
  have hres := decode_lower_push prog base Byte.push32 32 w (by omega) hbyte hp (by decide)
    (by rw [h32]; exact himm)
  rw [hres]; rfl

/-- **Non-push opcode leaf decode from a segment.** When `seg`'s bytes sit at `base` and
`seg[off]` is a zero-width opcode, decode at `base+off` is that opcode. Covers the consuming
`ADD` / `LT` / `SLOAD` / `GAS` `materialiseExpr` emits. -/
theorem nonpush_leaf_decode (prog : Program) (base off : ℕ) (byte : UInt8) (seg : List UInt8)
    (hbound : base + off < 2 ^ 32)
    (hoff : seg[off]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0)
    (hseg : ∀ j, j < seg.length → (flatBytes prog)[base + j]? = seg[j]?) :
    decode (lower prog) (UInt32.ofNat (base + off)) = some (Evm.parseInstr byte, .none) := by
  have hoffl : off < seg.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hoff; exact absurd hoff (by simp)
  have hbyte : (flatBytes prog)[base + off]? = some byte := by rw [hseg off hoffl]; exact hoff
  exact decode_lower_nonpush prog (base + off) byte hbound hbyte hnp

/-- **The byte-segment hypothesis.** The bytes of `materialiseExpr defs fuel e` sit in
`flatBytes prog` at offsets `[base, base + (materialiseExpr …).length)`. -/
def MatSeg (prog : Program) (base : ℕ) (defs : Tmp → Option Expr) (fuel : ℕ) (e : Expr) : Prop :=
  ∀ j, j < (materialiseExpr defs fuel e).length →
    (flatBytes prog)[base + j]? = (materialiseExpr defs fuel e)[j]?

/-- A prefix of a segment is a segment at the same base. -/
theorem seg_prefix (prog : Program) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → (flatBytes prog)[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < pre.length → (flatBytes prog)[base + j]? = pre[j]? := by
  intro j hj
  rw [h j (by rw [List.length_append]; omega), List.getElem?_append_left hj]

/-- A suffix of a segment is a segment at the shifted base. -/
theorem seg_suffix (prog : Program) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → (flatBytes prog)[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < suf.length → (flatBytes prog)[base + pre.length + j]? = suf[j]? := by
  intro j hj
  have := h (pre.length + j) (by rw [List.length_append]; omega)
  rw [show base + (pre.length + j) = base + pre.length + j from by ring] at this
  rw [this, List.getElem?_append_right (by omega), show pre.length + j - pre.length = j from by omega]

theorem ofNat_add' (a b : ℕ) : UInt32.ofNat a + UInt32.ofNat b = UInt32.ofNat (a + b) := by
  rw [UInt32.ofNat_add]

/-- **`.slot` leaf decode from a segment.** When `emitImm slot ++ [MLOAD]`'s bytes
sit at `base`, decode at `base` is `PUSH32 slot` and decode at `base + 33` is `MLOAD` —
exactly the `MatDec` `.slot` clause (the Route B memory-readback marker). -/
theorem slot_leaf_decode (prog : Program) (base slot : ℕ)
    (hbound : base + (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length →
      (flatBytes prog)[base + j]? = (emitImm (UInt256.ofNat slot) ++ [Byte.mload])[j]?) :
    decode (lower prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (UInt256.ofNat slot, 32))
    ∧ decode (lower prog) (UInt32.ofNat base
        + UInt32.ofNat (emitImm (UInt256.ofNat slot)).length) = some (.Smsf .MLOAD, .none) := by
  have hlen : (emitImm (UInt256.ofNat slot)).length = 33 := emitImm_length _
  rw [List.length_append, hlen, List.length_singleton] at hbound
  refine ⟨imm_leaf_decode prog base (UInt256.ofNat slot) (by omega)
      (seg_prefix prog base (emitImm (UInt256.ofNat slot)) [Byte.mload] hseg), ?_⟩
  rw [hlen, ofNat_add']
  have hmload := nonpush_leaf_decode prog base 33 Byte.mload
      (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) (by omega)
      (by rw [List.getElem?_append_right (by rw [hlen]), hlen]; rfl)
      (by decide) hseg
  simpa using hmload

/-! ### `MatFueled` — the recompute-fuel-sufficiency side-condition

`MatDec` marks fuel-exhaustion on a non-leaf as **`False`** ("no decode facts ⇒ unusable") —
B1's `materialise_runs` *consumes* that to discharge the unreachable branch. To *produce*
`MatDec` we need the complementary fact that the fuel is not exhausted: `MatFueled defs fuel
e`, the structural negation of bottoming out. It mirrors `MatDec`'s non-`False` shape
constructor-for-constructor. For a concrete lowering it holds because `recomputeFuel` exceeds
any well-formed def-chain depth (the honest well-formedness tie; see `matDec_of_lower`). -/
def MatFueled (defs : Tmp → Option Expr) : ℕ → Expr → Prop
  | _,      .imm _   => True
  | _,      .slot _ => True
  | 0,      _        => False
  | f + 1,  .tmp t   => match defs t with
                        | some e => MatFueled defs f e
                        | none   => True
  | f + 1,  .add a b => MatFueled defs f (.tmp b) ∧ MatFueled defs f (.tmp a)
  | f + 1,  .lt a b  => MatFueled defs f (.tmp b) ∧ MatFueled defs f (.tmp a)
  | f + 1,  .sload k => MatFueled defs f (.tmp k)
  | _ + 1,  .gas     => True

theorem matFueled_tmp_some (defs : Tmp → Option Expr) (f : ℕ) (t : Tmp) (e : Expr)
    (h : defs t = some e) : MatFueled defs (f + 1) (.tmp t) = MatFueled defs f e := by
  show (match defs t with | some e => MatFueled defs f e | none => True) = _; rw [h]

theorem matFueled_tmp_none (defs : Tmp → Option Expr) (f : ℕ) (t : Tmp)
    (h : defs t = none) : MatFueled defs (f + 1) (.tmp t) = True := by
  show (match defs t with | some e => _ | none => True) = _; rw [h]

/-- **The expression-`MatDec` reconstruction (core deliverable).** From the segment hypothesis
`MatSeg` (the materialise bytes sit at `base` in `flatBytes prog`), the fuel-sufficiency
`MatFueled`, and the pc fitting `UInt32`, the whole structured decode bundle `MatDec` holds at
`UInt32.ofNat base` — discharging B1's carried `MatDec` over `lower prog` generically. By
induction on `materialiseExpr`'s recursion: the binary ops split their two operand segments and
the consuming opcode off the parent; each leaf decode (`PUSH32`/`ADD`/`LT`/`SLOAD`/`GAS`) is
read from the segment byte; the running-pc anchors `UInt32.ofNat base + UInt32.ofNat (sub-len)`
collapse to `UInt32.ofNat (base + sub-len)` by `ofNat_add'`, matching `MatDec` exactly. -/
theorem matDec_of_seg (prog : Program) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : ℕ) (e : Expr) (base : ℕ)
    (hwf : MatFueled defs fuel e)
    (hbound : base + (materialiseExpr defs fuel e).length ≤ 2 ^ 32)
    (hseg : MatSeg prog base defs fuel e) :
    MatDec (lower prog) defs sloadChg fuel (UInt32.ofNat base) e := by
  induction fuel generalizing e base with
  | zero =>
    cases e with
    | imm w =>
      rw [matDec_imm]
      apply imm_leaf_decode prog base w
      · have : (materialiseExpr defs 0 (.imm w)).length = 33 := by simp [materialiseExpr, emitImm_length]
        rw [this] at hbound; omega
      · intro j hj
        have := hseg j (by simpa [materialiseExpr] using hj); simpa [materialiseExpr] using this
    | slot slot =>
      rw [matDec_slot]
      rw [materialiseExpr_slot] at hbound
      unfold MatSeg at hseg; rw [materialiseExpr_slot] at hseg
      exact slot_leaf_decode prog base slot hbound hseg
    | _ => exact absurd hwf (by simp [MatFueled])
  | succ f ih =>
    cases e with
    | imm w =>
      rw [matDec_imm]
      apply imm_leaf_decode prog base w
      · have : (materialiseExpr defs (f + 1) (.imm w)).length = 33 := by simp [materialiseExpr_imm_length]
        rw [this] at hbound; omega
      · intro j hj; have := hseg j hj; simpa [materialiseExpr] using this
    | slot slot =>
      rw [matDec_slot]
      rw [materialiseExpr_slot] at hbound
      unfold MatSeg at hseg; rw [materialiseExpr_slot] at hseg
      exact slot_leaf_decode prog base slot hbound hseg
    | gas =>
      show decode (lower prog) (UInt32.ofNat base) = some (.Smsf .GAS, .none)
      have hseg' : ∀ j, j < [Byte.gas].length → (flatBytes prog)[base + j]? = [Byte.gas][j]? := by
        intro j hj; have := hseg j (by simpa [materialiseExpr] using hj); simpa [materialiseExpr] using this
      have := nonpush_leaf_decode prog base 0 Byte.gas [Byte.gas]
        (by have : (materialiseExpr defs (f + 1) .gas).length = 1 := by simp [materialiseExpr]
            rw [this] at hbound; omega)
        (by decide) (by decide) hseg'
      simpa using this
    | tmp t =>
      cases ht : defs t with
      | some e' =>
        rw [matDec_tmp_some _ _ _ _ _ _ _ ht]
        have hmat : materialiseExpr defs (f + 1) (.tmp t) = materialiseExpr defs f e' :=
          materialiseExpr_tmp_some defs f t e' ht
        apply ih e' base
        · rw [matFueled_tmp_some defs f t e' ht] at hwf; exact hwf
        · rw [hmat] at hbound; exact hbound
        · intro j hj; have := hseg j (by rw [hmat]; exact hj); rw [hmat] at this; exact this
      | none =>
        rw [matDec_tmp_none _ _ _ _ _ _ ht]
        have hmat : materialiseExpr defs (f + 1) (.tmp t) = emitImm (0 : Word) :=
          materialiseExpr_tmp_none defs f t ht
        have := imm_leaf_decode prog base (0 : Word)
          (by rw [hmat, emitImm_length] at hbound; omega)
          (by intro j hj; have := hseg j (by rw [hmat]; exact hj); rw [hmat] at this; exact this)
        simpa using this
    | add a b =>
      rw [matDec_add]
      set sb := materialiseExpr defs f (.tmp b) with hsb
      set sa := materialiseExpr defs f (.tmp a) with hsa
      have hmat : materialiseExpr defs (f + 1) (.add a b) = sb ++ sa ++ [Byte.add] := materialiseExpr_add ..
      obtain ⟨hwfb, hwfa⟩ := hwf
      have hsegL : ∀ j, j < (sb ++ sa ++ [Byte.add]).length →
          (flatBytes prog)[base + j]? = (sb ++ sa ++ [Byte.add])[j]? := by
        intro j hj; have := hseg j (by rw [hmat]; exact hj); rw [hmat] at this; exact this
      have hboundL : base + (sb ++ sa ++ [Byte.add]).length ≤ 2 ^ 32 := by rw [hmat] at hbound; exact hbound
      have hsegBA := seg_prefix prog base (sb ++ sa) [Byte.add] hsegL
      have hsegb : MatSeg prog base defs f (.tmp b) := fun j hj =>
        (seg_prefix prog base sb sa hsegBA) j (by rw [← hsb] at hj; exact hj)
      have hsega : MatSeg prog (base + sb.length) defs f (.tmp a) := fun j hj =>
        (seg_suffix prog base sb sa hsegBA) j (by rw [← hsa] at hj; exact hj)
      have hboundLN : base + (sb.length + sa.length + 1) ≤ 2 ^ 32 := by
        rw [List.length_append, List.length_append] at hboundL; omega
      refine ⟨?_, ?_, ?_⟩
      · exact ih (.tmp b) base hwfb (by rw [← hsb]; omega) hsegb
      · rw [ofNat_add']; exact ih (.tmp a) (base + sb.length) hwfa (by rw [← hsa]; omega) hsega
      · rw [ofNat_add', ofNat_add']
        have := nonpush_leaf_decode prog base (sb.length + sa.length) Byte.add
          (sb ++ sa ++ [Byte.add]) (by omega)
          (by simp) (by decide) hsegL
        rw [show base + (sb.length + sa.length) = base + sb.length + sa.length from by ring] at this
        simpa using this
    | lt a b =>
      rw [matDec_lt]
      set sb := materialiseExpr defs f (.tmp b) with hsb
      set sa := materialiseExpr defs f (.tmp a) with hsa
      have hmat : materialiseExpr defs (f + 1) (.lt a b) = sb ++ sa ++ [Byte.lt] := materialiseExpr_lt ..
      obtain ⟨hwfb, hwfa⟩ := hwf
      have hsegL : ∀ j, j < (sb ++ sa ++ [Byte.lt]).length →
          (flatBytes prog)[base + j]? = (sb ++ sa ++ [Byte.lt])[j]? := by
        intro j hj; have := hseg j (by rw [hmat]; exact hj); rw [hmat] at this; exact this
      have hboundL : base + (sb ++ sa ++ [Byte.lt]).length ≤ 2 ^ 32 := by rw [hmat] at hbound; exact hbound
      have hsegBA := seg_prefix prog base (sb ++ sa) [Byte.lt] hsegL
      have hsegb : MatSeg prog base defs f (.tmp b) := fun j hj =>
        (seg_prefix prog base sb sa hsegBA) j (by rw [← hsb] at hj; exact hj)
      have hsega : MatSeg prog (base + sb.length) defs f (.tmp a) := fun j hj =>
        (seg_suffix prog base sb sa hsegBA) j (by rw [← hsa] at hj; exact hj)
      have hboundLN : base + (sb.length + sa.length + 1) ≤ 2 ^ 32 := by
        rw [List.length_append, List.length_append] at hboundL; omega
      refine ⟨?_, ?_, ?_⟩
      · exact ih (.tmp b) base hwfb (by rw [← hsb]; omega) hsegb
      · rw [ofNat_add']; exact ih (.tmp a) (base + sb.length) hwfa (by rw [← hsa]; omega) hsega
      · rw [ofNat_add', ofNat_add']
        have := nonpush_leaf_decode prog base (sb.length + sa.length) Byte.lt
          (sb ++ sa ++ [Byte.lt]) (by omega)
          (by simp) (by decide) hsegL
        rw [show base + (sb.length + sa.length) = base + sb.length + sa.length from by ring] at this
        simpa using this
    | sload k =>
      rw [matDec_sload]
      set sk := materialiseExpr defs f (.tmp k) with hsk
      have hmat : materialiseExpr defs (f + 1) (.sload k) = sk ++ [Byte.sload] := materialiseExpr_sload ..
      have hwfk : MatFueled defs f (.tmp k) := hwf
      have hsegL : ∀ j, j < (sk ++ [Byte.sload]).length →
          (flatBytes prog)[base + j]? = (sk ++ [Byte.sload])[j]? := by
        intro j hj; have := hseg j (by rw [hmat]; exact hj); rw [hmat] at this; exact this
      have hboundL : base + (sk ++ [Byte.sload]).length ≤ 2 ^ 32 := by rw [hmat] at hbound; exact hbound
      have hsegk : MatSeg prog base defs f (.tmp k) := fun j hj =>
        (seg_prefix prog base sk [Byte.sload] hsegL) j (by rw [← hsk] at hj; exact hj)
      have hboundLN : base + (sk.length + 1) ≤ 2 ^ 32 := by rw [List.length_append] at hboundL; omega
      refine ⟨?_, ?_⟩
      · exact ih (.tmp k) base hwfk (by rw [← hsk]; omega) hsegk
      · rw [ofNat_add']
        have := nonpush_leaf_decode prog base sk.length Byte.sload (sk ++ [Byte.sload]) (by omega)
          (by simp) (by decide) hsegL
        simpa using this

/-! ## `matDec_of_lower` — `MatDec` at a statement cursor

Specialising `matDec_of_seg` to a statement cursor: the materialise bytes of an operand are a
contiguous sub-list of the statement's `emitStmt` bytes, so `MatSeg` holds at
`pcOf prog L pc + offset` via the statement byte anchor (`flatBytes_at_pcOf_offset`). -/

/-- **`MatSeg` at a statement cursor.** When `materialiseExpr defs fuel e`'s bytes are the
sub-list of `emitStmt … s` starting at `offset`, they sit in `flatBytes prog` at
`pcOf prog L pc + offset` — built from `flatBytes_at_pcOf_offset`. -/
theorem matSeg_of_stmt (prog : Program) (L : Label) (b : Block) (pc : ℕ) (s : Stmt)
    (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hsub : ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length →
        (emitStmt (defsOf prog) (recomputeFuel prog) s)[offset + j]?
          = (materialiseExpr (defsOf prog) (recomputeFuel prog) e)[j]?)
    (hin : offset + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length
        ≤ (emitStmt (defsOf prog) (recomputeFuel prog) s).length) :
    MatSeg prog (pcOf prog L pc + offset) (defsOf prog) (recomputeFuel prog) e := by
  intro j hj
  have hanchor := flatBytes_at_pcOf_offset prog L b pc s (offset + j) hb hs (by omega)
  rw [show pcOf prog L pc + (offset + j) = pcOf prog L pc + offset + j from by ring] at hanchor
  rw [hanchor]; exact hsub j hj

/-- **`matDec_of_lower` (headline).** For an operand `e` whose materialise bytes form the
sub-list of statement `s`'s lowering at byte `offset`, `MatDec (lower prog) … (UInt32.ofNat
(pcOf prog L pc + offset)) e` holds — given fuel-sufficiency (`MatFueled`) and the pc bound.
This is the generic discharge of B1's carried `MatDec` hypothesis over `lower prog` at any
statement cursor. -/
theorem matDec_of_lower (prog : Program) (sloadChg : Tmp → ℕ) (L : Label) (b : Block)
    (pc : ℕ) (s : Stmt) (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hsub : ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length →
        (emitStmt (defsOf prog) (recomputeFuel prog) s)[offset + j]?
          = (materialiseExpr (defsOf prog) (recomputeFuel prog) e)[j]?)
    (hin : offset + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length
        ≤ (emitStmt (defsOf prog) (recomputeFuel prog) s).length)
    (hwf : MatFueled (defsOf prog) (recomputeFuel prog) e)
    (hbound : pcOf prog L pc + offset
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length ≤ 2 ^ 32) :
    MatDec (lower prog) (defsOf prog) sloadChg (recomputeFuel prog)
      (UInt32.ofNat (pcOf prog L pc + offset)) e :=
  matDec_of_seg prog (defsOf prog) sloadChg (recomputeFuel prog) e (pcOf prog L pc + offset)
    hwf (by omega) (matSeg_of_stmt prog L b pc s offset e hb hs hsub hin)

/-! ## `matDec_of_term` — `MatDec` at a terminator cursor

The terminator analogue of `matDec_of_lower`: when `materialiseExpr defs fuel e`'s bytes are
the sub-list of `emitTerm … b.term` starting at `offset`, they sit in `flatBytes prog` at
`termOf prog L + offset` (via the terminator byte anchor `flatBytes_at_termOf`), so `MatSeg`
holds there. The branch's cond materialise is exactly this at `offset = 0`. -/

/-- **`MatSeg` at a terminator cursor.** When `materialiseExpr defs fuel e`'s bytes are the
sub-list of `emitTerm … b.term` starting at `offset`, they sit in `flatBytes prog` at
`termOf prog L + offset` — built from `flatBytes_at_termOf`. -/
theorem matSeg_of_term (prog : Program) (L : Label) (b : Block) (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hsub : ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length →
        (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[offset + j]?
          = (materialiseExpr (defsOf prog) (recomputeFuel prog) e)[j]?)
    (hin : offset + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length
        ≤ (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length) :
    MatSeg prog (termOf prog L + offset) (defsOf prog) (recomputeFuel prog) e := by
  intro j hj
  have hanchor := flatBytes_at_termOf prog L b (offset + j) hb (by omega)
  rw [show termOf prog L + (offset + j) = termOf prog L + offset + j from by ring] at hanchor
  rw [hanchor]; exact hsub j hj

/-- **`matDec_of_term` (terminator headline).** For an operand `e` whose materialise bytes form
the sub-list of `emitTerm … b.term` at byte `offset`, `MatDec (lower prog) … (UInt32.ofNat
(termOf prog L + offset)) e` holds — given fuel-sufficiency (`MatFueled`) and the pc bound. The
branch's cond materialise is this at `offset = 0`. -/
theorem matDec_of_term (prog : Program) (sloadChg : Tmp → ℕ) (L : Label) (b : Block)
    (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hsub : ∀ j, j < (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length →
        (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[offset + j]?
          = (materialiseExpr (defsOf prog) (recomputeFuel prog) e)[j]?)
    (hin : offset + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length
        ≤ (emitTerm (defsOf prog) (recomputeFuel prog)
            (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length)
    (hwf : MatFueled (defsOf prog) (recomputeFuel prog) e)
    (hbound : termOf prog L + offset
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) e).length ≤ 2 ^ 32) :
    MatDec (lower prog) (defsOf prog) sloadChg (recomputeFuel prog)
      (UInt32.ofNat (termOf prog L + offset)) e :=
  matDec_of_seg prog (defsOf prog) sloadChg (recomputeFuel prog) e (termOf prog L + offset)
    hwf (by omega) (matSeg_of_term prog L b offset e hb hsub hin)

end Lir
