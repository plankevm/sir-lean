import Init.Data.Nat.Div
import Std.Tactic.BVDecide
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace Evm

def UInt256.size : ℕ :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

private theorem UInt256.size_eq_2pow256 : UInt256.size = 2^256 := by rfl

instance : NeZero UInt256.size where
  out := (by unfold UInt256.size; simp)

/--
A 256-bit EVM word as eight 32-bit limbs, least-significant first.

The representation is 32-bit limbs (not 64) so that every intermediate of the
limb-level multiplication fits `UInt64` (`(2^32-1)^2 + 2*(2^32-1) < 2^64`).
All eight fields are scalar, so a value is a single flat unboxed object —
no GMP allocation, unlike the previous `Fin (2^256)` representation.

The *semantic reference* is `BitVec 256` via `toBitVec`. Every limb-level
operation below is proven equivalent to its `BitVec` counterpart
(`toBitVec_add`, `toBitVec_mul`, …), so the limb arithmetic is not part of
the trust surface. Operations without a limb-level implementation go through
`toNat`/`ofNat` round-trips and are correct by construction.
-/
structure UInt256 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
  deriving DecidableEq

namespace UInt256

/-- Semantic reference value: most-significant limb first in the append. -/
def toBitVec (a : UInt256) : BitVec 256 :=
  a.l7.toBitVec ++ a.l6.toBitVec ++ a.l5.toBitVec ++ a.l4.toBitVec ++
  a.l3.toBitVec ++ a.l2.toBitVec ++ a.l1.toBitVec ++ a.l0.toBitVec

def ofBitVec (b : BitVec 256) : UInt256 :=
  ⟨ ⟨b.extractLsb'   0 32⟩, ⟨b.extractLsb'  32 32⟩
  , ⟨b.extractLsb'  64 32⟩, ⟨b.extractLsb'  96 32⟩
  , ⟨b.extractLsb' 128 32⟩, ⟨b.extractLsb' 160 32⟩
  , ⟨b.extractLsb' 192 32⟩, ⟨b.extractLsb' 224 32⟩ ⟩

def ofUInt32 (a : UInt32) : UInt256 := ⟨a, 0, 0, 0, 0, 0, 0, 0 ⟩

def ofUInt64 (a : UInt64) : UInt256 :=
  ⟨a.toUInt32, (a >>> (32 : UInt64)).toUInt32, 0, 0, 0, 0, 0, 0⟩

def toUInt64 (a : UInt256) : UInt64 :=
  a.l0.toUInt64 ||| (a.l1.toUInt64 <<< (32 : UInt64))

def toUInt64? (a : UInt256) : Option UInt64 :=
  if a.l2 == 0 && a.l3 == 0 && a.l4 == 0 && a.l5 == 0 && a.l6 == 0 && a.l7 == 0 then
    some a.toUInt64
  else
    none

def toUInt32? (a : UInt256) : Option UInt32 :=
  if a.l1 == 0 && a.l2 == 0 && a.l3 == 0 && a.l4 == 0 &&
      a.l5 == 0 && a.l6 == 0 && a.l7 == 0 then
    some a.l0
  else
    none

def toNat (a : UInt256) : ℕ := a.toBitVec.toNat

def ofNat (n : ℕ) : UInt256 :=
  ⟨ .ofNat n          , .ofNat (n >>> 32) , .ofNat (n >>> 64) , .ofNat (n >>> 96)
  , .ofNat (n >>> 128), .ofNat (n >>> 160), .ofNat (n >>> 192), .ofNat (n >>> 224) ⟩

/-- Runtime implementation of `toNat` (`@[csimp]`-substituted, proven equal):
values below 2^64 — gas, memory offsets, sizes — skip the `BitVec` append
construction entirely. -/
def toNatFast (a : UInt256) : ℕ :=
  if a.l2 == 0 && a.l3 == 0 && a.l4 == 0 && a.l5 == 0 && a.l6 == 0 && a.l7 == 0
  then (a.l0.toUInt64 + (a.l1.toUInt64 <<< 32)).toNat
  else a.toBitVec.toNat

/-- Runtime implementation of `ofNat` (`@[csimp]`-substituted, proven equal):
small naturals avoid the eight shifted `UInt32.ofNat` conversions. -/
def ofNatFast (n : ℕ) : UInt256 :=
  if n < 2^64
  then ⟨.ofNat n, .ofNat (n >>> 32), 0, 0, 0, 0, 0, 0⟩
  else
    ⟨ .ofNat n          , .ofNat (n >>> 32) , .ofNat (n >>> 64) , .ofNat (n >>> 96)
    , .ofNat (n >>> 128), .ofNat (n >>> 160), .ofNat (n >>> 192), .ofNat (n >>> 224) ⟩

instance {n : ℕ} : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩

instance : ToString UInt256 where
  toString a := toString a.toNat

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

/-- Limb decomposition of `toNat`. -/
theorem toNat_limbs (a : UInt256) :
    a.toNat = a.l0.toNat + a.l1.toNat * 2^32 + a.l2.toNat * 2^64 + a.l3.toNat * 2^96 +
      a.l4.toNat * 2^128 + a.l5.toNat * 2^160 + a.l6.toNat * 2^192 + a.l7.toNat * 2^224 := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := a
  simp only [toNat, toBitVec, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by exact l0.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l1.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l2.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l3.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l4.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l5.toBitVec.isLt),
      ← Nat.shiftLeft_add_eq_or_of_lt (by exact l6.toBitVec.isLt)]
  simp only [Nat.shiftLeft_eq]
  show _ = l0.toBitVec.toNat + l1.toBitVec.toNat * 2^32 + l2.toBitVec.toNat * 2^64 +
    l3.toBitVec.toNat * 2^96 + l4.toBitVec.toNat * 2^128 + l5.toBitVec.toNat * 2^160 +
    l6.toBitVec.toNat * 2^192 + l7.toBitVec.toNat * 2^224
  ring

@[csimp] theorem toNat_eq_toNatFast : @toNat = @toNatFast := by
  funext a
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := a
  simp only [toNatFast]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    subst h2 h3 h4 h5 h6 h7
    rw [toNat_limbs]
    have q0 : l0.toNat < 2^32 := l0.toBitVec.isLt
    have q1 : l1.toNat < 2^32 := l1.toBitVec.isLt
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.toNat_ofNat]
    norm_num
    omega
  · rfl

@[csimp] theorem ofNat_eq_ofNatFast : @ofNat = @ofNatFast := by
  funext n
  simp only [ofNatFast]
  split
  · rename_i h
    have e64 : n >>> 64 = 0 := by omega
    have e96 : n >>> 96 = 0 := by omega
    have e128 : n >>> 128 = 0 := by omega
    have e160 : n >>> 160 = 0 := by omega
    have e192 : n >>> 192 = 0 := by omega
    have e224 : n >>> 224 = 0 := by omega
    simp only [ofNat, e64, e96, e128, e160, e192, e224]
    rfl
  · rfl

/-! ### Limb-level operations (proven equivalent to `BitVec 256`) -/

def add (a b : UInt256) : UInt256 :=
  let s0 := a.l0.toUInt64 + b.l0.toUInt64
  let s1 := a.l1.toUInt64 + b.l1.toUInt64 + (s0 >>> 32)
  let s2 := a.l2.toUInt64 + b.l2.toUInt64 + (s1 >>> 32)
  let s3 := a.l3.toUInt64 + b.l3.toUInt64 + (s2 >>> 32)
  let s4 := a.l4.toUInt64 + b.l4.toUInt64 + (s3 >>> 32)
  let s5 := a.l5.toUInt64 + b.l5.toUInt64 + (s4 >>> 32)
  let s6 := a.l6.toUInt64 + b.l6.toUInt64 + (s5 >>> 32)
  let s7 := a.l7.toUInt64 + b.l7.toUInt64 + (s6 >>> 32)
  ⟨s0.toUInt32, s1.toUInt32, s2.toUInt32, s3.toUInt32,
   s4.toUInt32, s5.toUInt32, s6.toUInt32, s7.toUInt32⟩

/-- `a - b` as `a + ~b + 1`, one carry chain. -/
def sub (a b : UInt256) : UInt256 :=
  let s0 := a.l0.toUInt64 + (~~~b.l0).toUInt64 + 1
  let s1 := a.l1.toUInt64 + (~~~b.l1).toUInt64 + (s0 >>> 32)
  let s2 := a.l2.toUInt64 + (~~~b.l2).toUInt64 + (s1 >>> 32)
  let s3 := a.l3.toUInt64 + (~~~b.l3).toUInt64 + (s2 >>> 32)
  let s4 := a.l4.toUInt64 + (~~~b.l4).toUInt64 + (s3 >>> 32)
  let s5 := a.l5.toUInt64 + (~~~b.l5).toUInt64 + (s4 >>> 32)
  let s6 := a.l6.toUInt64 + (~~~b.l6).toUInt64 + (s5 >>> 32)
  let s7 := a.l7.toUInt64 + (~~~b.l7).toUInt64 + (s6 >>> 32)
  ⟨s0.toUInt32, s1.toUInt32, s2.toUInt32, s3.toUInt32,
   s4.toUInt32, s5.toUInt32, s6.toUInt32, s7.toUInt32⟩

/-- One multiply-accumulate step of the schoolbook multiplication:
returns the 32-bit digit and the carry-out. -/
def mulCarry (x m c : UInt64) : UInt32 × UInt64 :=
  let t := x * m + c
  (t.toUInt32, t >>> 32)

/-- 256×32-bit multiplication, truncated to 256 bits. Carry chain never
overflows `UInt64`: `(2^32-1)·(2^32-1) + (2^32-1) + (2^32-1) < 2^64`. -/
def mulLimb (a : UInt256) (m : UInt32) : UInt256 :=
  let m64 := m.toUInt64
  let s0 := mulCarry a.l0.toUInt64 m64 0
  let s1 := mulCarry a.l1.toUInt64 m64 s0.2
  let s2 := mulCarry a.l2.toUInt64 m64 s1.2
  let s3 := mulCarry a.l3.toUInt64 m64 s2.2
  let s4 := mulCarry a.l4.toUInt64 m64 s3.2
  let s5 := mulCarry a.l5.toUInt64 m64 s4.2
  let s6 := mulCarry a.l6.toUInt64 m64 s5.2
  let s7 := mulCarry a.l7.toUInt64 m64 s6.2
  ⟨s0.1, s1.1, s2.1, s3.1, s4.1, s5.1, s6.1, s7.1⟩

/-- Shift left by one limb (32 bits), dropping the top limb. -/
def shiftLimb (x : UInt256) : UInt256 := ⟨0, x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, x.l6⟩

/-- Full 256×256-bit multiplication mod 2^256: Horner over the limbs of `b`,
most significant first. Proven equivalent to `BitVec.mul` in `toBitVec_mul`
without any SAT/`ofReduceBool` dependence — see `toNat_mul`. -/
def mul (a b : UInt256) : UInt256 :=
  let acc := mulLimb a b.l7
  let acc := add (shiftLimb acc) (mulLimb a b.l6)
  let acc := add (shiftLimb acc) (mulLimb a b.l5)
  let acc := add (shiftLimb acc) (mulLimb a b.l4)
  let acc := add (shiftLimb acc) (mulLimb a b.l3)
  let acc := add (shiftLimb acc) (mulLimb a b.l2)
  let acc := add (shiftLimb acc) (mulLimb a b.l1)
  add (shiftLimb acc) (mulLimb a b.l0)


def land (a b : UInt256) : UInt256 :=
  ⟨a.l0 &&& b.l0, a.l1 &&& b.l1, a.l2 &&& b.l2, a.l3 &&& b.l3,
   a.l4 &&& b.l4, a.l5 &&& b.l5, a.l6 &&& b.l6, a.l7 &&& b.l7⟩

def lor (a b : UInt256) : UInt256 :=
  ⟨a.l0 ||| b.l0, a.l1 ||| b.l1, a.l2 ||| b.l2, a.l3 ||| b.l3,
   a.l4 ||| b.l4, a.l5 ||| b.l5, a.l6 ||| b.l6, a.l7 ||| b.l7⟩

def xor (a b : UInt256) : UInt256 :=
  ⟨a.l0 ^^^ b.l0, a.l1 ^^^ b.l1, a.l2 ^^^ b.l2, a.l3 ^^^ b.l3,
   a.l4 ^^^ b.l4, a.l5 ^^^ b.l5, a.l6 ^^^ b.l6, a.l7 ^^^ b.l7⟩

/-- Bitwise NOT. -/
def complement (a : UInt256) : UInt256 :=
  ⟨~~~a.l0, ~~~a.l1, ~~~a.l2, ~~~a.l3, ~~~a.l4, ~~~a.l5, ~~~a.l6, ~~~a.l7⟩

def beq (a b : UInt256) : Bool :=
  a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3 &&
  a.l4 == b.l4 && a.l5 == b.l5 && a.l6 == b.l6 && a.l7 == b.l7

instance : BEq UInt256 := ⟨beq⟩

/-- Unsigned less-than, lexicographic from the most significant limb. -/
def blt (a b : UInt256) : Bool :=
  (a.l7.toBitVec.ult b.l7.toBitVec) ||
  (a.l7 == b.l7 && ((a.l6.toBitVec.ult b.l6.toBitVec) ||
  (a.l6 == b.l6 && ((a.l5.toBitVec.ult b.l5.toBitVec) ||
  (a.l5 == b.l5 && ((a.l4.toBitVec.ult b.l4.toBitVec) ||
  (a.l4 == b.l4 && ((a.l3.toBitVec.ult b.l3.toBitVec) ||
  (a.l3 == b.l3 && ((a.l2.toBitVec.ult b.l2.toBitVec) ||
  (a.l2 == b.l2 && ((a.l1.toBitVec.ult b.l1.toBitVec) ||
  (a.l1 == b.l1 && a.l0.toBitVec.ult b.l0.toBitVec)))))))))))))

def ble (a b : UInt256) : Bool := !(blt b a)

/-! ### `BitVec 256` equivalence -/

section BitVecEquivalence

theorem toBitVec_ofBitVec (b : BitVec 256) : (ofBitVec b).toBitVec = b := by
  simp [ofBitVec, toBitVec]
  bv_decide

theorem ofBitVec_toBitVec (a : UInt256) : ofBitVec a.toBitVec = a := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := a
  simp [ofBitVec, toBitVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · apply UInt32.toBitVec_inj.mp; simp; bv_decide

set_option maxHeartbeats 1000000 in
/-- `add` is correct over `Nat` — proved without SAT/`ofReduceBool`. -/
theorem toNat_add (x y : UInt256) : (add x y).toNat = (x.toNat + y.toNat) % 2^256 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  simp only [add, toNat_limbs]
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_shiftRight,
    UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
  have q0 : x0.toNat < 2^32 := x0.toBitVec.isLt
  have q1 : x1.toNat < 2^32 := x1.toBitVec.isLt
  have q2 : x2.toNat < 2^32 := x2.toBitVec.isLt
  have q3 : x3.toNat < 2^32 := x3.toBitVec.isLt
  have q4 : x4.toNat < 2^32 := x4.toBitVec.isLt
  have q5 : x5.toNat < 2^32 := x5.toBitVec.isLt
  have q6 : x6.toNat < 2^32 := x6.toBitVec.isLt
  have q7 : x7.toNat < 2^32 := x7.toBitVec.isLt
  have r0 : y0.toNat < 2^32 := y0.toBitVec.isLt
  have r1 : y1.toNat < 2^32 := y1.toBitVec.isLt
  have r2 : y2.toNat < 2^32 := y2.toBitVec.isLt
  have r3 : y3.toNat < 2^32 := y3.toBitVec.isLt
  have r4 : y4.toNat < 2^32 := y4.toBitVec.isLt
  have r5 : y5.toNat < 2^32 := y5.toBitVec.isLt
  have r6 : y6.toNat < 2^32 := y6.toBitVec.isLt
  have r7 : y7.toNat < 2^32 := y7.toBitVec.isLt
  norm_num
  omega

theorem toBitVec_add (a b : UInt256) : (add a b).toBitVec = a.toBitVec + b.toBitVec :=
  BitVec.eq_of_toNat_eq (by simpa [BitVec.toNat_add] using toNat_add a b)

theorem toBitVec_sub (a b : UInt256) : (sub a b).toBitVec = a.toBitVec - b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [sub, toBitVec]
  bv_decide

/-! #### Multiplication correctness — axiom-free (no SAT / `ofReduceBool`) -/

theorem mulCarry_spec (x m c : UInt64)
    (hx : x.toNat < 2^32) (hm : m.toNat < 2^32) (hc : c.toNat < 2^32) :
    (mulCarry x m c).1.toNat + 2^32 * (mulCarry x m c).2.toNat = x.toNat * m.toNat + c.toNat
    ∧ (mulCarry x m c).2.toNat < 2^32 := by
  have hp : x.toNat * m.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [mulCarry, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_ofNat]
  generalize x.toNat * m.toNat = p at hp
  norm_num
  omega

set_option maxHeartbeats 1000000 in
theorem toNat_mulLimb (a : UInt256) (m : UInt32) :
    (mulLimb a m).toNat = (a.toNat * m.toNat) % 2^256 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  have h32 : ∀ x : UInt32, x.toUInt64.toNat < 2^32 := λ x ↦ by
    simp [UInt32.toNat_toUInt64]; exact x.toBitVec.isLt
  have h0' : (0 : UInt64).toNat < 2^32 := by simp
  obtain ⟨e0, b0⟩ := mulCarry_spec a0.toUInt64 m.toUInt64 0 (h32 a0) (h32 m) h0'
  obtain ⟨e1, b1⟩ := mulCarry_spec a1.toUInt64 m.toUInt64 _ (h32 a1) (h32 m) b0
  obtain ⟨e2, b2⟩ := mulCarry_spec a2.toUInt64 m.toUInt64 _ (h32 a2) (h32 m) b1
  obtain ⟨e3, b3⟩ := mulCarry_spec a3.toUInt64 m.toUInt64 _ (h32 a3) (h32 m) b2
  obtain ⟨e4, b4⟩ := mulCarry_spec a4.toUInt64 m.toUInt64 _ (h32 a4) (h32 m) b3
  obtain ⟨e5, b5⟩ := mulCarry_spec a5.toUInt64 m.toUInt64 _ (h32 a5) (h32 m) b4
  obtain ⟨e6, b6⟩ := mulCarry_spec a6.toUInt64 m.toUInt64 _ (h32 a6) (h32 m) b5
  obtain ⟨e7, b7⟩ := mulCarry_spec a7.toUInt64 m.toUInt64 _ (h32 a7) (h32 m) b6
  simp only [UInt32.toNat_toUInt64] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [mulLimb, toNat_limbs]
  rw [show
      (a0.toNat + a1.toNat * 2^32 + a2.toNat * 2^64 + a3.toNat * 2^96 + a4.toNat * 2^128 +
        a5.toNat * 2^160 + a6.toNat * 2^192 + a7.toNat * 2^224) * m.toNat =
      a0.toNat * m.toNat + (a1.toNat * m.toNat) * 2^32 + (a2.toNat * m.toNat) * 2^64 +
      (a3.toNat * m.toNat) * 2^96 + (a4.toNat * m.toNat) * 2^128 +
      (a5.toNat * m.toNat) * 2^160 + (a6.toNat * m.toNat) * 2^192 +
      (a7.toNat * m.toNat) * 2^224 from by ring]
  set s0 := mulCarry a0.toUInt64 m.toUInt64 0 with hs0
  set s1 := mulCarry a1.toUInt64 m.toUInt64 s0.2 with hs1
  set s2 := mulCarry a2.toUInt64 m.toUInt64 s1.2 with hs2
  set s3 := mulCarry a3.toUInt64 m.toUInt64 s2.2 with hs3
  set s4 := mulCarry a4.toUInt64 m.toUInt64 s3.2 with hs4
  set s5 := mulCarry a5.toUInt64 m.toUInt64 s4.2 with hs5
  set s6 := mulCarry a6.toUInt64 m.toUInt64 s5.2 with hs6
  set s7 := mulCarry a7.toUInt64 m.toUInt64 s6.2 with hs7
  set p0 := a0.toNat * m.toNat with hp0
  set p1 := a1.toNat * m.toNat with hp1
  set p2 := a2.toNat * m.toNat with hp2
  set p3 := a3.toNat * m.toNat with hp3
  set p4 := a4.toNat * m.toNat with hp4
  set p5 := a5.toNat * m.toNat with hp5
  set p6 := a6.toNat * m.toNat with hp6
  set p7 := a7.toNat * m.toNat with hp7
  have d0 : s0.1.toNat < 2^32 := s0.1.toBitVec.isLt
  have d1 : s1.1.toNat < 2^32 := s1.1.toBitVec.isLt
  have d2 : s2.1.toNat < 2^32 := s2.1.toBitVec.isLt
  have d3 : s3.1.toNat < 2^32 := s3.1.toBitVec.isLt
  have d4 : s4.1.toNat < 2^32 := s4.1.toBitVec.isLt
  have d5 : s5.1.toNat < 2^32 := s5.1.toBitVec.isLt
  have d6 : s6.1.toNat < 2^32 := s6.1.toBitVec.isLt
  have d7 : s7.1.toNat < 2^32 := s7.1.toBitVec.isLt
  norm_num at e0
  omega

theorem toNat_shiftLimb (x : UInt256) : (shiftLimb x).toNat = x.toNat * 2^32 % 2^256 := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := x
  simp only [shiftLimb, toNat_limbs]
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have q0 : l0.toNat < 2^32 := l0.toBitVec.isLt
  have q1 : l1.toNat < 2^32 := l1.toBitVec.isLt
  have q2 : l2.toNat < 2^32 := l2.toBitVec.isLt
  have q3 : l3.toNat < 2^32 := l3.toBitVec.isLt
  have q4 : l4.toNat < 2^32 := l4.toBitVec.isLt
  have q5 : l5.toNat < 2^32 := l5.toBitVec.isLt
  have q6 : l6.toNat < 2^32 := l6.toBitVec.isLt
  have q7 : l7.toNat < 2^32 := l7.toBitVec.isLt
  rw [h0]
  omega

set_option maxHeartbeats 2000000 in
theorem toNat_mul (a b : UInt256) : (mul a b).toNat = a.toNat * b.toNat % 2^256 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [mul, toNat_add, toNat_shiftLimb, toNat_mulLimb]
  rw [show (UInt256.mk b0 b1 b2 b3 b4 b5 b6 b7).toNat =
        b0.toNat + b1.toNat * 2^32 + b2.toNat * 2^64 + b3.toNat * 2^96 + b4.toNat * 2^128 +
        b5.toNat * 2^160 + b6.toNat * 2^192 + b7.toNat * 2^224 from toNat_limbs _]
  rw [show a.toNat * (b0.toNat + b1.toNat * 2^32 + b2.toNat * 2^64 + b3.toNat * 2^96 +
        b4.toNat * 2^128 + b5.toNat * 2^160 + b6.toNat * 2^192 + b7.toNat * 2^224) =
      a.toNat * b0.toNat + (a.toNat * b1.toNat) * 2^32 + (a.toNat * b2.toNat) * 2^64 +
      (a.toNat * b3.toNat) * 2^96 + (a.toNat * b4.toNat) * 2^128 +
      (a.toNat * b5.toNat) * 2^160 + (a.toNat * b6.toNat) * 2^192 +
      (a.toNat * b7.toNat) * 2^224 from by ring]
  set q0 := a.toNat * b0.toNat with hq0
  set q1 := a.toNat * b1.toNat with hq1
  set q2 := a.toNat * b2.toNat with hq2
  set q3 := a.toNat * b3.toNat with hq3
  set q4 := a.toNat * b4.toNat with hq4
  set q5 := a.toNat * b5.toNat with hq5
  set q6 := a.toNat * b6.toNat with hq6
  set q7 := a.toNat * b7.toNat with hq7
  omega

theorem toBitVec_mul (a b : UInt256) : (mul a b).toBitVec = a.toBitVec * b.toBitVec :=
  BitVec.eq_of_toNat_eq (by simpa [BitVec.toNat_mul] using toNat_mul a b)

theorem toBitVec_land (a b : UInt256) : (land a b).toBitVec = a.toBitVec &&& b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [land, toBitVec]
  bv_decide

theorem toBitVec_lor (a b : UInt256) : (lor a b).toBitVec = a.toBitVec ||| b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [lor, toBitVec]
  bv_decide

theorem toBitVec_xor (a b : UInt256) : (xor a b).toBitVec = a.toBitVec ^^^ b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [xor, toBitVec]
  bv_decide

theorem toBitVec_complement (a : UInt256) : (complement a).toBitVec = ~~~a.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  simp [complement, toBitVec]
  bv_decide

theorem toBitVec_inj {a b : UInt256} (h : a.toBitVec = b.toBitVec) : a = b := by
  have := congrArg ofBitVec h
  rwa [ofBitVec_toBitVec, ofBitVec_toBitVec] at this

theorem toNat_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b :=
  toBitVec_inj (BitVec.eq_of_toNat_eq h)

theorem beq_iff_eq (a b : UInt256) : beq a b = true ↔ a = b := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [beq, and_assoc]

theorem beq_iff_toBitVec_eq (a b : UInt256) : beq a b = true ↔ a.toBitVec = b.toBitVec :=
  ⟨λ h ↦ congrArg toBitVec ((beq_iff_eq a b).mp h),
   λ h ↦ (beq_iff_eq a b).mpr (toBitVec_inj h)⟩

private theorem ult_iff_toNat_lt (a b : UInt32) :
    a.toBitVec.ult b.toBitVec = true ↔ a.toNat < b.toNat := by
  rw [BitVec.ult]; simp [UInt32.toNat_toBitVec]

private theorem beq_iff_toNat_eq (a b : UInt32) :
    (a == b) = true ↔ a.toNat = b.toNat := by
  rw [_root_.beq_iff_eq (a := a) (b := b)]
  exact ⟨fun h => by rw [h], fun h => UInt32.toNat_inj.mp h⟩

theorem blt_iff_toBitVec_lt (a b : UInt256) : blt a b = true ↔ a.toBitVec < b.toBitVec := by
  -- Reduce both sides to a comparison of the limb decomposition over `Nat`:
  -- `blt` becomes the lexicographic disjunction (MSB limb first) and
  -- `toBitVec < toBitVec` becomes the weighted-sum-of-limbs `<`.  With the
  -- per-limb `< 2^32` bounds in scope, `omega` discharges the equivalence
  -- (every weight `2^(32·i)` is a literal constant, so it stays linear).
  rw [BitVec.lt_def]
  show blt a b = true ↔ a.toNat < b.toNat
  rw [toNat_limbs, toNat_limbs]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [blt, Bool.or_eq_true, Bool.and_eq_true, ult_iff_toNat_lt, beq_iff_toNat_eq]
  have ha0 := a0.toBitVec.isLt; have hb0 := b0.toBitVec.isLt
  have ha1 := a1.toBitVec.isLt; have hb1 := b1.toBitVec.isLt
  have ha2 := a2.toBitVec.isLt; have hb2 := b2.toBitVec.isLt
  have ha3 := a3.toBitVec.isLt; have hb3 := b3.toBitVec.isLt
  have ha4 := a4.toBitVec.isLt; have hb4 := b4.toBitVec.isLt
  have ha5 := a5.toBitVec.isLt; have hb5 := b5.toBitVec.isLt
  have ha6 := a6.toBitVec.isLt; have hb6 := b6.toBitVec.isLt
  have ha7 := a7.toBitVec.isLt; have hb7 := b7.toBitVec.isLt
  simp only [UInt32.toNat_toBitVec] at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  omega

end BitVecEquivalence

/-! ### Order and remaining instances -/

theorem toNat_eq_toBitVec_toNat (a : UInt256) : a.toNat = a.toBitVec.toNat := rfl

instance : LT UInt256 where
  lt a b := a.toBitVec < b.toBitVec

instance : LE UInt256 where
  le a b := a.toBitVec ≤ b.toBitVec

instance (a b : UInt256) : Decidable (a < b) :=
  decidable_of_iff _ (blt_iff_toBitVec_lt a b)

instance (a b : UInt256) : Decidable (a ≤ b) :=
  decidable_of_iff (blt b a = false) <| by
    have h := blt_iff_toBitVec_lt b a
    constructor
    · intro hf
      have : ¬ (b.toBitVec < a.toBitVec) := λ hc ↦ by simp [h.mpr hc] at hf
      exact BitVec.not_lt.mp this
    · intro hle
      cases hb : blt b a
      · rfl
      · exact absurd (h.mp hb) (BitVec.not_lt.mpr hle)

instance : Preorder UInt256 where
  le_refl a := BitVec.le_refl _
  le_trans _ _ _ h₁ h₂ := BitVec.le_trans h₁ h₂
  lt_iff_le_not_ge a b := by
    constructor
    · intro h; exact ⟨BitVec.le_of_lt h, BitVec.not_le.mpr h⟩
    · intro ⟨_, h⟩; exact BitVec.not_le.mp h

instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

instance : Ord UInt256 where
  compare a b := if a < b then .lt else if b < a then .gt else .eq

/-! ### Operations via `Nat`/`BitVec` round-trip (correct by construction) -/

def div (a b : UInt256) : UInt256 := ofNat (a.toNat / b.toNat)

def mod (a b : UInt256) : UInt256 := if b.toNat == 0 then 0 else ofNat (a.toNat % b.toNat)

def modn (a : UInt256) (n : ℕ) : UInt256 := if n == 0 then a else ofNat (a.toNat % n)

def shiftLeft (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then 0 else ofBitVec (a.toBitVec <<< b.toNat)

def shiftRight (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then 0 else ofBitVec (a.toBitVec >>> b.toNat)

def log2 (a : UInt256) : UInt256 := ofNat a.toNat.log2

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩
instance : Complement UInt256 := ⟨UInt256.complement⟩

def lnot (a : UInt256) : UInt256 := complement a

def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then sub 0 a
  else a

def toSigned (i : ℤ) : UInt256 :=
  match i with
    | .ofNat n => ofNat n
    | .negSucc n => ofNat (UInt256.size - 1 - n)

private def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux 1 b n.toNat

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

def eq0 (a : UInt256) : Bool := a == 0

def byteAt (a b : UInt256) : UInt256 :=
  if a > 31 then 0 else
    b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& 0xFF

def sgn (a : UInt256) : ℤ :=
  if 2 ^ 255 <= a.toNat then
    -1
  else
    if eq0 a then 0 else 1

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else sub 0 (abs a / b)
  else
    if 2 ^ 255 <= b.toNat then
      sub 0 (a / abs b)
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then 0
  else
    toSigned <| sgn a * (abs a % abs b).toNat

def sltBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b.toNat ≥ 2 ^ 255 then false
    else a < b

def sgtBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b.toNat ≥ 2 ^ 255 then true
    else a > b

abbrev fromBool (b : Bool) : UInt256 := if b then 1 else 0

def slt (a b : UInt256) :=
  fromBool (sltBool a b)

def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

def sar (a b : UInt256) : UInt256 :=
  if sltBool b 0
  then UInt256.complement (UInt256.complement b >>> a)
  else b >>> a

private partial def dbg_toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (dbg_toHex (n / 16)) ++ hexDigitRepr (n % 16)

def signextend (a b : UInt256) : UInt256 :=
  if a.toNat ≤ 31 then
    let test_bit := a * 8 + 7
    let sign_bit := (1 : UInt256) <<< test_bit
    if b &&& sign_bit ≠ 0 then
      b ||| (ofNat (UInt256.size - sign_bit.toNat))
    else b &&& (sign_bit - 1)
  else b

def addMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then 0 else
    ofNat <| Nat.mod (a.toNat + b.toNat) c.toNat

def mulMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then 0 else
    ofNat <| Nat.mod (a.toNat * b.toNat) c.toNat

def exp (a b : UInt256) : UInt256 := pow a b

def lt (a b : UInt256) := fromBool (a < b)

def gt (a b : UInt256) := fromBool (a > b)

def eq (a b : UInt256) := fromBool (a == b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end UInt256

end Evm

section CastUtils

open Evm UInt256

abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 := Evm.UInt256.ofNat a.toNat

def Bool.toUInt256 (b : Bool) : UInt256 := if b then 1 else 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = (1 : UInt256) := rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = (0 : UInt256) := rfl

end CastUtils

namespace Evm

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.toFin.val + 2^8 * fromBytes' bs

def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse
def fromByteArrayBigEndian (b : ByteArray) : ℕ := fromBytesBigEndian b.toList

variable {bs : List UInt8}
         {n : ℕ}

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := UInt8.ofNat (Nat.mod n UInt8.size)
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

/-- `toBytes' n` (little-endian byte digits of `n`) has at most `k` digits when
`n < 256 ^ k`. Strong induction on `k` via the `n / 256` recursion of `toBytes'`. -/
theorem toBytes'_length_le : ∀ (k n : ℕ), n < 256 ^ k → (toBytes' n).length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n h
    simp only [pow_zero, Nat.lt_one_iff] at h
    subst h
    simp [toBytes']
  | succ k ih =>
    intro n h
    match n with
    | 0 => simp [toBytes']
    | Nat.succ m =>
      rw [toBytes']
      simp only [List.length_cons]
      have hdiv : (Nat.succ m) / UInt8.size < 256 ^ k := by
        have hstep : (Nat.succ m) / 256 < 256 ^ (k + 1) / 256 :=
          Nat.div_lt_div_of_lt_of_dvd ⟨256 ^ k, by ring⟩ h
        have huint : UInt8.size = 256 := rfl
        rw [huint]
        simpa [pow_succ, Nat.mul_div_cancel] using hstep
      have hih := ih _ hdiv
      omega

/-- The big-endian byte expansion of `n` has at most `k` bytes when `n < 256 ^ k`. -/
theorem toBytesBigEndian_length_le {k n : ℕ} (h : n < 256 ^ k) :
    (toBytesBigEndian n).length ≤ k := by
  simpa [toBytesBigEndian] using toBytes'_length_le k n h

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.toNat)

def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  .ofNat <| fromBytes' arr.data.toList.reverse

end Evm

section HicSuntDracones

def ByteArray.copySlice' (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  if false -- srcOff < 2^64 && destOff < 2^64 && len < 2^64
  then src.copySlice srcOff dest destOff len exact -- NB only when `srcOff`, `destOff` and `len` are sufficiently small
  else let srcData := src.data
       let destData := dest.data
       let sourceChunk := srcData.extract srcOff (srcOff + len)
       let destBegin := destData.extract 0 destOff
       let destEnd := destData.extract (destOff + len) destData.size
       ⟨destBegin ++ sourceChunk ++ destEnd⟩

end HicSuntDracones
