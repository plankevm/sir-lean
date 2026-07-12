import Evm.UInt256
import Mathlib.Data.Finmap
import Evm.FFI.ffi

def BE : ℕ → ByteArray := List.toByteArray ∘ Evm.toBytesBigEndian

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

namespace Evm

def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val.toNat
  ffi.ByteArray.zeroes ⟨32 - b.size⟩ ++ b

/-- The big-endian byte array of `n` has at most `k` bytes when `n < 256 ^ k`
(`BE = List.toByteArray ∘ toBytesBigEndian`, so its size is the digit count). -/
theorem BE_size_le {k n : ℕ} (h : n < 256 ^ k) : (BE n).size ≤ k := by
  unfold BE
  simp only [Function.comp_apply, List.size_toByteArray]
  exact toBytesBigEndian_length_le h

/-- `ffi.ByteArray.zeroes` produces an array whose size is its `USize` argument
(reflected to `Nat`) — its reference body is `Array.replicate n.toNat 0`. -/
theorem zeroes_size (u : USize) : (ffi.ByteArray.zeroes u).size = u.toNat := by
  unfold ffi.ByteArray.zeroes
  simp [ByteArray.size, Array.size_replicate]

abbrev Literal := UInt256

def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero AccountAddress.size where
  out := (by unfold AccountAddress.size; simp)

abbrev AccountAddress : Type := Fin AccountAddress.size

instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

instance : Inhabited AccountAddress := ⟨Fin.ofNat _ 0⟩

namespace AccountAddress

theorem size_eq_2pow160 : AccountAddress.size = 2^160 := by rfl

def ofNat (n : ℕ) : AccountAddress := Fin.ofNat _ n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ v.toNat
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩

def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ffi.ByteArray.zeroes ⟨20 - b.size⟩ ++ b

/-- An address fits in 20 bytes: `a < 2^160 = 256^20`, so `BE a` has ≤ 20 bytes. -/
theorem BE_size_le_20 (a : AccountAddress) : (BE a.val).size ≤ 20 := by
  apply BE_size_le
  have : a.val < AccountAddress.size := a.isLt
  unfold AccountAddress.size at this
  norm_num
  omega

/-- The left zero-padding makes `toByteArray` exactly 20 bytes: the pad supplies
`20 - (BE a).size` and `BE a` supplies `(BE a).size`, summing to 20 since the
address fits in 20 bytes (`BE_size_le_20`). -/
theorem toByteArray_size (a : AccountAddress) : a.toByteArray.size = 20 := by
  have hle := BE_size_le_20 a
  unfold AccountAddress.toByteArray
  simp only [ByteArray.size_append, zeroes_size]
  have hb : (⟨20 - ↑(BE ↑a).size⟩ : USize).toNat = 20 - (BE ↑a).size := by
    show ((20 : BitVec System.Platform.numBits) - ↑(BE ↑a).size).toNat = 20 - (BE ↑a).size
    have h32 : (2:Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
      Nat.pow_le_pow_right (by norm_num) System.Platform.le_numBits
    have h20 : (BitVec.toNat (20 : BitVec System.Platform.numBits)) = 20 := by
      rw [show (20 : BitVec System.Platform.numBits) = BitVec.ofNat _ 20 from rfl,
          BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hsz : ((↑(BE ↑a).size : BitVec System.Platform.numBits)).toNat = (BE ↑a).size := by
      rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hle' : (↑(BE ↑a).size : BitVec System.Platform.numBits) ≤ (20 : BitVec _) := by
      rw [BitVec.le_def, h20, hsz]; omega
    rw [BitVec.toNat_sub_of_le hle', h20, hsz]
  rw [hb]
  omega

end AccountAddress

instance : Repr ByteArray where
  reprPrec s _ := toHex s

def Identifier := String
instance : ToString Identifier := inferInstanceAs (ToString String)
instance : Inhabited Identifier := inferInstanceAs (Inhabited String)
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)
instance : Repr Identifier := inferInstanceAs (Repr String)

end Evm

-- Axiom guards: the byte-size lemmas stay within the standard logical kernel.
#print axioms Evm.BE_size_le
#print axioms Evm.AccountAddress.toByteArray_size

/--
TODO(rework later to a sane version)
-/
instance : DecidableEq ByteArray := by
  rintro ⟨a⟩ ⟨b⟩
  rw [ByteArray.mk.injEq]
  apply decEq

def Option.option {α β : Type} (dflt : β) (f : α -> β) : Option α → β
  | .none => dflt
  | .some x => f x

def Option.toExceptWith {α β : Type} (dflt : β) (x : Option α) : Except β α :=
  x.option (.error dflt) Except.ok

def ByteArray.get? (self : ByteArray) (n : Nat) : Option UInt8 :=
  if h : n < self.size
  then self.get n h
  else .none

partial def Nat.toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (toHex (n / 16)) ++ hexDigitRepr (n % 16)

/-- Add `0`s to make the hex representation valid for `ByteArray.ofBlob` -/
def padLeft (n : ℕ) (s : String) :=
  let l := s.length
  if l < n then String.replicate (n - l) '0' ++ s else s


def HexPrefix := "0x"

def isHexDigitChar (c : Char) : Bool :=
  '0' <= c && c <= '9' || 'a' <= c.toLower && c.toLower <= 'f'

def cToHex? (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9'
  then .ok <| c.toString.toNat!
  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f'
        then let Δ := c.toLower.toNat - 'a'.toNat
            .ok <| 10 + Δ
        else .error s!"Not a hex digit: {c}"

def ofHex? : List Char → Except String UInt8
  | [] => pure 0
  | [msb, lsb] => do pure ∘ UInt8.ofNat <| (← cToHex? msb) * 16 + (← cToHex? lsb)
  | _ => throw "Need two hex digits for every byte."

def Blob := String

instance : Inhabited Blob := inferInstanceAs (Inhabited String)

def Blob.toString : Blob → String := λ blob ↦ blob

instance : ToString Blob := ⟨Blob.toString⟩

def getBlob? (s : String) : Except String Blob :=
  if isHex s then
    let rest := (s.drop HexPrefix.length).toString
    if rest.any (not ∘ isHexDigitChar)
    then .error "Blobs must consist of valid hex digits."
    else .ok rest.toLower
  else .error "Input does not begin with 0x."
  where
    isHex (s : String) := s.startsWith HexPrefix

def getBlob! (s : String) : Blob := getBlob? s |>.toOption.get!

def ByteArray.ofBlob (self : Blob) : Except String ByteArray := do
  let chunks ← self.toList.toChunks 2 |>.mapM ofHex?
  pure ⟨chunks.toArray⟩

def ByteArray.readBytes (source : ByteArray) (start size : ℕ) : ByteArray :=
  let read :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  read ++ ffi.ByteArray.zeroes ⟨size - read.size⟩

def ByteArray.readWithoutPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if addr ≥ source.size then .empty else
    let len := min len source.size
    source.extract addr (addr + len)

private def inf := 2^66

def ByteArray.readWithPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if len ≥ 2^64 then
    panic! s!"ByteArray.readWithPadding: can not handle byte arrays of length {len}"
  else
    let read := source.readWithoutPadding addr len
    read ++ ffi.ByteArray.zeroes ⟨len - read.size⟩

def ByteArray.write
  (source : ByteArray)
  (sourceAddr : ℕ)
  (dest : ByteArray)
  (destAddr len : ℕ)
  : ByteArray
:=
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (ffi.ByteArray.zeroes ⟨len⟩).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      let endPaddingAddr := min dest.size (destAddr + len)
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      let sourcePadding := ffi.ByteArray.zeroes ⟨sourcePaddingLength⟩
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding := ffi.ByteArray.zeroes ⟨destPaddingLength⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)
