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

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero AccountAddress.size where
  out := (by unfold AccountAddress.size; simp)

abbrev AccountAddress : Type := Fin AccountAddress.size

instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

instance : Inhabited AccountAddress := ⟨Fin.ofNat _ 0⟩

namespace AccountAddress

def ofNat (n : ℕ) : AccountAddress := Fin.ofNat _ n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.toNat % AccountAddress.size)
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩

def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ffi.ByteArray.zeroes ⟨20 - b.size⟩ ++ b

end AccountAddress

instance : Repr ByteArray where
  reprPrec s _ := toHex s

def Identifier := String
instance : ToString Identifier := inferInstanceAs (ToString String)
instance : Inhabited Identifier := inferInstanceAs (Inhabited String)
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)
instance : Repr Identifier := inferInstanceAs (Repr String)

end Evm

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
