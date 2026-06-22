import Evm.UInt256
import Evm.Wheels

/-- An RLP item: a byte string or a list of items. -/
inductive Rlp where
  | bytes : ByteArray → Rlp
  | list  : (List Rlp) → Rlp
  deriving Repr, BEq

namespace Rlp

/--
The length of the leading RLP item of `rlp`, header included — `none` when
`rlp` is empty or truncated.
-/
def itemLength (rlp : ByteArray) : Option ℕ :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      some 1
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        some (1 + strLen)
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            Evm.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          some (1 + lenOfStrLen + strLen)
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            some (1 + listLen)
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              Evm.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              some (1 + lenOfListLen + listLen)
            else
              none

/-- Split a concatenation of RLP items into the individual encoded items. -/
partial def splitItems (rlp : ByteArray) : Option (List ByteArray) := do
  if rlp.isEmpty then pure []
  else
    let headLen ← itemLength rlp
    let head := rlp.readWithoutPadding 0 headLen
    let tail ← splitItems (rlp.readWithoutPadding headLen rlp.size)
    pure <| head :: tail

/--
Decode the top level of an RLP item: the payload of a byte string, or the
still-encoded elements of a list.
-/
def decodeOne (rlp : ByteArray) : Option (Sum ByteArray (List ByteArray)) :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      let data := .inl ⟨#[rlp₀]⟩
      some data
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        let data := .inl (rlp.readWithoutPadding 1 strLen)
        some data
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            Evm.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          let data := .inl (rlp.readWithoutPadding (1 + lenOfStrLen) strLen)
          some data
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            let list ← splitItems (rlp.readWithoutPadding 1 listLen)
            some <| .inr list
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              Evm.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              let list ← splitItems (rlp.readWithoutPadding (1 + lenOfListLen) listLen)
              some <| .inr list
            else
              none

partial def decode (rlp : ByteArray) : Option Rlp := do
  match ← decodeOne rlp with
    | .inl byteArray =>
      some (.bytes byteArray)
    | .inr items =>
      let l ← items.mapM decode
      some (.list l)

/-- Encode an RLP byte string. -/
private def encodeBytes (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x.get! 0 < 128 then some x
  else
    if x.size < 56 then some <| [⟨128 + x.size⟩].toByteArray ++ x
    else
      if x.size < 2^64 then
        let be := BE x.size
        some <| [⟨183 + be.size⟩].toByteArray ++ be ++ x
      else none

mutual

/-- Encode and concatenate an RLP list payload. -/
private def encodeItems (l : List Rlp) : Option ByteArray :=
  match l with
    | [] => some .empty
    | t :: ts =>
      match encode t, encodeItems ts with
        | none     , _         => none
        | _        , none      => none
        | some rlpₗ, some rlpᵣ => rlpₗ ++ rlpᵣ

/-- Encode an RLP list. -/
def encodeList (l : List Rlp) : Option ByteArray :=
  match encodeItems l with
    | none => none
    | some s_x =>
      if s_x.size < 56 then
        some <| [⟨192 + s_x.size⟩].toByteArray ++ s_x
      else
        if s_x.size < 2^64 then
          let be := BE s_x.size
          some <| [⟨247 + be.size⟩].toByteArray ++ be ++ s_x
        else none

/-- Encode an RLP item. -/
def encode (t : Rlp) : Option ByteArray :=
  match t with
    | .bytes ba => encodeBytes ba
    | .list l => encodeList l

end

end Rlp
