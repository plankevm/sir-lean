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

/-! ### Totality of the encoder on bounded inputs

`encode` is `Option`-typed only to model the RLP length ceiling (a payload of
`≥ 2^64` bytes is not representable). For inputs within that ceiling — in
particular the `(20-byte address, ≤ 32-byte nonce)` pair the CREATE-address
preimage feeds it — every `none` branch is excluded, so `encode` is `some`.
These lemmas make that totality a theorem (used by `Evm.contractAddressBytes`
to extract the bytes without an `Option`/`Except` fault path). -/

/-- On any input below the RLP length ceiling, `encodeBytes` returns `some`:
each of the three constructors is a `some`, and the lone `none` needs
`¬ x.size < 2^64`, contradicting `h`. -/
theorem encodeBytes_isSome_of_lt {x : ByteArray} (h : x.size < 2 ^ 64) :
    (encodeBytes x).isSome := by
  unfold encodeBytes
  by_cases h1 : x.size = 1 ∧ x.get! 0 < 128
  · rw [if_pos h1]; rfl
  · rw [if_neg h1]
    by_cases h2 : x.size < 56
    · rw [if_pos h2]; rfl
    · rw [if_neg h2, if_pos h]; rfl

/-- The two `some` constructors of `encodeBytes` on a `<56`-byte string add at
most one header byte: the size is `x.size` (single low byte) or `1 + x.size`
(short-string header). -/
theorem encodeBytes_size_le {x : ByteArray} (h : x.size < 56) :
    ∀ e, encodeBytes x = some e → e.size ≤ 1 + x.size := by
  intro e he
  unfold encodeBytes at he
  by_cases h1 : x.size = 1 ∧ x.get! 0 < 128
  · -- single low byte: e = x
    rw [if_pos h1] at he
    simp only [Option.some.injEq] at he
    subst he; omega
  · rw [if_neg h1] at he
    rw [if_pos h] at he
    -- short-string header: e = [128+size] ++ x
    simp only [Option.some.injEq] at he
    subst he
    simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons,
      List.length_nil]
    omega

/-- `encodeItems` on a two-element byte-string list is `some`, with payload
size at most `(1 + a.size) + (1 + b.size)`, whenever both strings sit below the
RLP ceiling. -/
theorem encodeItems_pair_isSome {a b : ByteArray}
    (ha : a.size < 56) (hb : b.size < 56) :
    ∃ s, encodeItems [.bytes a, .bytes b] = some s ∧
      s.size ≤ (1 + a.size) + (1 + b.size) := by
  -- encodeBytes a, encodeBytes b are some
  obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.1 (encodeBytes_isSome_of_lt (x := a) (by omega))
  obtain ⟨eb, heb⟩ := Option.isSome_iff_exists.1 (encodeBytes_isSome_of_lt (x := b) (by omega))
  have hsea := encodeBytes_size_le ha ea hea
  have hseb := encodeBytes_size_le hb eb heb
  have hea' : encode (.bytes a) = some ea := by simp only [encode]; exact hea
  have heb' : encode (.bytes b) = some eb := by simp only [encode]; exact heb
  have hib : encodeItems [Rlp.bytes b] = some eb := by
    simp only [encodeItems, heb', Option.some.injEq]
    simp only [ByteArray.append_empty]
  refine ⟨ea ++ eb, ?_, ?_⟩
  · simp only [encodeItems, hea', hib]
  · rw [ByteArray.size_append]; omega

/-- `encode (.list [.bytes a, .bytes b])` is `some` whenever both strings sit
below 56 bytes and the encoded payload sits below the RLP ceiling. This is the
load-bearing totality lemma for the CREATE address preimage. -/
theorem encode_list_pair_isSome {a b : ByteArray}
    (ha : a.size < 56) (hb : b.size < 56)
    (hpay : (1 + a.size) + (1 + b.size) < 2 ^ 64) :
    (encode (.list [.bytes a, .bytes b])).isSome := by
  obtain ⟨s, hs, hssize⟩ := encodeItems_pair_isSome ha hb
  simp only [encode]
  unfold encodeList
  rw [hs]
  dsimp only
  by_cases hsc : s.size < 56
  · rw [if_pos hsc]; rfl
  · rw [if_neg hsc, if_pos (by omega : s.size < 2 ^ 64)]; rfl

end Rlp

-- Axiom guards: the RLP totality results stay within the standard logical kernel.
#print axioms Rlp.encodeBytes_isSome_of_lt
#print axioms Rlp.encode_list_pair_isSome
