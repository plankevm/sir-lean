namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

/--
A pure implementation (previously `@[extern "memset_zero"] opaque`): the
experiments in this repository interpret the semantics with `#eval`, which
requires a Lean reference implementation. Compiled conformance runs pay a
performance cost for this.
-/
def ByteArray.zeroes (n : USize) : ByteArray :=
  ⟨⟨List.replicate n.toNat 0⟩⟩

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
