import LirLean.Decode.LoweringLemmas
import Evm

/-!
# LirLean — generic decode-from-lowering infrastructure (`decode_lower`, C3)

A concrete *worked* program's decode facts — `Evm.decode (lower workedCall) pc = expected`
at every emitted pc — can be closed by kernel `rfl`. That is the C2 acceptance bar,
but it is per-program: each new program reproves ≈40 `rfl`s. This module factors out
the **program-independent core** of that reasoning so a decode fact follows from a
purely *local* statement about the lowered byte list — the byte at the offset and
(for pushes) the immediate window — rather than from a global kernel reduction.

The two foundation lemmas relate a list-backed `ByteArray` to its list:

* `bget` — `ByteArray.get? ⟨l.toArray⟩ n = l[n]?` (the byte `decode` reads at `pc`);
* `bextract` — `((⟨a⟩ : ByteArray).extract b e).data = a.extract b e` (the immediate
  window `decode` slices for a PUSH).

On top of them, the two generic decode lemmas (`decode_nonpush_of_list`,
`decode_push_of_list`) compute `Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n)` from
`l[n]?` (and, for pushes, the `uInt256OfByteArray` of the immediate sublist). Since
`lower prog = ⟨(flatBytes prog).toArray⟩` (`lower_eq_flatBytes`), discharging a
decode obligation over `lower prog` reduces to the **byte-layout arithmetic**: which
byte `flatBytes prog` holds at `pcOf prog L pc`. That prefix-sum/offset-table
arithmetic is the remaining C3 work (see `PLAN.md`); these lemmas are the reusable
bricks it feeds, and the bridge that lets the worked-program decode facts be stated
list-locally instead of by whole-array `rfl`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## `lower prog` as a flat byte list -/

/-- The flat byte list `lower prog` wraps: the per-block `JUMPDEST :: body`
concatenation, before `toArray`/`ByteArray`. `lower prog = ⟨(flatBytes prog).toArray⟩`
(`lower_eq_flatBytes`), so byte-indexing `lower prog` is list-indexing `flatBytes prog`.

Stated in terms of `defsOf` (not `allocate`/`emit`) so every downstream layout proof
that decomposes `flatBytes` over `offsetTable (defsOf …) …` is unchanged; the bridge
to the factored `lower` is `allocate_toDefs`. -/
def flatBytes (prog : Program) : List UInt8 :=
  let defs := defsOf prog
  let fuel := recomputeFuel prog
  let labelOff := offsetTable defs fuel prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody defs fuel labelOff b)

/-- `emit (allocate prog) prog` is `flatBytes prog`: `emit` runs the same per-block
assembly over `(allocate prog).toDefs`, which is `defsOf prog` (`allocate_toDefs`). -/
theorem emit_allocate_eq_flatBytes (prog : Program) :
    emit (allocate prog) prog = flatBytes prog := by
  unfold emit flatBytes; rw [allocate_toDefs]

/-- `lower prog` is the `ByteArray` wrapping `flatBytes prog`. The factored
`lower = encode ∘ emit (allocate prog)` emits exactly the old bytes via
`emit_allocate_eq_flatBytes`. -/
theorem lower_eq_flatBytes (prog : Program) : lower prog = ⟨(flatBytes prog).toArray⟩ := by
  unfold lower encode; rw [emit_allocate_eq_flatBytes]

/-! ## Fold-based flat byte list (Phase 2A P4)

`flatBytesF prog` is the fold twin of `flatBytes prog`: the per-block
`JUMPDEST :: emitBlockBodyF` concatenation built from the fold cache `matCache prog` and
the `allocate prog` policy, with branch destinations resolved via `offsetTableF`. `lowerF`
wraps it as a `ByteArray`. Added ALONGSIDE the old `flatBytes`/`lower`; because the fold is
byte-different from the fuel lowering on ill-formed inputs, `lowerF ≠ lower` in general (the
swap that makes them equal is P7). Geometry over `flatBytesF`/`lowerF` is UNCONDITIONAL. -/
def flatBytesF (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let alloc := allocate prog
  let labelOff := offsetTableF cache alloc prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBodyF cache alloc labelOff b)

/-- The fold lowering: the `ByteArray` wrapping `flatBytesF prog`. -/
def lowerF (prog : Program) : ByteArray := ⟨(flatBytesF prog).toArray⟩

theorem lowerF_eq_flatBytesF (prog : Program) : lowerF prog = ⟨(flatBytesF prog).toArray⟩ := rfl

/-! ## Foundation: list-backed `ByteArray` indexing -/

/-- The byte `ByteArray.get?` reads from a list-backed array is the list's element.
This is the byte `decode` consults at `pc`. -/
theorem bget (l : List UInt8) (n : Nat) :
    ByteArray.get? ⟨l.toArray⟩ n = l[n]? := by
  unfold ByteArray.get?
  split
  · rename_i h; simp [ByteArray.get] at *
  · rename_i h; simp [ByteArray.size] at h; rw [List.getElem?_eq_none]; omega

/-- `extract` of a list-backed array is the array's `extract` at the data level —
the immediate window `decode` slices for a PUSH (then `uInt256OfByteArray`s). -/
theorem bextract (a : Array UInt8) (b e : Nat) :
    ((⟨a⟩ : ByteArray).extract b e).data = a.extract b e := by
  unfold ByteArray.extract ByteArray.copySlice
  show (Array.extract _ 0 0 ++ a.extract b (b + (e - b)) ++ Array.extract _ _ _) = _
  have h0 : (ByteArray.empty).data = #[] := rfl
  simp only [h0, Array.extract_empty_of_stop_le_start, Nat.le_refl]
  rw [show b + (e - b) = max b e from by omega]
  rcases Nat.le_total b e with h | h
  · rw [Nat.max_eq_right h]; simp
  · rw [Nat.max_eq_left h]
    rw [Array.extract_empty_of_stop_le_start h, Array.extract_empty_of_stop_le_start (Nat.le_refl b)]
    simp

/-! ## Generic decode lemmas

Both compute `Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n)` from a *local* fact about
`l` at `n`. `n < 2^32` (the pc fits a `UInt32`, true of any realistically-sized
program) makes `(UInt32.ofNat n).toNat = n`, so `decode` reads `l[n]?`. -/

/-- **Generic non-push decode.** If `l[n] = byte` and `byte` parses to a zero-width
(non-PUSH) opcode, then `decode ⟨l.toArray⟩ n` is exactly that opcode with no
immediate. Covers every effecting opcode `lower` emits
(`JUMPDEST/SSTORE/SLOAD/ADD/LT/GAS/JUMP/JUMPI/CALL/STOP/RETURN`). -/
theorem decode_nonpush_of_list (l : List UInt8) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : l[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  unfold Evm.decode
  have hpc : (UInt32.ofNat n).toNat = n := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simpa using hn)
  rw [hpc, bget, hb]
  show some (Evm.parseInstr byte,
      (if Evm.pushArgWidth (Evm.parseInstr byte) > 0 then _ else Option.none)) = _
  rw [hnp]; simp

/-- **Generic push decode.** If `l[n] = byte` parses to a PUSH of width `w > 0` and
the `w` immediate bytes `l[n+1 .. n+1+w]` `uInt256OfByteArray` to `imm`, then
`decode ⟨l.toArray⟩ n` is that PUSH carrying `(imm, w)`. Covers every `PUSH32`
literal and `PUSH4` destination `lower` emits. -/
theorem decode_push_of_list (l : List UInt8) (n : Nat) (byte : UInt8) (w : UInt8) (imm : UInt256)
    (hn : n < 2 ^ 32) (hb : l[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray ⟨(l.toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n) = some (Evm.parseInstr byte, some (imm, w)) := by
  unfold Evm.decode
  have hpc : (UInt32.ofNat n).toNat = n := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simpa using hn)
  rw [hpc, bget, hb]
  have hext : (⟨l.toArray⟩ : ByteArray).extract (n + 1) (n + 1 + w.toNat)
      = ⟨(l.toArray).extract (n + 1) (n + 1 + w.toNat)⟩ := ByteArray.ext (bextract _ _ _)
  show some (Evm.parseInstr byte,
      (if Evm.pushArgWidth (Evm.parseInstr byte) > 0 then
        some (Evm.uInt256OfByteArray ((⟨l.toArray⟩ : ByteArray).extract (n + 1)
                (n + 1 + (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)),
              Evm.pushArgWidth (Evm.parseInstr byte))
       else Option.none)) = _
  rw [hp, if_pos hw, hext, himm]

/-! ## Specialisations over `lower prog`

The same two lemmas, phrased directly on `lower prog` via `lower_eq_flatBytes`, so a
caller discharges a decode obligation about the lowered program by exhibiting the
byte (and immediate window) of `flatBytes prog` at the pc. The remaining byte-layout
arithmetic (`flatBytes prog`'s byte at `pcOf prog L pc`) is what `PLAN.md` records as
the open C3 work; these are the bricks it plugs into. -/

/-- Non-push decode specialised to `lower prog`. -/
theorem decode_lower_nonpush (prog : Program) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : (flatBytes prog)[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  rw [lower_eq_flatBytes]; exact decode_nonpush_of_list _ n byte hn hb hnp

/-- Push decode specialised to `lower prog`. -/
theorem decode_lower_push (prog : Program) (n : Nat) (byte : UInt8) (w : UInt8) (imm : UInt256)
    (hn : n < 2 ^ 32) (hb : (flatBytes prog)[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytes prog).toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, some (imm, w)) := by
  rw [lower_eq_flatBytes]; exact decode_push_of_list _ n byte w imm hn hb hp hw himm

/-! ## Fold specialisations over `lowerF prog` -/

/-- Non-push decode specialised to `lowerF prog`. -/
theorem decode_lowerF_nonpush (prog : Program) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : (flatBytesF prog)[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lowerF prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  rw [lowerF_eq_flatBytesF]; exact decode_nonpush_of_list _ n byte hn hb hnp

/-- Push decode specialised to `lowerF prog`. -/
theorem decode_lowerF_push (prog : Program) (n : Nat) (byte : UInt8) (w : UInt8) (imm : UInt256)
    (hn : n < 2 ^ 32) (hb : (flatBytesF prog)[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytesF prog).toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lowerF prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, some (imm, w)) := by
  rw [lowerF_eq_flatBytesF]; exact decode_push_of_list _ n byte w imm hn hb hp hw himm

end Lir
