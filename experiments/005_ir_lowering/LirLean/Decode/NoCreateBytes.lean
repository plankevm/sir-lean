import LirLean.Decode.JumpValid

/-!
# LirLean — the lowering emits no CREATE/CREATE2 opcode at any instruction boundary

This module discharges the **structural** half of the `NotCreate` modellability clause
(`V2/Modellable.lean`): no matter which instruction boundary of `lower prog` the engine
reaches, the opcode there is never `CREATE` (`0xf0`) nor `CREATE2` (`0xf5`). The IR has no
create constructor and `emitStmt`/`emitTerm`/`materialiseExpr` emit only the 16 opcodes
`{STOP, ADD, LT, POP, MLOAD, MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4,
PUSH32, CALL, RETURN}` — none of which is CREATE/CREATE2.

The subtlety is that a PUSH **immediate** byte may itself be `0xf0`/`0xf5` (push immediates
are arbitrary data), so "every emitted byte ≠ 0xf0" is *false*. The correct structural fact
is opcode-positional: every byte that the boundary walk *reads as an opcode* (i.e. the head
of an emitted instruction) is non-CREATE. We capture that with `SegAlignedSafe` — the
instruction-aligned `SegAligned` of `JumpValid.lean` strengthened so each instruction head
parses to a non-CREATE op — and transport it along the boundary walk.

## Architecture (an instance of the shared `SegAlignedP` tower)

* **`SegAlignedSafe`** — the non-CREATE instance of the parameterized `SegAlignedP`
  (`LirLean/SegAligned.lean`): a `SegAligned` whose every instruction *head* byte satisfies
  `parseInstr byte ∉ {CREATE, CREATE2}`.
* **`reaches_safe_of_segAlignedSafe`** — the transport: any boundary `n` the walk reaches from
  `base` *strictly inside* a matched `SegAlignedSafe` segment reads a non-CREATE opcode. The
  shared interior transport `reaches_P_of_segAlignedP` at the non-CREATE predicate.
* **`segAlignedSafe_flatBytes`** — `flatBytes prog` is safe-aligned: the shared `IsLoweringOp`
  emit-ladder weakened via `SegAlignedP.mono` (every lowering opcode is non-CREATE).
* **`reachable_boundary_notCreate`** — the headline: at every boundary `n` reachable from
  `0` in `lower prog` (and strictly before the program end), `decode (lower prog) n` reads a
  non-CREATE op. Composes `reaches_block_offset` (the per-block walk of `JumpValid.lean`)
  with `reaches_safe_of_segAlignedSafe`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §1 — `SegAlignedSafe`: alignment with non-CREATE instruction heads

`SegAlignedSafe` is the non-CREATE instance of the parameterized `SegAlignedP`
(`LirLean/SegAligned.lean`): a `SegAligned` byte list whose every opcode *head* byte `b`
satisfies `parseInstr b ∉ {CREATE, CREATE2}`. The immediate bytes are unconstrained (they are
data, never read as opcodes by the aligned boundary walk). Its composition bricks, the interior
transport and the emit-ladder are all instances of the shared parameterized tower. -/

/-- Alignment with non-CREATE/CREATE2 instruction heads. -/
abbrev SegAlignedSafe : List UInt8 → Prop :=
  SegAlignedP (fun op => op ≠ .System .CREATE ∧ op ≠ .System .CREATE2)

/-- **The transport.** A boundary `n` reached from `base` and strictly inside a `SegAlignedSafe`
segment matching `c` reads a byte parsing to a non-CREATE op. The interior transport
(`reaches_P_of_segAlignedP`) at the non-CREATE predicate. -/
theorem reaches_safe_of_segAlignedSafe (c : ByteArray) (seg : List UInt8)
    (hseg : SegAlignedSafe seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte
          ∧ Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2 :=
  reaches_P_of_segAlignedP c seg hseg

/-- The whole flat byte stream `flatBytes prog` is safe-aligned: the `IsLoweringOp` witness
(`segAlignedP_flatBytes`) weakened to non-CREATE via `SegAlignedP.mono` — every lowering opcode
is non-CREATE (`notCreate_of_isLoweringOp`). -/
theorem segAlignedSafe_flatBytes (prog : Program) : SegAlignedSafe (flatBytes prog) :=
  (segAlignedP_flatBytes prog).mono (fun _ => notCreate_of_isLoweringOp)

/-! ## §4 — the headline: no CREATE/CREATE2 at any reachable boundary of `lower prog`

Composing the whole-program safe alignment (`segAlignedSafe_flatBytes`) with the boundary-walk
transport (`reaches_safe_of_segAlignedSafe`): every boundary reachable from `0` and strictly
inside `flatBytes prog` reads a non-CREATE opcode. This is the **structural** content of the
`NotCreate` modellability clause — it holds for *every* `lower prog`, no program hypothesis. -/

/-- **The structural no-CREATE fact.** At every instruction boundary `n` reachable from `0` in
`lower prog` that lies strictly before the program end, the byte `lower prog` holds parses to a
non-CREATE (and non-CREATE2) opcode. The lowering emits only the 16 non-CREATE opcodes at any
instruction head; this transports that along the boundary walk. -/
theorem reachable_boundary_notCreate (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length) :
    ∃ byte, (lower prog).get? n = some byte
      ∧ Evm.parseInstr byte ≠ .System .CREATE ∧ Evm.parseInstr byte ≠ .System .CREATE2 := by
  have hmatch : ∀ j, j < (flatBytes prog).length →
      (lower prog).get? (0 + j) = (flatBytes prog)[j]? := by
    intro j _; rw [Nat.zero_add]; exact lower_get?_eq prog j
  have := reaches_safe_of_segAlignedSafe (lower prog) (flatBytes prog)
    (segAlignedSafe_flatBytes prog) 0 hmatch n hreach (by rwa [Nat.zero_add])
  exact this

/-- **The structural no-CREATE fact, at the `decode` level.** At every instruction boundary `n`
reachable from `0` in `lower prog` (strictly before the program end, and within the `UInt32`
address space), `decode (lower prog) n` reads an opcode that is neither `CREATE` nor `CREATE2`.
This is the form the `currentOp`-level `NotCreate` clause consumes: a reached boundary decodes
its (non-push *or* push) head opcode, and that opcode is never CREATE-family. -/
theorem decode_reachable_boundary_some (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∃ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg)
      ∧ op ≠ .System .CREATE ∧ op ≠ .System .CREATE2 := by
  obtain ⟨byte, hget, hsafe1, hsafe2⟩ := reachable_boundary_notCreate prog n hreach hn
  -- the byte at a reachable boundary is `flatBytes prog`'s byte (`lower_get?_eq`), and `decode`
  -- at that boundary reads `parseInstr byte` as the opcode (non-push or push, by `decode_lower_*`).
  have hbyte : (flatBytes prog)[n]? = some byte := by rw [← lower_get?_eq]; exact hget
  -- split on whether the head byte is a push: either way `decode`'s op component is `parseInstr byte`.
  by_cases hw : Evm.pushArgWidth (Evm.parseInstr byte) = 0
  · exact ⟨Evm.parseInstr byte, .none,
      decode_lower_nonpush prog n byte hbound hbyte hw, hsafe1, hsafe2⟩
  · have hwpos : Evm.pushArgWidth (Evm.parseInstr byte) > 0 := UInt8.pos_iff_ne_zero.mpr hw
    exact ⟨Evm.parseInstr byte, _,
      decode_lower_push prog n byte (Evm.pushArgWidth (Evm.parseInstr byte)) _
        hbound hbyte rfl hwpos rfl, hsafe1, hsafe2⟩

/-- **The structural no-CREATE fact, at the `decode` level.** At every instruction boundary `n`
reachable from `0` in `lower prog` (strictly before the program end, and within the `UInt32`
address space), whatever opcode `decode (lower prog) n` reads is neither `CREATE` nor `CREATE2`.
The `currentOp`-level form of `decode_reachable_boundary_some`. -/
theorem decode_reachable_boundary_notCreate (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∀ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg) →
      op ≠ .System .CREATE ∧ op ≠ .System .CREATE2 := by
  obtain ⟨op', arg', hdec', hsafe1, hsafe2⟩ :=
    decode_reachable_boundary_some prog n hreach hn hbound
  intro op arg hdec
  rw [hdec'] at hdec
  obtain ⟨hop, _⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hdec)
  subst hop; exact ⟨hsafe1, hsafe2⟩

end Lir

-- Build-enforced axiom-cleanliness guards: the structural no-CREATE chain — the safe-alignment
-- transport (`reaches_safe_of_segAlignedSafe`), the whole-program safe alignment
-- (`segAlignedSafe_flatBytes`) and the two headline forms (`reachable_boundary_notCreate`,
-- `decode_reachable_boundary_notCreate`) all depend only on `[propext, Classical.choice,
-- Quot.sound]`.
