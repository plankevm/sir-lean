# 03 — Code geometry: the `Decode/` layer

Part of the [exp005 tour](00-overview.md). Neighbours: [01-trusted-base](01-trusted-base.md)
(exp003 machine + Engine/), [02-spec-layer](02-spec-layer.md) (the emitter definitions this
layer reasons about), [05-simulation](05-simulation.md) and [06-realisability](06-realisability.md)
(the consumers), [07-assembler](07-assembler.md) (where this layer should eventually live).

## TL;DR

`LirLean/Decode/` (8 files, 2,355 lines) is the **code-geometry layer**: everything that must be
true of the *byte list* `lower prog` emits — where blocks start, what decodes at every cursor,
that jump targets are valid `JUMPDEST`s, that no reachable pc ever lands inside a PUSH
immediate — proven **once, for an arbitrary program**, replacing per-program kernel-`rfl` decode
walks. Its root trick is [`lower_eq_flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L59)
(byte-array indexing = list indexing) plus the prefix-sum decomposition
[`flatBytes_block_split`](../../../LirLean/Decode/Layout.lean#L117), which turn every global
decode obligation into a list-local byte fact. The headline exports are the generic-M1 anchor
[`flatBytes_at_pcOf`](../../../LirLean/Decode/Layout.lean#L248), the jump-validity theorem
[`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226), the unconditional
alignment theorem [`segAlignedP_flatBytes`](../../../LirLean/Decode/SegAligned.lean#L443), and the
boundary allow-list
[`decode_reachable_boundary_loweringOp`](../../../LirLean/Decode/BoundaryReach.lean#L529).
Everything in scope is sorry/axiom/`native_decide`-free (grep-verified; build green reported by
[the R11 plan checkpoint](../../planning/r11-plan-2026-07-08.md), not re-run); the four `sorry`s
in this layer's *consumer* (the R6 boundary invariant in
[`Realisability/Machinery.lean`](../../../LirLean/Realisability/Machinery.lean#L1390)) are
tracked WIP outside this folder. One headline finding: the layering inversion and `pcOf`
misplacement that [the 2026-07-06 codebase map](../../codebase-map-2026-07-06.md) flagged have
since been **fixed in source** — `pcOf` now lives in `Decode/Layout.lean`, and no `Decode/` file
imports `Frame/` — so the map (and this tour's own briefing) is stale on that point.

## 1. Why this layer has to exist at all

It is tempting to think exp003's Hoare logic already covers pc/frame reasoning. It does not,
and the reason is structural. Every exp003 rule (`runs_push`, `runs_jump`, `runs_sstore`, …)
is **conditional on a decode fact**: *given* `decode code fr.pc = some (op, imm)`, the frame
steps so-and-so. On a hand-written 20-byte example those decode hypotheses close by kernel
`rfl`. On `lower prog` for an **arbitrary** `prog` they cannot — each one is a claim about a
byte list built by nested `flatMap`s over the whole CFG. Five families of *global* facts about
that list are needed before a single Hoare rule fires:

1. **Where each block starts** — the offset table is a prefix sum of emitted block lengths,
   which is only well-defined because destination pushes are fixed-width
   ([`Layout.lean`](../../../LirLean/Decode/Layout.lean)).
2. **What decodes at a cursor** — the byte (and PUSH immediate window) at the offset-table
   address of statement `(L, pc)` is that statement's emitted byte
   ([`DecodeLower.lean`](../../../LirLean/Decode/DecodeLower.lean),
   [`DecodeAnchors.lean`](../../../LirLean/Decode/DecodeAnchors.lean)).
3. **Every emitted jump target is a valid `JUMPDEST`** — the EVM's `validJumpDests` scan walks
   the code *skipping PUSH immediates*, so "the byte there is `0x5b`" is not enough; the scan
   must be shown to *reach* it past every preceding PUSH32/PUSH4
   ([`JumpValid.lean`](../../../LirLean/Decode/JumpValid.lean)).
4. **No pc lands mid-immediate** — the emitted stream is a concatenation of complete
   instructions, so the boundary walk can never desynchronise
   ([`SegAligned.lean`](../../../LirLean/Decode/SegAligned.lean)).
5. **Every reachable boundary reads an allow-listed opcode** — the whole-run invariant needs to
   case-analyse "what can the next step be?" over the 18 opcodes the lowering emits, not all 256
   bytes ([`BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean),
   [`BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean)).

None of this mentions IR *semantics*. It is, de facto, the correctness proof of an **assembler**
that happens to be fused into the IR backend — which is exactly the case
[07-assembler](07-assembler.md) builds for de-fusing it (see §6).

The objects it is all about are the emitter definitions in
[`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean) (reviewed in
[02-spec-layer](02-spec-layer.md); quoted here because every statement below mentions them):

```lean
-- Spec/Lowering.lean
def emitBlockBody (cache : Tmp → List UInt8) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) : List UInt8 :=
  (b.stmts.flatMap (emitStmt cache alloc)) ++ emitTerm cache labelOff b.term

def blockLen (cache : Tmp → List UInt8) (alloc : Alloc) (b : Block) : Nat :=
  1 + (emitBlockBody cache alloc (fun _ => 0) b).length

def offsetTable (cache : Tmp → List UInt8) (alloc : Alloc) (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map (blockLen cache alloc)).sum

def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)
```
([`emitBlockBody`](../../../LirLean/Spec/Lowering.lean#L169),
[`blockLen`](../../../LirLean/Spec/Lowering.lean#L173),
[`offsetTable`](../../../LirLean/Spec/Lowering.lean#L176),
[`lower`](../../../LirLean/Spec/Lowering.lean#L186); statements are emitted by
[`emitStmt`](../../../LirLean/Spec/Lowering.lean#L114), terminators by
[`emitTerm`](../../../LirLean/Spec/Lowering.lean#L158), operand values by the fold cache
[`matCache`](../../../LirLean/Spec/Lowering.lean#L84).)

Note `blockLen` measures with the **zero** offset table while `emit` resolves with the real one —
the whole layout story hinges on those two passes emitting the same *lengths*, which is
[the first thing `Layout.lean` proves](../../../LirLean/Decode/Layout.lean#L46).

## 2. The abstraction stack

Bottom-up; each file's job in one line, with its main export.

| File | Lines | Job | Key exports |
|---|---|---|---|
| [`LoweringLemmas.lean`](../../../LirLean/Decode/LoweringLemmas.lean) | 139 | **Stowaway — zero geometry.** Proof companions of `defsOf`/`rematOf` spill routing (extracted so `Spec/Lowering.lean` stays definitions-only) | [`defsOf_ne_gas`](../../../LirLean/Decode/LoweringLemmas.lean#L21), [`rematOf_of_defsOf`](../../../LirLean/Decode/LoweringLemmas.lean#L116) |
| [`DecodeLower.lean`](../../../LirLean/Decode/DecodeLower.lean) | 157 | List-backed `ByteArray` ↔ list bridge; generic decode-from-a-byte lemmas | [`lower_eq_flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L59), [`decode_lower_nonpush`](../../../LirLean/Decode/DecodeLower.lean#L142)/[`_push`](../../../LirLean/Decode/DecodeLower.lean#L149) |
| [`Layout.lean`](../../../LirLean/Decode/Layout.lean) | 257 | Prefix-sum byte layout: block split, `pcOf` and its byte anchor | [`flatBytes_block_split`](../../../LirLean/Decode/Layout.lean#L117), [`pcOf`](../../../LirLean/Decode/Layout.lean#L227), [`flatBytes_at_pcOf`](../../../LirLean/Decode/Layout.lean#L248) |
| [`DecodeAnchors.lean`](../../../LirLean/Decode/DecodeAnchors.lean) | 317 | Decode-at-cursor anchors A1–A3 (stmt head / stmt interior / terminator), `termOf` | [`decode_at_offset_push`](../../../LirLean/Decode/DecodeAnchors.lean#L256), [`termOf`](../../../LirLean/Decode/DecodeAnchors.lean#L156), [`decode_at_term_nonpush`](../../../LirLean/Decode/DecodeAnchors.lean#L282) |
| [`SegAligned.lean`](../../../LirLean/Decode/SegAligned.lean) | 456 | The predicate-parameterized instruction-alignment tower + the emit ladder proven once | [`SegAlignedP`](../../../LirLean/Decode/SegAligned.lean#L63), [`IsLoweringOp`](../../../LirLean/Decode/SegAligned.lean#L205), [`segAlignedP_flatBytes`](../../../LirLean/Decode/SegAligned.lean#L443) |
| [`JumpValid.lean`](../../../LirLean/Decode/JumpValid.lean) | 271 | The `validJumpDests` scan reaches every block offset (E3) | [`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226), [`decode_at_block_offset_jumpdest`](../../../LirLean/Decode/JumpValid.lean#L252) |
| [`BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean) | 607 | Boundary-walk bricks for the whole-run R6 invariant: scan converse, sequential extension, opcode allow-list, local-region drops, call-site inversion | [`decode_reachable_boundary_loweringOp`](../../../LirLean/Decode/BoundaryReach.lean#L529), [`reachesBoundary_of_mem_validJumpDests`](../../../LirLean/Decode/BoundaryReach.lean#L458) |
| [`BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean) | 151 | Cursor inversion: classify any in-range byte offset by its source region | [`LowerBoundaryCursor`](../../../LirLean/Decode/BoundaryCursor.lean#L50), [`flatBytes_cursor_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L99) |

Internal dependency spine (imports, left feeds right):

```
LoweringLemmas → DecodeLower → Layout → DecodeAnchors ┐
                          └──→ SegAligned ────────────┼→ JumpValid → BoundaryReach → BoundaryCursor
```

Geometry that lives *outside* the folder but belongs to this layer:

- **`pcOf` and its anchors** — now in [`Layout.lean#L227`](../../../LirLean/Decode/Layout.lean#L227),
  **not** in `Frame/Match.lean` as the [codebase map](../../codebase-map-2026-07-06.md) (§L4, §4.5
  recommendation 4) and this tour's briefing state. The recommended relocation was executed:
  [`Frame/Match.lean`](../../../LirLean/Frame/Match.lean#L5) now imports `Decode/Layout` and its
  `M1` clause merely *pins* the frame pc to `pcOf`
  ([`Match.pc_eq`](../../../LirLean/Frame/Match.lean#L81)). No `Decode/` file imports `Frame/`
  anymore (grep-verified) — the "geometry imports Frame/Match" inversion is gone.
- **`ReachesBoundary` / `validJumpDests` and their characterization** — exp003's
  [`Decode.lean`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L167): the
  walk relation, the total `Nat`-indexed scan
  [`validJumpDestsAuxNat`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L100),
  and the forward direction
  [`mem_validJumpDests_of_reachable_jumpdest`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L189)
  (a consumer-driven addition to exp003; see [01-trusted-base](01-trusted-base.md)).
- **Engine-side step inversions** — landed with R11 chunk 1 in
  [`BytecodeLayer/Hoare/Descent.lean`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean#L205)
  ([`stepFrame_needsCall_site_inv`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean#L205),
  [`stepFrame_needsCreate_site_inv`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean#L460),
  [`resumeAfterCreate_pc`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean#L663)); engine territory
  ([01-trusted-base](01-trusted-base.md)), consumed by this layer's call-site lemmas (§4.6).

Upward consumers (who imports the geometry): `Frame/Match` (M1 pin →
[05-simulation](05-simulation.md)),
[`Sim/SimTerm.lean`](../../../LirLean/Sim/SimTerm.lean#L2) (jump/branch landing),
[`Materialise/MatDecLower.lean`](../../../LirLean/Materialise/MatDecLower.lean#L1)
([04-value-channel](04-value-channel.md)),
[`Spec/WellFormed.lean`](../../../LirLean/Spec/WellFormed.lean#L5) and
[`Spec/BudgetDerivations.lean`](../../../LirLean/Spec/BudgetDerivations.lean#L4)
([02-spec-layer](02-spec-layer.md)),
[`Decode/Modellable.lean`](../../../LirLean/Decode/Modellable.lean#L2), and the whole
[`Realisability/`](../../../LirLean/Realisability/Machinery.lean#L2) line
([06-realisability](06-realisability.md)).

## 3. The specs that matter

### 3.1 The root: byte-array facts are list facts

[`flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L45) names the flat byte list `lower`
wraps, and [`lower_eq_flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L59) is the layer's
single point of contact with `ByteArray`:

```lean
-- Decode/DecodeLower.lean
def flatBytes (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let alloc := defsOf prog
  let labelOff := offsetTable cache alloc prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache alloc labelOff b)

theorem lower_eq_flatBytes (prog : Program) : lower prog = ⟨(flatBytes prog).toArray⟩
```

Two foundation lemmas relate a list-backed `ByteArray` to its list —
[`bget`](../../../LirLean/Decode/DecodeLower.lean#L66) (the byte `decode` reads) and
[`bextract`](../../../LirLean/Decode/DecodeLower.lean#L75) (the immediate window it slices) —
and on top of them the two generic decode lemmas compute `Evm.decode` from a purely local fact:

```lean
-- Decode/DecodeLower.lean
theorem decode_lower_nonpush (prog : Program) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : (flatBytes prog)[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, .none)
```
([`decode_lower_nonpush`](../../../LirLean/Decode/DecodeLower.lean#L142); the PUSH twin
[`decode_lower_push`](../../../LirLean/Decode/DecodeLower.lean#L149) additionally takes the
`w`-byte immediate window.) This is the layer's whole discipline in one signature: a decode
obligation over the program becomes "which byte does `flatBytes prog` hold at `n`?".

### 3.2 The prefix-sum layout and the generic M1

[`Layout.lean`](../../../LirLean/Decode/Layout.lean) answers that question at block/statement
cursors. First it shows the offset table is the genuine layout — emitted lengths do not depend
on the resolved table because destination pushes are fixed-width
([`emitTerm_length_labelOff`](../../../LirLean/Decode/Layout.lean#L46),
[`blockLen_eq_length`](../../../LirLean/Decode/Layout.lean#L63)) — then decomposes the stream
around any block:

```lean
-- Decode/Layout.lean
theorem flatBytes_block_split (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    flatBytes prog
      = ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
                        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))
        ++ (Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
              (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)
        ++ ((prog.blocks.toList.drop (L.idx + 1)).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
                        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b))
```
([`flatBytes_block_split`](../../../LirLean/Decode/Layout.lean#L117); the prefix's length *is*
the offset table, [`blockPrefix_length`](../../../LirLean/Decode/Layout.lean#L95) /
[`flatBytes_block_offset`](../../../LirLean/Decode/Layout.lean#L135). Generic list bricks:
[`flatMap_split`](../../../LirLean/Decode/Layout.lean#L75),
[`mid_index`](../../../LirLean/Decode/Layout.lean#L153).)

The statement cursor and its byte anchor — the **generic M1** that
[`Match.pc_eq`](../../../LirLean/Frame/Match.lean#L81) pins the frame pc to:

```lean
-- Decode/Layout.lean
def pcOf (prog : Program) (L : Label) (pc : Nat) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b =>
          ((b.stmts.take pc).flatMap (emitStmt cache alloc)).length)).getD 0)

theorem flatBytes_at_pcOf (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hne : emitStmt (matCache prog) (defsOf prog) s ≠ []) :
    (flatBytes prog)[pcOf prog L pc]?
      = (emitStmt (matCache prog) (defsOf prog) s)[0]?
```
([`pcOf`](../../../LirLean/Decode/Layout.lean#L227),
[`flatBytes_at_pcOf`](../../../LirLean/Decode/Layout.lean#L248), via
[`pcOf_eq_anchor`](../../../LirLean/Decode/Layout.lean#L236) and
[`stmt_byte_anchor`](../../../LirLean/Decode/Layout.lean#L164). Proofs are `take/drop/append`
index arithmetic closed by `omega`; nothing fancy, discharged once instead of per program.)

### 3.3 Decode-at-cursor anchors (A1–A3)

[`DecodeAnchors.lean`](../../../LirLean/Decode/DecodeAnchors.lean) generalises the anchor to an
arbitrary offset `k` *inside* a statement's emitted bytes
([`stmt_byte_anchor_k`](../../../LirLean/Decode/DecodeAnchors.lean#L51),
[`flatBytes_at_pcOf_offset`](../../../LirLean/Decode/DecodeAnchors.lean#L143)) and to the block
terminator, whose cursor gets its own name:

```lean
-- Decode/DecodeAnchors.lean
def termOf (prog : Program) (L : Label) : Nat :=
  let cache := matCache prog
  let alloc := defsOf prog
  offsetTable cache alloc prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b => (b.stmts.flatMap (emitStmt cache alloc)).length)).getD 0)
```
([`termOf`](../../../LirLean/Decode/DecodeAnchors.lean#L156),
[`flatBytes_at_termOf`](../../../LirLean/Decode/DecodeAnchors.lean#L173).) Composed with the
§3.1 decode bricks these yield the six anchors the simulation engine consumes — A1
[`decode_at_stmt_head_nonpush`](../../../LirLean/Decode/DecodeAnchors.lean#L194)/[`_push`](../../../LirLean/Decode/DecodeAnchors.lean#L214),
A2 [`decode_at_offset_nonpush`](../../../LirLean/Decode/DecodeAnchors.lean#L240)/[`_push`](../../../LirLean/Decode/DecodeAnchors.lean#L256)
(the engine stepping through a materialised PUSH sequence), A3
[`decode_at_term_nonpush`](../../../LirLean/Decode/DecodeAnchors.lean#L282)/[`_push`](../../../LirLean/Decode/DecodeAnchors.lean#L299)
(the terminator's `JUMP`/`JUMPI`/`RETURN`/`STOP` and its `PUSH4` destinations).

### 3.4 Segment alignment, proven once for the tightest predicate

[`SegAligned.lean`](../../../LirLean/Decode/SegAligned.lean) is the elegant part of the folder.
The one inductive covers what used to be two (previously three) duplicated towers:

```lean
-- Decode/SegAligned.lean
inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hP : P (Evm.parseInstr byte))
      (hrest : SegAlignedP P rest) :
      SegAlignedP P (byte :: (imm ++ rest))
```
([`SegAlignedP`](../../../LirLean/Decode/SegAligned.lean#L63): "a concatenation of complete
instructions, every head satisfying `P`".) Two transports do all the walking:
[`reaches_end_of_segAlignedP`](../../../LirLean/Decode/SegAligned.lean#L113) (the boundary walk
over a matched aligned segment lands exactly at its end — the push-skipping subtlety, discharged
once) and [`reaches_P_of_segAlignedP`](../../../LirLean/Decode/SegAligned.lean#L155) (any
boundary reached strictly inside a matched segment reads a `P`-head).
[`SegAlignedP.mono`](../../../LirLean/Decode/SegAligned.lean#L74) then lets the emit ladder be
proven **once** at the tightest predicate and weakened on demand:

```lean
-- Decode/SegAligned.lean
def IsLoweringOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD
    ∨ op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP
    ∨ op = .JUMPI ∨ op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4
    ∨ op = .PUSH32 ∨ op = .CALL ∨ op = .RETURN
    ∨ op = .System .CREATE ∨ op = .System .CREATE2

theorem segAlignedP_flatBytes (prog : Program) :
    SegAlignedP IsLoweringOp (flatBytes prog)
```
([`IsLoweringOp`](../../../LirLean/Decode/SegAligned.lean#L205) — 18 opcodes, count verified;
[`segAlignedP_flatBytes`](../../../LirLean/Decode/SegAligned.lean#L443).) Note the theorem is
**unconditional** — no well-formedness hypothesis anywhere. The engine is a structural induction
over the fold value channel ([`segAlignedP_matCache`](../../../LirLean/Decode/SegAligned.lean#L303):
the initial cache is aligned, [`matStep`](../../../LirLean/Decode/SegAligned.lean#L281)
preserves pointwise alignment) followed by the per-construct emit ladder
([`segAlignedP_emitStmt`](../../../LirLean/Decode/SegAligned.lean#L310),
[`segAlignedP_emitTerm`](../../../LirLean/Decode/SegAligned.lean#L383)), each concrete head
discharged by a small `decide` on one byte — no big-term `decide`, no heartbeat cranking
anywhere in the folder.

### 3.5 Jump validity (E3)

[`JumpValid.lean`](../../../LirLean/Decode/JumpValid.lean) instantiates the tower at
`P = fun _ => True` ([`SegAligned`](../../../LirLean/Decode/JumpValid.lean#L85), a one-line
`abbrev` + [`.mono`](../../../LirLean/Decode/JumpValid.lean#L98) corollary) and walks the scan
block by block ([`reaches_block_offset`](../../../LirLean/Decode/JumpValid.lean#L167), induction
on the block index with [`offsetTable_succ`](../../../LirLean/Decode/JumpValid.lean#L118)):

```lean
-- Decode/JumpValid.lean
theorem block_offset_validJump (prog : Program) (L : Label) (hL : L.idx < prog.blocks.size) :
    (UInt32.ofNat (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx))
      ∈ validJumpDests (lower prog) 0
```
([`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226): every block offset is
a recorded jump destination — the fact every emitted `JUMP`/`JUMPI` needs. Companion:
[`decode_at_block_offset_jumpdest`](../../../LirLean/Decode/JumpValid.lean#L252), the decode of
the landing byte.) This generalises what used to be per-program `by decide` walks
(`nineteen_mem_validJumps`) to arbitrary programs, unconditionally.

### 3.6 Boundary reachability (the R6 brick set) and the R11 chunk-1 landings

[`BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean) supplies the bricks for the
whole-run invariant `AtReachableBoundary`
([`Decode/Modellable.lean#L398`](../../../LirLean/Decode/Modellable.lean#L398)): *every
`Runs`-reachable frame of a lowered program sits at an instruction boundary reachable from 0,
in range*. Three original bricks:

```lean
-- Decode/BoundaryReach.lean
theorem reachesBoundary_of_mem_validJumpDests (c : ByteArray) {x : UInt32}
    (hx : x ∈ validJumpDests c 0) :
    ∃ j, ReachesBoundary c 0 j ∧ x = j.toUInt32 ∧ j < c.size

theorem reachesBoundary_nextInstr {c : ByteArray} {start n : Nat} {byte : UInt8}
    (hreach : ReachesBoundary c start n) (hget : c.get? n = some byte) :
    ReachesBoundary c start (nextInstrPosNat n (Evm.parseInstr byte))

theorem decode_reachable_boundary_loweringOp (prog : Program) (n : Nat)
    (hreach : ReachesBoundary (lower prog) 0 n) (hn : n < (flatBytes prog).length)
    (hbound : n < 2 ^ 32) :
    ∃ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg) ∧ IsLoweringOp op
```
([`reachesBoundary_of_mem_validJumpDests`](../../../LirLean/Decode/BoundaryReach.lean#L458) —
the *converse* of exp003's characterization, turning a taken `JUMP` back into a walk witness;
proof: well-founded induction on the scan via the membership inversion
[`mem_validJumpDestsAuxNat_inv`](../../../LirLean/Decode/BoundaryReach.lean#L419).
[`reachesBoundary_nextInstr`](../../../LirLean/Decode/BoundaryReach.lean#L477) — the sequential
fall-through edge. [`decode_reachable_boundary_loweringOp`](../../../LirLean/Decode/BoundaryReach.lean#L529)
— the allow-list that scopes the per-step case analysis to 18 arms instead of 256 bytes.)

**The R11 chunk-1 additions** (commits `763ca84`, `2ce43d1`, `2876a46`, `c760145`, 2026-07-09)
extend this brick set in three directions, all aimed at the still-`sorry`d R6 edge bricks in
[`Machinery.lean`](../../../LirLean/Realisability/Machinery.lean#L1364) (B-pc / B-inrange)
and the CALL/CREATE resume edges:

1. **Cursor inversion** ([`BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean),
   commit `2ce43d1`) — the *inverse* of the Layout anchors. Where §3.2 computes the byte at a
   known source cursor, this classifies an arbitrary in-range byte offset by the region that
   contains it:

   ```lean
   -- Decode/BoundaryCursor.lean
   inductive LowerBoundaryCursor (prog : Program) (b : Nat) : Prop where
     | blockEntry (L : Label) (blk : Block)
         (hb : prog.blocks.toList[L.idx]? = some blk)
         (heq : b = offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx)
     | stmt (L : Label) (blk : Block) (pc k : Nat) (s : Stmt)
         (hb : prog.blocks.toList[L.idx]? = some blk)
         (hs : blk.stmts[pc]? = some s)
         (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length)
         (heq : b = pcOf prog L pc + k)
     | term (L : Label) (blk : Block) (k : Nat)
         (hb : prog.blocks.toList[L.idx]? = some blk)
         (hk : k < (emitTerm (matCache prog)
           (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk.term).length)
         (heq : b = termOf prog L + k)

   theorem flatBytes_cursor_cases {prog : Program} {b : Nat}
       (hin : b < (flatBytes prog).length) :
       LowerBoundaryCursor prog b
   ```
   ([`LowerBoundaryCursor`](../../../LirLean/Decode/BoundaryCursor.lean#L50),
   [`flatBytes_cursor_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L99); generic list
   bricks [`flatMap_index_inv`](../../../LirLean/Decode/BoundaryCursor.lean#L20) and
   [`append_region_inv`](../../../LirLean/Decode/BoundaryCursor.lean#L39).) This is what lets a
   proof *start from a pc* (as the R6 induction must) and recover which statement/terminator it
   is inside — the pivot from "walk forward from the CFG" to "invert from the byte offset".
   The wrapper [`reachable_lowering_boundary_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L145)
   currently ignores its `ReachesBoundary` hypothesis (classification needs only in-range).

2. **Opcode-shape support** (commit `2876a46`, [`§0` of BoundaryReach](../../../LirLean/Decode/BoundaryReach.lean#L44)) —
   a second `SegAlignedP` instantiation at
   [`NoCallCreateOp`](../../../LirLean/Decode/BoundaryReach.lean#L46) (`op ≠ CALL ∧ op ≠ CREATE ∧
   op ≠ CREATE2`), proven for the operand channels only: the fold cache
   ([`segAlignedNoCall_matCache`](../../../LirLean/Decode/BoundaryReach.lean#L123)), any
   materialised expression, and every terminator
   ([`segAlignedNoCall_emitTerm_matCache`](../../../LirLean/Decode/BoundaryReach.lean#L168)) —
   deliberately *not* `emitStmt`, whose `.call`/`.create` arms do emit those bytes. Together
   with the region classification this pins a `.needsCall`/`.needsCreate` step to the one
   `Byte.call`/`Byte.create*` head of its statement: operand materialisation can never fake a
   call site. Plus the region-drop transport
   [`reachesBoundary_drop_segAlignedP`](../../../LirLean/Decode/BoundaryReach.lean#L174) (if the
   walk passes an aligned matched segment, it can be restarted at the segment's end).

3. **Local-region walks** (commit `c760145`) — compositions of the drop transport that
   relocalise a global walk to the enclosing statement or terminator:
   [`reachesBoundary_drop_to_blockEntry`](../../../LirLean/Decode/BoundaryReach.lean#L251) →
   [`reachesBoundary_drop_jumpdest`](../../../LirLean/Decode/BoundaryReach.lean#L277) →
   [`reachesBoundary_drop_stmtPrefix`](../../../LirLean/Decode/BoundaryReach.lean#L345),
   packaged as
   [`reachesBoundary_local_stmt`](../../../LirLean/Decode/BoundaryReach.lean#L368) and
   [`reachesBoundary_local_term`](../../../LirLean/Decode/BoundaryReach.lean#L385): a walk from
   0 to a byte inside statement `(L, pc)` restricts to a walk from `pcOf prog L pc` — i.e., a
   reachable boundary is a boundary *of its own statement's* emitted segment. This is the exact
   shape the B-inrange brick ("a sequential-advancing instruction's successor stays in range,
   because blocks end in terminators") needs.

4. **Call/create site inversions** (commit `763ca84`) — the decode-level closures
   [`decode_of_loweringByte`](../../../LirLean/Decode/BoundaryReach.lean#L543),
   [`loweringOp_call_family_eq_call`](../../../LirLean/Decode/BoundaryReach.lean#L554) (of the
   four CALL-family ops only `CALL` is allow-listed), and

   ```lean
   -- Decode/BoundaryReach.lean
   theorem stepFrame_needsCall_lowering_site_inv {prog : Program} {fr : Evm.Frame}
       {cp : Evm.CallParams} {pd : Evm.PendingCall} {b : Nat} {byte : UInt8}
       (hcode : fr.exec.executionEnv.code = lower prog) (hpc : fr.exec.pc = UInt32.ofNat b)
       (hbnd : b < 2 ^ 32) (hget : (lower prog).get? b = some byte)
       (hop : IsLoweringOp (Evm.parseInstr byte))
       (hstep : Evm.stepFrame fr = .needsCall cp pd) :
       Evm.parseInstr byte = .CALL ∧ pd.frame.exec.pc = fr.exec.pc
         ∧ pd.frame.validJumps = fr.validJumps
   ```
   ([`stepFrame_needsCall_lowering_site_inv`](../../../LirLean/Decode/BoundaryReach.lean#L564),
   twin [`stepFrame_needsCreate_lowering_site_inv`](../../../LirLean/Decode/BoundaryReach.lean#L584);
   built on the engine inversions in [`BytecodeLayer/Hoare/Descent.lean`](../../../../../EVM/BytecodeLayer/Hoare/Descent.lean#L205).)
   This **already closed the B-call brick**: the R6 CALL edge
   [`atReachableBoundaryVJ_call`](../../../LirLean/Realisability/Machinery.lean#L1416) cites
   it at [Machinery.lean#L1428](../../../LirLean/Realisability/Machinery.lean#L1428).

**What they feed.** The consumer is R6, assembled in
[`Machinery.lean`](../../../LirLean/Realisability/Machinery.lean#L1519): invariant
[`AtReachableBoundaryVJ`](../../../LirLean/Realisability/Machinery.lean#L1345)
(`AtReachableBoundary` + a pinned `validJumps` table, without which the taken-jump arm is
unprovable), seed [`atReachableBoundaryVJ_entry`](../../../LirLean/Realisability/Machinery.lean#L1352),
edges [`_step`](../../../LirLean/Realisability/Machinery.lean#L1372) /
[`_call`](../../../LirLean/Realisability/Machinery.lean#L1416) /
[`_create`](../../../LirLean/Realisability/Machinery.lean#L1462), combinator
[`_of_runs`](../../../LirLean/Realisability/Machinery.lean#L1472), headline
[`runs_atReachableBoundary`](../../../LirLean/Realisability/Machinery.lean#L1519). In the
tree under review that assembly still carries **four `sorry`s** — B-pc
([L1390](../../../LirLean/Realisability/Machinery.lean#L1390)), B-inrange step
([L1398](../../../LirLean/Realisability/Machinery.lean#L1398)), B-inrange call
([L1431](../../../LirLean/Realisability/Machinery.lean#L1431)), and the whole CREATE edge
([L1464](../../../LirLean/Realisability/Machinery.lean#L1464)). The
[R11 plan checkpoint](../../planning/r11-plan-2026-07-08.md) reports B-pc and the CALL
in-range closed in a box run (commits `ff825e3`/`9d45927`) **not present in this local tree**
(verified: `ff825e3` is not a local object). Consequently, in *this* tree the chunk-1 items
(1)–(3) above are **staged, unconsumed leaves**: `LowerBoundaryCursor`, the `reachesBoundary_local_*`
family and the entire `NoCallCreateOp` tower have zero consumers outside `Decode/` (only the
`import` at [Machinery.lean#L2](../../../LirLean/Realisability/Machinery.lean#L2) anticipates
them). The plan's own rule applies: "Support lemmas do not count as progress until a named WIP
`sorry` consumes them; delete or private-ize unused support at the next green checkpoint."

## 4. Hypotheses & modeling

The geometry layer is refreshingly hypothesis-light; nothing here smuggles a conclusion.

- **Unconditionality is the norm.** `segAlignedP_flatBytes`, `block_offset_validJump`,
  `flatBytes_cursor_cases` hold for **every** `Program`, including ill-formed ones —
  [`lower`](../../../LirLean/Spec/Lowering.lean#L186) emits *something* for any input, and that
  something is always instruction-aligned with allow-listed heads. Well-formedness only enters
  upstream (whether those bytes mean the right thing).
- **`n < 2^32`** on every decode lemma: the EVM pc is a `UInt32`, so `UInt32.ofNat n` must not
  wrap. Threaded at the R6 level as `hsize : (flatBytes prog).length ≤ 2^32`, a bound any real
  program satisfies (destinations are `PUSH4`). Legitimate, not conclusion-smuggling.
- **Block/statement presence witnesses** (`prog.blocks.toList[L.idx]? = some b`,
  `b.stmts[pc]? = some s`) — the minimal "this cursor is real" facts; suppliers get them from
  the CFG walk.
- **`hne : emitStmt … s ≠ []`** on the head anchors: an `assign` routed to `.remat` emits
  nothing, so "the byte at this statement's cursor" is only meaningful for emitting statements.
  Honest, and handled by the `k`-indexed A2 forms.
- **One vestigial hypothesis**:
  [`reachable_lowering_boundary_cases`](../../../LirLean/Decode/BoundaryCursor.lean#L145) takes
  a `ReachesBoundary` argument it discards (`_hreach`), as do
  [`reachesBoundary_local_stmt`](../../../LirLean/Decode/BoundaryReach.lean#L368)'s `_hs`/`_hk`.
  Harmless interface padding for the intended consumer; worth trimming at consumption time.

## 5. Generic byte/decoder algebra vs Lir-specific emitter facts

This split is the direct input to the assembler question
([07-assembler](07-assembler.md), and
[bytecode-interface.md §2.4](../../fleet-2026-07-02/bytecode-interface.md)): the generic half is
true of **any** `ByteArray` under EVMLean's decoder and belongs in exp003 (or a standalone Asm
library); the specific half mentions `emitStmt`/`matCache`/`offsetTable` and would be
regenerated per emitter.

**Generic (portable as-is; no Lir symbol in the statement):**

| Brick | What it is |
|---|---|
| [`bget`](../../../LirLean/Decode/DecodeLower.lean#L66), [`bextract`](../../../LirLean/Decode/DecodeLower.lean#L75) | list-backed `ByteArray` indexing/slicing |
| [`decode_nonpush_of_list`](../../../LirLean/Decode/DecodeLower.lean#L98), [`decode_push_of_list`](../../../LirLean/Decode/DecodeLower.lean#L114) | decode of any list-backed code from one byte + immediate window |
| [`flatMap_split`](../../../LirLean/Decode/Layout.lean#L75), [`mid_index`](../../../LirLean/Decode/Layout.lean#L153), [`flatMap_index_inv`](../../../LirLean/Decode/BoundaryCursor.lean#L20), [`append_region_inv`](../../../LirLean/Decode/BoundaryCursor.lean#L39) | pure list index algebra (both directions) |
| [`SegAlignedP`](../../../LirLean/Decode/SegAligned.lean#L63) + [`mono`](../../../LirLean/Decode/SegAligned.lean#L74)/[`append`](../../../LirLean/Decode/SegAligned.lean#L84)/[`nonpush`](../../../LirLean/Decode/SegAligned.lean#L93)/[`push`](../../../LirLean/Decode/SegAligned.lean#L101) | the instruction-alignment calculus |
| [`reaches_end_of_segAlignedP`](../../../LirLean/Decode/SegAligned.lean#L113), [`reaches_P_of_segAlignedP`](../../../LirLean/Decode/SegAligned.lean#L155), [`reachesBoundary_le`](../../../LirLean/Decode/SegAligned.lean#L51) | the two boundary-walk transports |
| [`ReachesBoundary.trans`](../../../LirLean/Decode/JumpValid.lean#L68), [`reachesBoundary_nextInstr`](../../../LirLean/Decode/BoundaryReach.lean#L477) | walk composition |
| [`mem_validJumpDestsAuxNat_inv`](../../../LirLean/Decode/BoundaryReach.lean#L419), [`reachesBoundary_of_mem_validJumpDests`](../../../LirLean/Decode/BoundaryReach.lean#L458) | the jump-dest scan's membership inversion (the converse of exp003's own [`mem_validJumpDests_of_reachable_jumpdest`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L189) — it arguably belongs next to it) |
| [`reachesBoundary_drop_segAlignedP`](../../../LirLean/Decode/BoundaryReach.lean#L174), [`segAlignedP_flatMap`](../../../LirLean/Decode/BoundaryReach.lean#L219) | region-drop transport, flatMap alignment |

**Lir-specific (mentions the emitter; the fused-assembler mass):** everything else — the length
invariance and prefix-sum facts (`Layout` §§1–3), `pcOf`/`termOf` and all anchors, the
`IsLoweringOp`/`NoCallCreateOp` emit ladders, `reaches_block_offset`/`block_offset_validJump`,
`LowerBoundaryCursor`, and the `stepFrame_*_lowering_site_inv` pair. Note however that even this
half is *shape-generic*: it consumes only "blocks = `JUMPDEST :: stmts ++ term`, fixed-width
destination pushes", never IR semantics — precisely the interface an `assemble` function would
present, which is why [bytecode-interface.md](../../fleet-2026-07-02/bytecode-interface.md)
(§2.4) can propose retargeting `lower` as `assemble ∘ lowerAsm` with the proofs moving mostly
intact.

## 6. Results taxonomy

- **Headline (of this layer):**
  [`flatBytes_at_pcOf`](../../../LirLean/Decode/Layout.lean#L248) + the A1–A3 anchors (the
  generic M1 discharge), [`segAlignedP_flatBytes`](../../../LirLean/Decode/SegAligned.lean#L443),
  [`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226),
  [`decode_reachable_boundary_loweringOp`](../../../LirLean/Decode/BoundaryReach.lean#L529),
  [`reachesBoundary_of_mem_validJumpDests`](../../../LirLean/Decode/BoundaryReach.lean#L458).
  All feed the tour's flagship chain via `Frame/Match` → Sim ([05](05-simulation.md)) and via
  R6 → Realisability ([06](06-realisability.md)).
- **Bricks:** everything in §§3.1–3.3 below the anchors; the `SegAlignedP` calculus; the
  drop/local-region transports. Proof methods are uniformly boring in the good sense —
  structural/list induction plus `omega`, per-byte `decide`; no `maxHeartbeats` overrides, no
  big-term `decide`, no `native_decide` anywhere in scope (grep-verified).
- **Examples:** none in this folder (the per-program `rfl` walks this layer superseded live
  elsewhere).
- **Staged/unconsumed (flag):** `LowerBoundaryCursor` + `flatBytes_cursor_cases`,
  `reachesBoundary_local_stmt`/`_term` + the drop family, the whole `NoCallCreateOp` tower, and
  [`stepFrame_needsCreate_lowering_site_inv`](../../../LirLean/Decode/BoundaryReach.lean#L584)
  have **no consumer in this tree** — they are pre-positioned for the R6 B-pc/B-inrange and
  CREATE-edge `sorry`s. No headline depends on them yet; risk is bounded to "wasted mass if the
  boxed R6 closure took a different route". Reconcile at merge time per the plan's own
  consume-or-delete rule.
- **Smells (all isolated, none under a closed headline):**
  1. **`LoweringLemmas.lean` is a stowaway** — [confirmed](../../../LirLean/Decode/LoweringLemmas.lean#L21):
     spill-routing/`rematOf` projection facts, zero geometry. It sits in `Decode/` only because
     [`DecodeLower.lean#L1`](../../../LirLean/Decode/DecodeLower.lean#L1) uses it as its route to
     `Spec/Lowering`. Belongs beside the Materialise/value-channel material
     ([04-value-channel](04-value-channel.md)).
  2. **Stale-count residue:** the folder itself is clean (the "16 lowering opcodes" comments the
     [codebase map §5.12](../../codebase-map-2026-07-06.md) flagged now correctly say 18), but
     one survivor sits in the consumer:
     [Machinery.lean#L1385](../../../LirLean/Realisability/Machinery.lean#L1385) still says
     "the 16 `IsLoweringOp` arms". Also pending: the
     [R11 plan's CREATE2-only decision](../../planning/r11-plan-2026-07-08.md) will delete the
     `Byte.create` branch of [`emitStmt`](../../../LirLean/Spec/Lowering.lean#L114), shrinking
     `IsLoweringOp` to 17 — expect another count sweep.
  3. **Stale narration:** [`DecodeLower.lean#L133`](../../../LirLean/Decode/DecodeLower.lean#L133)
     still describes the `pcOf` byte-layout arithmetic as "the open C3 work" that `Layout.lean`
     long since closed; [`Frame/Match.lean`](../../../LirLean/Frame/Match.lean#L25) similarly
     still calls the program-global M1 discharge "the remaining C3 work". Doc-rot only.
  4. **Minor:** [`JumpValid.lean#L4`](../../../LirLean/Decode/JumpValid.lean#L4) imports
     `DecodeAnchors` without using anything from it; leftover "Build-enforced guard" trailer
     comments at [JumpValid.lean#L269](../../../LirLean/Decode/JumpValid.lean#L269) and
     [BoundaryReach.lean#L606](../../../LirLean/Decode/BoundaryReach.lean#L606) after guard
     consolidation.

## 7. Doc-vs-source discrepancies (verified)

1. **`pcOf` location / import inversion — docs stale, source fixed.**
   [codebase-map-2026-07-06.md](../../codebase-map-2026-07-06.md) (§L4 table rows for `Frame/`
   and `Decode/`, misplacement #4) states `pcOf`/`pcOf_eq_anchor`/`flatBytes_at_pcOf` live at
   `Frame/Match.lean:67-108` and that `Decode/` imports `Frame/Match` (inverted layering). In
   current source they live at [`Decode/Layout.lean#L227`](../../../LirLean/Decode/Layout.lean#L227)–[L255](../../../LirLean/Decode/Layout.lean#L248),
   and no `Decode/` file imports `Frame/` (grep-verified). The map's recommendation was executed
   after the map was written.
2. **[bytecode-interface.md](../../fleet-2026-07-02/bytecode-interface.md) file inventory stale**
   (expected — 2026-07-02): it lists `NoCreateBytes.lean` (433 ln) as live — the tower was
   **deleted** when `emitStmt .create` made CREATE bytes legal (recorded at
   [SegAligned.lean#L15](../../../LirLean/Decode/SegAligned.lean#L15)); `LowerDecode.lean` and
   `MatDecLower.lean` have moved to [`CfgSim/`](../../../LirLean/CfgSim/LowerDecode.lean) and
   [`Materialise/`](../../../LirLean/Materialise/MatDecLower.lean); line counts have shifted
   substantially (e.g. JumpValid 515→271 after the `SegAlignedP` dedup, BoundaryReach 435→607
   after R11 chunk 1). Its *architectural* claims (§2.4 signatures, "assembler fused into Lir")
   remain accurate and are corroborated by this review.
3. **[r11-plan-2026-07-08.md](../../planning/r11-plan-2026-07-08.md) checkpoint vs this tree:**
   the checkpoint says B-pc and CALL-successor-in-range are closed via `ff825e3`/`9d45927`;
   those commits are **not in this local tree**, whose R6 edges still carry the four `sorry`s
   listed in §3.6. Not a contradiction — box-run branches pending integration — but a reader of
   the plan would over-count what is closed *here*.

## 8. Recommendations

1. **Integrate or re-derive the boxed B-pc/B-inrange closures**, then apply the plan's
   consume-or-delete rule to the currently-unconsumed chunk-1 bricks (`LowerBoundaryCursor`,
   `reachesBoundary_local_*`, the `NoCallCreateOp` tower).
2. **Relocate `LoweringLemmas.lean`** out of `Decode/` (it is value-channel material), and drop
   the unused `DecodeAnchors` import from `JumpValid.lean`.
3. **One stale-count/narration sweep** at the CREATE2-only landing: Machinery's "16 arms"
   comment, DecodeLower's and Frame/Match's "open C3" narration, the guard trailer comments,
   and the 18→17 `IsLoweringOp` shrink.
4. **Upstream the generic half** (§5 table) toward exp003's
   [`Decode.lean`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L129)
   characterization section — `reachesBoundary_of_mem_validJumpDests` in particular is the
   missing converse of a lemma already there — or into the Asm layer proposed in
   [07-assembler](07-assembler.md). This folder is the existence proof that the Asm extraction
   is a refactor, not new mathematics.
5. **Refresh the codebase map's §L4** rows now that misplacement #4 is fixed, so the next
   reviewer isn't sent to `Frame/Match.lean:67` for `pcOf` (as this one was).
