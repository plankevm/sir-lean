# 07 — The planned verified assembler (Asm layer)

Part of the [exp005 tour](00-overview.md).

**The point in one paragraph.** exp005 already contains an assembler — it is just fused into the
IR: [`emitStmt`/`emitTerm` → `flatBytes` → `offsetTable` → `encode`](../../../LirLean/Spec/Lowering.lean#L114)
is byte emission with computed label offsets, and its correctness proof (decode anchors, jumpdest
validity, landing behavior, boundary reachability) is ~3.6k lines smeared across
[`Decode/`](../../../LirLean/Decode/Layout.lean) and [`CfgSim/LowerDecode.lean`](../../../LirLean/CfgSim/LowerDecode.lean),
all stated over `lower prog` and therefore unusable by any second IR. The planned Asm layer
([target-architecture §6 item 4](../../target-architecture-2026-07-02.md#L143), design in
[bytecode-interface §2.4](../../fleet-2026-07-02/bytecode-interface.md#L139)) de-fuses it: a
structured `AsmProgram` (blocks + labeled jumps + data segments) with a verified `assemble`, the
geometry algebra proven once against `assemble` output, and `lower` retargeted as
`assemble ∘ lowerAsm`. It cannot make pc/jumpdest reasoning disappear — nothing can — but it makes
it a one-time cost instead of a per-IR cost, and it is the natural home for the real Plank IR's
placement nondeterminism (allocators, data segments). It is gated behind R11: the
[r11-plan](../../planning/r11-plan-2026-07-08.md#L51) explicitly defers "the assembler facade until
the active producer files are quiescent."

Related tour stops: [01-trusted-base](01-trusted-base.md) (the exp003 machine the assembled bytes
run on), [02-spec-layer](02-spec-layer.md) (where `emit`/`lower` live today),
[03-code-geometry](03-code-geometry.md) (the Decode/ proof mass the assembler would absorb),
[05-simulation](05-simulation.md) (Corr's geometric fields), [06-realisability](06-realisability.md)
(the flagship whose closure gates this work).

---

## 1. What exists today: an assembler fused into the IR

The whole pipeline is ~75 lines of [`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean#L114)
(188 lines total). Statements and terminators emit byte lists; label references are `PUSH4` of a
prefix-sum offset table; blocks concatenate under a leading `JUMPDEST`:

```lean
def emitTerm (cache : Tmp → List UInt8) (labelOff : Nat → Nat) : Term → List UInt8
  | .ret t              => cache t
                             ++ emitImm 0 ++ [Byte.mstore]
                             ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]
  | .stop               => [Byte.stop]
  | .jump dst           => emitDest (labelOff dst.idx) ++ [Byte.jump]
  | .branch cond thenL elseL =>
      cache cond
      ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
      ++ emitDest (labelOff elseL.idx) ++ [Byte.jump]
```

```lean
def offsetTable (cache : Tmp → List UInt8) (alloc : Alloc) (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map (blockLen cache alloc)).sum

def emit (a : Alloc) (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let labelOff := offsetTable cache a prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache a labelOff b)

def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)
```

([emitTerm](../../../LirLean/Spec/Lowering.lean#L158), [offsetTable/emit/lower](../../../LirLean/Spec/Lowering.lean#L176).)
That *is* an assembler: symbolic labels resolved to concrete pcs by a two-pass layout (the measuring
pass is well-defined because `emitDest` is fixed-width `PUSH4` —
[`emitTerm_length_labelOff`](../../../LirLean/Decode/Layout.lean#L48)). It is fused because the
"instruction stream" is Lir syntax itself and the "operand segments" are the opaque byte lists
`matCache prog` produces from Lir `Expr`s.

The assembler's correctness proof is the geometry mass (detail in
[03-code-geometry](03-code-geometry.md)):

| File | Lines | Content |
|---|---|---|
| [`Decode/Layout.lean`](../../../LirLean/Decode/Layout.lean#L4) | 257 | prefix-sum decomposition of `flatBytes`; [`pcOf`](../../../LirLean/Decode/Layout.lean#L227) (the cursor→pc map) |
| [`Decode/DecodeLower.lean`](../../../LirLean/Decode/DecodeLower.lean#L45) | 157 | [`flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L45), decode-at-index reduction to list lookups |
| [`Decode/DecodeAnchors.lean`](../../../LirLean/Decode/DecodeAnchors.lean#L51) | 317 | per-statement/term byte anchors, decode-at-cursor |
| [`Decode/SegAligned.lean`](../../../LirLean/Decode/SegAligned.lean#L5) | 456 | the parameterized instruction-alignment tower `SegAlignedP` |
| [`Decode/JumpValid.lean`](../../../LirLean/Decode/JumpValid.lean#L226) | 271 | [`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226): every block offset ∈ `validJumpDests (lower prog) 0` |
| [`Decode/BoundaryReach.lean`](../../../LirLean/Decode/BoundaryReach.lean#L5) | 607 | boundary-reachability bricks for the whole-run `AtReachableBoundary` invariant (R6) |
| [`Decode/BoundaryCursor.lean`](../../../LirLean/Decode/BoundaryCursor.lean#L1) | 151 | boundary→cursor inversion |
| [`Decode/LoweringLemmas.lean`](../../../LirLean/Decode/LoweringLemmas.lean#L1) | 139 | `emitStmt`/`emitTerm` shape reductions |
| [`CfgSim/LowerDecode.lean`](../../../LirLean/CfgSim/LowerDecode.lean#L8) | 1,069 | discharges the sims' carried decode bundles from the anchors |
| [`Materialise/MatDecLower.lean`](../../../LirLean/Materialise/MatDecLower.lean#L1) | 147 | decode channel for materialised operand segments |

Total: **3,571 lines** today (plus [`Materialise/MatFoldChannel.lean`](../../../LirLean/Materialise/MatFoldChannel.lean#L1),
1,347 lines, whose fold decode channel is geometry-adjacent). The
[bytecode-interface taxonomy](../../fleet-2026-07-02/bytecode-interface.md#L64) called this band
"(ii-a) Code geometry / 'assembler correctness' (~4,100 ln)" and named it exactly:

> Nothing here mentions IR *semantics* — only the byte lists `emitStmt`/`emitTerm` produce. This
> is, de facto, the correctness proof of an assembler fused into Lir.

The dynamic half — landing on a `JUMPDEST` and re-establishing the coupling — now lives in
[`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503) (Sim-side; see §6 for why that
placement matters). exp003 itself offers no generic emitted-code geometry: its decode lemmas are
literal per-program facts for a fixed example
([`decode_seq_0`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L25)), which is
why exp005 built all of the above in-house — the central finding of
[bytecode-interface §0](../../fleet-2026-07-02/bytecode-interface.md#L19).

## 2. The planned layer

[bytecode-interface §2.4](../../fleet-2026-07-02/bytecode-interface.md#L139) — "the centerpiece" —
specifies `BytecodeLayer/Asm.lean` (exp003-side):

```lean
inductive AsmInstr | push (v : UInt256) | op (o : StraightOp)   -- no pc-affecting ops in a body
inductive AsmTerm  | stop | ret | jump (dst : Label) | branch (dst thenL elseL : Label)
structure AsmBlock where body : List AsmInstr ; term : AsmTerm
structure AsmProgram where blocks : Array AsmBlock ; data : Array ByteArray  -- data segs: v2

def assemble  : AsmProgram → ByteArray                 -- JUMPDEST-prefixed blocks + offset table
def entryPc   : AsmProgram → Label → ℕ                 -- packages Layout.lean's offsetTable
def cursorPc  : AsmProgram → Label → ℕ → ℕ

-- static geometry, proven ONCE about `assemble`:
theorem assemble_decode_at   : instrAt p L i = some ins →
    decode (assemble p) (cursorPc p L i) = some (opcodeOf ins)
theorem assemble_validJumps  : validJumpDests (assemble p) 0 = entryPcSet p
theorem assemble_no_create   : …
theorem assemble_boundary_reach : …

-- the cursor judgment hiding Corr's geometric fields (pc_eq/code_eq/validJumps_eq/stack_nil):
def AtCursor (p : AsmProgram) (fr : Frame) (L : Label) (i : ℕ) (stk : List UInt256) : Prop

-- dynamic landing, proven ONCE:
theorem jump_landing   : AtCursor p frT L (bodyLen p L) [] → termOf p L = .jump dst →
    CleanHaltsNonException frT → ∃ fj, Runs frT fj ∧ AtEntry p fj dst ∧ EffectFree frT fj
theorem branch_landing : …  (cond-split form, mirroring runs_branch)
```

Plus, for data segments (v2), the placement-quotient theorem named at
[bytecode-interface :168](../../fleet-2026-07-02/bytecode-interface.md#L168):
`assemble_codecopy_data : CODECOPY of handle d reads segment d's bytes at whatever offset assemble chose`.

Migration shape (the [phased order at the end of the doc](../../fleet-2026-07-02/bytecode-interface.md#L216)):
extract the algebra from the geometry files, then **retarget `lower` as `assemble ∘ lowerAsm` with a
definitional-equality bridge to `lower prog` so the closed conformance proof survives unmodified.**
`Lir.lowerAsm : Program → AsmProgram` keeps all of Lir's materialisation policy (the `matCache`
byte segments become `AsmInstr.push`/`.op` sequences); `assemble` owns layout, `JUMPDEST` placement,
and label resolution. Corr's four geometric fields collapse into one `AtCursor` fact; the semantic
fields stay Lir's (see §4).

## 3. Why it helps future IRs

This is the lead's actual question; three parts.

**(a) The pc/jumpdest/landing reasoning cannot be eliminated — but it can be paid once.**
[target-architecture :149](../../target-architecture-2026-07-02.md#L149) states it exactly:

> pc/jumpdest/landing reasoning cannot be *eliminated* (it is the semantic content of "bytes
> implement this CFG"; no fork does it — they evade the problem, not solve it), but it can be
> *paid once*.

The prior-art survey backs the "no fork" claim:
[remediation-plan :15](../../remediation-plan-2026-07-02.md#L15) — "all forks target structured
Yul/IR interpreters — **no pc/stack/jumpdest reasoning**. Our bytecode layer … has no fork
analogue" — and [:11](../../remediation-plan-2026-07-02.md#L11): Verity *supplies* its run-match as
a hypothesis (`EndToEnd.lean:128`). The forks are precedent that IRs want a structured target; none
has the verified assembler underneath. [bytecode-interface §3](../../fleet-2026-07-02/bytecode-interface.md#L196)
draws the right conclusion: this layer is the project's novel asset — make it reusable rather than
regret it.

**(b) The ratio flip.** The [taxonomy headline stat](../../fleet-2026-07-02/bytecode-interface.md#L70):
of exp005's ~24.7k lines (now ~26.9k, see §6), ~20% is misplaced pure engine theory, ~57%
frame-level lowering machinery, **<10% actual IR content**. Under the current interface IR #2
re-pays the 57%. Against the full exported surface (Exec + Recorder + Invariants + **Asm** +
CyclicSim), [the recommendation](../../fleet-2026-07-02/bytecode-interface.md#L204) is that IR #2
proves *only*: its lowering into `AsmProgram`, per-statement effect sims, its coupling invariant's
semantic fields, its value channel, and its oracle ties — "a substrate-free IR proof whose
obligations are all IR-shaped," i.e. the "Philogy can vibe-code passes on it" criterion.

**(c) The forward-looking clincher: placement nondeterminism.** The real Plank IR has a memory
allocator and data segments — both are *placement* choices. Quoting
[bytecode-interface :202](../../fleet-2026-07-02/bytecode-interface.md#L202):

> Against raw bytes, every IR would fight offset-existentials in decode proofs forever. Against
> `AsmProgram` with symbolic labels + data handles, nondeterministic placement is the assembler's
> freedom, and the algebra's theorems (`assemble_decode_at`, `assemble_codecopy_data`) are precisely
> the quotient by placement.

This dovetails with the settled future-proofing decisions
([target-architecture §7](../../target-architecture-2026-07-02.md#L154)): nondeterminism =
∀-quantified placement (offset-independence enforced by the theorem's *shape* —
[future-proofing §2](../../fleet-2026-07-02/future-proofing.md#L74)); the one BREAKS-level overfit
today is the `slot' = slotOf tw` pin ([future-proofing §1b](../../fleet-2026-07-02/future-proofing.md#L27));
data-after-code as a design commitment keeps the Layout anchors untouched, while the
instruction-aligned alignment walk is unsound over a data suffix and must be rescoped to
pc-reachability — the same work as the R6 `hrb` residual
([future-proofing §1d](../../fleet-2026-07-02/future-proofing.md#L39)). The structured target is
the home where all of these land as assembler freedom rather than per-IR proof debt. The
[spilling-encoding review](../../design/spilling-encoding.md#L150) already routes cleanup into it:
the redundant `Expr.slot`-era placement residue folds into "the Phase-5 `Asm.lean` restructure …
make `Loc`/`Alloc` the sole authority."

## 4. What each IR still pays (the assembler is not magic)

Per [bytecode-interface §3, "what stays with each IR, irreducibly"](../../fleet-2026-07-02/bytecode-interface.md#L200):

1. **Lowering + per-statement effect sims** — that statement `s` compiles to a body slice whose
   *effect* (via exp003's post-frame transformers `addFrame`/`sloadFrame`/`gasFrame`/…) matches the
   IR step. This is the actual semantic content of the IR's compiler.
2. **The coupling invariant's semantic fields** — Lir's
   [`storage`/`defsSound`/`wellScoped`/`memAgree`](../../../LirLean/Sim/SimStmt.lean#L119) survive
   as-is; only the geometric fields fold into `AtCursor`.
3. **Value-channel policy** — recompute-on-use + spill-to-slot is a Lir *policy*; the (ii-c) band
   (~3,600 ln) "ports as a worked pattern, not a library."
4. **Oracle seams** — the CallRealises-shaped ties from the recorded log; realisability closure is
   per-IR (see [06-realisability](06-realisability.md)).
5. **Block-boundary stack profile** — within-block stacks are the IR's business; boundary profiles
   become an `AtCursor` parameter, with v1 hard-fixing Lir's "empty stack at boundaries" convention.

## 5. Sequencing, risks, and where it lives

**Strictly after R11.** [target-architecture](../../target-architecture-2026-07-02.md#L145): the Asm
layer is "**Phase 5, strictly after Phase 3** — it churns exactly the files Phase 3 rewrites," and
[bytecode-interface §4 item 3](../../fleet-2026-07-02/bytecode-interface.md#L214) adds the second
reason: doing the closure first *reveals which recorder laws it actually needs*. The live gate is
the [r11-plan](../../planning/r11-plan-2026-07-08.md#L51): "Defer import-moving spec surgery and the
assembler facade until the active producer files are quiescent." As of the 2026-07-09 checkpoint the
producer is not quiescent: [`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251)
is a WIP shell with 16 sorries across the WIP cone and four boxed runs churning R6/CALL/CREATE2/gas
arms. The [full migration order](../../fleet-2026-07-02/bytecode-interface.md#L216) is: Phase 3
(≈ R11) → Phase 4 (relocate category (i) engine theory into `Exec`/`Recorder`/`Invariants`, restate
the flagship frame-free) → **Phase 5 = Asm extraction** → IR #2 starts against the finished surface.

**Risk: the parameterization is an untested design bet.** The
[doc's own caveat](../../fleet-2026-07-02/bytecode-interface.md#L204): "until a second IR actually
exercises it, the Asm interface parameterization (opcode alphabet, boundary stack profile, data
handles) is a design bet; keep v1 minimal (Lir's 16-opcode alphabet, empty-stack boundaries) and let
IR #2's needs — not speculation — drive generalization." That is the right discipline; the matching
[target-architecture §7 rule](../../target-architecture-2026-07-02.md#L195) defers any `IRLang`
typeclass until IR #2 exists.

**Where: exp003-side.** As `BytecodeLayer/Asm.lean`, item 4 of the
[five-file exported surface](../../target-architecture-2026-07-02.md#L136). Rationale: the algebra
mentions only bytes, `decode`, `validJumpDests`, `Frame`, `Runs` — bytecode-layer vocabulary — and
exp003 is the layer that broke its own encapsulation promise
([`Hoare.lean:27`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L27): "`Runs` … never
appears in an exported statement", violated by exp005's headline); Asm + `Exec` is how it repays
that debt. One toolchain note: exp003 is pinned to v4.30.0 and exp005 vendors its own engine copy,
so "exp003-side" in practice means the shared bytecode layer exp005 builds against — the relocation
mechanics are Phase 4's problem and the Asm decision inherits them.

## 6. Critical assessment

Does the code actually support "it factors cleanly"? **Mostly yes, with three honest qualifications
and some doc drift.**

**The IR-semantics claim checks out.** Grep over `Decode/` for `IRState`, `RunFrom`, `EvalStmt`,
`evalExpr`, `Observable`, `StorageAgree`, `MemRealises`: zero hits. Imports are only
`Evm`, [`Spec.Lowering`](../../../LirLean/Spec/Lowering.lean#L1) (syntax + emitters), the other
Decode files, and `Engine.Descent` (BoundaryReach only — engine, not IR). And `Corr`'s split is
exactly as claimed: [`pc_eq`/`code_eq`/`validJumps_eq`/`stack_nil`](../../../LirLean/Sim/SimStmt.lean#L105)
mention only the frame and the lowered code (plus `can_modify`, which is neither geometry nor IR),
while `storage`/`defsSound`/`wellScoped`/`memAgree` are the IR half;
[`Corr.validJumps_lower`](../../../LirLean/Sim/SimStmt.lean#L140) is already a purely structural
discharge. The seam is real.

**Qualification 1 — IR-semantics-free ≠ IR-free.** Every Decode/ theorem is *indexed* by Lir syntax:
statements are over `flatBytes prog`, `pcOf prog L pc`, `matCache prog`, with lemmas recursing over
`Expr` (e.g. [`segAlignedNoCall_matExpr`](../../../LirLean/Decode/BoundaryReach.lean#L75)). So the
extraction is a re-indexing of every statement from `lower prog` to `assemble p`, not a file move.
"The proofs themselves move mostly intact"
([bytecode-interface :198](../../fleet-2026-07-02/bytecode-interface.md#L198)) is fair for the
arithmetic core (prefix sums, list splitting, the `SegAlignedP` tower) but the statement layer is a
rewrite. Mitigating: a chunk of the mass *evaporates* rather than ports — the alignment tower exists
only because `emit` produces opaque byte lists; `assemble` output is instruction-aligned by
construction, and the `matExpr`-recursion lemmas become definitional once operand segments are
structured `AsmInstr` lists. Net one-time cost plausibly below a straight port; net *reusable* mass
also smaller than "~4,100 lines move" suggests.

**Qualification 2 — the landing algebra has drifted toward Corr since the doc.** The doc's exhibit
for "dynamic landing, proven ONCE" was `branch_landing_of_cleanHalt` (then LowerDecode.lean:755,
322 lines). That lemma no longer exists; post-P8/P9 the landing fact is
[`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503), stated *through* `Corr` — it
takes the four geometric facts and the four IR-semantic facts as separate hypotheses and rebuilds
`Corr` at the successor entry. The geometry is still separable (the IR fields pass through
untouched), but Phase 5 now has to de-fuse this lemma into the `AtCursor`-shaped `jump_landing`
plus a trivial IR-side transport, where the doc implied a ready-made geometric lemma. Small, but it
is churn the doc doesn't account for.

**Qualification 3 — the definitional-equality bridge is a bet, not a fact.** "So the closed
conformance proof survives unmodified" requires `assemble (lowerAsm prog)` to be judgmentally (or
at least `rfl`-lemma) equal to today's `emit` fold, including the exact `matCache` byte granularity
and the two-pass offset-table trick. Achievable — `assemble` can replicate the fold — but it
constrains `assemble`'s definition to Lir's current shape, which slightly tensions with "keep v1
minimal but IR-agnostic." Worth an explicit prototype before committing the migration order.

**Doc line-count drift** (claims from [bytecode-interface :64](../../fleet-2026-07-02/bytecode-interface.md#L64),
written 2026-07-02; tree has since gone through P5–P9 and R11 chunks):

| Claim (2026-07-02) | Now (2026-07-09) |
|---|---|
| (ii-a) ~4,100 ln across 8 files | ~3,571 across 10 files (Decode/ 2,355 + LowerDecode 1,069 + MatDecLower 147); + MatFoldChannel 1,347 geometry-adjacent |
| `NoCreateBytes.lean` (433) | **deleted** — CREATE/CREATE2 are now emitted opcodes ([SegAligned.lean:15](../../../LirLean/Decode/SegAligned.lean#L15)); `assemble_no_create` as specced is obsolete, superseded by the "descents exactly at emitted sites" predicate ([target-architecture §7](../../target-architecture-2026-07-02.md#L190)) |
| `LowerDecode.lean` 1,517 incl. 322-line `branch_landing_of_cleanHalt` | 1,069; the landing lemma replaced by Corr-fused [`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503) |
| `MatDecLower` 516, `JumpValid` 515 | 147 and 271 (P8 shrink; the `SegAlignedP` unification absorbed the duplication) |
| exp005 total ~24.7k | 26,867 (R11 machinery: `Realisability/` is 5,135 ln) |
| `TieDischarge.lean` 4,506, headline at :4292 | file dissolved; flagship now [`RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251) |

None of the drift undermines the design argument — the fused-assembler diagnosis and the
factorability evidence are stronger now (the `SegAlignedP` unification and the `Loc`/`Alloc` seam
are both moves *toward* the Asm shape) — but §2.4's signature list should be refreshed against the
post-R11 tree before Phase 5 starts: `assemble_no_create` is dead as stated, the landing lemma must
be re-derived rather than relocated, and the (ii-a) inventory names four files that no longer exist
under those names.

**Bottom line.** The layer is well-motivated (pay the un-evadable geometry once; give placement
nondeterminism a home before the real Plank IR needs it), the code evidence for factorability is
genuine, and the sequencing discipline is right and currently binding: nothing to build until the
R11 producer closes. The two things to watch: prototype the `assemble ∘ lowerAsm` defeq bridge
early, and treat the §2.4 signatures as 2026-07-02 sketches, not a frozen spec.
