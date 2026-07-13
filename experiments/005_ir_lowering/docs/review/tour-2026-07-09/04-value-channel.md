# 04 — The value channel and effect oracles (`Materialise/` + `Frame/`)

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

Part of the [exp005 tour](00-overview.md).

**Scope.** `LirLean/Materialise/` in full — the machinery that proves the bytes the lowering
emits for an expression reconstruct the IR's value on the EVM stack — plus the effect-oracle
half of `LirLean/Frame/` (`Call.lean`, `Create.lean`, `Match.lean`, `SmallStep.lean`).
Upstream definitions (`matCache`, `defsOf`, `lower`) are covered in [02-spec-layer.md](02-spec-layer.md);
byte-layout algebra in [03-code-geometry.md](03-code-geometry.md); the per-statement sims that
consume this layer in [05-simulation.md](05-simulation.md); the coupled walk and flagships in
[06-realisability.md](06-realisability.md). The IR-free per-opcode step dichotomies inside
`CleanHaltExtract.lean` belong conceptually to the trusted base — see
[01-trusted-base.md](01-trusted-base.md); this report covers the lowering-shaped envelope
family built on them.

**Verification status** (one line): every file in scope is `sorry`/`axiom`/`native_decide`-free
(grepped); no `maxHeartbeats` cranks (one `maxRecDepth 8192` noted in §7);
[`Audit.lean#L33`](../../../LirLean/Audit.lean#L33) build-enforces the axiom footprint of the
central deliverable `materialise_runsC_of_cleanHalt` (`propext`, `Classical.choice`,
`Quot.sound` only) — recorded guard, build not re-run for this review.

---

## 1. TL;DR

This layer proves the **value channel**: running the byte cache `matCache prog` for an
expression `e` from any well-anchored frame pushes exactly `evalExpr st obs e` onto the EVM
stack, with pc/gas/memory/storage effects pinned — the fuel-free linchpin
[`materialise_runsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L812). Its best design
idea is **uniform spill-to-slot** (D3): after the old universally-quantified
`GasRealises`/`SloadRealises` value ties were *machine-checked unsatisfiable* on real runs,
every non-recomputable temp (gas read, sload, call/create result) is stashed once to memory
slot `slotOf t = t.id * 32` and read back by `PUSH32 slot ; MLOAD`, so the value question
became positional and is carried by the honest per-slot invariant
[`MemRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366). Gas envelopes are
**derived, not supplied**: a single
[`CleanHaltsNonException`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L62) witness at the entry
cursor yields every per-opcode gas bound by step-inversion
([`materialise_runsC_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372),
[`gas_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L700)).
The call/create effect oracles pin the IR's external-call effect *reflexively* to exp003's
resume ([`call_reflects_lowered`](../../../LirLean/Frame/Match.lean#L473),
[`create_reflects_lowered`](../../../LirLean/Frame/Match.lean#L530)). One clean negative
finding: the v1 machine in `Frame/SmallStep.lean` (the `Match` invariant, `callResult`/
`createResult` slots, `applyCall`/`applyCreate`, `bindCallResult`/`bindCreateResult`) has
**zero theorem consumers** — the live path is the V2 stream semantics (§6). The 2026-07-06
codebase map is stale on this layer (fuel-era names; P9 deleted them) — see §8.

## 2. Module map (every file in scope)

| File | Lines | Role | Status |
|---|---|---|---|
| [`Materialise/MaterialiseRuns.lean`](../../../LirLean/Materialise/MaterialiseRuns.lean) | 506 | B1 carriers: post-frame accessor reductions, [`StashRuns`](../../../LirLean/Materialise/MaterialiseRuns.lean#L217) bundle, [`MemRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366) + transport, memory-coverage bricks, RETIRED `GasRealises`/`SloadRealises` | live (retired defs kept as regression subjects) |
| [`Materialise/MaterialiseGas.lean`](../../../LirLean/Materialise/MaterialiseGas.lean) | 217 | the charge-list fold [`chargeExpr`](../../../LirLean/Materialise/MaterialiseGas.lean#L92)/[`chargeCache`](../../../LirLean/Materialise/MaterialiseGas.lean#L121) + `subCharges` arithmetic | live |
| [`Materialise/MatFoldChannel.lean`](../../../LirLean/Materialise/MatFoldChannel.lean) | 1347 | the core: [`MatDecC`](../../../LirLean/Materialise/MatFoldChannel.lean#L373), [`MatRunsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L782), [`materialise_runsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L812), fold fixpoints, segment bridges | live — the linchpin |
| [`Materialise/MaterialiseCleanHalt.lean`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean) | 401 | gas envelope DERIVED from clean-halt: [`materialise_runsC_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372) | live |
| [`Materialise/MatDecLower.lean`](../../../LirLean/Materialise/MatDecLower.lean) | 147 | PUSH32 immediate round-trip [`uInt256_wordBytesBE`](../../../LirLean/Materialise/MatDecLower.lean#L110) + byte-window bricks | live |
| [`Materialise/DefsSound.lean`](../../../LirLean/Materialise/DefsSound.lean) | 650 | recompute-soundness: [`DefsSound`](../../../LirLean/Materialise/DefsSound.lean#L209), [`NonRecomputable`](../../../LirLean/Materialise/DefsSound.lean#L127), preservation [`defsSound_preserved`](../../../LirLean/Materialise/DefsSound.lean#L608) | live |
| [`Materialise/StashTail.lean`](../../../LirLean/Materialise/StashTail.lean) | 478 | the uniform `PUSH32 slot ; MSTORE` stash tail, proved once: [`stash_tail_runs`](../../../LirLean/Materialise/StashTail.lean#L157) + gas/sload variants | live |
| [`Materialise/CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean) | 1123 | per-op OOG/inversion/dichotomy bricks (IR-free half → [01-trusted-base.md](01-trusted-base.md)) + the lowering-shaped envelope family (§5.3 here) | live |
| [`Frame/Call.lean`](../../../LirLean/Frame/Call.lean) | 164 | `CallOracle` / `evmCallOracle` | oracle live; `applyCall` removed (§6) |
| [`Frame/Create.lean`](../../../LirLean/Frame/Create.lean) | 137 | `CreateOracle` / `evmCreateOracle` | oracle live; `applyCreate` removed (§6) |
| [`Frame/Match.lean`](../../../LirLean/Frame/Match.lean) | 618 | `selfStorage` lens, `sim_*` opcode bricks, reflexivity headlines, halt/discharge bricks | live bricks; `Match` structure removed (§6) |
| `Frame/SmallStep.lean` (deleted) | 129 | the v1 IR machine state | **removed** (§6) |
| [`Frame/StorageErase.lean`](../../../LirLean/Frame/StorageErase.lean) | 217 | pure `RBMap.erase` read-back facts ([`findD_erase_self`](../../../LirLean/Frame/StorageErase.lean#L189), [`findD_erase_of_ne`](../../../LirLean/Frame/StorageErase.lean#L199)) for zero-write SSTORE; not on this report's critical path | live brick |

**Naming note.** The reviewer-familiar names `MatDec` / `MatRuns` / `materialise_runs` /
`chargeOf` are the *deleted fuel-era* stack (P9); the live successors are the fold twins
`MatDecC` / `MatRunsC` / `materialise_runsC` / `chargeExpr`+`chargeCache`. Only
`gas_envelope_of_cleanHalt`, `MemRealises`, `DefsSound`, `stash_tail_runs` survive under
their old names.

## 3. The uniform spill-to-slot design (D3) — and the refutation that forced it

The lowering is **recompute-on-use**: a pure temp stores no register; every use re-emits its
defining expression's bytes. The design question is what to do with temps whose defining read
is *not* reproducible: a `GAS` read (gas descends), an `SLOAD` (value stable but warmth cost
changes 2100→100 on re-read), a CALL success flag, a CREATE address (both dynamic).

The first architecture tried to keep recompute universal and paper over the mismatch with
*constant-value realisability universals*, still in the tree as retired, documented subjects:

```lean
-- MaterialiseRuns.lean:318 — RETIRED (Phase B)
def GasRealises (obs : Word) (fr : Frame) : Prop :=
  ∀ (g : Frame),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    obs = UInt256.ofUInt64 (g.exec.gasAvailable - UInt64.ofNat Gbase)
```
([`GasRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L318);
[`SloadRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L297) is the warmth twin.)

The free `∀ g` over *every* same-address frame forces one word `obs` to equal the gas reading
at **all** frames of the run. A real run's gas strictly descends, so any two distinct GAS
reads refute it; for SLOAD, any cold-then-warm re-read of the same key forces
`sloadChg k = 2100 = 100`. This was machine-checked (`gasRealises_universal_unsatisfiable`,
`sloadRealises_universal_unsatisfiable` in the now-deleted `HonestGasTie.lean`); the
surviving records are the docstrings above, the
[`RealisabilitySpec.lean` header](../../../LirLean/Realisability/RealisabilitySpec.lean#L19),
and [`docs/gas-decision.md`](../../gas-decision.md). Consequence: any headline carrying those
hypotheses was **vacuous** — the finding that triggered the pivot
([`docs/uniform-spill-alloc-plan.md`](../../uniform-spill-alloc-plan.md) §0).

The fix reframes the question. The value of a non-recomputable temp is *positional* — "the
word produced by **that one read**, at **that one frame**" — so the lowering makes the
position physical: **compute once at the def-site, stash to a fixed memory slot, reuse the
stash**. The allocation is the two-answer `Loc` in
[`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean#L30) (details in
[02-spec-layer.md](02-spec-layer.md)):

```lean
inductive Loc where
  | remat (e : Expr)          -- pure: re-emit the defining expression's bytes at each use
  | slot  (n : Nat)           -- spilled: def-site stash, uses read back PUSH32 n ; MLOAD

def slotOf (t : Tmp) : Nat := t.id * 32
```

[`defEnv`](../../../LirLean/Spec/Lowering.lean#L46) routes `assign t .gas`,
`assign t (.sload _)`, and CALL/CREATE `resultTmp`s to `Loc.slot (slotOf t)`; everything else
stays `remat`. After the spill:

* the **value** tie is `MemRealises` (§5.1) — "the slot currently holds the IR's bound
  value", trivially satisfiable by the run that did the stash;
* the **cost** is charged exactly once, at the single def-site read; the positional
  selection ties [`GasLogAligned`](../../../LirLean/Drive/SelfPresent.lean#L98) /
  [`SloadLogAligned`](../../../LirLean/Drive/SelfPresent.lean#L267) and their discharges
  [`gasRealises_obs_of_witness`](../../../LirLean/Drive/SelfPresent.lean#L205) /
  [`sloadRealises_charge_of_witness`](../../../LirLean/Drive/SelfPresent.lean#L319)
  live in the realisability layer ([06-realisability.md](06-realisability.md));
* the value channel's `.gas`/`.sload` materialise arms become **unreachable** — a bare
  `Expr.gas`/`Expr.sload` is never materialised (hypotheses `e ≠ .gas`, `∀ k, e ≠ .sload k`,
  preserved across recursion by
  [`defsOf_ne_gas`](../../../LirLean/Decode/LoweringLemmas.lean#L21) /
  [`defsOf_ne_sload`](../../../LirLean/Decode/LoweringLemmas.lean#L64));
* a use restriction survives only for CALL results:
  [`WellFormed`](../../../LirLean/Materialise/DefsSound.lean#L144) (used ≤ once), with the
  decidable surrogate [`WellFormedDec`](../../../LirLean/Materialise/DefsSound.lean#L162) and
  [`wellFormed_of_dec`](../../../LirLean/Materialise/DefsSound.lean#L177). Gas/sload multi-use
  is unrestricted — the spill made it safe.

The old `Expr.slot` encoding smell was resolved by P9 exactly as
[`docs/design/spilling-encoding.md`](../../design/spilling-encoding.md) recommended (its P9
status note confirms; the current `Expr` has no `.slot` constructor).

## 4. The value channel, bottom-up

The channel is three parallel folds over the def-environment `defEnv prog`, kept in lockstep:
**bytes** ([`matCache`](../../../LirLean/Spec/Lowering.lean#L84), defined in the Spec layer),
**charges** ([`chargeCache`](../../../LirLean/Materialise/MaterialiseGas.lean#L121)), and
**decode obligations** ([`MatDecC`](../../../LirLean/Materialise/MatFoldChannel.lean#L373)).
Termination everywhere is the same fuel-free measure.

### 4.1 The termination measure (the fuel replacement)

```lean
-- MatFoldChannel.lean:297,303
def tmpIdx (prog : Program) (t : Tmp) : Nat := (defEnv prog).findIdx (fun p => p.1 == t)

def matDecMeasure (prog : Program) : Expr → Nat
  | .imm _   => 0
  | .gas     => 0
  | .tmp t   => 3 * tmpIdx prog t + 1
  | .add a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .lt  a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .sload k => 3 * tmpIdx prog k + 2
```

Well-foundedness of the `.tmp t → definiens` step is
[`matDecMeasure_remat_lt`](../../../LirLean/Materialise/MatFoldChannel.lean#L346), resting on
[`DefEnvOrdered`](../../../LirLean/Spec/WellFormed.lean#L99) (every operand of a `remat` entry
sits strictly earlier in `defEnv`) and
[`DefsConsistent`](../../../LirLean/Spec/WellFormed.lean#L37) (SSA single binding). These two
well-formedness facts, plus the fold fixpoint
[`matCache_unfold`](../../../LirLean/Spec/WellFormed.lean#L349), are the entire interface this
layer needs from [02-spec-layer.md](02-spec-layer.md). P9 replaced the fuel index with this
measure; the old `recomputeFuel` undercounting problem (fuel truncation of deep chains) is
gone by construction.

### 4.2 The gas twin: `chargeExpr` / `chargeCache`

One charge-list entry per emitted opcode, in execution order:

```lean
-- MaterialiseGas.lean:92,102
def chargeExpr (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) : Expr → List ℕ
  | .imm _   => [GasConstants.Gverylow]
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [GasConstants.Gverylow]
  | .lt  a b => cache b ++ cache a ++ [GasConstants.Gverylow]
  | .sload k => cache k ++ [sloadChg k]
  | .gas     => [GasConstants.Gbase]

def chargeLoc (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) : Loc → List ℕ
  | .remat e => chargeExpr sloadChg cache e
  | .slot _  => [GasConstants.Gverylow, GasConstants.Gverylow]   -- PUSH n ; MLOAD
```

`sloadChg : Tmp → ℕ` keeps the lists pure by parameterising the runtime warmth cost. The
fixpoint [`chargeCache_unfold`](../../../LirLean/Materialise/MatFoldChannel.lean#L180) is the
exact twin of `matCache_unfold`, proved by the same def-env induction (prefix stability
[`chargeFold_take_eq_chargeCache`](../../../LirLean/Materialise/MatFoldChannel.lean#L106),
operand-locality [`chargeExpr_congr`](../../../LirLean/Materialise/MatFoldChannel.lean#L32)).
The **byte↔charge lockstep**
[`matCache_chargeCache_unfold`](../../../LirLean/Materialise/MatFoldChannel.lean#L244) states
that both caches unfold under the identical `Loc`; the length corollaries
([`chargeCache_length_slot`](../../../LirLean/Materialise/MatFoldChannel.lean#L261) = 2, etc.)
and the `sloadChg`-independence of lengths
([`chargeCache_length_sloadChg_eq`](../../../LirLean/Materialise/MaterialiseGas.lean#L209))
are what the stack-room folds in `Spec/WellFormed.lean` consume. Charge lists subtract off gas
via exp003's [`subCharges`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L62),
with the append laws in [`BytecodeLayer/Hoare/Sequence.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L66).

### 4.3 The decode bundle: `MatDecC` and its segment bridge

`MatDecC` states, per expression, exactly which opcodes must decode at which cursors of the
running code — the shape hypothesis `materialise_runsC` walks:

```lean
-- MatFoldChannel.lean:373 (abridged: .imm/.gas/.lt/.sload arms analogous)
def MatDecC (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (code : ByteArray) : UInt32 → Expr → Prop
  | p, .add a b =>
      MatDecC prog hdc hord code p (.tmp b)
      ∧ MatDecC prog hdc hord code (p + UInt32.ofNat (matCache prog b).length) (.tmp a)
      ∧ decode code (p + … + UInt32.ofNat (matCache prog a).length) = some (.ArithLogic .ADD, .none)
  | p, .tmp t  =>
      match h : allocate prog t with
      | some (.remat e) => MatDecC prog hdc hord code p e
      | some (.slot n)  =>
          decode code p = some (.Push .PUSH32, some (UInt256.ofNat n, 32))
          ∧ decode code (p + UInt32.ofNat (emitImm (UInt256.ofNat n)).length)
              = some (.Smsf .MLOAD, .none)
      | none            => decode code p = some (.Push .PUSH32, some ((0 : Word), 32))
```

It is discharged generically over the real lowered bytes by
[`matDecC_of_seg`](../../../LirLean/Materialise/MatFoldChannel.lean#L579): given only that the
fold bytes `matExpr (matCache prog) e` sit as a segment of
[`flatBytes prog`](../../../LirLean/Decode/DecodeLower.lean#L45), the whole bundle holds over
`lower prog`. Cursor-level specialisations
[`matDecC_of_lower`](../../../LirLean/Materialise/MatFoldChannel.lean#L1306) (statement
operands, anchored by `flatBytes_at_pcOf_offset`) and
[`matDecC_of_term`](../../../LirLean/Materialise/MatFoldChannel.lean#L1328) (terminator
operands) connect to the byte-geometry layer ([03-code-geometry.md](03-code-geometry.md)).
The genuine 256-bit leaf is the PUSH32 immediate round-trip in `MatDecLower.lean`:

```lean
-- MatDecLower.lean:110
theorem uInt256_wordBytesBE (w : Word) :
    uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ = w
```

proved bottom-up through the 32-digit base-256 reconstruction
[`fromBytes_wordBytesBE`](../../../LirLean/Materialise/MatDecLower.lean#L67) — this is what
turns "decode = PUSH32 carrying *the window's* value" into "carrying `w`".

### 4.4 Recompute soundness: `DefsSound`

Recompute-on-use is sound only if re-evaluating a temp's definition yields the value the IR
bound. That invariant, restricted to the recomputable temps and the currently-bound ones:

```lean
-- DefsSound.lean:209,127
def DefsSound (prog : Program) (st : IRState) : Prop :=
  ∀ (t : Tmp) (e : Expr) (w : Word),
    rematOf prog t = some e →
    ¬ NonRecomputable prog t →
    st.locals t = some w →
    some w = evalExpr st 0 e

def NonRecomputable (prog : Program) (t : Tmp) : Prop :=
  isGasDef prog t ∨ isSloadDef prog t ∨ isCallResult prog t ∨ isCreateResult prog t
```

(`st` is the V2 [`IRState`](../../../LirLean/Spec/Semantics.lean#L10) — locals + world;
`evalExpr` reads its `obs` argument only in the `.gas` arm, so pinning `obs = 0` is harmless —
[`evalExpr_obs_irrel`](../../../LirLean/Materialise/MaterialiseRuns.lean#L248).) It holds
vacuously at entry ([`defsSound_entry`](../../../LirLean/Materialise/DefsSound.lean#L222)) and
is preserved across every IR step:

```lean
-- DefsSound.lean:608
theorem defsSound_preserved {prog : Program}
    {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream} {s : Stmt}
    (hstep : EvalStmt prog st T C D s st' T' C' D')
    (hsc : StepScoped prog st s)
    (hsound : DefsSound prog st) :
    DefsSound prog st'
```

dispatching to five per-arm lemmas
([`assignPure`](../../../LirLean/Materialise/DefsSound.lean#L300),
[`assignGas`](../../../LirLean/Materialise/DefsSound.lean#L344),
[`assignSload`](../../../LirLean/Materialise/DefsSound.lean#L379),
[`sstore`](../../../LirLean/Materialise/DefsSound.lean#L424),
[`call`](../../../LirLean/Materialise/DefsSound.lean#L473),
[`create`](../../../LirLean/Materialise/DefsSound.lean#L527)). The side-condition bundle
[`StepScoped`](../../../LirLean/Materialise/DefsSound.lean#L575) packages honest
define-before-use / single-assignment / no-live-sload-across-a-write facts per statement
shape; each is syntactic and decidable on concrete programs. The gas/sload/call/create arms
are where `NonRecomputable` earns its keep: the freshly bound temp is *excluded* from the
invariant (its value lives in the slot, not in recompute), and prior bindings are stable by
scoping. Note `defsSound_preserved` is where the world-replacement hazard of CALL/CREATE is
honestly confronted: an oracle replaces the *whole world*, so no live recomputable sload may
straddle the call (the `hnoSload` conjunct).

### 4.5 The linchpin: `MatRunsC` / `materialise_runsC`

The endpoint bundle — 13 named fields, everything a materialise run delivers:

```lean
-- MatFoldChannel.lean:782
structure MatRunsC (prog : Program) (sloadChg : Tmp → ℕ) (e : Expr) (w : Word) (fr fr' : Frame) :
    Prop where
  runs       : Runs fr fr'
  stack      : fr'.exec.stack = fr.exec.stack.push w
  code       : fr'.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps : fr'.validJumps = fr.validJumps
  addr       : fr'.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod     : fr'.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts   : fr'.exec.accounts = fr.exec.accounts
  storage    : ∀ k, selfStorage fr' k = selfStorage fr k
  pc         : fr'.exec.pc = fr.exec.pc + UInt32.ofNat (matExpr (matCache prog) e).length
  gasCharge  : fr'.exec.gasAvailable
                 = subCharges fr.exec.gasAvailable (chargeExpr sloadChg (chargeCache prog sloadChg) e)
  gasToNat   : fr'.exec.gasAvailable.toNat
                 = fr.exec.gasAvailable.toNat - (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum
  memBytes   : fr'.exec.toMachineState.memory = fr.exec.toMachineState.memory
  memActive  : fr.exec.toMachineState.activeWords.toNat ≤ fr'.exec.toMachineState.activeWords.toNat
```

([`Runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L140) is exp003's small-step
reachability.) The theorem:

```lean
-- MatFoldChannel.lean:812
theorem materialise_runsC {prog : Program} (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSound prog st)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hgas : (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024) :
    ∃ fr', MatRunsC prog sloadChg e w fr fr'
```

**Claim in English:** if the code at the cursor decodes as the lowering prescribes for `e`,
the IR state is recompute-sound, scoped, storage-agreeing, and memory-realising, and the IR
evaluates `e` to `w`, then — given whole-expression gas and stack room — the bytecode run
exists and pushes exactly `w`, with all thirteen effects pinned. The recursion mirrors
`MatDecC`: `.imm/.add/.lt` reuse the one-opcode bricks
[`sim_imm`](../../../LirLean/Frame/Match.lean#L104)/[`sim_add`](../../../LirLean/Frame/Match.lean#L128)/[`sim_lt`](../../../LirLean/Frame/Match.lean#L140);
`.tmp t` resolves through `allocate prog t` — a `remat` recurses into the definiens with the
value bridged by `DefsSound`, a `slot n` runs `PUSH32 n ; MLOAD` with the readback value from
`MemRealises` and the zero-expansion gas fact
[`memoryExpansionWords?_ofNat_32_of_covered`](../../../LirLean/Materialise/MaterialiseRuns.lean#L474);
an unallocated tmp is ruled out by `hscoped`. Storage/memory ties are transported across
sub-runs by [`StorageAgree.transport`](../../../LirLean/Materialise/MaterialiseRuns.lean#L337)
and [`MemRealises.transport`](../../../LirLean/Materialise/MaterialiseRuns.lean#L399).

The two still-live realisability side-conditions:

```lean
-- MaterialiseRuns.lean:326 — the M3 storage lens tie
def StorageAgree (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ key, selfStorage fr key = st.world key
```

## 5. Spill support: `MemRealises`, the stash tail, and derived envelopes

### 5.1 `MemRealises` — the positional memory value channel

```lean
-- MaterialiseRuns.lean:366
def MemRealises (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.slot slot) → st.locals t = some v →
    (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.memory.size
    ∧ (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32
    ∧ slot + 63 < 2 ^ 64
    ∧ (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v
```

For every spilled temp the IR currently binds: the 32-byte window is allocated, *active*
(inside the memory-expansion frontier), realistically addressed, and `mload`s back the bound
value. Coverage travels with the value deliberately: `MLOAD` is not a pure read (it can grow
`activeWords` and retroactively un-zero an uncovered read), and the `≤ activeWords*32` clause
is exactly "this MLOAD expands nothing", which pins the readback's gas to
`[Gverylow, Gverylow]` — the memory analogue of the old warmth-resolver, now honest.
[`MemRealises.transport`](../../../LirLean/Materialise/MaterialiseRuns.lean#L399) carries it
across any sub-run with unchanged bytes and nondecreasing `activeWords` (the two clauses
`MatRunsC.memBytes`/`memActive` supply), via
[`mload_covered_congr`](../../../LirLean/Materialise/MaterialiseRuns.lean#L379).

### 5.2 The uniform stash tail (proved once)

Every spill def-site ends in the same two opcodes; `StashTail.lean` proves that tail once.
The endpoint bundle (named structure — the fix for the earlier anonymous-conjunct copy-pasta,
see §7):

```lean
-- MaterialiseRuns.lean:217
structure StashRuns (fr endFr : Frame) (slot : Nat) (v : Word) (pcΔ : Nat) (rest : Stack Word) :
    Prop where
  runs        : Runs fr endFr
  memory      : endFr.exec.toMachineState.memory
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).memory
  activeWords : endFr.exec.toMachineState.activeWords
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).activeWords
  pc          : endFr.exec.pc = fr.exec.pc + UInt32.ofNat pcΔ
  code        : endFr.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps  : endFr.validJumps = fr.validJumps
  addr        : endFr.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod      : endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts    : endFr.exec.accounts = fr.exec.accounts
  storage     : ∀ k, selfStorage endFr k = selfStorage fr k
  stack       : endFr.exec.stack = rest
```

The `memory`/`activeWords` fields are the **honest** memory channel: an earlier tie asserted
the *full* `toMachineState` equal to the `mstore` image, which also pins `gasAvailable` — a
field no real descending-gas run preserves; the module header records that over-constraint
and exposes only the two projections consumers actually read. The core lemma:

```lean
-- StashTail.lean:157 (hypotheses abridged: decode anchors for PUSH32/MSTORE, stack shape,
-- push gas, the MSTORE expansion witness `words'` and its two gas bounds)
theorem stash_tail_runs (fr : Frame) (slot : Nat) (v : Word) (rest : Stack Word)
    (words' : UInt64) … :
    ∃ endFr, StashRuns fr endFr slot v 34 rest
```

with three parameterisations:
[`stash_tail_runs_covered`](../../../LirLean/Materialise/StashTail.lean#L244) (already-covered
slot ⇒ zero expansion charge),
[`stash_tail_gas`](../../../LirLean/Materialise/StashTail.lean#L295) (`GAS ; PUSH32 ; MSTORE`
— the stashed value is *the* realised read `ofUInt64 (fr.gas − Gbase)`, pcΔ = 35), and
[`stash_tail_sload`](../../../LirLean/Materialise/StashTail.lean#L383)
(`matCache k ; SLOAD ; PUSH32 ; MSTORE`, composing a supplied `MatRunsC` key prefix with
[`sim_sload`](../../../LirLean/Frame/Match.lean#L153) and the tail; its one genuinely
structural extra hypothesis is `hawk : frk.activeWords = fr.activeWords` — materialising the
key expanded no memory — because `MatRunsC` only guarantees `activeWords` nondecreasing).
Consumers: [`sim_assign_gas`](../../../LirLean/Sim/SimStmt.lean#L880) /
[`sim_assign_sload`](../../../LirLean/Sim/SimStmt.lean#L1030) / the CALL-flag stash in
[`sim_call_stmt`](../../../LirLean/Sim/SimStmt.lean#L579)
([05-simulation.md](05-simulation.md)), constructed over real bytes in
[`sim_assign_gas_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L705) /
[`sim_assign_sload_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L915).

### 5.3 Gas envelopes DERIVED from a clean-halt witness

`materialise_runsC` takes its whole-expression gas bound `hgas` as a hypothesis. Supplying
such bounds per cursor is exactly the tie shape the 2026-07-02 audit found unsatisfiable in
`StmtTies` ([`docs/audit-2026-07-02.md`](../../audit-2026-07-02.md)); the replacement derives
them from **one** honest fact about the run:

```lean
-- BytecodeLayer/Hoare/CleanHalt.lean:62
def CleanHaltsNonException (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt ∧ HaltNonException halt
```

"From `fr`, the run reaches a terminal that is `.success` or `.revert` — never
`.exception`." This is the honest scope boundary of a gas-agnostic IR (a genuine OOG run is
un-modellable, and *should* be out of scope), it is a single witness at the entry cursor, it
is forward-closed along any sub-run
([`cleanHaltsNonException_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L80)), and it is
satisfiable by exactly the runs conformance is about. The extraction argument
(`CleanHaltExtract.lean` §2): a halted frame `Runs` only to itself
([`halted_runs_eq`](../../../LirLean/Materialise/CleanHaltExtract.lean#L409)); a continuing
opcode's only halt is `.exception`; so a cursor under a non-exception clean-halt **must
step**, and the step's `.next`-inversion reads off its own gas guard
([`next_of_cleanHalt_continuing`](../../../LirLean/Materialise/CleanHaltExtract.lean#L429)).
The per-opcode OOG / inversion / dichotomy bricks (`stepFrame_*_oog` / `_inv` /
`_dichotomy` for GAS/PUSH/SLOAD/ADD/LT/MLOAD/MSTORE/JUMP/JUMPDEST/JUMPI, e.g.
[`stepFrame_gas_oog`](../../../LirLean/Materialise/CleanHaltExtract.lean#L83),
[`stepFrame_mload_inv`](../../../LirLean/Materialise/CleanHaltExtract.lean#L367)) are IR-free
engine facts — reviewed with the trusted base in [01-trusted-base.md](01-trusted-base.md).

On top of those, this layer builds the lowering-shaped family:

* the per-op `next_*_of_cleanHalt` specialisations
  ([`next_push_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L535),
  [`next_sload_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L548),
  [`next_mstore_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L563),
  [`next_add_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L622),
  [`next_lt_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L635),
  [`next_mload_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L649),
  [`next_jump_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L986),
  [`next_jumpdest_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L1002),
  [`next_jumpi_taken_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L1086),
  [`next_jumpi_fallthrough_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L1103));
* the multi-step stash envelopes — for the gas stash:

```lean
-- CleanHaltExtract.lean:700 (conclusion; hypotheses are clean-halt + stack-nil + 3 decode anchors)
theorem gas_envelope_of_cleanHalt (fr : Frame) (slot : Nat) … :
    Gbase ≤ fr.exec.gasAvailable.toNat
    ∧ 3 ≤ (gasFrame fr).exec.gasAvailable.toNat
    ∧ ∃ words',
        memoryExpansionWords? (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.activeWords
          (UInt256.ofNat slot) 32 = some words'
        ∧ memExpansionChargeOf … words' ≤ … .gasAvailable.toNat
        ∧ Gverylow ≤ (… - UInt64.ofNat (memExpansionChargeOf … words')).toNat
```

  and the SLOAD twin
  [`sload_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L790)
  (keyed on the post-materialise frame `frk`, clean-halt threaded to it along the `MatRunsC`
  run; everything derived except the structural `hawk` flatness residual);
* the whole-expression **gas fold**
  [`materialise_chargeC_le_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L71),
  which recurses the same `matDecMeasure` descent, using `materialise_runsC` itself to
  produce intermediate frames and `cleanHaltsNonException_forward` to thread the witness,
  accumulating `(chargeExpr …).sum ≤ fr.gas`; and the deliverable:

```lean
-- MaterialiseCleanHalt.lean:372 (same premises as materialise_runsC with hgas REPLACED by hcs)
theorem materialise_runsC_of_cleanHalt {prog : Program} … (hcs : CleanHaltsNonException fr) … :
    ∃ fr', MatRunsC prog sloadChg e w fr fr'
      ∧ (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat
```

**Why deriving beats supplying:** a supplied envelope is a hypothesis the final theorem must
carry per cursor — dozens of runtime gas inequalities whose joint satisfiability is exactly
what went wrong before; a derived envelope costs one satisfiable, meaningful hypothesis
("the run completed cleanly") and turns every gas guard into a *consequence* of the run
having happened. The stack-room bound `hstk` is deliberately **not** derived from clean-halt
— it is a separate structural fold (block-entry stack-nil + the 1024 budget) supplied by the
sim layer.

## 6. The effect oracles and the v1 machine — live vs dead

### 6.1 The oracles (live)

The IR is call-agnostic: an external call's effect is deferred to an abstract oracle, and
lowering instantiates the oracle to *exactly* what the lowered CALL does, making the
correspondence reflexive rather than proved:

```lean
-- Frame/Call.lean:79,108
structure CallOracle where
  postStorage : CallResult → PendingCall → AccountAddress → Word → Word
  restoredGas : CallResult → PendingCall → UInt64
  successWord : CallResult → PendingCall → Word

def evmCallOracle : CallOracle where
  postStorage := fun result pd addr key =>
    (resumeAfterCall result pd).exec.accounts.find? addr |>.option 0 (·.lookupStorage key)
  restoredGas := fun result pd => (resumeAfterCall result pd).exec.gasAvailable
  successWord := fun result pd => (resumeAfterCall result pd).exec.stack.head?.getD 0
```

Every field is a projection of exp003's
[`resumeAfterCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L122), so
the headline is `rfl`-clean:

```lean
-- Frame/Match.lean:473
theorem call_reflects_lowered {callFr resumeFr : Frame}
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCallOracle.restoredGas result pd = resumeFr.exec.gasAvailable
      ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd
```

**What it pins:** given exp003's returning-call witness
[`CallReturns`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L91), the resumed
frame *is* `resumeAfterCall result pd`, and the oracle's three projections coincide with the
resumed frame's observables — post-storage through the
[`storageAt`](../../../LirLean/Frame/Match.lean#L74) lens, restored gas, and the 0/1 success
word pinned to the concrete flag
[`callSuccessFlag`](../../../LirLean/Frame/Call.lean#L120) (exp003's `x`:
0 on failure / insufficient funds / depth 1024, else 1, via
[`evmCallOracle_successWord_eq_x`](../../../LirLean/Frame/Call.lean#L128)). The CREATE twin
[`create_reflects_lowered`](../../../LirLean/Frame/Match.lean#L530) mirrors it against
[`resumeAfterCreate`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L189),
with [`CreateOracle`](../../../LirLean/Frame/Create.lean#L64) /
[`evmCreateOracle`](../../../LirLean/Frame/Create.lean#L99) /
[`createAddrOrZero`](../../../LirLean/Frame/Create.lean#L75) (the deployed-address-or-0
word); its storage side is not `rfl` — `resumeAfterCreate` is `Except`-typed (63/64
retention guard), so the oracle reads `result.accounts` directly and the headline unfolds the
guarded resume once to identify the two. **Feed-forward:** both headlines are consumed by the
realisability bridges
[`callRealises_bridge`](../../../LirLean/CallRealises.lean#L77) /
[`createRealises_bridge`](../../../LirLean/CallRealises.lean#L118), which turn the resumed
frame's observables into the world/flag conjuncts the coupled walk needs — see
[06-realisability.md](06-realisability.md). Also live in `Match.lean`: the `Runs`-node
wrappers [`sim_call`](../../../LirLean/Frame/Match.lean#L433) /
[`sim_create`](../../../LirLean/Frame/Match.lean#L496), the halt bricks
[`halt_stop`](../../../LirLean/Frame/Match.lean#L322) /
[`stepFrame_return_word`](../../../LirLean/Frame/Match.lean#L357) (+
[`returnWordPost`](../../../LirLean/Frame/Match.lean#L341)), the boundary discharges
[`lower_preserves_discharge`](../../../LirLean/Frame/Match.lean#L573) /
[`lower_preserves_stop`](../../../LirLean/Frame/Match.lean#L585) /
[`lower_preserves_ret`](../../../LirLean/Frame/Match.lean#L600) (consumed by the terminator
sims, [05-simulation.md](05-simulation.md)), the whole `sim_*` opcode-brick family
(§4.5, §5.2), and [`sim_sstore`](../../../LirLean/Frame/Match.lean#L219) with its
value-agnostic zero-write read-backs
[`sstoreFrame_storage_self'`](../../../LirLean/Frame/Match.lean#L167) resting on
`Frame/StorageErase.lean`.

### 6.2 The v1 machine (dead) — verified

The reviewer's suspicion **confirms by grep** (definition sites excluded, docstring mentions
only):

* `Frame/SmallStep.lean` (deleted) — the v1
  `IRState` (with its
  `callResult`/`createResult` slots), v1
  `evalExpr`, v1 `IRHalt`, `bindCallResult`, `bindCreateResult`, `setLocal` /
  `setStorage`: **zero theorem consumers**
  anywhere in `LirLean/`. Despite its name the file contains no step relation.
* `IRState.applyCall` and `IRState.applyCreate`: removed after confirming zero consumers.
* The `Match` simulation invariant (M1/M2/M3/M5): removed after confirming zero
  consumers. The live coupling is V2's `Corr` in the realisability layer.

The live design took the other fork: the V2 semantics
([`Spec/Semantics.lean`](../../../LirLean/Spec/Semantics.lean#L48) `EvalStmt`) binds call and
create results by **popping an oracle stream** (`CallStream`/`CreateStream`) directly into
`setLocal`, and the lowered flag-on-stack is bridged by the reflexivity headlines + the
CALL-flag stash — the `callResult`-slot indirection was never needed. The files' extensive
docstrings still present the slot design as the resolution of the recompute problem, which
now misdescribes the architecture. **Recommendation:** delete the v1 state (`SmallStep.lean`
minus nothing worth keeping), `applyCall`/`applyCreate`, and the `Match` structure; keep the
oracles, the lens defs, and all `sim_*`/halt/discharge bricks. Per the repo's own
deep-read-before-touching rule this was traced caller-by-caller, not inferred from imports.

## 7. Results taxonomy

**Headlines of this layer** (each feeds the flagships through
[05-simulation.md](05-simulation.md)/[06-realisability.md](06-realisability.md)):
[`materialise_runsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L812),
[`materialise_runsC_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372),
[`call_reflects_lowered`](../../../LirLean/Frame/Match.lean#L473) /
[`create_reflects_lowered`](../../../LirLean/Frame/Match.lean#L530),
[`defsSound_preserved`](../../../LirLean/Materialise/DefsSound.lean#L608),
[`stash_tail_runs`](../../../LirLean/Materialise/StashTail.lean#L157) family.

**Bricks:** the fold fixpoints and lockstep (§4.2), `MatDecC` + segment bridges (§4.3), the
`MemRealises`/`StorageAgree` transports, the coverage arithmetic
([`M_32_eq_self_of_covered`](../../../LirLean/Materialise/MaterialiseRuns.lean#L423),
[`memoryExpansionWords?_ofNat_32_of_covered`](../../../LirLean/Materialise/MaterialiseRuns.lean#L474)),
the PUSH32 round-trip, the `next_*_of_cleanHalt` family, the frame-accessor `rfl` reductions
(≈40 `@[simp]` lemmas in `MaterialiseRuns.lean`/`StashTail.lean`/`Match.lean`), and
`StorageErase`'s RBMap facts. Proof methods throughout are honest and boring: def-env
induction, `stepFrame`-unfold + `charge` if-splitting, `omega` arithmetic — nothing
trust-reducing.

**Examples:** none in scope (this layer is fully general; concrete programs live elsewhere).

**Retired-by-design (kept deliberately):**
[`GasRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L318) /
[`SloadRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L297) — no headline
depends on them; they exist as documented subjects of the positional discharges in
`Drive/SelfPresent.lean`. Not a risk; keep (the docstrings are the institutional memory of
the vacuity lesson).

**Smells, each with the does-a-headline-depend-on-it call:**

* **The former ~10-conjunct anonymous stash bundle does *not* verify as a current smell** —
  it was fixed: [`StashRuns`](../../../LirLean/Materialise/MaterialiseRuns.lean#L217) and
  [`MatRunsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L782) are named structures
  ("Named so a clause reorder does not ripple across the destructurings"). Residual, milder:
  the `gas_envelope_of_cleanHalt` / `sload_envelope_of_cleanHalt` conclusions are still
  anonymous `∧`-chains with a nested `∃ words'` (5 conjuncts), and `StashTail.lean`
  internally destructures `StashRuns` positionally (`refine ⟨endFr, …, ?_, ?_, …⟩` with 11
  holes). Headlines depend on these, but the exposure is reorder-brittleness, not soundness.
  Worth a named `MstoreEnvelope` structure if the envelope family grows.
* **Copy-pasta between the value channel and its gas fold**: the `.add`/`.lt` arms of
  [`materialise_runsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L1080) and
  [`materialise_chargeC_le_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L194)
  are ~100-line near-duplicates of each other (and `.add` vs `.lt` within each). A headline
  sits on top, so a `binop`-generic helper would cut real maintenance risk. The gas fold also
  invokes `materialise_runsC` per operand *in addition to* recursing itself — double
  traversal; harmless for soundness, mildly wasteful for elaboration.
* **`set_option maxRecDepth 8192`** in
  [`MatDecLower.lean#L32`](../../../LirLean/Materialise/MatDecLower.lean#L32), serving the
  32-limb brute-force in
  [`fromBytes_wordBytesBE`](../../../LirLean/Materialise/MatDecLower.lean#L67) (32 explicit
  `show … from rfl` rewrites + one big `omega`). Headlines depend on it transitively via
  `uInt256_wordBytesBE`. It is a stable arithmetic leaf, not a reduction blow-up on a model;
  acceptable, but a `List.range`-generic reconstruction lemma would remove both the option
  and the 40-line rewrite block. No `maxHeartbeats` anywhere in scope.
* **Dead v1 machine** (§6.2): no headline depends on any of it — pure noise, plus actively
  misleading docstrings. Delete.

## 8. Source-vs-doc discrepancies found

1. **[`docs/codebase-map-2026-07-06.md`](../../codebase-map-2026-07-06.md) §L5a is stale on
   every named symbol of this layer.** It cites `MatDec` (MaterialiseRuns.lean:237),
   `MatRuns` (:336), `materialise_runs` (:771), `MemRealises` (:605), `chargeOf`
   (MaterialiseGas.lean:73), `materialise_runs_of_cleanHalt` (MaterialiseCleanHalt.lean:377).
   None exist: P9 deleted the fuel stack; `MaterialiseRuns.lean` is 506 lines;
   the live successors are `MatDecC`/`MatRunsC`/`materialise_runsC` in `MatFoldChannel.lean`
   and `chargeExpr`/`chargeCache`; `MemRealises` is at
   [`MaterialiseRuns.lean#L366`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366);
   the clean-halt twin is at
   [`MaterialiseCleanHalt.lean#L372`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372).
   The map's *shape* description remains accurate. (The same staleness affects
   [`docs/uniform-spill-alloc-plan.md`](../../uniform-spill-alloc-plan.md)'s
   `MaterialiseRuns.lean:550/:539` pointers, though that doc carries an UPDATE banner.)
2. **The refutation record moved.** Reviewers pointed at `MaterialiseRuns.lean:496-560`; the
   file ends at 506. The record now lives in the RETIRED docstrings at
   [`:280-321`](../../../LirLean/Materialise/MaterialiseRuns.lean#L280); the machine-checked
   unsatisfiability witnesses were deleted with `HonestGasTie.lean` and survive as prose
   in [`RealisabilitySpec.lean`'s header](../../../LirLean/Realisability/RealisabilitySpec.lean#L19)
   and [`docs/gas-decision.md`](../../gas-decision.md) (which says so explicitly).
3. **`Frame/*` docstrings overstate the v1 slot design's role** (§6.2): `SmallStep.lean`,
   `Call.lean`, and `Create.lean` present `callResult`/`bindCallResult` as *the* resolution of
   the non-recomputable-flag problem, but nothing consumes them; the live resolution is the
   V2 stream pop + the spill stash. [`docs/design/spilling-encoding.md`](../../design/spilling-encoding.md)
   also still cites a `Frame/SmallStep.lean:93` `.slot` arm that no longer exists (its P9
   banner covers this).

## 9. Recommendations

1. Delete the dead v1 machine surface (§6.2) and rewrite the three `Frame/*` module
   docstrings around the stream-pop design; fold what remains of `Frame/` into clearer homes
   (the oracles + reflexivity headlines are L5a; `Match.lean`'s live content is opcode bricks
   + lenses, not an invariant module).
2. Regenerate the §L5a block of the codebase map against the fold-era names (item 1 of §8).
3. Factor the `.add`/`.lt` duplication in `materialise_runsC` and its gas fold into one
   binop-generic lemma; consider a named envelope structure for the `*_envelope_of_cleanHalt`
   conclusions.
4. Keep the retired universals and their docstrings — they are the cheapest vaccine against
   reintroducing a free-`∀` tie (the failure mode `docs/gas-decision.md` warns recurs).
