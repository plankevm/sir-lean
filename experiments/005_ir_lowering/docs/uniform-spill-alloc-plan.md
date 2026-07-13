# Uniform spill/remat lowering — design + migration plan

*Status: design accepted (Eduardo, 2026-06-28); migration not yet started. Supersedes the
ad-hoc per-construct gas/call/sload handling in `Lowering.lean` and the vacuous gas/sload
universals in `MaterialiseRuns.lean`.*

> **UPDATE (2026-07-03):** the migration has since been executed (the gas/sload universals are
> retired in the tree — see the `SimStmt.lean`/`MaterialiseRuns.lean` headers), and
> `HonestGasTie.lean` — the regression-witness file referenced below — was **deleted** in
> Phase 2 along with the rest of the gas-law apparatus (Mono/Oracle/HonestGasTie). Plan of
> record is `target-architecture-2026-07-02.md` + `execution-plan-2026-07-02.md`.

## 0. Why this exists (the finding that triggered it)

The conformance spine carried a **vacuous** gas/sload realisability tie:
`Lir.GasRealises obs fr := ∀ g (same self-address), obs = ofUInt64 (g.gas − Gbase)`
(`MaterialiseRuns.lean:550`), and the `SloadRealises` twin (`:539`). The `∀`-over-all-frames
shape forces gas (and sload warmth) to be **constant** across the run, which a real
descending-gas run never is — so the headline hypotheses (`hgasr`/`hsload`) are unsatisfiable
and `lower_conforms` is **vacuous on the gas/sload axes**. (Proven: `HonestGasTie.lean`,
`gasRealises_universal_unsatisfiable`.)

Tracing *why* the spine ever needed a constant revealed the real cause: the lowering uses
**recompute-on-use** (re-emit a tmp's defining expression at each use). That is sound only when
re-executing the code reproduces the same observable result. It does **not** for two kinds of
value:

- **`GAS`** — re-emitting `GAS` returns a *different* word each time (gas descends).
- **call results** — re-emitting a `CALL` re-does the call.

For these, recompute is unsound, so the design marked them `NonRecomputable` and tried to paper
over the resulting one-IR-read-vs-many-bytecode-reads mismatch with the constant universal.
That is the vacuity.

There is a third value that recompute handles *correctly but expensively*:

- **`SLOAD`** — re-reading key `k` gives the same value while no write intervenes (value-stable,
  guarded today by `DefsSound` scoping), BUT re-emitting `SLOAD` re-charges **100 (warm) / 2100
  (cold)** every reuse, versus **3** for an `MLOAD` of a cached copy. Since gas is the entire
  optimization target for EVM, **no real backend ever recomputes `SLOAD`** — it caches it.
  Caching `SLOAD` is also *cleaner*: a cached copy is the value frozen at read time, so (a) the
  "can't reuse across a write" scoping side-condition **disappears**, and (b) the per-tmp warmth
  cost stops being smeared across reuses (one IR read = one `SLOAD` opcode).

## 1. The unifying realization

**`GAS`, the call result, and `SLOAD` are the same operation: compute an effectful/dynamic value
once, stash it, reuse the stash.** Only genuinely cheap, pure, stable values (constants,
arithmetic over other tmps) should be rematerialized. So the lowering's job per value is a single
*policy* decision — **remat or spill** — and the *mechanism* is uniform.

This is the standard compiler tradeoff (rematerialization vs. spilling). The IR is genuinely
**higher-level than bytecode**: it has named, reusable value-variables (tmps) and treats
`GAS`/`SLOAD`/`CALL` as pure-looking value expressions. Bytecode has neither — only a stack,
memory, and re-runnable opcodes. The lowering bridges that gap; spilling is just the spill half of
the bridge, applied to the values that aren't rematerializable.

## 2. The clean shape of `lower`

```
lower    : Program → ByteArray
lower    = encode ∘ emit (allocate prog) prog

allocate : Program → Alloc            -- POLICY    (which tmps spill, to which slots)
emit     : Alloc → Program → CFGAsm   -- MECHANISM (uniform, alloc-driven; no per-construct cases)
encode   : CFGAsm → ByteArray         -- BACKEND   (offset table, jumpdests, byte encoding — exists)
```

### 2.1 Policy: a per-tmp location

```lean
inductive Loc
  | remat (e : Expr)   -- recompute the defining expression at each use
  | slot  (n : Nat)    -- value lives in memory slot n; load on use
abbrev Alloc := Tmp → Loc
```

`allocate` is one *replaceable* policy among many (see §5). The **default** policy:

- `.slot` for every `NonRecomputable` tmp (gas, call result) — *correctness floor*; and for
  every `SLOAD`-defined tmp — *gas-optimal default* (cache loads);
- `.remat` for `.imm` and pure arithmetic (`.add`/`.lt`/`.tmp`-chains).

### 2.2 Mechanism: one rule for uses, one for defs

```lean
-- USE site
materialise (a : Alloc) : Expr → CFGAsm
  | .imm w   => [PUSH w]
  | .add x y => materialise a x ++ materialise a y ++ [ADD]      -- pure: recurse
  | .lt  x y => materialise a x ++ materialise a y ++ [LT]
  | .tmp t   => match a t with
                | .remat e => materialise a e                    -- rematerialize
                | .slot n  => [PUSH n, MLOAD]                     -- reuse the stash
  | .sload k => materialise a k ++ [SLOAD]                       -- only reached at a def-site stash
  | .gas     => [GAS]                                            -- only reached at a def-site stash

-- DEF site
emitStmt (a : Alloc) : Stmt → CFGAsm
  | .assign t e => match a t with
                   | .remat _ => []                              -- nothing; recomputed at uses
                   | .slot n  => materialise a e ++ [PUSH n, MSTORE]   -- compute ONCE, stash
  | .sstore k v => materialise a v ++ materialise a k ++ [SSTORE]
  | .call cs    => emitCall cs ++ stashResult a cs               -- the same spill tail
```

`GAS`, the call result, and `SLOAD` are **not special** in `emit` — they are ordinary `.slot`
tmps whose defining expression happens to be `.gas` / a call / `.sload k`. The Route-B
`MSTORE`/`MLOAD` that today lives only in `emitStmt .call` becomes the generic def/use rule.

### 2.3 We are not building from scratch — the seam already exists

In the current `Lowering.lean`:
- `materialiseExpr` already treats **`.callResult slot` as a generic `PUSH slot; MLOAD`** (line 104).
- `defsOf` already records a call result's "definition" **as** `.callResult (slotOf t)` (line 187).
- `emitStmt .call` already emits the `... CALL; PUSH slot; MSTORE` stash tail (line 152).
- `emitStmt .assign` emits nothing (line 141) — the remat path.

So `.callResult slot` *is already* the spill-load. The refactor is: rename `.callResult` →
`.slot` (a generic spill-load), generalize `defs : Tmp → Option Expr` to `Alloc` (make the
remat/slot distinction explicit), route gas/sload defs to `.slot`, and emit the stash tail at
their `assign` def-sites. Mostly generalization + renaming of **already-proven** machinery.

## 3. Why this is the clean *proof* architecture

The conformance proof factors along the same composition, and the value channel **unifies**:

- **Every `.slot` tmp** (gas, call, sload, any spilled value) is tied by *one* predicate — the
  generalized **`MemRealises`**: "slot `n` holds the value." One lemma, three clients.
  - gas tie: the single `GAS` opcode's output = the supplied oracle value (**honest positional
    tie**, one read — no constancy, no `∀`-over-frames). Replaces the vacuous universal.
  - sload value tie: the single `SLOAD`'s output, **frozen** in the slot (reuse via `MLOAD` can't
    be corrupted by a later `SSTORE` — the across-write scoping side-condition is **deleted**).
  - call tie: the existing call-oracle tie (`resumeAfterCall`).
- **Every `.remat` tmp** (imm, arithmetic) is tied by recompute-soundness (`DefsSound`) — and
  since remat now applies *only* to pure exprs, no storage-read hazard remains on that path.

The whole thing is proved **parameterized over any sound allocation**:

```lean
def SoundAlloc (prog : Program) (a : Alloc) : Prop :=
  ∀ t, NonRecomputable prog t → ∃ n, a t = .slot n     -- gas/call MUST be slots
```

(`SLOAD` and pure tmps *may* be slots — the policy's choice, above the floor.) The current
behavior is the special case "pure ⇒ remat, call ⇒ slot", so the refactor **strictly subsumes**
what is green today, and the gas vacuity is gone *by construction* (gas is an in-scope `.slot`
tmp with the positional tie).

## 4. The headline payoff

`lower_conforms : ∀ (a : Alloc), SoundAlloc prog a → conforms (encode (emit a prog)) prog`.
Once conformance is `∀ SoundAlloc`, **every future gas-optimizing pass** — slot packing,
dead-store elimination, remat-vs-spill tuning — only has to produce a `SoundAlloc` to inherit
correctness for free. The optimizer chases gas; the proof does not move.

## 5. Modular / composable / **replaceable** passes (Eduardo's requirement)

`allocate` is not one fixed function — it is a **pipeline of replaceable passes** producing an
`Alloc`, so a specific contract can turn passes on/off / swap policies and still inherit
conformance (any `SoundAlloc` is correct). Default pipeline: `floor` (gas/call ⇒ slot) → `cacheSload`
(sload ⇒ slot) → `rematPure` (imm/arith ⇒ remat). A contract could, e.g., drop `cacheSload` or add
a slot-packing pass; as long as the result satisfies `SoundAlloc`, `lower_conforms` applies
unchanged. The `SoundAlloc`-parameterized headline is precisely what makes passes replaceable.

## 6. Migration plan (phased; green + axiom-clean at every checkpoint)

Discipline: no `sorry`/`axiom`/`native_decide`; `lake build` green and axioms exactly
`[propext, Classical.choice, Quot.sound]` at each committed checkpoint; honest interim over any
shortcut; commit only green states.

- **Phase A — structural reskin, NO behavior change (theorem-preserving). ✅ DONE (2026-06-28).**
  Introduce `Loc`/`Alloc`; factor `lower` into `encode ∘ emit (allocate prog) prog` such that the
  emitted bytes are the old `lower`'s (bridged by `allocate_toDefs`/`emit_allocate_eq_flatBytes`;
  `lower_eq_flatBytes` is now a one-rw lemma rather than `rfl`, so downstream proofs are untouched).
  `allocate` reproduces `defsOf` exactly (pure ⇒ `remat`, call result ⇒ `slot`). Renamed
  `Expr.callResult` → `Expr.slot` (generic spill-load) with a full sweep. Build green (1159 jobs),
  all headline theorems unchanged + axiom-clean. *Lowest risk; sets the structure.*
  - **Deviation:** `Alloc := Tmp → Option Loc` (partial), not the total `Tmp → Loc` of §2.1 —
    so the `defsOf … = none` (undefined-tmp) case round-trips exactly and no downstream theorem
    changes. The total shape is adoptable once `WellFormed` rules out undefined tmps (a later phase).
  - **Reused, not removed:** `defsOf`/`materialiseExpr`/`emitStmt`/`emitTerm`/`emitBlockBody`/
    `offsetTable` are the *mechanism* `emit` drives (via `Alloc.toDefs`) and remain the canonical
    object every downstream layout/sim proof reasons about; only the old monolithic `lower` body is
    gone. Generalising those internals to consult `Alloc` directly is Phase B/C/D work.

- **Phase B — gas through the spill (kills the gas vacuity). ✅ DONE (2026-06-28).**
  `defsOf` maps a gas assign to `Expr.slot (slotOf t)`; `emitStmt .assign` is **alloc-native** —
  a slot-allocated tmp's `assign` stashes `materialise e ++ PUSH n ++ MSTORE` (for gas, `[GAS] ++
  PUSH ++ MSTORE`), rematerialised tmps still emit nothing. Uses load from the slot via the existing
  `Expr.slot` ⇒ `PUSH;MLOAD` path. `MemRealises` already covers any `defsOf t = .slot` tmp, so it
  now carries the gas value too; the new `sim_assign_gas` (mirroring the call-result Route-B tail)
  runs the stash and re-establishes `Corr`, with the gas slot holding the **consumed read `ob`** —
  the honest **positional one-read** value tie (one frame, one read), supplied as the stash
  hypothesis. The vacuous universal `Lir.GasRealises`/`gasReal`/`hgasr` is **removed from the entire
  conformance spine** (`Corr`, `materialise_runs` — its `.gas` arm is now `absurd rfl hne` via
  `e ≠ .gas`, unreachable since gas is never materialised — every `sim_*`, `CallRealises`,
  `StmtTies`, `entry_corr`, and all headlines). `WellFormed` is relaxed to restrict only call
  results, so multi-use gas is in scope: `guardIR` (reads its first gas value twice) flips from
  `¬ WellFormed` to **`WellFormed`** by `decide`. `HonestGasTie.lean` reframed as the regression
  record (vacuity-of-universal + satisfiability-of-positional witnesses kept), plus
  `spilled_gas_value_tie_realisable` (the per-def-site slot value = the real `GAS` output).
  - **Deviation / honest scope (SUPERSEDED by P1, below):** `sim_assign_gas` took the
    GAS;PUSH;MSTORE stash run + its frame pins as a **supplied hypothesis** (`hstash`), exactly as
    `sim_call_stmt` takes the call-result MSTORE tail (`htail`).

- **P1 — the uniform stash-tail forward lemma + gas-`hstash` discharge. ✅ DONE (2026-06-28).**
  The keystone of the discharge effort. `LirLean/StashTail.lean` proves the `PUSH32 slot ; MSTORE`
  stash tail **once**, parameterized over the stashed value `v` and residual stack `rest`, as a
  forward `Runs` lemma over `lower prog`:
  - **`stash_tail_runs`** (core): `PUSH32 slot ; MSTORE` from `stack = v :: rest` with the slot
    addressable + the honest runtime gas facts (expansion witness + the two `sim_mstore` gas
    bounds) → `Runs fr endFr`, the memory channel, pc + 34, frame pins, `stack = rest`.
  - **`stash_tail_gas`** (GAS-prefix): composes one `GAS` step, stashing the realised output
    `ofUInt64 (fr.gas − Gbase) = gasReadOf (gasFrame fr)` — the honest positional one-read value
    (no `∀`-frames, no constancy). pc + 35.
  - **`stash_tail_runs_covered`**: covered-slot specialization (zero expansion charge) — Phase C's
    cached-SLOAD reuse. Reusable for gas / call / sload via the `v`/`rest`/prefix parameters.
  - **Finding (fixed):** the old `hstash`/`htail` ties asserted `endFr.exec.toMachineState =
    fr….mstore …`. Because `gasAvailable` is a `MachineState` field, that equality also pins gas —
    which a real descending-gas run never preserves, so the ties were **over-constrained
    (effectively unsatisfiable)**. The lemmas (and the reshaped `sim_assign_gas`/`sim_call_stmt`
    ties) expose only the **honest** content `MemRealises`/`Corr` actually read: the `.memory`
    bytes + `.activeWords` of `fr….mstore (ofNat slot) v` (gas-independent, true on a real run).
  - **Discharge:** `sim_assign_gas_lowered` (`LirLean/LowerDecode.lean`) **constructs** the gas
    stash run internally — decode anchors from the byte layout (A2 `decode_at_offset_nonpush` for
    GAS/MSTORE, `imm_leaf_decode` for PUSH32) + `stash_tail_gas` — so the spine's gas arm
    (`StmtTies`/`simStmtStep_block`/`LowerConforms`) **no longer supplies the opaque `hstash`
    run**. The §7 gas tie now supplies only the honest residual: the positional value tie `ob =
    ofUInt64 (fr.gas − Gbase)`, addressability + pc-bound, and the `sim_gas`/`sim_mstore` runtime
    gas + `memoryExpansionWords?` witness — all genuinely satisfiable, none vacuous.
  - **Call arm:** `sim_call_stmt`'s `htail` is reshaped to the same honest memory+activeWords
    form (over-constraint removed); the call tail's `PUSH32 slot ; MSTORE` part is dischargeable by
    the *same* `stash_tail_runs` (`v = flag`, `rest = []`), but the CALL trace itself stays
    supplied (the `CallReturns` node is genuine §7), so the call arm keeps its `htail` (now
    honest/satisfiable). The full call-tail `_lowered` constructor is left for the spine phase.
  - green (1160 jobs); `stash_tail_runs`/`_covered`/`_gas`, `sim_assign_gas_lowered`,
    `sim_call_stmt`, and all four headlines axiom-clean `[propext, Classical.choice, Quot.sound]`.

- **Phase C — sload through the spill (kills the scoping wart + cost smear). ✅ DONE.**
  Default `allocate` maps sload-tmps to `.slot`; stash at def (`materialise k ++ SLOAD ++ PUSH slot
  ++ MSTORE`), load at use (MLOAD). Delete the across-write `DefsSound` scoping side-condition on
  the cached path. Replace `Lir.SloadRealises` (the universal) with the positional warmth-cost tie
  (`SloadLogAligned` infra). Remove `hsload`.
  - **Satisfiability re-audit BANKED (green, axiom-clean) — `HonestGasTie.lean`.** Before
    migrating the spine, the gas precedent's regression witnesses are mirrored for SLOAD: (1)
    `sloadRealises_universal_unsatisfiable` — the `Lir.SloadRealises` universal is
    **machine-checked unsatisfiable** under a cold-then-warm same-key re-read (the cost flips
    `Gcoldsload 2100 → Gwarmaccess 100`, forcing one resolver to equal both); (2)
    `new_sloadLogAligned_two_read_satisfiable` — the honest positional `SloadLogAligned` admits
    exactly that distinct list `[2100, 100]`; (3) `sload_tie_vacuity_resolved` — the one-statement
    contrast (new form satisfied, old form refuted), the SLOAD twin of `gas_tie_vacuity_resolved`.
    These are the non-vacuity evidence + the satisfiability re-audit the design owes; no
    full-`toMachineState` pin and no `∀`-over-frames in the positional form.
  - **Step 1 BANKED (green, axiom-clean) — WorkedCall decoupled from the headline cone.** The
    prerequisite layering-inversion fix landed (commit `exp005 Step 1`): the WorkedCall-coupled
    worked examples (`wcV2Oracle`, `wc_call_parity_v2`; `wcRunLog`, `realisedCall_wcRunLog`,
    `wc_observe_conforms`) moved out of `CallRealises.lean` + `RunLog.lean` into the new leaf
    `WorkedCallParity.lean`. **Verified via transitive-import cone analysis:** none of the four
    headlines (`lower_conforms`, `lower_conforms_acyclic_cfg`, `lower_conforms_cyclic`,
    `lower_conforms_cyclic'`) now transitively import `LirLean.WorkedCall` *or*
    `LirLean.WorkedCallParity`. WorkedCall is a leaf example; `RunLog` stays in the cone but
    carries only general recorder defs. So the earlier parenthetical "both in the headline import
    chain via CallRealises" is **no longer true** — WorkedCall/Decode are now leaves.
  - **Step 2 mechanism VERIFIED CONE-COMPATIBLE (not yet committed — leaves break).** Flipping
    `defsOf`'s `assign t (.sload k)` arm to `Expr.slot (slotOf t)` (one-line mirror of the gas arm;
    `emitStmt .assign`'s existing alloc-native `.slot` arm then stashes `materialise k ++ [SLOAD] ++
    PUSH slot ++ MSTORE` — already byte-correct) was applied and the **entire headline cone built
    green** (`LowerConforms`, `Acyclic`, `DriveSim` and all their dependencies, incl.
    `DecodeAnchors`/`DecodeLower`/`MatDecLower`/`JumpValid`/`MaterialiseRuns`/`SimStmt`/`SimTerm`).
    The general `materialiseExpr`/`MatDec`/`chargeOf`/`Corr` machinery absorbs the sload→slot flip
    exactly as it already absorbs gas→slot — the cone does **not** depend on sload being recomputed.
    The breakage is confined to **three byte-layout leaf examples** whose concrete `workedCall`
    offsets shift (the def-site stash relocates the SLOAD bytes before the CALL):
    `LirLean/Decode.lean` (34 `rfl` decode anchors), `LirLean/WorkedCall.lean` (36, the 1752-line
    `Runs` proof), and `LirLean/WorkedCallParity.lean` (36, downstream). None feeds a headline.
  - **Remaining Step 2 work (the actual goal).** Two independent large pieces gate a green commit:
    (a) **leaves** — re-derive the shifted `workedCall` offsets in `Decode.lean` + `WorkedCall.lean`
    (the dominant cost is `WorkedCall`'s offset-coupled `Runs` proof, not the `rfl` anchors), or
    excise them from the default target as superseded worked examples; (b) **the universal removal
    proper** — drop `Corr.sloadReal : SloadRealises …` and re-wire `Corr` onto the per-cursor
    positional `realisedSload log` warmth-cost tie (`SloadLogAligned`/`alignedSload_read_eq_obs`/
    `sloadRealises_charge_of_witness`, all already proven in `TieDischarge.lean`). (b) touches ~97
    references across 10 spine files (`SimStmt`/`SimStmts`/`SimTerm`/`MaterialiseRuns`/`DriveSim`/
    `LowerConforms`/`Acyclic`/`MatDecLower`/`MaterialiseGas`/`RunLog`) plus `NonRecomputable`/
    `DefsSound` gaining `isSloadDef`, and a new `sim_assign_sload` dispatch branch (the
    `sim_assign_gas` twin: `materialise k` via `materialise_runs` → `sim_sload` → `stash_tail_runs_
    covered`). The mechanism (a-prerequisite) is held back un-committed because, on its own, it
    delivers no headline benefit (the headlines still carry `sloadChg` + the universal until (b)
    lands) while breaking three worked examples — so the tree is kept at the green Step-1 checkpoint.
  - **Step 3 LANDED (green, axiom-clean) — the `SloadRealises` universal is GONE from `Corr`/the
    spine.** Both (a) and (b) are done:
    - **(b) the universal removal.** `Corr.sloadReal : SloadRealises` is **deleted**; `materialise_runs`
      now takes `(∀ k, e ≠ .sload k)` (the `.sload` arm is unreachable — sload is spilled, uses go via
      `.slot`/MLOAD, preserved across the `.tmp` recursion by `defsOf_ne_sload`), exactly mirroring the
      Phase-B gas `e ≠ .gas`. The SLOAD **value** tie is now `MemRealises` (the slot holds the frozen
      `st.world key`); the SLOAD **warmth-cost** tie is the single cold/warm def-site read (the
      positional `realisedSload`/`SloadLogAligned` selection via `sloadRealises_charge_of_witness`, NOT
      the single-resolver universal). `sloadChg` STAYS as the charge resolver in
      `chargeOf`/`MatDec`/`MatRuns` (only the universal it fed is gone). `hsload` removed from
      `entry_corr`/`lower_conforms`(`_wf`/`_acyclic`*/`_cyclic`*)/`corr_at_jumpdest_landing`/`jump_to_block`/
      the DriveSim jump/branch bundles. `NonRecomputable` gains `isSloadDef`; `DefsSound` gains
      `defsSound_preserved_assignSload` and a split `StepScoped .assign` arm. New
      `sim_assign_sload` dispatch arm (the `sim_assign_gas` twin: the def-site stash run + frame pins
      are the honest supplied tie — `stash_tail_runs_covered` is how a concrete caller builds the
      `endFr` witness — and the value `w = st.world key` is stashed at `slotOf t`, tied by
      `MemRealises`). The across-write `DefsSound` sload hazard is gone on the spilled path (a frozen
      MLOAD copy can't be corrupted by a later SSTORE). Every introduced sload tie is satisfiable by a
      real run — `.memory`+`.activeWords` shape (NEVER full `.toMachineState`, which pins gas), and no
      `∀`-over-frames; confirmed by the cold-then-warm `sload_tie_vacuity_resolved` witness.
    - **(a) leaves.** `LirLean/Decode.lean`, `LirLean/WorkedCall.lean`, `LirLean/WorkedCallParity.lean`
      are SUPERSEDED worked examples (byte layout stale under the sload spill) and EXCLUDED from the
      default build target: the lib switched from the submodule glob to `roots := [`LirLean]`, and the
      three leaf imports were removed from `LirLean.lean` (with superseded notes). Excluding them
      weakens NO theorem — none is in a headline cone. Re-derivation deferred.
    - **Build: green (1157 jobs).** The four headlines (`lower_conforms`, `lower_conforms_acyclic_cfg`,
      `lower_conforms_cyclic`, `lower_conforms_cyclic'`), `sim_assign_sload`, `Corr`, and the SLOAD
      regression witnesses (`sloadRealises_universal_unsatisfiable`,
      `new_sloadLogAligned_two_read_satisfiable`, `sload_tie_vacuity_resolved`, kept in the cone via an
      explicit `LirLean.HonestGasTie` import) are all axiom-clean `[propext, Classical.choice,
      Quot.sound]`. No `sorry`/`axiom`/`native_decide`/`admit`.

- **Phase D — `∀ SoundAlloc` headline + replaceable-pass pipeline + cleanup.**
  Generalize `Corr`/`sim_*`/`materialise_runs`/`DriveSim`/`LowerConforms` to quantify over any
  `SoundAlloc a` (current behavior = one instance). Land the default `allocate` pipeline (§5).
  Sweep dead code (the old per-construct special cases, retired universals, stale comments). Mark
  v1/v2 gas/sload docs superseded; update `ir-design-v3.md` cross-refs.
  > **Note (2026-07-02, gas-decision.md + remediation-plan-2026-07-02.md).** Per `docs/gas-decision.md`
  > gas is now a **log-fed exact-equality oracle** (like an external call), and the gas-monotonicity
  > law is dropped. The spill/remat reskin (Phases A–C, DONE) *did* kill the vacuous gas/sload
  > universals — but the remaining honesty gap is no longer a "vacuous universal" problem: it is the
  > **realisability closure** (build the per-cursor `StmtTies`/`TermTies` ties for `lower prog` from
  > `runWithLog` and instantiate the headline end-to-end), tracked as **Phase 3 of the remediation
  > plan**. Treat that closure — not further universal-removal — as the successor of this Phase D
  > cleanup for the gas/sload axes.

Each phase runs the established loop: an implementation subagent → an independent review subagent →
self-review against the diff, before moving to the next.

## 7. Open questions / notes

> **Note (2026-07-02).** Per `docs/gas-decision.md`, gas is now a **log-fed exact-equality oracle**
> (the recorder captures the machine `GAS` output, feeds it into the IR oracle, and equality is
> proved — handled exactly like an external call); the gas-monotonicity law is dropped. This plan's
> Phases A–C already removed the vacuous gas/sload *universals*; the remaining work on those axes is
> the **realisability closure** (Phase 3 of `docs/remediation-plan-2026-07-02.md`), which supersedes
> this doc's original "vacuous-universal removal" framing.

- **Default policy** confirmed: spill-the-effectful (gas/call/sload spilled, arithmetic
  rematerialized) — exercises both remat and spill paths from day one.
- Slot allocation: `slotOf t = t.id*32` (disjoint per-tmp) suffices for soundness; a packing pass
  is a later, conformance-free optimization.
- Multi-use gas is now *free* (it is just a `.slot` tmp reused via `MLOAD`); the `WellFormed`
  single-use restriction on gas can be relaxed/retired once Phase B lands.
- Stack discipline (empty stack at statement boundaries, `Corr.M5`) is preserved: stash/load
  leave the stack empty between statements, same as remat.
```
