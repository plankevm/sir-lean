# Uniform spill/remat lowering — design + migration plan

*Status: design accepted (Eduardo, 2026-06-28); migration not yet started. Supersedes the
ad-hoc per-construct gas/call/sload handling in `Lowering.lean` and the vacuous gas/sload
universals in `MaterialiseRuns.lean`.*

## 0. Why this exists (the finding that triggered it)

The conformance spine carried a **vacuous** gas/sload realisability tie:
`Lir.GasRealises obs fr := ∀ g (same self-address), obs = ofUInt64 (g.gas − Gbase)`
(`MaterialiseRuns.lean:550`), and the `SloadRealises` twin (`:539`). The `∀`-over-all-frames
shape forces gas (and sload warmth) to be **constant** across the run, which a real
descending-gas run never is — so the headline hypotheses (`hgasr`/`hsload`) are unsatisfiable
and `lower_conforms` is **vacuous on the gas/sload axes**. (Proven: `V2/HonestGasTie.lean`,
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

- **Phase A — structural reskin, NO behavior change (theorem-preserving).**
  Introduce `Loc`/`Alloc`; factor `lower` into `encode ∘ emit (allocate prog) prog` such that the
  emitted bytes are **definitionally the old `lower`** (so downstream proofs are untouched).
  `allocate` reproduces `defsOf` exactly (pure ⇒ `remat`, call result ⇒ `slot`). Rename
  `Expr.callResult` → `Expr.slot` (generic spill-load) with a full call-site sweep. Build green,
  all headline theorems unchanged. *Lowest risk; sets the structure.*

- **Phase B — gas through the spill (kills the gas vacuity).**
  Default `allocate` maps gas-tmps to `.slot`; `emitStmt .assign t .gas` emits the stash; uses load
  from the slot. Generalize `MemRealises` to cover gas slots; replace `Lir.GasRealises` (the
  universal) with the positional one-read tie via the existing alignment infra
  (`V2/TieDischarge.lean`, `V2/Oracle.lean`). Remove `hgasr` from the headlines. Gas is now an
  in-scope, honestly-tied, multi-use-safe observable. Retire `HonestGasTie.lean`'s "documented
  vacuity" once the real fix lands (keep the satisfiability witnesses as tests).

- **Phase C — sload through the spill (kills the scoping wart + cost smear).**
  Default `allocate` maps sload-tmps to `.slot`; stash at def, load at use. Delete the
  across-write `DefsSound` scoping side-condition on the cached path. Replace `Lir.SloadRealises`
  (the universal) with the positional warmth-cost tie (`SloadLogAligned` infra). Remove `hsload`.

- **Phase D — `∀ SoundAlloc` headline + replaceable-pass pipeline + cleanup.**
  Generalize `Corr`/`sim_*`/`materialise_runs`/`DriveSim`/`LowerConforms` to quantify over any
  `SoundAlloc a` (current behavior = one instance). Land the default `allocate` pipeline (§5).
  Sweep dead code (the old per-construct special cases, retired universals, stale comments). Mark
  v1/v2 gas/sload docs superseded; update `ir-design-v3.md` cross-refs.

Each phase runs the established loop: an implementation subagent → an independent review subagent →
self-review against the diff, before moving to the next.

## 7. Open questions / notes

- **Default policy** confirmed: spill-the-effectful (gas/call/sload spilled, arithmetic
  rematerialized) — exercises both remat and spill paths from day one.
- Slot allocation: `slotOf t = t.id*32` (disjoint per-tmp) suffices for soundness; a packing pass
  is a later, conformance-free optimization.
- Multi-use gas is now *free* (it is just a `.slot` tmp reused via `MLOAD`); the `WellFormed`
  single-use restriction on gas can be relaxed/retired once Phase B lands.
- Stack discipline (empty stack at statement boundaries, `Corr.M5`) is preserved: stash/load
  leave the stack empty between statements, same as remat.
```
