# GAS/SLOAD coupled arms — the missing state-indexed invariant (design, 2026-07-09)

Track D of the R11 wave ([run plan Phase 3](r11-run-plan-2026-07-09.md), [chunk 4](r11-plan-2026-07-08.md)).
Design only; no Lean edits. Baseline: merged main `d95d178`.

## Conclusion (read this first)

The two blocked arms [`simStmt_coupled_gas`](../../LirLean/V2/Realisability/Producer.lean#L453)
and [`simStmt_coupled_sload`](../../LirLean/V2/Realisability/Producer.lean#L474) are **unprovable
as stated** — no amount of proof effort closes them. Their conclusion
[`CoupledAdvance`](../../LirLean/V2/Realisability/Producer.lean#L114) embeds the **strong**
per-cursor [`Corr`](../../LirLean/Sim/SimStmt.lean#L102), whose `defsSound` field is **false at
real mid-block states immediately after a gas/sload rebind** in rebinding loop programs. This is
not new analysis: it is the already-machine-checked lesson-8 finding
([`not_defsSound_stale`](../../LirLean/V2/Realisability/Witness.lean#L236) at
[`staleSt`](../../LirLean/V2/Realisability/Witness.lean#L221)), and the mandated fix is already
written down as the never-executed R0b reshape criterion in the
[R0b docstring](../../LirLean/V2/Realisability/Machinery.lean#L59).

The missing "state-indexed producer invariant" is therefore **not** a warmth-set or gas-value
tracker. It is the **invalidation-set-scoped mid-block `DefsSound` carrier**: the walk's
per-statement `Corr` must carry
[`DefsSoundS prog I st`](../../LirLean/Spec/WellFormed.lean#L69) where `I : Tmp → Prop` is the
[`invalStep`](../../LirLean/Spec/WellFormed.lean#L56) fold over the block prefix — the state
index is the *set of tmps staled so far in this block*, threaded statement-by-statement and
collapsed to `∅` at block boundaries by
[`RevalidatesPerBlock`](../../LirLean/Spec/WellFormed.lean#L89). Everything on the coupling side
(suffix peeling through the stash sequences) already exists or is a mechanical twin of an
existing brick; §5 lists the two genuinely new coupling bricks.

Explicitly, on the question the run plan asks: **the sload-charge tie stays positional** — no
warmth-set tracking enters the walk invariant (§3).

## 1 — Why the arms are unprovable as stated

The refutation instance, verbatim from the
[R0b docstring](../../LirLean/V2/Realisability/Machinery.lean#L59): at `exProg`'s loop-exit
iteration, block 1 is `[t6 := gas; t7 := 1000; t8 := lt t6 t7]` and the walk re-enters it with
`t6,t7,t8` still bound from the previous iteration. At pc 0 the block-entry state satisfies the
strong `Corr` (block boundaries are healed — that is why the boundary invariant
[`DriveCorrLog`](../../LirLean/V2/Realisability/Surface.lean#L270) survives). Fire the gas arm:
`EvalStmt.assignGas` ([`Semantics.lean`](../../LirLean/Spec/Semantics.lean#L55)) rebinds
`t6 := ⟨fresh gas word⟩`, while `t8` keeps the previous iteration's `lt`-value. The post-state
now violates the strong recompute invariant

```lean
/-- B3 — recompute-on-use soundness. -/
defsSound  : DefsSound prog st
```

because `t8`'s registered def `.lt t6 t7` recomputes to a *different* word under the rebound
`t6`. [`not_defsSound_stale`](../../LirLean/V2/Realisability/Witness.lean#L236) machine-checks
exactly this state. Since every other antecedent of `simStmt_coupled_gas` is satisfiable at that
cursor, the arm's conclusion (`CoupledAdvance` ⟹ strong `Corr` at `(L, pc+1)`) is **refutable**,
not merely hard. The sload arm is the same disease: its target is likewise
`NonRecomputable`-rebound (spilled), so readers go stale identically. Two consecutive box passes
grinding to "missing state-indexed producer invariants" is the expected terminal state of an
unprovable goal.

Why the two *closed* arms did not hit this:

* [`simStmt_coupled_assignPure`](../../LirLean/V2/Realisability/Producer.lean#L398) — the target
  is **recomputable**, so
  [`defsSound_setLocal_recomputable`](../../LirLean/V2/Realisability/Producer.lean#L343)
  self-repairs: the rebind is a no-op (loop re-entry recomputes the same value) or the target was
  unbound. No reader can go stale.
* [`simStmt_coupled_sstore`](../../LirLean/V2/Realisability/Producer.lean#L1199) — an `sstore`
  rebinds no local (`invalStep` is the identity on `.sstore`), and lesson 8 already made its
  scoping conclusion static ([`StepScopedS`](../../LirLean/Spec/WellFormed.lean#L79) sstore arm
  dominates the state-gated one).

GAS/SLOAD (and CALL-result — see §6) are precisely the `NonRecomputable` **rebinds with possible
live readers**; they are the first arms that cannot dodge the reshape.

The mechanism of the block: the in-tree brick
[`sim_assign_gas`](../../LirLean/Sim/SimStmt.lean#L880) re-establishes strong `Corr` only from
the live-scope clause of the retired
[`StepScoped`](../../LirLean/Materialise/DefsSound.lean#L575)

```lean
∧ (e = .gas →
  isGasDef prog t ∧
  (∀ t₀ e₀, rematOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0))
```

(fed to [`defsSound_preserved_assignGas`](../../LirLean/Materialise/DefsSound.lean#L344)). The
reshaped ties deliberately supply only the static
[`StepScopedS`](../../LirLean/Spec/WellFormed.lean#L79) (lesson 8: the live-scope clause is
refutable at `exProg`'s own loop), so the arm cannot reconstruct the brick's input. That is not a
ties gap to re-widen — the clause is *false* at the refuting states; the *conclusion* must weaken.

## 2 — What already exists (inventory; do not rebuild)

Per the run plan's suspects (a)–(c), verified against source:

* **(a) gas-head tie through the stash: EXISTS, green.**
  [`gas_suffix_head_realised`](../../LirLean/V2/Realisability/Machinery.lean#L1734) (R1) pins
  `gS.head? = some (ofUInt64 (fr.gasAvailable − Gbase))` from coupling + clean-halt +
  `Corr`-decode, and is already a conclusion of
  [`StmtTies'` arm (3)](../../LirLean/V2/Realisability/Surface.lean#L397). The
  [`GasLogAligned`](../../LirLean/V2/Drive/SelfPresent.lean#L98) /
  [`SloadLogAligned`](../../LirLean/V2/Drive/SelfPresent.lean#L267) family is the *older*
  single-`obs` positional-alignment track ("RETAINED for Phase 3"); the coupled walk does **not**
  consume it — the restart equation of
  [`RecorderCoupled`](../../LirLean/V2/Realisability/Surface.lean#L234) supersedes it. No missing
  `gasRecord` lemma.
* **(b) sload-charge tie: the peel EXISTS; only nonemptiness is missing.**
  [`recorderCoupled_sload`](../../LirLean/V2/Realisability/Machinery.lean#L1765) (R7c) consumes
  the head and pins `n = sloadWarmthOf fr` (state-indexed *by the concrete frame*, via restart
  determinism — no invariant involved). What is missing is the public destructuring twin of the
  private [`gasSuffix_nonempty`](../../LirLean/V2/Realisability/Machinery.lean#L1680) (§5, N1).
* **(c) no-record transport through stash sequences: EXISTS.**
  [`recorderCoupled_step_other`](../../LirLean/V2/Realisability/Machinery.lean#L1803) (R7d) peels
  one non-recording step; [`recorderCoupled_matRunsC`](../../LirLean/V2/Realisability/Producer.lean#L510)
  (S1, green) rides the coupling across a whole variable-length `materialise` run — exactly the
  sload key prefix. The gas envelope
  [`gas_envelope_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L700) and sload
  envelope [`sload_envelope_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L790)
  derive every runtime gas/mem side-condition of the `_lowered` bricks from the threaded
  clean-halt, as the un-coupled walk already demonstrates
  ([gas arm](../../LirLean/Assembly/LowerConforms.lean#L481),
  [sload arm](../../LirLean/Assembly/LowerConforms.lean#L438)). The sload pc bound comes from
  [`WellFormedLowered.bound_sload`](../../LirLean/Assembly/LowerConforms.lean#L152) via `hwl.wf`
  (no ties change needed; the gas bound is already ties arm (3)'s `pcOf + 34 < 2^32` conjunct).

So the coupling channel is essentially done. The block is entirely on the `Corr` carrier.

## 3 — Warmth: positional, NOT tracked in the invariant

Decision (per the run plan's explicit question): **no warmth-set (or gas-value) tracking enters
the walk invariant.** Justification:

1. **Nothing consumes the charge value.** The IR side of a spilled sload is
   `EvalStmt.assignPure` — it consumes no stream; the observable never mentions sload charges.
   The sload suffix `sS` exists in `RecorderCoupled` only because the restart equation returns
   all recorded streams; the walk needs to *peel* its head at an SLOAD site, never to *predict*
   it. R7c's `n = sloadWarmthOf fr` output is discarded by the arm.
2. **Where the charge does matter (bytecode gas-sufficiency at the SLOAD step), it is derived
   pointwise** at the concrete frame from clean-halt
   ([`next_sload_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L548) inside
   [`sload_envelope_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L790)) — the
   frame *contains* its access set (`fr.exec.substate.accessedStorageKeys`,
   [`sloadWarmthOf`](../../LirLean/Spec/Recorder.lean#L32)), so restart determinism pins the
   recorded charge per-frame with zero invariant support.
3. **Tracking it would contradict the coupling design.** The §2 design notes on
   [`RecorderCoupled`](../../LirLean/V2/Realisability/Surface.lean#L234) settled the coupling as
   frame-indexed precisely to be cyclic-correct; an accessed-keys projection in `DriveCorrLog`
   re-introduces the per-cursor state function of rejected option (iii), and would be dead
   weight per (1).

The same argument kills a gas-value tracker: R1 already delivers the head equation pointwise.

## 4 — The invariant: the `invalStep`-scoped `Corr` (R0b executed)

### 4.1 Statement shape and home

Generalize `Corr` **in place** ([`Sim/SimStmt.lean`](../../LirLean/Sim/SimStmt.lean#L102),
default lib) over the staleness set:

```lean
structure Corr (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (I : Tmp → Prop)
    (st : V2.IRState) (fr : Frame) (L : Label) (pc : Nat) : Prop where
  ... (all eight non-defsSound fields verbatim) ...
  /-- B3, scoped: recompute-on-use soundness OUTSIDE the staled set `I`. -/
  defsSound : DefsSoundS prog I st
```

with the strong form as the `I := fun _ => False` instance
([`defsSoundS_empty_iff`](../../LirLean/Spec/WellFormed.lean#L74) makes it definitionally the
old field). A WIP-side twin (`CorrS`) is rejected: it duplicates the ~250-line
`memAgree`/mstore-disjointness bodies of
[`sim_assign_gas`](../../LirLean/Sim/SimStmt.lean#L880) /
[`sim_assign_sload`](../../LirLean/Sim/SimStmt.lean#L1030) and the whole arm surface, all deleted
later — the same shape as the Phase-2 `CorrF` twin that was already rejected. The sweep is
mechanical: green default-lib call sites instantiate `I := fun _ => False` and keep their proofs
(one `defsSoundS_empty_iff` shim where `hcorr.defsSound` is consumed). Syntactic option to
shrink the sweep: make `I` a trailing `optParam (fun _ => False)`.

### 4.2 Threading through the walk

* **`DriveCorrLog` is unchanged.** Block boundaries carry the strong instance — exactly what
  [`RevalidatesPerBlock`](../../LirLean/Spec/WellFormed.lean#L89) guarantees and what the
  boundary entry lemma
  [`driveCorrLog_entry`](../../LirLean/V2/Realisability/Producer.lean#L168) already establishes.
* **`CoupledAdvance` gains the set** and advances it by one `invalStep`:

```lean
def CoupledAdvance (prog …) (I : Tmp → Prop) (L : Label) (pc : Nat) … (s : Stmt) : Prop :=
  ∃ st' fr' T' C' D' gS' sS' cS',
    EvalStmt prog st T C D s st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (invalStep prog I s) st' fr' L (pc + 1)
    ∧ fr'.exec.stack = []
    ∧ RecorderCoupled log fr' gS' sS' cS'
    ∧ StreamsAligned self log gS' cS' T' C' D'
```

  Each `simStmt_coupled_*` arm takes `hcorr : Corr … I st fr L pc` and concludes
  `CoupledAdvance … I … s`.
* **Establishment at entry of every block**: `I₀ := fun _ => False`, supplied by
  `DriveCorrLog.corr` (strong ⟹ scoped-at-`∅` is the trivial direction of
  `defsSoundS_empty_iff`). Nothing changes in P1b.
* **Per-arm preservation** is *uniform and already proven*:
  [`defsSoundS_preserved_step`](../../LirLean/V2/Realisability/Machinery.lean#L89) (R0b, green)
  covers all five statement shapes with **no per-state side conditions** — the live-scope demand
  is absorbed by the set transfer. Per arm:

  | arm | `invalStep` transfer | discharge |
  |---|---|---|
  | assign pure | target ↦ self-read; others ↦ `I ∨ ReadsOf` | R0b `assignPure` case (replaces `defsSound_setLocal_recomputable` — simpler than today) |
  | assign `.gas` | target excluded (`NonRecomputable`); readers of target enter `I` | R0b `assignGas` case |
  | assign `.sload k` | same as gas | R0b `assignPure` case (sload fires `assignPure`) |
  | `sstore` | `I` unchanged | R0b `sstore` case |
  | `call`/`create` | result tmp's readers enter `I` | R0b `call`/`create` cases |

* **Collapse at the terminator** (P3a,
  [`simStmts_coupled_block`](../../LirLean/V2/Realisability/Producer.lean#L1327)): after the fold,
  `I_end = b.stmts.foldl (invalStep prog) (fun _ => False)`; `RevalidatesPerBlock` gives
  `∀ t', ¬ I_end t'`, and a two-line bridge (O2 below) restores the strong `Corr` that
  `CoupledBlockRun`/`DriveCorrLog` package at the successor boundary. `TermTies'` antecedents are
  untouched (terminator cursors sit at the healed set).

### 4.3 Use-site non-invalidation (R0b criterion (3), the honest residue)

Scoping the *carrier* is not free at the *readers*: the materialise value channel
([`materialise_runsC`](../../LirLean/Materialise/MatFoldChannel.lean#L812),
[`recorderCoupled_matRunsC`](../../LirLean/V2/Realisability/Producer.lean#L510),
[`materialise_chargeC_le_of_cleanHalt`](../../LirLean/Materialise/MaterialiseCleanHalt.lean#L71),
[`materialise_runsC_of_cleanHalt`](../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372))
consumes `hsound : DefsSound prog st` at every `.tmp`-remat readback. Under the scoped carrier
each such read needs its tmp **outside `I`**, transitively through remat chains (a staled read is
where IR-vs-lowered divergence is *real*: the lowered code rematerialises fresh, the IR reads the
stale binding). Two new statics:

```lean
/-- The remat-read closure of `e` avoids the staled set `I`
    (matDecMeasure recursion, like `MatDecC`). -/
def RematClosureFree (prog : Program) (I : Tmp → Prop) : Expr → Prop
  | .imm _ | .gas | .sload _ => True     -- (.gas/.sload never materialised; key handled at .tmp)
  | .tmp t => ¬ I t ∧ (∀ e', allocate prog t = some (.remat e') → RematClosureFree prog I e')
  | .add a b | .lt a b => RematClosureFree prog I (.tmp a) ∧ RematClosureFree prog I (.tmp b)

/-- Static: at every cursor, the statement's operands avoid the prefix staled set.
    Home: Spec/WellFormed.lean, next to RevalidatesPerBlock. -/
def ScopedUses (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat) (s : Stmt),
    blockAt prog L = some b → b.stmts[pc]? = some s →
    ∀ t, readsStmt s t →       -- operand tmps of `s` (key of sload/sstore, value, call args…)
      RematClosureFree prog ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp t)
```

> **Amendment 2026-07-10 (sanctioned): `RematClosureFree` is an `inductive`, not a `def`.**
> The recursive `def` sketched above does not termination-check: the `.tmp` arm recurses through
> `allocate`-resolved remat bodies, which is not structurally decreasing, and the existing
> `matDecMeasure_remat_lt` measure needs `DefsConsistent`/`DefEnvOrdered` evidence that does not
> belong in this signature (first reshape pass blocked on exactly this, correctly). Realize the
> SAME arms as an inductive predicate:
>
> ```lean
> inductive RematClosureFree (prog : Program) (I : Tmp → Prop) : Expr → Prop where
>   | imm   (w) : RematClosureFree prog I (.imm w)
>   | gas       : RematClosureFree prog I .gas
>   | sload (k) : RematClosureFree prog I (.sload k)
>   | tmp   (t) (hI : ¬ I t)
>       (hrem : ∀ e', allocate prog t = some (.remat e') → RematClosureFree prog I e') :
>       RematClosureFree prog I (.tmp t)
>   | add (a b) (ha : RematClosureFree prog I (.tmp a)) (hb : RematClosureFree prog I (.tmp b)) :
>       RematClosureFree prog I (.add a b)
>   | lt  (a b) (ha : RematClosureFree prog I (.tmp a)) (hb : RematClosureFree prog I (.tmp b)) :
>       RematClosureFree prog I (.lt a b)
> ```
>
> Semantics are unchanged (least fixed point of the same clauses); cyclic remat chains — already
> excluded by `DefEnvOrdered` — are simply unprovable, which is the desired behavior for a
> closure certificate. Witness discharges construct the inductive directly along the defEnv
> order. No signature pollution, no fuel.

Notes: the gas arm has **no operands** — it needs none of this; the sload arm needs it only for
the key `k`; the (already-closed) sstore arm needs it for `key`/`value` after the reshape.
Terminator operands (branch cond / ret value) read at the *end-of-block* fold, which
`RevalidatesPerBlock` makes empty — free. `exProg` satisfies `ScopedUses` (its only staled tmp,
`t8`, is read only by the terminator, after healing —
[`revalidatesPerBlock_exProg`](../../LirLean/V2/Realisability/Witness.lean#L147) already walks
these folds). Both statics join
[`WellLowered`](../../LirLean/V2/Realisability/Surface.lean#L151) as fields
(`revalidates : RevalidatesPerBlock prog`, `scopedUses : ScopedUses prog`) — internal adapter
only; the public flagship keeps rebuilding `WellLowered` from `IRWellFormed`, whose
checker-side twins are R9 territory (follow-on, not this wave).

## 5 — The coupling-side bricks (small; the arms' assembly)

Layering constraint: `RecorderCoupled` is WIP-lib
([`Surface.lean`](../../LirLean/V2/Realisability/Surface.lean#L234)); the sim bricks are default
lib. So the coupling is threaded in `Producer.lean`, S3-style
([`sim_sstore_stmt'`](../../LirLean/V2/Realisability/Producer.lean#L1036) is the template), over
**named** stash endpoints.

* **N1 — `sloadSuffix_nonempty`** (Machinery.lean, next to R7c; public twin of the private
  [`gasSuffix_nonempty`](../../LirLean/V2/Realisability/Machinery.lean#L1680)):

  ```lean
  theorem sloadSuffix_nonempty
      (hcp : RecorderCoupled log fr gS sS cS)
      (hsl : isSloadOp fr = true) (hstep : stepFrame fr = .next exec) :
      ∃ n sS', sS = n :: sS'
  ```

  Proof mirrors the gas one on the `sloadAcc` splice of `driveLog`. (The gas arm needs no
  analogue: ties arm (3)'s `gS.head?` equation destructures `gS`.)

* **N2 — named-endpoint stash lemmas.**
  [`stash_tail_gas`](../../LirLean/Materialise/StashTail.lean#L295) /
  [`stash_tail_sload`](../../LirLean/Materialise/StashTail.lean#L383) hide their endpoint behind
  `∃ endFr`, and [`sim_assign_gas`](../../LirLean/Sim/SimStmt.lean#L880) /
  [`sim_assign_sload`](../../LirLean/Sim/SimStmt.lean#L1030) re-existentialize — the coupled arm
  cannot attach `RecorderCoupled` to the same frame. Expose the witnesses the proofs already
  construct: conclude `StashRuns fr (mstoreFrame (pushFrameW (gasFrame fr) (ofNat slot) 32)
  (ofNat slot) gasVal words' []) …` (gas; sload analogously from `sloadFrame frk keyVal []`),
  and give `sim_assign_gas`/`sim_assign_sload` named-endpoint forms (`hstash` keyed on an
  explicit `endFr`, conclusion at that `endFr`); the current `∃`-forms become one-line
  corollaries. Default-lib, mechanical.

* **N3 — coupled stash transport** (Producer.lean, S-family): thread the coupling across the
  named frames with exactly one recording peel.
  * GAS: `hcp : RecorderCoupled log fr (g :: gS') sS cS` →
    [`recorderCoupled_step_gas`](../../LirLean/V2/Realisability/Machinery.lean#L1640) at the GAS
    step (its `stepFrame` fact from
    [`next_gas_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L524); `isGasOp`
    from [`decode_gasstash`](../../LirLean/Assembly/LowerDecode.lean#L632) anchor 1), then two
    [`recorderCoupled_step_other`](../../LirLean/V2/Realisability/Machinery.lean#L1803) peels
    (PUSH32, MSTORE). Output: coupling at the named endpoint on `(gS', sS, cS)`, plus
    `g = ofUInt64 (fr.gasAvailable − Gbase)` (cross-checks ties arm (3)).
  * SLOAD: coupling to `frk` via
    [`recorderCoupled_matRunsC`](../../LirLean/V2/Realisability/Producer.lean#L510) (key prefix,
    non-recording), N1 destructures `sS`,
    [`recorderCoupled_sload`](../../LirLean/V2/Realisability/Machinery.lean#L1765) peels at the
    SLOAD step, two R7d peels for PUSH32/MSTORE. Output: coupling on `(gS, sS', cS)`.

* **Arm assembly** (P2-gas, in order): fire ties arm (3) → destructure `gS = g :: gS'` from the
  head equation → `decode_gasstash` →
  [`gas_envelope_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L700) → N2/N3
  produce the named coupled stash run → named-endpoint `sim_assign_gas` (scoped, §4) gives
  `Corr … (invalStep …) (st.setLocal t g) endFr L (pc+1)` → package `CoupledAdvance` with
  `EvalStmt.assignGas` (alignment `T = gS` forces the consumed IR head `= g`; new alignment
  `⟨rfl, hal.2.1, hal.2.2⟩` at `gS'`). P2-sload: fire ties arm (2) → `hwl.wf.bound_sload` →
  [`decode_sloadstash`](../../LirLean/Assembly/LowerDecode.lean#L806) →
  [`sload_envelope_of_cleanHalt`](../../LirLean/Materialise/CleanHaltExtract.lean#L790) (ties
  arm (2) supplies the stack-room fold and activeWords-flatness) → N1/N3 → named-endpoint
  `sim_assign_sload` → package with `EvalStmt.assignPure` (no stream consumed; suffix advance is
  `sS → sS'` only).

## 6 — Obligation list (statement sketches; existing dischargers)

| # | obligation | home | status/discharger |
|---|---|---|---|
| O1 | `Corr` gains `I`; field `defsSound : DefsSoundS prog I st` | `Sim/SimStmt.lean` | sweep; green cone at `I = ∅` via [`defsSoundS_empty_iff`](../../LirLean/Spec/WellFormed.lean#L74) |
| O2 | `corr_strong_of_revalidated : Corr … I … → (∀ t', ¬ I t') → Corr … (fun _ => False) …` | SimStmt.lean | two lines (pointwise) |
| O3 | scoped re-plumb of [`sim_assign_gas`](../../LirLean/Sim/SimStmt.lean#L880)/[`sim_assign_sload`](../../LirLean/Sim/SimStmt.lean#L1030) (+`_lowered`): drop `StepScoped`, take `isGasDef`/`isSloadDef` (from ties' `StepScopedS`), conclude at `invalStep` | SimStmt/LowerDecode | `defsSound` clause by [`defsSoundS_preserved_step`](../../LirLean/V2/Realisability/Machinery.lean#L89); rest verbatim |
| O4 | materialise folds take `DefsSoundS prog I st` + `RematClosureFree prog I e` | Materialise/* | recursion unchanged; `.tmp`-remat arm consumes the closure premise |
| O5 | `RematClosureFree`, `ScopedUses`, `readsStmt`; `WellLowered.{revalidates, scopedUses}` | Spec/WellFormed.lean, Surface.lean | `exProg` instances: extend [`revalidatesPerBlock_exProg`](../../LirLean/V2/Realisability/Witness.lean#L147)'s fold walk |
| O6 | N1 `sloadSuffix_nonempty` | Machinery.lean | mirror of [`gasSuffix_nonempty`](../../LirLean/V2/Realisability/Machinery.lean#L1680) |
| O7 | N2 named-endpoint `stash_tail_gas`/`stash_tail_sload` + `sim_assign_gas`/`sim_assign_sload` | StashTail/SimStmt | expose existing witnesses |
| O8 | N3 coupled stash transport (gas, sload) | Producer.lean | R7b/R7c/R7d + clean-halt step extractors, all green |
| O9 | restate `CoupledAdvance`/arms with `I`; re-thread the closed assign/sstore arms | Producer.lean | assign arm *simplifies* (R0b replaces the self-repair lemma); sstore re-thread is mechanical |
| O10 | P2-gas / P2-sload assembly per §5 | Producer.lean | the actual chunk-4 deliverable |

Sequencing note: O1–O5 are the default-lib atomic swap (one pass, build-green before any arm
work); O6–O8 are independent of it; O9–O10 land last. The CALL arm
([`simStmt_coupled_call`](../../LirLean/V2/Realisability/Producer.lean#L1279)) and the chunk-3
CREATE arm have the **same staleness disease** (result-tmp rebind) — state them scoped from the
start; their `invalStep` cases in R0b are already proven.

## 7 — Alternatives considered and rejected

* **Warmth-set / gas-value tracking in `DriveCorrLog`** — rejected (§3): value consumed by
  nothing; restart determinism pins it per-frame; re-introduces the option-(iii) per-cursor
  state function.
* **WIP-side `CorrS` twin** — rejected: duplicates the heavy `sim_assign_*` bodies and the arm
  surface; `CorrF` precedent.
* **Re-widening the ties with the live-scope clause** — rejected: lesson 8 showed it refutable
  at on-run states; it would re-poison `stmtTies'_of_runWithLog` (R10a).
* **Restricting the flagship to non-rebinding programs** (making the live-scope clause static) —
  rejected: public-premise no-go (track rules), and `exProg` itself rebinds.

## Decision needed from Eduardo

1. **Execute R0b now (O1: parameterize `Corr` in place, default lib)?** This is the load-bearing
   call: chunk 4 cannot close without *some* carrier weakening, and the docstring-mandated
   reshape is the non-twin option. Sub-choice: explicit `I` parameter (honest, bigger sweep) vs
   trailing `optParam (fun _ => False)` (smaller diff, slightly hides the index).
2. **`ScopedUses` shape (§4.3)**: per-cursor operand closure over the prefix fold, as sketched —
   or a stronger/simpler global form (e.g. "no statement reads a tmp staled earlier in its own
   block"), trading generality for checker simplicity?
3. **`WellLowered` growth**: accept two new internal fields (`revalidates`, `scopedUses`) with
   checker twins deferred to R9, per the existing `gasBound`/`slotAddr` precedent?
4. **N2 named-endpoint refactor** of the default-lib bricks (vs S3-style full re-proof of the
   `Corr` bodies inside `Producer.lean`): named-endpoint is recommended (kills ~500 lines of
   would-be duplication); confirm touching `SimStmt.lean`/`StashTail.lean` for it is in-scope
   for the proof pass.
5. **Scope confirmation**: state the CALL/CREATE coupled arms scoped from the start (they share
   the disease), so chunk-3/chunk-2 work lands on the new carrier rather than being repaired
   after.
