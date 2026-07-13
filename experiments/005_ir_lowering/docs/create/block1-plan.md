# Block #1 — `simStmt_coupled_sstore`: A-vs-B resolution + close plan

> **P9 status note (2026-07-08).** This planning note predates the Phase 2A deletion pass.
> Mentions of `Expr.slot`, `materialiseExpr`, `materialise`, `recomputeFuel`, `MatFueled`,
> `Assembly/Acyclic.lean`, or `NoSlotSource` below are historical; the current value channel is
> fold-based over `Loc`/`matCache`.

Date: 2026-07-06. Worktree `.worktrees/producer` (branch `exp005-producer`), read-only.
Target: `LirLean/Realisability/Producer.lean:498-514` (`simStmt_coupled_sstore`, `sorry` at `:514`).

## TL;DR verdict

**Diagnosis A is WRONG on the mechanism; Diagnosis B is right on the mechanism but
too optimistic about the tooling; and BOTH miss the secondary re-plumb.** The real
task is a bounded **threading proof plus a bounded re-plumb** — NOT "an impossible
non-recording GAS/SLOAD-at-nonempty-stack edge" (A), and NOT "just fold an existing
edge" (B, the fold does not yet exist). Effort: MEDIUM. No genuinely new *concept* is
needed; two new WIP-cone lemmas that mirror existing green ones.

---

## 1. A vs B, pinned to the code

### (i) Are all oracle temps spilled so `materialise` never re-emits GAS/SLOAD? — YES.

`defsOf` (`Spec/Lowering.lean:262-272`) routes **every** non-recomputable temp to
`Expr.slot`:
- `.assign t .gas       => (t, Expr.slot (slotOf t))`  (`:266`)
- `.assign t (.sload _) => (t, Expr.slot (slotOf t))`  (`:267`)
- `.call ⟨_,_,some t⟩`, `.create … some t` → `Expr.slot` (`:269-270`)
- every other `.assign t e` keeps `e` (rematerialised).

`allocate = (defsOf …).map locOfExpr` (`:291`), and `locOfExpr (.slot n) = .slot n`
(`:285-287`), so `Alloc.toDefs (allocate prog)` is `defsOf prog`, whose **range never
contains a bare `.gas`/`.sload`**. `materialiseExpr` (`:142-156`) only produces a
`[GAS]` byte on the `.gas` arm (`:156`) and a `... ++ [SLOAD]` on the `.sload k` arm
(`:154-155`); it reaches those arms **only** when it directly *sees* an `Expr.gas` /
`Expr.sload` node. Uses go through `.tmp t → defs t → .slot n → emitImm n ++ [MLOAD]`
(`:144, :146-148`). So a `.tmp` use of a gas/sload/call temp materialises as **PUSH32;
MLOAD**, never GAS/SLOAD. This is stated verbatim at `MaterialiseRuns.lean:47-48`
("a *bare* `.gas`/`.sload k` is never materialised by this recursion") and enforced by
`materialise_runs`'s `e ≠ .gas` / `∀ k, e ≠ .sload k` antecedents
(`MaterialiseRuns.lean:771` sig).

`emitStmt .sstore key value = materialise value ++ materialise key ++ [SSTORE]`
(`Spec/Lowering.lean:191-192`). GAS/SLOAD bytes are emitted **only** at the
`emitStmt .assign` def-site stash (`:181-190`: for `assign t .gas`,
`materialiseExpr … .gas = [GAS]`; for `assign t (.sload k)`,
`materialise k ++ [SLOAD]`). **`emitStmt .sstore` contains no stash**, hence no
GAS/SLOAD. Concrete witness: `exProg` block 0's `sstore ⟨0⟩ ⟨3⟩` has t0↦`imm 5`,
t3↦`imm 1` (both pure remat — `Witness.lean:42-64`), so the run is literally
`PUSH32 1 ; PUSH32 5 ; SSTORE` — three steps, all non-recording.

**⇒ Diagnosis A's premise "materialise emits GAS/SLOAD opcodes for recomputable
operands" is FALSE for the sstore emission.** There are zero GAS/SLOAD frames in
`materialise value ++ materialise key ++ [SSTORE]`, regardless of what value/key are.

### (ii) The recorder gate — descent/Pending stack or operand stack? — PENDING stack.

`driveLog` (`Spec/Recorder.lean:206-273`) carries `stack : List Pending` (the
DESCENT/pending stack). Its GAS/SLOAD record gates are `isGasOp current && stack.isEmpty`
(`:258`) and `isSloadOp current && stack.isEmpty` (`:261`) — **`stack` is the pending
descent stack**, `[]` at top-level. `sloadWarmthOf` (`:153-158`) reads
`fr.exec.stack.head?` — the **operand** stack — for the key. `isGasOp`/`isSloadOp`
(`:131,:144`) are pure *decode* predicates (`decode … == .Smsf .GAS/.SLOAD`).

**⇒ Diagnosis B is CORRECT: the gate is the Pending stack, not the operand stack.
Diagnosis A's parenthetical "the recorder records nothing (nonempty stack)"
conflates the two** — a GAS/SLOAD op at a nonempty *operand* stack but empty *pending*
stack IS recorded. (For sstore this is moot — there are no GAS/SLOAD ops at all — but
it is decisive for the *sload* arm, and shows A's model of the recorder is wrong.)

### (iii) Is the top-level `assign t (.sload k)` SLOAD actually recorded? — YES.

For the *sload arm* (`simStmt_coupled_sload`, not this block): the def-site stash
`materialise k ++ [SLOAD] ++ PUSH slot ++ MSTORE` runs at top level (pending `= []`),
so at the SLOAD frame `isSloadOp = true ∧ stack.isEmpty`, and it IS recorded;
`recorderCoupled_sload` (`Machinery.lean:1671`) consumes exactly that head and pins
`n = sloadWarmthOf fr`, reading the key off the operand head (`:1677`). B's account of
the sload arm is correct — but this is **not** the sstore arm. **For sstore there is no
recorded op to peel.**

### (iv) What do the R7 edges provide? — single-step, no multi-step fold.

- `recorderCoupled_step_other` (R7d, `Machinery.lean:1709`): `RecorderCoupled log fr …`
  + `isGasOp fr = false` + `isSloadOp fr = false` + `stepFrame fr = .next exec`
  ⟹ `RecorderCoupled log {fr with exec := exec} …` (all three suffixes preserved).
  **One `.next` step.**
- `recorderCoupled_stepsTo_other` (R7d′, `:1997`): the `StepsTo` rephrasing of the
  above. **One `StepsTo` step.**
- `recorderCoupled_sload` (R7c, `:1671`): consumes one sload-suffix head at a SLOAD
  `.next` step. (Not needed for sstore.)

**There is NO Runs-level fold.** The docstring at `:1990-1996` explicitly defers it:
"Folded over the arg-push `Runs` (once its per-frame `isGasOp`/`isSloadOp = false`
facts are in hand from the lowering decode) this is Piece-A step 1." The entry seed
uses `recorderCoupled_stepsTo_other` for a **single** JUMPDEST step only
(`Producer.lean:276`).

**⇒ Diagnosis B's "just FOLD the existing `recorderCoupled_step_other`" understates:
the fold lemma must be BUILT.** It is bounded and mechanical (mirrors the existing
green `materialise_runs`), but it is a new lemma, not a citation.

---

## 2. The secondary blocker BOTH diagnoses under-weight: `SstoreRealises` re-plumb

`sim_sstore_stmt` (`Sim/SimStmt.lean:347-373`) takes `hsstore : SstoreRealises fr kw vw
acc`, which is `∀ g` (any frame at `fr`'s address with operand stack `kw::vw::[]`)
asserting `¬ g.gas ≤ Gcallstipend ∧ charge ≤ g.gas ∧ acc present` (`:319-325`). The
`∀ g` over **unconstrained gas** makes it unsatisfiable from the walk's hypotheses
(an adversarial low-gas `g` refutes the stipend clause) — A's secondary point is
CORRECT, and `sim_sstore_stmt` only ever instantiates it at the internal frame `frk`
(`:439`).

The honest replacement already exists and is **GREEN**: `sstoreRealises_at_frame` (R4,
`Machinery.lean:416-437`) derives all three conclusions **point-wise at a concrete
frame `g`** from `SelfPresent g` + `CleanHaltsNonException g` + stack + SSTORE-decode +
canModify. `simStmt_coupled_sstore` already carries `hsp : SelfPresent fr` (`:509`) and
`hch : CleanHaltsNonException fr` (`:508`) precisely for this. The remaining gap: R4's
NOTE (`Machinery.lean:413-415`) says `sim_sstore_stmt` must be re-plumbed to the
point-wise form — "not performable here (no edits to existing files)". In the WIP cone
that constraint is lifted: we write a WIP-local `sim_sstore_stmt'`.

---

## 3. Recommended plan (MEDIUM effort, threading + bounded re-plumb)

Two new WIP-cone lemmas (both import `MaterialiseRuns` + `Surface`, both live in
`Machinery.lean` or `Producer.lean`), then assemble.

### Step S1 — `recorderCoupled_matRuns` (the missing fold). Confidence HIGH, effort MEDIUM.

Statement (WIP cone):
```
theorem recorderCoupled_matRuns {log fr fr' gS sS cS} (defs := defsOf prog) …
  (hmd  : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e)
  (hne  : e ≠ .gas) (hnsl : ∀ k, e ≠ .sload k)
  (hmr  : MatRuns (defsOf prog) sloadChg fuel e w fr fr')   -- endpoints from materialise_runs
  (hcp  : RecorderCoupled log fr  gS sS cS) :
        RecorderCoupled log fr' gS sS cS
```
Proof by induction on the **same** `fuel`/`Expr` structure `materialise_runs` uses
(`MaterialiseRuns.lean:771`), mirroring its leaf lemmas:
- `.imm`/`.slot` leaves (matRuns_imm/_slot analogues): the sub-run is a short explicit
  step chain (`pushFrameW`, and for `.slot` a PUSH then MLOAD). At each step the MatDec
  clause (`matDec_imm`/`matDec_slot`, `:273-285`) gives `decode = PUSH32/MLOAD`, so
  `isGasOp = false` and `isSloadOp = false` (both by `unfold; rw [hdec]; rfl`, exactly
  the `Producer.lean:262-265` pattern); apply `recorderCoupled_step_other` per step.
- `.tmp` arm: `matDec_tmp_some`/`_none` reduce to the sub-expr (`:287-298`); recurse.
- `.add`/`.lt` arms: `matDec_add`/`_lt` (`:300-320`) split into two sub-`MatRuns` plus a
  final ADD/LT decode; recurse on each, then one `step_other` for the ADD/LT frame.
- `.gas`/`.sload` arms: unreachable, discharged by `hne`/`hnsl` (verbatim as
  `materialise_runs`).
No gas/stack/storage/memory bookkeeping — this is the light shadow of `materialise_runs`.
The intermediate endpoints come from `hmr` / the sub-`MatRuns` produced alongside; the
cleanest packaging is to prove S1 as a corollary threaded through the *same* recursion
that produces `MatRuns` (a joint `materialise_runs_coupled` in WIP), so the sub-run
step structure is in hand rather than re-derived from an opaque `Runs`.

*Risk*: `Runs` is opaque in `MatRuns.runs`; the step-by-step application needs the
sub-run *shape*. Mitigation: re-run the leaf constructions (matRuns_imm etc. expose the
explicit post-frame), so we never decompose an opaque `Runs` — we rebuild it in lockstep.

### Step S2 — SSTORE step transport. Confidence HIGH, effort LOW.

The final `[SSTORE]` frame: `hdop` (`SimStmt.lean:361`) gives `decode … = .Smsf .SSTORE`,
so `isGasOp = false`, `isSloadOp = false`; `sim_sstore`'s `stepFrame frk = .next _`
(the continuing case) gives the `.next` witness; one `recorderCoupled_step_other`.

### Step S3 — `sim_sstore_stmt'` (WIP re-plumb). Confidence HIGH, effort LOW-MEDIUM.

Copy `sim_sstore_stmt`'s body (`SimStmt.lean:347-~460`) into a WIP-cone lemma that
**drops** `hsstore : SstoreRealises` and instead takes `hsp : SelfPresent fr`
(+ existing `hcs`). Transport `SelfPresent`/canModify/clean-halt across the two
materialise runs (`MatRuns.accounts` `:350` + `.addr` `:342` transport `SelfPresent`;
`cleanHaltsNonException_forward` for the halt scope, already used at `:402`), then at
`frk` discharge the three `sim_sstore` runtime facts via `sstoreRealises_at_frame`
(R4). Everything else is identical. (Alternatively inline directly in
`simStmt_coupled_sstore` — but a named `sim_sstore_stmt'` keeps the sload/gas arms'
future reuse clean.)

### Step S4 — assemble `simStmt_coupled_sstore`. Confidence HIGH, effort LOW.

`CoupledAdvance` (`Producer.lean:114-124`) fields:
- `EvalStmt.sstore hk hvv` (IR side, `IRRun.lean:72-96`; consumes no stream head — T/C/D
  and gS/sS/cS ride UNCHANGED, exactly like the assignPure arm `Producer.lean:435-437`).
- `Runs fr fr'` from S3 (`sim_sstore_stmt'`).
- `Corr … (pc+1)` and `fr'.exec.stack = []` from S3.
- `RecorderCoupled log fr' gS sS cS` = S1 (value) ▸ S1 (key) ▸ S2 (SSTORE), chained by
  the `Runs.trans` decomposition S3 already builds (frv, frk, fr'). Suffixes unchanged.
- `StreamsAligned` rides unchanged (`hal`; sstore touches no aligned stream — cf.
  `Producer.lean:66-69`: T=gS, C=callStreamOf cS, D unchanged; none moves).

**No `CoupledAdvance` restatement is needed for sstore** (unlike the gas/sload arms,
which hit the separate `DefsSoundS` R0 obstruction documented at
`producer-status.md:102-125` — sstore's target is a storage write, not a rebind, so the
strong-`Corr`-at-`pc+1` `defsSound` is re-established by B3 `defsSound_preserved_sstore`,
already inside `sim_sstore_stmt`). This is why sstore is closeable *now* and the
gas/sload arms are not.

**Verdict on nature of the work: THREADING PROOF + bounded re-plumb.** Not new
concepts; two mirror-lemmas over existing green machinery. The single point of
schedule risk is S1's Runs-shape handling (rated below).

---

## 4. Confidence & effort ledger

| Step | What | Confidence it closes | Effort |
|------|------|----------------------|--------|
| S1 | `recorderCoupled_matRuns` fold over materialise | HIGH (mechanism proven; mirror of green `materialise_runs`) | MEDIUM |
| S2 | SSTORE-step `step_other` | VERY HIGH | LOW |
| S3 | `sim_sstore_stmt'` off point-wise R4 | HIGH (R4 green; transports exist) | LOW-MED |
| S4 | assemble `CoupledAdvance` | VERY HIGH (mirrors assignPure) | LOW |

Aggregate: **MEDIUM**, ~1–2 days Lean. No `sorry`-scaffold required; each step is
independently green-able (S3, S2 first; S1 next; S4 last).

---

## 5. Alternatives (and why S1–S4 is best)

1. **Generic Runs-fold `recorderCoupled_runs_of_all_next`** (Runs + ∀-intermediate-frame
   non-recording ⟹ preserved). *Rejected as primary*: supplying the ∀-intermediate-frame
   decode facts from an opaque `MatRuns.runs` still requires a structured induction over
   materialise — i.e. it needs S1 anyway, plus an awkward "enumerate intermediates of a
   Runs" layer. Strictly more work.
2. **Fold at the `driveLog`/`drive` level** (reuse the `driveLog_frame_nonempty`
   `:1733` style: a non-recording top-level segment threads the accumulator unchanged).
   *Viable, similar effort*; but it re-proves at the interpreter level what
   `recorderCoupled_step_other` already gives per step, so folding the existing edge (S1)
   is more direct and reuses green atoms.
3. **Spill the SSTORE key first / restructure the stash.** *Not applicable* — sstore has
   no stash and no recorded op; nothing to restructure. This alternative addresses a
   non-problem (it is A's phantom edge).
4. **Finer per-frame coupling granularity** (state the walk invariant per-frame, not per
   block-boundary). *Rejected*: `RecorderCoupled`/`DriveCorrLog` are deliberately stated
   at stack-nil block boundaries (`Surface.lean:506-508`) so the restart pending stack is
   `[]`; per-frame restatement would ripple the entire `DriveCorrLog` walk and re-open the
   nil-boundary alignment — a skeleton-wide change for no sstore-specific gain.

**Best: S1–S4** — smallest new surface, all over existing green lemmas, closes sstore
without touching the default cone or restating `CoupledAdvance`.

---

## 6. One caveat for the lead

Closing `simStmt_coupled_sstore` does **not** unblock the flagship: `simStmts_coupled_block`
(P3a) still needs the gas/sload arms (`Producer.lean:468,:490`), which are blocked on the
**separate** `DefsSoundS` R0 obstruction (`producer-status.md:102-125`) — a genuine
skeleton-wide design decision, orthogonal to the sstore transport analysed here. Sstore
is the one blocked arm that is a pure proof task; report S1 (`recorderCoupled_matRuns`) as
reusable by the sload arm's `materialise k` sub-run once R0 lands.
