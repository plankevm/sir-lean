# Phase 2A — value-channel core retype (ordered def-env + `Expr.slot` removal)

Design of record for exp005 branch `exp005-phase2-valuechannel`. Scope: FULL FUEL
PURGE. Kill `fuel`/`recomputeFuel`/`MatFueled`/rank apparatus by replacing the
unordered `defsOf : Tmp → Option Expr` map with an **ordered def-environment** and
redefining `materialise` as a **structural left-fold** (`matCache`), composed with
**`Expr.slot` removal** (D4). Semantics (`Spec/Semantics.lean` execution relations) is
UNTOUCHED except removing the now-dead `evalExpr .slot` arm. Default `lake build` must
stay green + sorry-free; `WIP` keeps only its pre-existing sorries.

> ### *** 2026-07-07 — CRITICAL CORRECTION: THE BRIDGE IS UNSOUND. DO NOT USE IT. ***
>
> The prior plan (S3/S6) proposed a byte bridge
> `matCache prog t = materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)` and
> transferred the value/sim tower by rewriting `lowerFold = lower`. **This bridge is
> FALSE even under `DefEnvOrdered`.** `recomputeFuel prog = #stmts + 1`
> (`Lowering.lean:164`), but `materialiseExpr` burns **two** fuel per binary level (each
> of the two `materialiseExpr defs f (.tmp _)` recursions at `Lowering.lean:150-155`
> decrements `f`), so it undercounts the recompute depth by ~2×. On programs
> `DefEnvOrdered` admits — e.g. `t1 = imm 0; t2 = add t1 t1; t3 = add t2 t2` (three
> assigns ⇒ `recomputeFuel = 4`) — `materialiseExpr` bottoms out to `[]` garbage
> (≈3 bytes) while the fold `matCache` fully expands (135 bytes). The old `rank_lt_fuel`
> side condition of `IRWellFormed.acyclicDefs` was exactly the soundness envelope that
> hid this truncation, and it is precisely what we are deleting. **THEREFORE:** the
> value channel, the per-statement sims, AND the geometry tower are re-proven **DIRECTLY
> OVER THE FOLD** by structural induction on `defEnv` / `matCache` — with NO reference to
> `materialiseExpr`'s fuel structure and NO `MatFueled` hypothesis anywhere. Nothing is
> "transferred" from the fuel proofs; everything is re-proven over the total fold. The
> only *internal* fold lemma is the **fixpoint** `matCache_unfold`
> (`matCache prog t = matLoc (matCache prog) (allocate prog t)`, §2.3) — a fold-to-fold
> equation, NOT a fold-to-fuel bridge.

Verdict: **PROCEED**. Every obligation is sound. The cost is a whole-value-channel and
whole-geometry re-proof over the fold (~25 files), but the fold is total and the
inductions are along a finite list (define-before-use is what makes them terminate),
so the proofs are mechanical relative to the existing fuel proofs. The load-bearing new
lemma is `matCache_unfold` (§2.3); everything downstream is its consumer.

---

## 1. The crux: is program order a valid topological order? — RESOLVED: YES

### 1.1 The static def-graph

`materialiseExpr`'s ONLY recursion is `.tmp t → defsOf prog t = some e → recurse e`
(`Lowering.lean:146-148`); binary ops already take `Tmp` operands (`IR.lean:75-95`), so
the IR is ANF-flat and the def-graph is exactly: node `t` with `defsOf prog t = some e`,
edge `t → t'` iff `t'` occurs in `e`. In the fold this is the same graph read off
`defEnv prog : List (Tmp × Loc)` (`Lowering.lean:330`): a `(t, Loc.remat e)` entry has
edges to every tmp `usesInExpr t' e ≠ 0`.

Edges arise ONLY from `.remat` expressions carrying tmp references (`add`/`lt`/`tmp`);
`defsOf`/`defEnv` route **every** gas / sload / call-result / create-result def to
`Loc.slot (slotOf t)` — a leaf with no tmp references (`Lowering.lean:333-337`). So the
only edge-bearing entries are pure `add`/`lt`/`tmp`. Verified on `exProg`
(`Witness.lean:66`): only `t8 ↦ lt t6 t7` bears edges.

### 1.2 Program order IS topological (grounded in the invariants)

Program order = the `blocks`-array-then-`stmts`-list `flatMap` order both `defsOf`
(`Lowering.lean:263`) and `defEnv` (`Lowering.lean:331`) scan. For a program satisfying
`IRWellFormed`, every edge-bearing entry lists each referenced tmp at an *earlier*
position, grounded in three facts (unchanged from the prior analysis):

1. **Self-contained blocks (from `RunDefinableG`, `WellFormed.lean:95-113`).** The
   block-entry state is universally quantified, so an operand can be guaranteed bound
   only if the block *prefix* binds it — within-block statement order is a topological
   order of within-block dataflow.
2. **Consistent redefinition (from `DefsConsistent`, `WellFormed.lean:132`).** `defsOf`
   is a **first-find** over program order (`pairs.find?`, `Lowering.lean:272`);
   `DefsConsistent` forces every def-site of a tmp id to agree with `defsOf`'s
   registration, so cross-block reuse registers the same expression.
3. **CFG loops ≠ def-graph cycles.** A tmp has ONE static registration; a CFG back-edge
   re-executes the same defs, adding no later→earlier edge. `exProg`'s block-1 self-loop
   leaves the def-graph acyclic.

### 1.3 How to land the topo fact: carry it as `DefEnvOrdered`

`DefEnvOrdered prog` (`WellFormed.lean:296`, LANDED S0) is the decidable static field
that replaces `acyclicDefs`:

```lean
def DefEnvOrdered (prog : Program) : Prop :=
  ∀ (i : Nat) (t : Tmp) (e : Expr),
    (defEnv prog)[i]? = some (t, Loc.remat e) →
    ∀ t' : Tmp, usesInExpr t' e ≠ 0 →
      ∃ j, j < i ∧ ∃ loc : Loc, (defEnv prog)[j]? = some (t', loc)
```

It is a **net simplification** of `acyclicDefs : ∃ rank, Acyclic ∧ ∀t, rank t + 1 <
recomputeFuel` (`WellFormed.lean:487`): no existential rank, no fuel-fitting side
condition (there is no fuel). It is exactly define-before-use SSA over the ordered
carrier; §1.2 is its *justification*, not a new restriction. Discharged for `exProg` by
`decide`/`rfl` (obligation 2).

---

## 2. Direct reproof over the fold — NO BRIDGE

### 2.1 The unconditional / conditional split (unchanged in shape)

- **Geometry / decode tower — UNCONDITIONAL.** `SegAligned`, `DecodeAnchors`,
  `JumpValid`, `Layout`, `BoundaryReach` hold for ALL programs. The fold is total
  (`foldl` over a finite list; undefined-tmp → `emitImm 0`, `Lowering.lean:373`), so the
  fold's garbage cases are themselves seg-aligned — geometry over the fold needs NO
  well-formedness (obligation 4).
- **Value / sim tower — CONDITIONAL on `DefEnvOrdered` (+ `DefsConsistent`).** As today
  the value tower is conditional (old: `MatFueled`; new: `DefEnvOrdered` via
  `matCache_unfold`). Conclusions are unchanged.

### 2.2 Why there is no bridge and geometry cannot transfer by rewrite

`matCache ≠ materialise(defsOf, recomputeFuel)` on `DefEnvOrdered`-admissible programs
(the correction above). So neither the value tower NOR the geometry tower may be
transferred from the fuel proofs by any equation to the fuel emission. Both are
**re-proven over the fold from scratch**. This is mechanical (identical block/opcode
shape; `SegAlignedP.append` reused verbatim), but it is real work and is the bulk of the
purge.

### 2.3 The one internal fold lemma: `matCache_unfold` (the inductive core)

The single new load-bearing lemma. It is a **fold-to-fold** fixpoint equation (NOT a
bridge to `materialiseExpr`):

> **`matCache_unfold`** — under `DefsConsistent prog` and `DefEnvOrdered prog`, for every
> `t` present in `defEnv prog`:
> `matCache prog t = matLoc (matCache prog) (allocate prog t)`
> (and, absent from `defEnv`, `matCache prog t = emitImm 0`).

Consequence, used everywhere downstream: for a rematerialised `t` (`allocate prog t =
some (.remat e)`), `matCache prog t = matExpr (matCache prog) e`, so the cached bytes for
`t` *are* the byte-assembly of `e` resolving each operand `t'` to its **final** cache
value `matCache prog t'`. For a spilled `t` (`allocate prog t = some (.slot n)`),
`matCache prog t = emitImm (ofNat n) ++ [MLOAD]`.

Proof shape (the replacement for `rank_lt_fuel`/`MatFueled`): strong induction on the
`defEnv` position, using
- `matCache_last_eq_first` (`WellFormed.lean:402`, now unconditional after obligation 1):
  all entries for a tmp id carry the same `Loc = allocate prog t`, so the last-wins
  `Function.update` fold and the first-find `defsOf` select the same `Loc`;
- `DefEnvOrdered`: every operand `t'` of a `.remat e` entry at position `i` occurs at some
  `j < i`, so its cache value is already final when `t` is computed — the `Function.update`
  prefix cache at position `i` agrees with the full `matCache prog` on every operand of `e`.
  Formalised via a **byte-stability** helper: `matStep`'s update at a later position never
  changes an already-settled operand value (operands settle at `j < i`).

Termination is structural (finite list); there is NO fuel-sufficiency obligation because
the fold always fully expands. `matCache_unfold` is the exact node where the deleted
`matFueled_of_acyclic` (`Acyclic.lean:94`) content is replaced by an induction along the
ordered list rather than an induction on fuel.

### 2.4 `Expr.slot` removal is byte-neutral and lands with the swap

Both `matExpr`'s `.slot` arm (`Lowering.lean:351`) and `matLoc`'s `.slot` arm
(`Lowering.lean:358`) already emit `emitImm (ofNat n) ++ [MLOAD]`, identical to
`materialiseExpr`'s `.slot` arm (`Lowering.lean:144`). Once `defsOf` is `Loc`-valued and
the spine reads `rematOf` (S1, landed), `Expr.slot` has no producer and no live consumer,
so its deletion (obligation 6) is byte-neutral by construction. `evalExpr .slot ⇒ none`
(`Semantics.lean:147`) is dead once `Expr.slot` is gone; `evalExpr` becomes total-and-pure.

---

## 3. Final shapes

### 3.1 `Loc`, `Alloc`, def-env — unchanged from S0

`Loc = remat Expr | slot Nat` (`Lowering.lean:94`), `Alloc = Tmp → Option Loc`
(`Lowering.lean:103`), `defEnv prog : List (Tmp × Loc)` (`Lowering.lean:330`),
`matExpr`/`matLoc`/`matStep`/`matFold`/`matCache` (`Lowering.lean:344-374`), all LANDED.
`defsOf` is retyped to `Program → Alloc` at the swap (obligation 5): oracle/spilled temps
↦ `Loc.slot (slotOf t)`, pure ↦ `Loc.remat e`. **Deleted last** (obligation 6):
`Loc.toDef`/`Alloc.toDefs` (`Lowering.lean:107-113`), `allocate`/`locOfExpr`
(`Lowering.lean:300-306`), `materialiseExpr`/`materialise`/`recomputeFuel`
(`Lowering.lean:142-165`).

### 3.2 Fold-based emission (no fuel)

`emitStmt`/`emitTerm`/`emitBlockBody`/`emit` are redefined to consume the fold cache:
each `materialise defs fuel _` / `materialiseExpr defs fuel _` becomes
`matExpr (matCache prog) _` = `matCache prog _`. `emit` passes `matCache prog` where it
passed `(a.toDefs, recomputeFuel prog)`. The offset table `offsetTable` re-bases to
`blockLen` over the fold emission. Structural termination throughout (no fuel).

### 3.3 `MatDec` / `MatRuns` / `chargeOf` retype (cache-keyed, fuel-free)

`MatDec` (`MaterialiseRuns.lean:237`) is restated as a cache-keyed relation `MatDecC` over
`Expr`: the `.tmp t` arm resolves to the decode facts of the cached bytes `matCache prog t`
at `p` (via `matCache_unfold`), and the composite `.add`/`.lt`/`.sload` arms anchor
sub-decodes at offsets `(matCache prog t').length` (cache lengths) instead of
`(materialiseExpr defs f (.tmp _)).length`. `MatRuns` (`MaterialiseRuns.lean:336`) and
`chargeOf` (`MaterialiseGas.lean:73`) likewise lose `fuel` and read `matCache`. Their
**conclusions are unchanged** (decode-fact bundle; value push = `evalExpr`; per-opcode gas
list). `MatFueled` (`MatDecLower.lean:262`) and its lemmas are **deleted** (obligation 6).

### 3.4 Shrunk `IRWellFormed` (`WellFormed.lean:471`)

Final field list: `defineBeforeUse, defsConsistent, entry0, cfgClosed, defEnvOrdered,
revalidates, slotAddr`.
- `acyclicDefs` (`:487`) → **replaced** by `defEnvOrdered : DefEnvOrdered prog`.
- `noSlotSource` (`:492`) → **deleted** (`Expr.slot` gone ⇒ impossible by construction;
  `NoSlotSource` def `:283` deleted).
- `defsConsistent` gains the **create-result arm** (obligation 1).

### 3.5 Shrunk `WellFormedLowered` (`LowerConforms.lean:148`)

Final field list: `bound_sstore, bound_sload, bound_ret, bound_stop, bound_jump,
bound_branch, slots_slot`.
- `matFueled_sstore`/`matFueled_sload`/`matFueled_ret`/`matFueled_branch` (`:150-183`) →
  **deleted** (structural termination ⇒ no fuel-sufficiency obligation).
- `bound_*` (`:154-205`) → restated fuel-free: `materialiseExpr (defsOf prog)
  (recomputeFuel prog) (.tmp ·)` → `matCache prog ·`; `offsetTable (defsOf) (recomputeFuel)`
  → the fold offset table.
- `slots_slot` (`:215`) → kept, restated over the `Loc`-valued `defsOf` (`.slot n`).

`Acyclic.lean` whole (`ExprRankLt`/`Acyclic`/`AcyclicWellFormed`/`matFueled_of_exprRankLt`/
`matFueled_tmp_of_acyclic`/`wellFormedLowered_of_acyclic`) is **deleted** last.

---

## 4. Green-incremental step sequence (DIRECT REPROOF — no bridge, no monolith)

S0/S1/S2 have LANDED (commits `f364dde`/`63a26c0`/`21e7bf5`): the fold carrier + reduction
lemmas, the `rematOf` spine-decouple, and the (hcreate-conditional) `defEnv↔defsOf`
alignment. The sequence builds the fold-based tower ALONGSIDE the old, migrates consumers,
and DELETES the old fuel/`Expr.slot` machinery LAST. Each step is a landable green commit
(`lake build` = `LirLean` cone green + sorry-free; `lake build WIP` keeps ONLY its
pre-existing tracked sorries). NO monolithic delete-everything step; NO fold↔fuel bridge
step (unsound, §2.2).

- **P1 — (Ob 1) discharge S2's `hcreate`.** Add a third conjunct to `DefsConsistent`
  (`WellFormed.lean:132`), the verbatim twin of the call-result conjunct:
  `∀ (cs : CreateSpec) (t : Tmp), b.stmts[pc]? = some (.create cs) → cs.resultTmp = some t
  → defsOf prog t = some (.slot (slotOf t))`. Discharge the `hcreate` parameter of
  `defEnv_entry_eq_allocate` (`WellFormed.lean:323`) and `matCache_last_eq_first`
  (`:402`) from `hdc.<create-arm>` and DELETE the parameter, so both become UNCONDITIONAL
  in `DefsConsistent`. Update the `DefsConsistent` witness for `exProg` (create-arm
  vacuous — `exProg` has no create). *Files:* `Spec/WellFormed.lean`,
  `V2/Realisability/Witness.lean`. *Green gate:* `lake build` green; `WIP` pre-existing
  sorries only; `exProg`'s `DefsConsistent` witness green by `decide`/construction.

- **P2 — (Ob 2) `DefEnvOrdered` adequacy.** Prove `DefEnvOrdered exProg` by `decide`/`rfl`
  (non-vacuity; mirrors `acyclic_exProg`, `Witness.lean:365`). Prove
  `defEnvOrdered_subsumes_acyclic : DefEnvOrdered prog → ∃ rank, Lir.Acyclic (defsOf prog)
  rank` with `rank t := 2 * (first index of t in defEnv prog)` (an operand at `j < i` gives
  `rank·+1 = 2j+1 < 2i = rank t`, the strict-by-2 `ExprRankLt` needs; `.gas`/`.sload` arms
  never fire — `defsOf` spills them, `rematOf_ne_gas`/`_ne_sload`; `.imm`/`.slot` arms are
  `True`). **NO `rank_lt_fuel`** (fuel is being deleted). Gates the later
  `acyclicDefs → defEnvOrdered` swap. *Files:* `Spec/WellFormed.lean` or a new
  `Spec/DefEnvOrderedLemmas.lean`, `V2/Realisability/Witness.lean`. *Green gate:* both
  lemmas green, alongside old `acyclic_exProg`.

- **P3 — the fold fixpoint `matCache_unfold` (the inductive core, §2.3).** Prove
  `matCache_unfold` and its byte-stability helper by strong induction on the `defEnv`
  position, from `DefsConsistent` (unconditional `matCache_last_eq_first`, P1) +
  `DefEnvOrdered`. This is the SINGLE hardest proof and the node that replaces
  `matFueled_of_acyclic`. Derive the two immediate corollaries: `matCache prog t =
  matExpr (matCache prog) e` when `allocate prog t = some (.remat e)`; the slot readback
  when `= some (.slot n)`. **NO reference to `materialiseExpr`.** *Files:*
  `Spec/Lowering.lean` (or a new `Materialise/MatCacheUnfold.lean`). *Green gate:*
  `matCache_unfold` + corollaries green, no new sorry.

- **P4 — (Ob 4) geometry over the fold (UNCONDITIONAL), alongside old.** Prove the
  pointwise-alignment invariant `segAlignedP_matExpr : (∀ t, SegAlignedP IsLoweringOp
  (cache t)) → ∀ e, SegAlignedP IsLoweringOp (matExpr cache e)` (cases on `e`, operand
  lookups discharged by the hypothesis; the `SegAlignedP.append`/`nonpush`/`push` combinators
  reused from `SegAligned.lean:225-276`), and `matFold_aligned : (∀ t, aligned (init t)) →
  ∀ t, aligned (matFold init l t)` (list induction; `matStep` preserves the pointwise
  invariant via `segAlignedP_matExpr`/`segAlignedP_slot`), hence `matCache prog` is pointwise
  aligned UNCONDITIONALLY (init `emitImm 0` aligned). Introduce fold-emit twins
  `emitStmtF`/`emitTermF`/`emitBlockBodyF`/`flatBytesF`/`lowerF` over `matCache` and re-prove
  `segAlignedP_flatBytesF`, `DecodeAnchorsF`, `JumpValidF`, `LayoutF`, `BoundaryReachF` by
  REUSING `SegAlignedP.append` over the identical `JUMPDEST :: body` block shape. NO
  well-formedness hyp anywhere. *Files:* `Decode/SegAligned.lean`, `Decode/DecodeAnchors.lean`,
  `Decode/JumpValid.lean`, `Decode/Layout.lean`, `Decode/BoundaryReach.lean`,
  `Decode/DecodeLower.lean`, `Spec/Lowering.lean`. *Green gate:* fold geometry green; old
  geometry still consumed. (May split per geometry file, each a green sub-commit.)

- **P5 — (Ob 3) value channel over the fold, alongside old.** Restate `MatDecC`/`MatRunsC`/
  `chargeC` over `matCache`/`defEnv` (fuel-free, §3.3). Re-prove
  `matDec_of_seg` → `matDecC_of_seg` and `materialise_runs` → `materialise_runsC` by
  structural recursion on `Expr` combined with induction along `defEnv` (the `.tmp t` arm
  unfolds via `matCache_unfold` (P3) to the operand's own cache bytes; operands are earlier
  in `defEnv` so their value/decode facts hold by the outer IH), **without `MatFueled`** —
  the `f + 1`/`0`/fuel cases of the old proofs (`MatDecLower.lean:296-311`) VANISH.
  Re-establish the `chargeC`/`matCache` length-lockstep the `StackRoomOK`/`maxChargeDepth`
  folds read (`WellFormed.lean:427-457`, restated fuel-free). MemRealises / spill-slot
  readback unchanged in spirit. *Files:* `Materialise/MaterialiseGas.lean`,
  `Materialise/MatDecLower.lean`, `Materialise/MaterialiseRuns.lean`,
  `Materialise/StashTail.lean`, `Materialise/CleanHaltExtract.lean`,
  `Materialise/MaterialiseCleanHalt.lean`, `Materialise/DefsSound.lean`. *Green gate:* fold
  value channel green, alongside old.

- **P6 — (Ob 3/5) migrate the per-statement + whole-CFG sims onto the fold.** Restate the
  `Sim/` lemmas (`sim_assign`/`sim_sstore`/`sim_call`/`sim_create`, `sim_stmts`,
  `sim_term_*`) and the `Assembly/` tie assembly (`sim_cfg`, `SimStmtStep`/`SimTermStep`
  dischargers, `LowerDecode`) over the fold value channel (P5) + fold geometry (P4).
  Statement CONCLUSIONS unchanged; this is signature/threading. Land per file-group, each
  green. **This is the bulk and the producer-coupled surface — safe only while the branch
  is quiescent.** *Files:* `Sim/SimStmt.lean`, `Sim/SimTerm.lean`, `Sim/SimStmts.lean`,
  `Assembly/LowerDecode.lean`, `Assembly/LowerConforms.lean`, `Spec/BudgetDerivations.lean`,
  `V2/Drive/DriveSim.lean`, and the WIP `V2/Realisability/{Surface,Machinery,Producer}.lean`.
  *Green gate:* each file-group green; `WIP` pre-existing sorries only.

- **P7 — (Ob 5) THE SWAP: redefine `lower`/`flatBytes`/`emit` + retype `defsOf → Alloc`.**
  Redefine `emit`/`flatBytes`/`lower` to the fold versions (rename `*F` → canonical;
  because fold ≠ fuel this is a genuine definition change, and it is green precisely because
  every consumer was migrated to the fold-proven facts in P4-P6). Retype
  `defsOf : Program → Alloc` (returns `Loc` directly: oracle/spilled ↦ `Loc.slot (slotOf t)`,
  pure ↦ `Loc.remat e`); re-base `rematOf` off the new `defsOf` (`some (.remat e) => some e
  | _ => none`, same value — spine statements do not churn, S1 groundwork). Retype the
  residual `defsOf`-references in `DefsConsistent`/`ReadsOf`/`StepScopedS`/`invalStep`/
  `DefsSoundS`/`slots_slot` to `Loc` (minimal textual churn). *Files:* `Spec/Lowering.lean`,
  `Spec/WellFormed.lean`, `Assembly/LowerConforms.lean`, `Decode/*`, `Materialise/*`.
  *Green gate:* full `lake build` green; `#print axioms` guards intact.

- **P8 — (Ob 5) shrink `IRWellFormed`/`WellFormedLowered`/`WellLowered` + flagship + witness.**
  `IRWellFormed` (`WellFormed.lean:471`): replace `acyclicDefs` with `defEnvOrdered`
  (wired via P2 subsumption where a consumer still needs `Acyclic`), drop `noSlotSource`.
  `WellFormedLowered` (`LowerConforms.lean:148`): drop the four `matFueled_*` fields, restate
  the six `bound_*` + `slots_slot` fuel-free over `matCache` lengths / fold offset table
  (§3.5). `WellLowered` (`Surface.lean:401`): drop `noSlotSource`. Rewrite
  `wellFormedLowered_of_IRWellFormed` (`RealisabilitySpec.lean:124`): drop the
  `acyclicDefs`/`matFueled_of_acyclic`/`slots_slot_of_noSlotSource` lines. Update the
  `exProg` witness (`Witness.lean:363-707`): `defEnvOrdered_exProg` by `decide`; drop
  `acyclic_exProg`/`acyclicWellFormedExProg`/`noSlotSource_exProg`/the `acyclicDefs`/
  `noSlotSource` witness fields. *Green gate:* `WIP` green, ONLY pre-existing sorries;
  `exProg` witness green.

- **P9 — (Ob 6) delete the orphaned old machinery.** With all consumers migrated, DELETE:
  `Expr.slot` (`IR.lean:94`) + `evalExpr .slot` arm (`Semantics.lean:147`, `evalExpr` becomes
  total-and-pure) + every dead `.slot` arm (`usesInExpr`, `evalExpr_setLocal_of_unused`/`_*`,
  `defsSound_preserved`'s `| slot n =>` case, `matExpr_slot`); `materialiseExpr`/`materialise`/
  `recomputeFuel` (`Lowering.lean:142-165`); `MatFueled` + `matFueled_tmp_some/none`
  (`MatDecLower.lean:262`); `Assembly/Acyclic.lean` whole + the now-orphaned P2 subsumption
  lemma; `Loc.toDef`/`Alloc.toDefs`/`allocate`/`locOfExpr` (`Lowering.lean:107-113,300-306`)
  + `allocate_toDefs`/`toDef_locOfExpr` (`Decode/LoweringLemmas.lean`); `NoSlotSource`
  (`WellFormed.lean:283`). *Green gate:* full `lake build` green + sorry-free; `WIP`
  pre-existing sorries only; `#print axioms` guards intact.

---

## 5. Retype ripple (full surface — executors must expect all of it)

Files touching `materialiseExpr`/`MatDec`/`MatFueled`/`recomputeFuel` (grep counts):
`Assembly/LowerDecode.lean` (128), `Materialise/MatDecLower.lean` (107),
`Materialise/MaterialiseRuns.lean` (98), `Spec/BudgetDerivations.lean` (87),
`Assembly/LowerConforms.lean` (75), `V2/Realisability/Machinery.lean` (42),
`V2/Realisability/Producer.lean` (41), `Assembly/Acyclic.lean` (40, DELETED),
`Decode/DecodeAnchors.lean` (37), `V2/Realisability/Surface.lean` (29),
`Sim/SimStmt.lean` (27), `Sim/SimTerm.lean` (23), `Decode/SegAligned.lean` (21),
`Decode/Layout.lean` (20), `Decode/JumpValid.lean` (19), `Materialise/MaterialiseGas.lean`
(15), `Materialise/MaterialiseCleanHalt.lean` (15), `Spec/WellFormed.lean` (14),
`Spec/Lowering.lean` (9), `Materialise/{StashTail,DefsSound,CleanHaltExtract}.lean`,
`Sim/SimStmts.lean`, `V2/Drive/DriveSim.lean`, `Decode/DecodeLower.lean`,
`V2/Realisability/Witness.lean`.

`Expr.slot` dead-arm removal spans ~24 files (grep `.slot`).

Specific casualties/rewrites: `WellFormedLowered.matFueled_{sstore,sload,ret,branch}` and
the four `bound_*` restatements (`LowerConforms.lean:150-205`); `matFueled_of_acyclic`,
`AcyclicWellFormed`, `wellFormedLowered_of_acyclic`, `matFueled_of_exprRankLt`, `ExprRankLt`,
`Acyclic` (`Assembly/Acyclic.lean`) DELETED; `wellFormedLowered_of_IRWellFormed`
(`RealisabilitySpec.lean:124`) drops the acyclicDefs/matFueled/noSlotSource lines;
`allocate_toDefs`/`defsOf_ne_gas`/`_ne_sload` (`Decode/LoweringLemmas.lean`) shrink/vanish;
`acyclic_exProg`/`acyclicWellFormedExProg`/`noSlotSource_exProg` (`Witness.lean:365-707`) →
`defEnvOrdered_exProg` (`decide`).

---

## 6. Risks

1. **`matCache_unfold` (highest).** The fold fixpoint (§2.3) is the single hardest proof
   and everything downstream consumes it. The byte-stability helper (operands settle at
   `j < i`, later `Function.update`s do not disturb them) must be stated carefully; if the
   `Function.update` fold does not `simp`-reduce cleanly, the reduction lemmas
   `matFold_cons`/`matStep` (`Lowering.lean:398-402`) plus a pointwise-agreement lemma
   between the prefix cache and the full cache on `e`'s operands are the mechanical handles.
2. **No transfer from fuel proofs.** The value/sim tower is re-proven, not rewritten. The
   fuel-case arms of every fuel-inductive proof (`MatDecLower.lean:296-311`,
   `SegAligned.lean:236-276`) VANISH, but the leaf/composite arms are re-derived over
   `matCache`. This is mechanical but voluminous (P5/P6).
3. **The swap (P7) is a genuine definition change.** `lower` changes from fuel to fold and
   is byte-different on ill-formed inputs; it is green ONLY because P4-P6 migrated every
   consumer to fold-proven facts first. Do not attempt P7 before P4-P6 land.
4. **Scale + producer coupling.** ~25 files incl. the producer's sim-lemma instantiations
   (`Producer.lean`/`Machinery.lean`). Must run producer-quiescent (branch stated quiescent).
5. **`DefEnvOrdered`/`DefsConsistent` discharge for `exProg`.** Must reduce by `decide`/`rfl`;
   low risk given `defsOf_exProg_eq` already reduces by `rfl` (`Witness.lean:66`).
