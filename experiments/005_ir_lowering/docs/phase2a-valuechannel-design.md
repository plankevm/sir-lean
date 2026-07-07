# Phase 2A — value-channel core retype (ordered def-env + `Expr.slot` removal)

Design of record for exp005 branch `exp005-phase2-valuechannel`. Scope: kill the
`fuel`/`recomputeFuel`/`MatFueled`/rank apparatus by replacing the unordered
`defsOf : Tmp → Option Expr` map with an **ordered def-environment** and redefining
`materialise` as a **structural left-fold**, composed with **`Expr.slot` removal**
(D4). Semantics (`Spec/Semantics.lean` execution relations) is UNTOUCHED. Default
`lake build` must stay green + sorry-free; `WIP` keeps only its pre-existing sorries.

Verdict: **PROCEED**. The design is sound; byte-preservation holds in the correct
(conditional-on-well-formedness) sense. The cost is a whole-value-channel re-thread
(~25 files), but it is a mechanical signature/threading refactor with conclusions
unchanged, not a from-scratch re-proof. Read the risks (§6) — the framing "byte-for-byte
identical, facts survive" hides one real subtlety (the unconditional geometry tower must
be *re-proven over the new emission*, not transferred by rewrite, because new ≠ old on
ill-formed inputs).

> **2026-07-07 — SCOPE: FULL FUEL PURGE (project lead).** `lower`/`emit` are redefined
> over the structural fold; `recomputeFuel`, the fuel parameter, `MatFueled`, the rank
> apparatus (`Assembly/Acyclic.lean`), and `Expr.slot` are removed ENTIRELY. The prior
> run established the crux: the UNCONDITIONAL geometry tower (`segAlignedP_flatBytes`,
> `DecodeAnchors`, `JumpValid`, `Layout`) cannot transfer via a conditional byte bridge
> (§2.2), so it is RE-PROVEN directly over the fold — mechanical (identical block/opcode
> shape; `SegAlignedP.append` reused; only the leaf induction is redone) and provably
> **unconditional** (the fold is total: `foldl` over a finite list, undefined-tmp →
> `emitImm 0`, so `SegAligned` over the fold needs NO well-formedness). The old
> monolithic S1 ("delete `Expr.slot` + retype + remove fuel in one shot") is ATOMIC and
> is REPLACED by the green-incremental sequence in §4 (below), honoring obligations
> (a)-(e): rematOf spine-decouple → bridge + alignment + DefEnvOrdered adequacy →
> redefine-lower-over-fold + geometry re-proof → value/sim migration → delete old +
> shrink `IRWellFormed` LAST. Semantics (`Spec/Semantics.lean` execution relations)
> untouched except the removal of the now-dead `evalExpr .slot` arm.

---

## 1. The crux: is program order a valid topological order? — RESOLVED: YES

### 1.1 The static def-graph

`materialiseExpr`'s ONLY recursion is `.tmp t → defsOf prog t = some e → recurse e`
(`Lowering.lean:146-148`); binary ops already take `Tmp` operands (`IR.lean:75-95`), so
the IR is ANF-flat and the def-graph is exactly: node `t` with `defsOf prog t = some e`,
edge `t → t'` iff `t'` occurs in `e`.

Edges arise ONLY from `.remat` expressions carrying tmp references: `add a b`, `lt a b`,
`.tmp t'`, `sload k`. But `defsOf` (`Lowering.lean:262-272`) routes **every** gas / sload
/ call-result / create-result def to `.slot (slotOf t)` — a **leaf with no tmp
references**. After Phase 2A these become `Loc.slot n` (also a leaf). So the only
edge-bearing `defsOf` entries are pure `add`/`lt`/`tmp` (never `sload`, which is always
spilled). Verified on `exProg` (`Witness.lean:66-71`): of nine entries, only
`t8 ↦ lt t6 t7` bears edges.

### 1.2 Program order IS topological (grounded in the invariants)

Program order = the `blocks`-array-then-`stmts`-list `flatMap` order `defsOf` scans
(`Lowering.lean:263-264`). Claim: for a program satisfying `IRWellFormed`, every
edge-bearing entry `(t, e)` lists each tmp referenced in `e` at an *earlier* position.
Three facts, each grounded in code:

1. **Self-contained blocks (from `RunDefinableG`).** `RunDefinableG.stmts`
   (`WellFormed.lean:95-101`) quantifies the block-*entry* state `st` over **all**
   `IRState`, demanding `StmtDefinableG st' s` at every `st'` a prefix-run
   `RunStmts … (b.stmts.take pc) …` reaches. Because `st` is arbitrary (in particular
   empty-locals), an operand of the statement at `pc` can be guaranteed bound at `st'`
   only if the block *prefix* binds it — cross-block inflow cannot be relied on. Hence
   every operand tmp a statement uses is defined earlier **in the same block**, i.e.
   within-block statement order is a topological order of within-block dataflow. (The
   `pc = 0` case is the sharpest: the nil `RunStmts` forces `∃w, evalExpr st 0 e = some w`
   at arbitrary `st`, so a first statement's assign RHS must be closed — `imm`/`gas`/
   spilled — never a bare tmp/add at empty locals.) `exProg` obeys this exactly: every
   block's every used tmp is assigned earlier in that block (`Witness.lean:38-55`).

2. **Consistent redefinition (from `DefsConsistent`).** `defsOf` is a **first-find**
   over program order (`pairs.find?`, `Lowering.lean:272`; the docstring "the last assign"
   is a known misnomer, flagged in `DefsConsistent`'s own docstring `WellFormed.lean:120`).
   `DefsConsistent` (`WellFormed.lean:132-140`) forces every def-site of a tmp id to agree
   with `defsOf`'s registration, so cross-block re-uses of a tmp id register the *same*
   expression; no shadowing back-reference arises. Combined with (1), `defsOf t`'s
   operands are the operands of `t`'s *first* def, all defined earlier in that block, so
   their own first-defs sit at earlier program-order positions.

3. **CFG loops ≠ def-graph cycles.** A tmp has ONE static definition (`defsOf`
   first-find). A CFG back-edge re-executes the same defs; it adds no edge from a
   later-defined tmp to an earlier one. `exProg`'s block-1 self-loop
   (`branch t8 L2 L1`, `Witness.lean:53`) leaves the def-graph `t6,t7 → t8` acyclic and
   program-ordered. Confirmed: `Acyclic` is the def-graph rank (`Acyclic.lean:82`), a
   different notion from CFG acyclicity, which was already retired by the dynamic
   `totalGas` measure (decision D7).

**Decision: program-order-valid. No explicit topo-sort inside `lower`.** The def-env is
the program-order pairs list carrying `Loc`. This is exactly the shape `defsOf` already
builds; we do not sort.

### 1.3 How to *land* the topo fact: carry it, don't prove it dynamically

The §1.2 derivation from `RunDefinableG` is TRUE but its Lean proof needs a
run-construction argument (from an operand *not* bound in the prefix, build a valid
prefix-run leaving it unbound → contradiction). That is avoidable and not worth it.

Instead, make topo-ness a **decidable static field** of `IRWellFormed`, replacing
`acyclicDefs`:

```lean
/-- The program-order def-env is a valid ordered list: each remat entry references only
    tmps that appear earlier in the list. Decidable per program; strictly implies the
    old `Acyclic (defsOf prog) _` (a topo order is acyclic). -/
def DefEnvOrdered (prog : Program) : Prop := <"each entry refs only earlier entries">
```

This is what the master plan (item 3) anticipates: `acyclicDefs`/`noSlotSource`
"disappear (subsumed by 'the def-env is a valid ordered list')". It is a **net
simplification** of `acyclicDefs : ∃ rank, Acyclic ∧ ∀t, rank t + 1 < recomputeFuel`
(`WellFormed.lean:360-361`): no existential rank, no fuel-fitting side-condition (there
is no fuel). It is discharged for `exProg` by `decide`/`rfl` (mirroring
`acyclic_exProg`). The §1.2 argument is recorded as the *justification* that
`DefEnvOrdered` is not a new real restriction — it is exactly define-before-use SSA.

---

## 2. Byte-preservation — ACHIEVABLE, but conditional (this is the load-bearing risk)

### 2.1 The unconditional/conditional split (verified against code)

`flatBytes prog` (`DecodeLower.lean:46-50`) — and therefore `lower prog` via
`lower_eq_flatBytes` (`:61`) — is defined **unconditionally** in terms of
`materialiseExpr (defsOf prog) (recomputeFuel prog)`. Two consumer classes sit on it:

- **Geometry / decode tower — UNCONDITIONAL.** `segAlignedP_flatBytes prog`
  (`SegAligned.lean:416`, no well-formedness hyp), the decode anchors
  (`DecodeAnchors.lean:193-298`), `block_offset_validJump` (`JumpValid.lean:223`, only
  `L.idx < size`). These hold even for ill-formed programs because the fuel-garbage
  cases (`[]` on exhaustion, `PUSH32 0` on undefined tmp) are *themselves* seg-aligned.
  The single fuel-inducting lemma is `segAlignedP_materialiseExpr` (`SegAligned.lean:236`,
  `induction fuel generalizing e`); everything else composes it with `SegAlignedP.append`.

- **Sim / value tower — CONDITIONAL on well-formedness.** `MatDec`/`MatRuns`/`sim_*`
  carry `MatFueled` (`MatDecLower.lean:262`) and the pc/stack bounds, so they already
  hold only under `WellFormedLowered`/`WellLowered`.

### 2.2 Why the bridge is conditional (and why unconditional is impossible)

A fold-with-cache differs from fuel-recursion on **ill-formed** inputs: for a cyclic
`t := add t t` (`recomputeFuel = 2`), the fuel recursion bottoms out to specific garbage
bytes, while the fold hits a cache-miss and emits its fallback. So
`lowerNew prog = lower prog` is **false unconditionally** and can only be proved
**conditional on `DefEnvOrdered` (+ completeness)**. This is fine — byte-for-byte is
required only "for well-formed programs" (task statement) — but it has a consequence:

**The unconditional geometry tower does NOT transfer by rewriting `lowerNew = lower`.** It
must be **re-proven over the new emission** (staying unconditional in well-formedness).
This is mechanical: the new emission keeps the identical per-block `JUMPDEST :: body`
shape and identical opcode templates/operand order; only the leaf recursion changes
(`segAlignedP_materialiseExpr` → `segAlignedP_matExpr` by list/cache induction), and the
compositional `append` lemmas are reused verbatim. But it is real work, and it is the
part the "facts survive" framing understates.

### 2.3 The bridge lemma (sketch)

Let `defEnv prog : List (Tmp × Loc)` be the program-order pairs (carrying `Loc`), and
`matCache prog : Tmp → List UInt8` the left-fold result (each entry's bytes computed from
`Loc.remat e` by resolving operand tmps against the cache built so far, or from
`Loc.slot n ↦ emitImm (ofNat n) ++ [MLOAD]`). Then:

> **`matCache_eq_materialiseExpr`** — under `DefEnvOrdered prog` (topo) and the def-env
> covering every referenced tmp, for every `t` present in `defEnv prog`:
> `matCache prog t = materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)`.

Proof shape: induction along the topo-ordered def-env. For entry `(t, .remat e)`, the
cache already holds every operand tmp `t'` of `e` (topo), and by IH each equals its
`materialiseExpr` value; the fold's byte assembly for `e` matches `materialiseExpr`'s
constructor arms (`add`/`lt` reverse-operand order, `sload k`, `imm`, `gas`) by the
existing reduction lemmas (`materialiseExpr_tmp_some` `Lowering`-side, `chargeOf_*`
analogues). Fuel-sufficiency `recomputeFuel ≥ topo-depth` is exactly what
`acyclicDefs`/`MatFueled` asserted today, now subsumed by `DefEnvOrdered` + list length.
For `(t, .slot n)`: both sides are `emitImm (ofNat n) ++ [MLOAD]` (the `Expr.slot` arm
`Lowering.lean:144` = the new inline slot arm), definitional.

From this, `flatBytesNew prog = flatBytes prog` and `lowerNew prog = lower prog`
(conditional), so the CONDITIONAL sim tower transfers by rewrite; the UNCONDITIONAL
geometry tower is re-proven over `flatBytesNew` (§2.2).

### 2.4 `Expr.slot` removal is separately byte-UNCONDITIONALLY preserving

Removing `Expr.slot` and retyping `materialiseExpr` to consume `Alloc = Tmp → Option Loc`
(with the `.tmp t` arm doing `match a t with .remat e => recurse | .slot n => emitImm ..
++ [MLOAD]`) produces **byte-identical output on ALL programs, keeping fuel** — because
old `materialiseExpr defs fuel (.tmp t)` with `defs t = .slot n` already emits
`emitImm (ofNat n) ++ [MLOAD]` (`Lowering.lean:144`). So this half can land FIRST, with an
*unconditional* bridge (or definitional equality), de-risking the fuel→fold half.

---

## 3. Final shapes

### 3.1 `Loc`, `Alloc`, def-env

`Loc` (`Lowering.lean:94-99`) is kept: `| remat (e : Expr) | slot (n : Nat)`.
`Alloc := Tmp → Option Loc` (`:103`) is kept. **Deleted**: `Loc.toDef`/`Alloc.toDefs`
(`:107-113`) and `allocate_toDefs` (their only consumers are `DecodeLower`/`LoweringLemmas`,
which fold into this retype). `defsOf : Program → Alloc` now returns `Loc` directly (oracle
temps ↦ `Loc.slot (slotOf t)`, pure ↦ `Loc.remat e`) — `allocate`/`locOfExpr` collapse into it.

Def-env: `def defEnv (prog) : List (Tmp × Loc)` = the program-order `pairs` list `defsOf`
already builds internally (no sort). `defsOf` becomes its `find?`-view. Both keep the same
value; `defEnv` is the ordered carrier the fold walks.

### 3.2 Fold-based materialise (no fuel)

```lean
def matExpr (cache : Tmp → List UInt8) : Expr → List UInt8
  | .imm w   => emitImm w
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [Byte.add]
  | .lt  a b => cache b ++ cache a ++ [Byte.lt]
  | .sload k => cache k ++ [Byte.sload]
  | .gas     => [Byte.gas]
  -- no .slot arm (Expr.slot deleted)

def matLoc (cache) : Loc → List UInt8
  | .remat e => matExpr cache e
  | .slot n  => emitImm (UInt256.ofNat n) ++ [Byte.mload]

def matCache (prog) : Tmp → List UInt8 :=            -- structural left-fold over defEnv
  (defEnv prog).foldl (fun c (t, loc) => Function.update c t (matLoc c loc))
                      (fun _ => emitImm 0)            -- undefined-tmp fallback (= old `none` leaf)

def materialise (prog) (t : Tmp) : List UInt8 := matCache prog t
```

`materialiseExpr` at use sites (sstore key/value, ret operand, branch cond, call/create
args) becomes `matExpr (matCache prog) (.tmp _)` = `matCache prog _`. Structural
termination: `foldl` over a finite list; no fuel, no rank, no `MatFueled`.

### 3.3 `MatDec` / `chargeOf` retype

Both lose `fuel` and the `.slot` arm; both take the `matCache`/`defEnv` view. `MatDec`
(`MaterialiseRuns.lean:237`) becomes structural over the def-env / `Expr` shape; `chargeOf`
(`MaterialiseGas.lean:73`) likewise. Their **conclusions are unchanged** (decode-fact
bundle; per-opcode gas list). `MatFueled` (`MatDecLower.lean:262`) and its lemmas
(`matFueled_tmp_some/none`) are **deleted**. `recomputeFuel` (`Lowering.lean:164`) deleted.

### 3.4 Shrunk `IRWellFormed` (`WellFormed.lean:344`)

| field | disposition |
|---|---|
| `defineBeforeUse : RunDefinableG` | keep |
| `defsConsistent : DefsConsistent` | keep |
| `entry0` | keep |
| `cfgClosed` | keep |
| `acyclicDefs : ∃ rank, Acyclic ∧ rank_lt_fuel` | **replace** with `defEnvOrdered : DefEnvOrdered prog` (§1.3) |
| `revalidates : RevalidatesPerBlock` | keep |
| `noSlotSource : NoSlotSource` | **delete** (`Expr.slot` gone ⇒ impossible by construction; `NoSlotSource` def `:283` deleted) |
| `slotAddr` | keep |

Final `IRWellFormed` field list: `defineBeforeUse, defsConsistent, entry0, cfgClosed,
defEnvOrdered, revalidates, slotAddr`.

`WellFormedLowered` (`LowerConforms.lean:148`): the four `MatFueled` fields
(`matFueled_sstore/sload/ret/branch`, `:150-183`) are **deleted** (structural termination
⇒ no fuel-sufficiency obligation). The `bound_*` fields + `slots_slot` stay, restated over
the new emission-length function (drop the `recomputeFuel`/`Expr.slot` arguments).
`Acyclic.lean` (`AcyclicWellFormed`, `matFueled_of_acyclic`, `wellFormedLowered_of_acyclic`)
is deleted or reduced to the `bound_*` carrier; `ExprRankLt`/`Acyclic`/`matFueled_of_exprRankLt`
lose their consumer and go.

---

## 4. Green-incremental step sequence (FULL PURGE — corrected 2026-07-07)

S0 has LANDED (commit `f364dde`): `defEnv`, `matExpr`/`matLoc`/`matStep`/`matFold`/
`matCache`, the reduction lemmas, and `DefEnvOrdered` (`WellFormed.lean:296`) exist
ALONGSIDE the old machinery, green, wired into nothing. The sequence below BUILDS ON
THESE. Ordering principle (sound, non-atomic): decouple the soundness spine from
`defsOf`'s codomain FIRST (so the later `defsOf → Alloc` retype does not churn spine
statements), prove the bridge/alignment/adequacy lemmas ALONGSIDE the old, then swap
`lower`/`emit` to the fold, migrate the value/sim tower via the bridge, and delete the
old machinery + shrink `IRWellFormed` LAST. Each step is a landable green commit
(`lake build` = the `LirLean` cone green + sorry-free; `lake build WIP` keeps ONLY its
pre-existing tracked sorries). NO monolithic delete-everything step.

Obligations (a)-(e) map onto the steps as annotated.

- **S1 — (a) `rematOf` spine-decouple.** Introduce `rematOf : Program → Tmp → Option Expr`,
  the **non-slot projection** of `defsOf` (`rematOf prog t = match defsOf prog t with
  | some (.slot _) => none | some e => some e | none => none`; once `defsOf` is Loc-valued
  it re-bases to `some (.remat e) => some e | _ => none`, same value). Migrate the
  soundness spine — `DefsSound` (`DefsSound.lean:209`), the `DefsConsistent` recompute arm
  (`WellFormed.lean:135`), `DefsSoundS`/`ReadsOf`/`StepScopedS` (`WellFormed.lean:181-256`),
  and the `defsSound_preserved_*` walk (`DefsSound.lean:301-655`) — from `defsOf t = some e`
  onto `rematOf t = some e`. Provide the `rematOf` twins of the spill-routing exhaustiveness
  facts (`rematOf_ne_gas`/`rematOf_ne_sload`, replacing `defsOf_ne_gas`/`_ne_sload` at their
  spine consumers: `Machinery.lean:166/172/206`, `Producer.lean:792/796`,
  `MaterialiseCleanHalt.lean:195/198`, `MaterialiseRuns.lean:1110/1115`). Behaviour-preserving
  (`rematOf`-view is a sound weakening: `evalExpr st 0 (.slot n) = none`, so `defsOf`-view
  never made a satisfiable claim at a slot entry with a bound tmp). `Expr.slot` and `fuel`
  still exist. Green gate: `lake build` green; `WIP` pre-existing sorries only.

- **S2 — (c) `defEnv ↔ defsOf` alignment.** Prove `defsOf` is `defEnv`'s `find?`-view:
  `defsOf prog t = ((defEnv prog).find? (·.1 == t)).map (Loc.toDef ∘ ·.2)` (definitional —
  same `filterMap`/order). CRUX: `defEnv` is NOT deduplicated (one entry per assign / call /
  create-result stmt), `matCache` is a `Function.update` fold so it takes the **last** entry,
  while `defsOf`/`find?` take the **first**; they agree ONLY under SSA single-binding. PROVE
  `matCache prog t = matLoc (…) (first-find entry for t)` from `DefsConsistent` (all entries
  for a tmp id carry the same `Loc`, so last = first). Green: alignment lemmas green,
  alongside old.

- **S3 — (b) the fold↔fuel byte bridge (BRIDGE-FIRST).** Prove, under `DefEnvOrdered prog`
  (+ the S2 alignment): `matCache prog t = materialiseExpr (defsOf prog) (recomputeFuel prog)
  (.tmp t)` for every `t` (present → induction along the topo-ordered `defEnv`, operands
  resolved earlier in the fold equal their `materialiseExpr` by IH; absent → both sides are
  the `emitImm 0` fallback), hence `matExpr (matCache prog) e = materialiseExpr (defsOf prog)
  (recomputeFuel prog) e`; the `.slot`/`Loc.slot` arm is definitionally the same
  `emitImm (ofNat n) ++ [MLOAD]`; fuel-sufficiency is subsumed by `defEnv` length. Derive the
  `matCache = materialise` corollary and, from it, the byte corollary `flatBytesFold prog =
  flatBytes prog` (with `flatBytesFold`/`emitFold`/`lowerFold` the fold-based twins introduced
  here). Green gate: bridge + corollaries green, no new sorry.

- **S4 — (d) `DefEnvOrdered` adequacy.** Prove `DefEnvOrdered exProg` by `decide`/`rfl`
  (mirrors `acyclic_exProg`, `Witness.lean:363`; non-vacuity witness). Prove
  `defEnvOrdered_subsumes_acyclic : DefEnvOrdered prog → ∃ rank, Lir.Acyclic (defsOf prog)
  rank` with `rank t := 2 * (first-index of t in defEnv prog)` (so an operand at earlier
  index `j < i` gives `rank · + 1 = 2j+1 < 2i = rank t`, the strict-by-2 `ExprRankLt` needs;
  the `.gas`/`.sload` `ExprRankLt` arms never fire because `defsOf` routes them to `.slot`
  — discharged by `rematOf_ne_gas`/`_ne_sload`; `.imm`/`.slot` arms are `True`). This GATES
  the later `acyclicDefs → defEnvOrdered` swap: `DefEnvOrdered` genuinely subsumes the
  `Acyclic` content. Green.

- **S5 — (e.i) fold-emit twins + geometry re-proof (UNCONDITIONAL), alongside old.**
  Re-prove the whole geometry tower over `flatBytesFold`/`lowerFold` (new lemma names):
  `segAlignedP_matExpr` / `segAlignedP_matCache` by a `matFold` INVARIANT induction ("every
  value the cache returns is `SegAlignedP IsLoweringOp`" — the `emitImm 0` init is aligned,
  and `matStep` preserves it: `matLoc` is either `matExpr c e` (aligned by the fold IH on
  operand caches) or the slot-load `segAlignedP_slot`); then `SegAligned` per-block +
  `flatBytes`, `DecodeAnchors`, `JumpValid`, `Layout`, `BoundaryReach` by REUSING
  `SegAlignedP.append` verbatim over the identical `JUMPDEST :: body` block shape. NO
  well-formedness hyp anywhere (the fold is total). Green: new geometry green; old still
  consumed.

- **S6 — (e.ii) charge-fold twin + its bridge.** Introduce `chargeCache`/`chargeFold` (the
  gas-list twin of `matCache`, structurally identical fold over `defEnv`) and its bridge
  `chargeCache prog t = chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)` under
  `DefEnvOrdered` + S2 alignment (mirrors S3). Re-establish the length-lockstep
  `(chargeCache prog t).length`-vs-`(matCache prog t).length` the `StackRoomOK`/
  `maxChargeDepth` folds read. Green: charge twins green, alongside old.

- **S7 — (e.iii) migrate the value/sim tower onto the fold (via the S3/S6 bridges).**
  RESTATE `MatDec`/`MatRuns`/`chargeOf`-consuming lemmas over `matCache`/`chargeCache`
  (fuel-free), proving each via the bridge + the existing proof: `MaterialiseGas`,
  `MatDecLower`, `MaterialiseRuns`, `StashTail`, `CleanHaltExtract`,
  `MaterialiseCleanHalt`, then `Sim/SimStmt`, `Sim/SimTerm`, `Sim/SimStmts`, then the WIP
  `Assembly/LowerDecode`, `Assembly/LowerConforms`, `Spec/BudgetDerivations`,
  `V2/Drive/DriveSim`, and the WIP `Surface`/`Machinery`/`Producer`/`Witness` instantiations
  (their `chargeOf (defsOf prog) … (recomputeFuel prog - 1)` / `MatRuns (defsOf prog) …`
  become `chargeCache`/`matCache`; the `defsOf prog t = some (.slot …)` patterns are
  UNCHANGED once `defsOf` is Loc-valued — same `.slot` constructor). Statement CONCLUSIONS
  unchanged; this is signature/threading. Land per file-group, each green
  (`WIP` pre-existing sorries only). **This is the bulk and the producer-coupled surface —
  the branch is quiescent, which is why this window is safe.**

- **S8 — (e.iv) swap definitions + `defsOf → Alloc` retype.** Redefine `lower`/`flatBytes`/
  `emit` to the fold versions (rename `*Fold` → canonical, redirect the geometry consumers
  from the old lemma names to the re-proven ones); retype `defsOf : Program → Alloc`
  (returns `Loc` directly, oracle/spilled temps ↦ `Loc.slot (slotOf t)`, pure ↦
  `Loc.remat e`); re-base `rematOf` off the new `defsOf`; retype the `DefsConsistent` slot
  arm / `ReadsOf` / `StepScopedS` / `invalStep` / `DefsSoundS` / `slots_slot` residual
  `defsOf`-references to `Loc` (`.slot`/`.remat` — minimal textual churn: the spine already
  reads `rematOf`). Green gate: full `lake build` green; `#print axioms` guards intact.

- **S9 — (e.iv cont.) shrink `IRWellFormed` / `WellFormedLowered` / `WellLowered` + flagship.**
  `IRWellFormed` (`WellFormed.lean:359`): replace `acyclicDefs` with `defEnvOrdered :
  DefEnvOrdered prog` (wired via S4 subsumption where a consumer still needs `Acyclic`), drop
  `noSlotSource`. `WellFormedLowered` (`LowerConforms.lean:148`): drop the four `MatFueled`
  fields (`matFueled_sstore/sload/ret/branch`), restate `bound_sstore/sload/ret/stop/jump/
  branch` + `slots_slot` fuel-free (`materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp
  ·)` → `matCache prog ·`; `offsetTable (defsOf) (recomputeFuel)` → the fold offset table).
  `WellLowered` (`Surface.lean:149`): drop `noSlotSource` (`:198`). Rewrite
  `wellFormedLowered_of_IRWellFormed` (`RealisabilitySpec.lean:124-161`): drop the
  `obtain ⟨rank,…⟩ := hwf.acyclicDefs` / `matFueled_of_acyclic` / `slots_slot_of_noSlotSource`
  lines. Update the `exProg` witness (`Witness.lean:363-705`): `defEnvOrdered_exProg` by
  `decide`; drop `acyclic_exProg`/`acyclicWellFormedExProg`/`noSlotSource_exProg`. Green gate:
  `WIP` green, ONLY pre-existing sorries; `exProg` witness green.

- **S10 — (e.iv cont.) delete the orphaned old machinery.** With all consumers migrated,
  DELETE: `Expr.slot` (`IR.lean:94`) + `evalExpr .slot` arm (`Semantics.lean:147`, `evalExpr`
  becomes total-and-pure) + every dead `.slot` arm (`usesInExpr`,
  `evalExpr_setLocal_of_unused`/`_setStorage_of_noSload`/`_world_irrel_of_noSload`,
  `defsSound_preserved`'s `| slot n =>` case, `matExpr`'s `.slot` arm, `matExpr_slot`,
  `ExprRankLt .slot`, `MatFueled .slot`); `materialiseExpr` + `materialise` + `recomputeFuel`
  (`Lowering.lean:142-165`); `MatFueled` + `matFueled_tmp_some/none` (`MatDecLower.lean:262`);
  `Assembly/Acyclic.lean` whole (`ExprRankLt`/`Acyclic`/`AcyclicWellFormed`/
  `matFueled_of_exprRankLt`/`matFueled_tmp_of_acyclic`/`wellFormedLowered_of_acyclic`) + the
  now-orphaned S4 subsumption lemma; `Loc.toDef`/`Alloc.toDefs`/`allocate`/`locOfExpr`
  (`Lowering.lean:107-113,285-291`, byte path is `defEnv`-native) + `allocate_toDefs`/
  `toDef_locOfExpr` (`LoweringLemmas.lean`); `NoSlotSource` (`WellFormed.lean:283`). Green
  gate: full `lake build` green + sorry-free; `WIP` pre-existing sorries only; `#print axioms`
  guards intact.

If S5's unconditional geometry re-proof over the fold proves heavier than budgeted, it may
be split per geometry file (SegAligned → DecodeAnchors → JumpValid → Layout → BoundaryReach),
each a green sub-commit — but it must NOT be folded into the S8 definition-swap (a rewrite
`lowerFold = lower` that cannot hold unconditionally would strand the geometry tower).

---

## 5. Retype ripple (full surface — executors must expect all of it)

Files touching `materialiseExpr`/`MatDec`/`MatFueled`/`recomputeFuel` (verified by grep,
counts = mentions): `Assembly/LowerDecode.lean` (128), `Materialise/MatDecLower.lean`
(107), `Materialise/MaterialiseRuns.lean` (98), `Spec/BudgetDerivations.lean` (87),
`Assembly/LowerConforms.lean` (75), `V2/Realisability/Machinery.lean` (42),
`V2/Realisability/Producer.lean` (41), `Assembly/Acyclic.lean` (40, mostly DELETED),
`Decode/DecodeAnchors.lean` (37), `V2/Realisability/Surface.lean` (29), `Sim/SimStmt.lean`
(27), `Sim/SimTerm.lean` (23), `Decode/SegAligned.lean` (21), `Decode/Layout.lean` (20),
`Decode/JumpValid.lean` (19), `Materialise/MaterialiseGas.lean` (15),
`Materialise/MaterialiseCleanHalt.lean` (15), `Spec/WellFormed.lean` (14),
`Spec/Lowering.lean` (9), `Materialise/{StashTail,DefsSound,CleanHaltExtract}.lean`,
`Sim/SimStmts.lean`, `V2/Drive/DriveSim.lean`, `Decode/DecodeLower.lean`,
`V2/Realisability/Witness.lean`.

`Expr.slot` dead-arm removal spans 24 files (grep `.slot`): incl.
`Spec/{IR,Semantics,Lowering,WellFormed,BudgetDerivations}.lean`, `Frame/SmallStep.lean`,
`Decode/{SegAligned,LoweringLemmas}.lean`, all `Materialise/*`, `Sim/*`, and the WIP
`V2/Realisability/*` + `V2/Drive/Headline.lean`.

Specific derived-lemma casualties/rewrites:
- `WellFormedLowered.matFueled_{sstore,sload,ret,branch}` (`LowerConforms.lean:150-183`) — deleted.
- `matFueled_of_acyclic`, `AcyclicWellFormed`, `wellFormedLowered_of_acyclic`,
  `matFueled_of_exprRankLt`, `ExprRankLt`, `Acyclic` (`Assembly/Acyclic.lean`) — deleted
  (only consumers were the deleted headlines + `wellFormedLowered_of_IRWellFormed`).
- `wellFormedLowered_of_IRWellFormed` (`RealisabilitySpec.lean:124-161`) — drop the
  `acyclicDefs`/`matFueled`/`noSlotSource` derivations.
- `Decode/LoweringLemmas.lean` (`allocate_toDefs`, `defsOf_ne_gas`/`_ne_sload`) — shrinks
  or vanishes (master plan #5 folds in here, per its own note).
- Producer sim-lemma instantiations (`Producer.lean`, `Machinery.lean`) threading
  `MatDec`/`fuel` — re-threaded to the fold; conclusions unchanged.
- Witness: `acyclic_exProg`/`acyclicWellFormedExProg`/`noSlotSource_exProg`
  (`Witness.lean:642-705`) → replaced by `defEnvOrdered_exProg` (`decide`).

---

## 6. Risks

1. **Unconditional geometry re-proof (highest).** `flatBytes`/geometry are unconditional
   on the fuel emission; new ≠ old on ill-formed inputs ⇒ the tower cannot transfer by
   rewrite and must be re-proven over the fold (S2). Mechanical (same block/opcode shape,
   `append` lemmas reused) but real; the "facts survive by byte-identity" framing hides it.
2. **Scale + producer coupling.** ~25 files, incl. the producer's sim-lemma
   instantiations (`Producer.lean`/`Machinery.lean`). Must run producer-quiescent (branch
   is stated quiescent). Any concurrent producer edit to the value channel invalidates S4/S6.
3. **`DefEnvOrdered` discharge for `exProg`.** Must reduce by `decide`/`rfl` like
   `acyclic_exProg`; if the def-env's `find?`/order does not compute cleanly, a manual
   proof is needed (low, given `defsOf_exProg_eq` already reduces by `rfl`).
4. **`matCache` fold definitional friction.** `Function.update`-based cache may not
   `simp`-reduce as cleanly as the old `match defs t`; the reduction lemmas
   (`matExpr_tmp`, `matCache_cons`) must be supplied to keep S3/S4 proofs mechanical.
5. **`chargeOf` gas envelopes.** `chargeOf` length must stay in lockstep with the new
   `matExpr` (the `StackRoomOK`/`maxChargeDepth` folds in `WellFormed.lean:296-334` read
   its length); re-establish the length-lockstep lemma before S4.
