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

## 4. Green-incremental step sequence (expand-contract where feasible)

Ordering principle: land `Expr.slot`→`Loc` FIRST (byte-unconditional, §2.4), then the
fuel→fold swap (byte-conditional). Each step builds green (`lake build` + `WIP`).

- **S0 — def-env carrier + fold, alongside old.** Add `defEnv`, `matExpr`/`matLoc`/
  `matCache`, `DefEnvOrdered` in `Spec/Lowering.lean`/`Spec/WellFormed.lean`. Do NOT touch
  `materialiseExpr`/`lower` yet. Green: builds; no consumer changed.
- **S1 — `Expr.slot` → `Loc` retype (fuel KEPT).** Retype `materialiseExpr`/`MatDec`/
  `chargeOf`/`MatFueled` from `defs : Tmp → Option Expr` to `Alloc`; move the slot-load to
  the `.tmp` lookup arm; delete `Expr.slot` (`IR.lean:94`), `evalExpr .slot` arm
  (`Semantics.lean:147`), `Loc.toDef`/`Alloc.toDefs` (`Lowering.lean:107-113`), and every
  `.slot` dead arm (24 files). Bridge `lower' = lower` is definitional/unconditional.
  Green gate: `lake build` byte facts unchanged (spot-check `lower_eq_flatBytes`,
  `segAlignedP_flatBytes` still hold); `WIP` only pre-existing sorries.
- **S2 — geometry tower over the fold, alongside old.** Introduce `flatBytesNew`/
  `emitNew` on `matCache`; re-prove `segAlignedP_matExpr` + anchors + `JumpValid`/`Layout`
  for the new emission (UNCONDITIONAL). Green: new lemmas green; old still consumed.
- **S3 — byte-equality bridge.** Prove `matCache_eq_materialiseExpr` (§2.3) under
  `DefEnvOrdered`, hence `lowerNew prog = lower prog` conditional. Green gate: the bridge
  lemma green, no new sorry.
- **S4 — migrate `MatDec`/`MatRuns`/`chargeOf` + `Sim/` to the fold.** Retype to the
  fuel-free forms; transfer conditional sim facts via S3 bridge. Green gate: `Sim/`,
  `Materialise/` green; conclusions identical.
- **S5 — swap `lower`/`flatBytes` to the fold; delete old + fuel.** Redefine `lower`/
  `flatBytes` = the `New` versions; delete `materialiseExpr`-fuel, `recomputeFuel`,
  `MatFueled`, `Acyclic`/`ExprRankLt`/`matFueled_of_*`, `AcyclicWellFormed`. Green gate:
  full `lake build` green + sorry-free; `#print axioms` guards intact.
- **S6 — shrink `IRWellFormed`/`WellFormedLowered` + producer/flagship.** Swap
  `acyclicDefs`→`defEnvOrdered`, drop `noSlotSource`, drop the four `MatFueled` fields;
  rewrite `wellFormedLowered_of_IRWellFormed` (`RealisabilitySpec.lean:124-161`, drop the
  `obtain ⟨rank,…⟩`/`matFueled_of_acyclic`/`slots_slot_of_noSlotSource` lines); update
  `exProg` witness (`Witness.lean:472-705`, `decide` the new field). Green gate: `WIP`
  green with only pre-existing sorries; `exProg` witness green.

If S2's unconditional re-proof of geometry proves heavier than budgeted, S2+S5 may be
merged into one atomic emission-swap (re-prove geometry directly on the swapped `lower`),
accepting a larger single step — call this out rather than gate on a rewrite that cannot
hold unconditionally.

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
