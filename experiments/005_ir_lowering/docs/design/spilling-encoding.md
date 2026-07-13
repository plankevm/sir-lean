# Spilling encoding: is `Expr.slot` a design smell?

> **P9 status note (2026-07-08).** The recommendation in this note has landed: `Expr.slot`,
> `Loc.toDef`/`Alloc.toDefs`, legacy fuel materialisation, `MatFueled`,
> `Assembly/Acyclic.lean`, and `NoSlotSource` have been deleted. The body is kept as design
> provenance.

*exp005 LirLean IR→EVM lowering-conformance — design analysis, 2026-07-06*

## The objection

`Expr` (`Spec/IR.lean:75`) carries a constructor `Expr.slot (slot : Nat)` (`:94`) that
is deliberately **not evaluable**: all three `evalExpr` copies return `none` for it
(`Spec/Semantics.lean:147`, `Frame/SmallStep.lean:93`, and the v1 line). The lead's
charge: a value-AST node you cannot evaluate makes `evalExpr` partial-on-purpose and
forces every `Expr` consumer to carry a "can't happen" case, conflating (a) genuine IR
value-expressions with (b) a lowering-level *reconstruction directive* ("this temp is
spilled to memory slot n; MLOAD it").

Verdict up front: **the objection is correct.** `Expr.slot` is a real smell, and the
codebase already contains the principled replacement (`Loc`) — it simply isn't the
authority. Details, then a dated recommendation (defer, with reasons).

## 1. What `Expr.slot` actually does

It is a **def-env-only reconstruction directive**, never an expression.

- `defsOf : Tmp → Option Expr` (`Spec/Lowering.lean:262-272`) scans every `assign`
  program-globally and routes the **three non-recomputable definers** to
  `Expr.slot (slotOf t)`: `assign t .gas` (`:266`), `assign t (.sload _)` (`:267`), a
  CALL result `call ⟨_,_,some t⟩` (`:269`), and a CREATE result (`:270`). Every pure
  assign keeps its own expression.
- `materialiseExpr` (`:142-156`) treats `.slot slot` as a **leaf**:
  `emitImm (ofNat slot) ++ [MLOAD]` (`:144`) — a load-from-memory, not a computation.
- `emitStmt .assign` (`:187-190`) matches `some (.slot n)` to emit the **def-site
  stash** `materialise(e) ++ PUSH n ++ MSTORE` (compute-once), and emits nothing for a
  rematerialised tmp.

So `.slot` is a whole-temp placement fact wearing an `Expr` costume. It never carries a
value; `evalExpr .slot = none` is not a partial function that happens to be undefined
here — it is a category error made total by `Option`.

## 2. `Expr.slot` is redundant with `Loc.slot` — proven so

This is the decisive finding. The codebase **already** has the clean two-answer
placement type:

```
inductive Loc | remat (e : Expr) | slot (n : Nat)      -- Spec/Lowering.lean:94-99
abbrev Alloc := Tmp → Option Loc                        -- :103
```

`Loc` *is* exactly the `DefSource := recompute Expr | spill Slot` that alternative (i)
proposes. But instead of being the authority, it is flattened **back into `Expr`** so
the pre-existing byte mechanism doesn't have to change its type:

- `locOfExpr : Expr → Loc` (`:285-286`) splits `.slot n ↦ .slot n`, else `.remat e`.
- `Loc.toDef : Loc → Expr` (`:107-109`) flattens back `.slot n ↦ .slot n`,
  `.remat e ↦ e`.
- `Alloc.toDefs a := fun t => (a t).map Loc.toDef` (`:113`) re-presents an `Alloc` as
  the `Tmp → Option Expr` env the mechanism consumes.

And the two encodings are **proven mutually inverse**:
`toDef_locOfExpr : (locOfExpr e).toDef = e` (`Decode/LoweringLemmas.lean:99`) and
`allocate_toDefs : (allocate prog).toDefs = defsOf prog` (`:105`). `allocate` (`:291`)
is literally `(defsOf prog ·).map locOfExpr`.

So `defsOf : Tmp → Option Expr` and `allocate : Tmp → Option Loc` are **two round-trip
equivalent encodings of one fact**, and the only reason `Expr.slot` exists is to be the
flattening target of `Loc.slot` so that `materialiseExpr : (Tmp → Option Expr) → … →
Expr → …` keeps its signature. The principled layer is already built and green; it is
just not wired as the single authority.

## 3. Is there any *other* reason `.slot` must live in `Expr`? No.

`.slot` is **never a genuine sub-expression**. The binary/unary ops take `Tmp`
operands, not nested `Expr`: `add (a b : Tmp)`, `lt (a b : Tmp)`, `sload (key : Tmp)`
(`Spec/IR.lean:81-85`). Hence every `Expr` subterm is a `Tmp` or an `imm`; a `.slot`
can only ever appear as a whole-temp def value emitted by `defsOf`/`Loc.toDef`. There is
no structural obligation for it to be an `Expr` constructor. The lead's diagnosis of the
actual reason — "the def-env needs a non-recomputable case, so `Expr` was reused as the
def-env codomain" — is exactly right, and is redundant given `Loc`.

## 4. The tax the smell predicts is present

The objection predicts a "can't happen" case rippling through consumers. It is there:

- **`WellFormedLowered.noSlotSource`** (`Realisability/Surface.lean:450-451`): a
  static, decidable, "vacuous for real IR" field asserting no source
  `assign t (.slot n)` exists. This is the pure-tax obligation.
- **`slots_slot`** invariant (`Assembly/Acyclic.lean:197`,
  `CfgSim/LowerConforms.lean:210`, `Sim/SimStmt.lean:626`…): every registered
  `.slot`-def has slot `= slotOf t`.
- Sim proofs carry `.slot` arms discharged by `evalExpr .slot = none`
  (`Materialise/MaterialiseRuns.lean:811-825`, `:1071-1087`;
  `Materialise/MaterialiseCleanHalt.lean:121-190`), and the pure-assign arm must
  everywhere exclude `∃ n, defsOf t = some (.slot n)` (dozens of hypotheses of the form
  `¬ NonRecomputable ∨ ∃ slot, defsOf = some (.slot slot)`).

## 5. Principled encoding & prior art

Mature verified compilers keep the value language pure and put placement in a **separate
location environment** consulted by the backend; allocation is a *refinement*, not an
AST extension:

- **CompCert**: `Locations.loc = R mreg | S slot …`; register allocation
  (LTL/Linear/Mach) threads a `Locmap`/location environment. The RTL/Cminor *expression*
  language never gains a "this is spilled" constructor; the code generator reads the
  allocation to decide reload-from-stack vs recompute. `Loc` here is precisely
  CompCert's `loc`.
- **CakeML**: `dataLang → wordLang` carries a store-position map (`sptree`) outside the
  value language; spilling is a pass over that map.

The fix that fits **this** codebase is alternatives (i)+(ii) merged (they collapse to the
same edit, because `Loc` already exists): **make `Alloc`/`Loc` the single placement
authority and delete `Expr.slot`.** Concretely — retype the mechanism to consume the
`Alloc` (or a `DefSource := recompute Expr | spill Slot`, i.e. rename `Loc`); in
`materialiseExpr`'s `.tmp t` case, consult `a t : Option Loc` and emit `PUSH; MLOAD` for
`.slot n`, recurse into `e` for `.remat e`; then delete `Expr.slot`, `Loc.toDef`,
`Alloc.toDefs`, the `evalExpr` slot arm, and `noSlotSource`. `evalExpr` becomes total
(modulo undefined-tmp) and pure.

Alternative (iii) — a separate post-alloc IR — is **overkill** here: it duplicates the
whole AST for no gain over the `Loc` env that is already present.

## 6. Cost, blast radius, and — crucially — does it help the blocker?

**Blast radius: large but mechanical, and entirely inside GREEN static machinery.** ~100
call sites match `defsOf … = some (.slot …)` (Sim/*, Materialise/*, Decode/*, CfgSim/*,
Realisability/*). Retyping `defs : Tmp → Option Expr` to `Alloc` ripples through
`materialiseExpr`/`emitStmt`/`emitTerm`/`emitBlockBody`/`offsetTable`/`defsOf` and every
lemma quantifying over that env. Days of re-proof.

**Does it help the open producer proof or R0? No — it is orthogonal.** The live blocker
is `runFrom_of_driveCorrLog`, the single `sorry` at `RealisabilitySpec.lean:247`: a
**dynamic forward-simulation producer** that walks the `RecorderCoupled` invariant across
the F2 recursion to emit the IR `RunFrom` + boundary walk (`:224-247`). R0
(target-architecture §3) is the recorder-suffix-coupling reshape — also **dynamic**
(head-consumption of the gas/call streams). Neither touches the *static* slot/remat
representation. Cleaning up `Expr.slot` would re-prove dozens of already-green
materialisation lemmas and move the sorry **zero** inches.

## Recommendation (2026-07-06)

**Real smell: YES.** `Expr.slot` is a placement directive masquerading as a value-AST
node; it is provably redundant with `Loc` (`toDef_locOfExpr`/`allocate_toDefs`), is never
a genuine sub-expression, and levies the exact "can't happen" tax (`noSlotSource`,
`slots_slot`, the `evalExpr = none` arms) the objection anticipates.

**But DEFER — do not refactor now.** Reasoning: (1) it is strictly orthogonal to the one
remaining headline blocker (`runFrom_of_driveCorrLog`) and to R0 — it advances neither;
(2) it churns ~100 lines of green proof for zero headline progress, against the
"no rushing / finish the current thing properly" standard; (3) the *right* home for it
already exists in the plan of record — the **Phase-5 `Asm.lean` restructure**
(target-architecture §6: "placement = assembler freedom … where allocator
non-determinism naturally lives"). Fold the `Expr.slot` removal into that restructure:
make `Loc`/`Alloc` the sole authority, retype the mechanism, delete `Expr.slot` and its
round-trip scaffolding.

Leaving it until then is defensible precisely because the redundancy is **contained** by
a proven round-trip — `allocate_toDefs` guarantees the two encodings can never drift —
and the mechanism is green. It is a smell with a fence around it, not a live hazard. Land
the producer first.
