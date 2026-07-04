import LirLean.Decode.LoweringLemmas
import LirLean.Spec.Semantics

/-!
# LirLean — `WellFormed` + `DefsSound` (Layer B3 of the `lower_conforms` grind)

This module is the **soundness foundation for recompute-on-use** that the linchpin
**B1 `materialise_runs`** consumes (its `.tmp t → defsOf prog t` recursion). See
`docs/lower-conforms-plan.md`, the `DESIGN DECISION` block and node **B3**.

## Why two predicates

The lowering is **recompute-on-use** (`LirLean/Lowering.lean`): an `assign` emits
**no** bytes; the work happens at the consuming opcode, which re-emits the
push-sequence of the operand's defining expression via `materialiseExpr defsOf …`.
This is sound **only when recomputing a tmp gives the same value it had when the IR
assigned it**. That holds for *pure* expressions (`imm/add/lt/sload`: recompute =
same value, modulo the world, which `sstore` is sequenced before its readers). It is
**unsound** for:

* `Expr.gas` — re-emitting `GAS` reads a *fresh, different* value (the IR binds the
  *consumed* read via `EvalStmt.assignGas`, not a recomputable expression);
* `Expr.sload k` — re-emitting `SLOAD` re-reads the cell at a *different warmth* (the
  second access is warm, 100, not cold, 2100), mis-charging; the value is correct but the
  cost smears, so an sload-defined tmp is spilled too (Phase C); and
* a **call-result tmp** (`CallSpec.resultTmp`) — bound to the dynamic CALL success
  flag by `EvalStmt.call`, not recomputable at all.

`WellFormed prog` (the DESIGN DECISION) makes the lowering faithful for these
**non-recomputable** tmps by requiring each is **used at most once**: a single
materialisation site, so "recompute" never re-reads a fresh/dynamic value. `DefsSound`
then states the recompute-coherence the value channel needs — but **only over the
recomputable tmps**; the non-recomputable ones are accounted by `WellFormed`'s
single-use (B1 materialises each at its unique site, never via the `defsOf` recursion).

Pure-IR (frame-free): this module depends only on `IR.lean`, `Lowering.lean` and
`V2/Machine.lean`. -/

namespace Lir

open Evm Lir.V2

/-! ## Tmp-use counting

A tmp is *used* wherever it is **read**: as an operand of an expression, a key/value
of `sstore`, a `call`'s callee/gas-forward, or a terminator's `ret`/`branch` operand.
(`assign`'s left-hand `t` is a *definition*, not a use; `jump` reads nothing.) We
count uses syntactically over the whole program. -/

/-- Number of reads of tmp `t` inside expression `e`. -/
def usesInExpr (t : Tmp) : Expr → Nat
  | .imm _   => 0
  | .tmp t'  => if t' = t then 1 else 0
  | .add a b => (if a = t then 1 else 0) + (if b = t then 1 else 0)
  | .lt  a b => (if a = t then 1 else 0) + (if b = t then 1 else 0)
  | .sload k => if k = t then 1 else 0
  | .gas     => 0
  | .slot _ => 0

/-- Number of reads of tmp `t` inside statement `s`. -/
def usesInStmt (t : Tmp) : Stmt → Nat
  | .assign _ e      => usesInExpr t e
  | .sstore key val  => (if key = t then 1 else 0) + (if val = t then 1 else 0)
  | .call cs         => (if cs.callee = t then 1 else 0) + (if cs.gasFwd = t then 1 else 0)
  | .create cs       => (if cs.value = t then 1 else 0) + (if cs.initOffset = t then 1 else 0)
                          + (if cs.initSize = t then 1 else 0)
                          + (match cs.salt with | some s => if s = t then 1 else 0 | none => 0)

/-- Number of reads of tmp `t` inside terminator `term`. -/
def usesInTerm (t : Tmp) : Term → Nat
  | .ret t'              => if t' = t then 1 else 0
  | .stop               => 0
  | .jump _             => 0
  | .branch cond _ _    => if cond = t then 1 else 0

/-- Number of reads of tmp `t` inside one block (its statements + terminator). -/
def usesInBlock (t : Tmp) (b : Block) : Nat :=
  (b.stmts.map (usesInStmt t)).sum + usesInTerm t b.term

/-- Total number of reads of tmp `t` across the whole program. -/
def useCount (prog : Program) (t : Tmp) : Nat :=
  (prog.blocks.toList.map (usesInBlock t)).sum

/-! ## Non-recomputable tmps

A tmp is **non-recomputable** when recompute-on-use would change its value: it is
defined by `Expr.gas`, or it is some `Stmt.call`'s `resultTmp`. These are exactly the
tmps `WellFormed` constrains to single-use and `DefsSound` deliberately excludes. -/

/-- Is `t` the `resultTmp` of some `Stmt.call` in the program? -/
def isCallResult (prog : Program) (t : Tmp) : Prop :=
  ∃ b ∈ prog.blocks.toList, ∃ cs : CallSpec,
    Stmt.call cs ∈ b.stmts ∧ cs.resultTmp = some t

/-- Is `t` the `resultTmp` of some `Stmt.create` in the program? The twin of `isCallResult`:
a CREATE binds the pushed deployed-address word into `resultTmp`, which — like a CALL success
flag — is a dynamic value NOT reproducible by `evalExpr` recompute-on-use, hence
non-recomputable. -/
def isCreateResult (prog : Program) (t : Tmp) : Prop :=
  ∃ b ∈ prog.blocks.toList, ∃ cs : CreateSpec,
    Stmt.create cs ∈ b.stmts ∧ cs.resultTmp = some t

/-- Is `t` the target of an `assign t .gas` somewhere in the program? Phrased
**syntactically** (on the source statements) rather than on `defsOf`: after Phase B a
gas-defined tmp is registered in `defsOf` as the spill-load `Expr.slot (slotOf t)` (it is
stashed once and read back from memory, never re-emitting `GAS`), so the old
`defsOf prog t = some .gas` characterisation no longer fires. The syntactic form is what
`gasAssignTmps`/`WellFormedDec` already use, and what the gas value-channel keys on. -/
def isGasDef (prog : Program) (t : Tmp) : Prop :=
  ∃ b ∈ prog.blocks.toList, Stmt.assign t .gas ∈ b.stmts

/-- Is `t` the target of an `assign t (.sload k)` somewhere in the program? Phrased
**syntactically** (on the source statements) rather than on `defsOf`, mirroring `isGasDef`:
after Phase C an sload-defined tmp is registered in `defsOf` as the spill-load
`Expr.slot (slotOf t)` (the SLOAD value + its warmth charge is read once at the def-site stash
and reused from memory via `MLOAD`), so a `defsOf prog t = some (.sload _)` characterisation no
longer fires. This is the predicate keying the SLOAD value/warmth channel. -/
def isSloadDef (prog : Program) (t : Tmp) : Prop :=
  ∃ b ∈ prog.blocks.toList, ∃ k : Tmp, Stmt.assign t (.sload k) ∈ b.stmts

/-- A tmp whose value/charge recompute-on-use would **not** reproduce: gas-defined,
sload-defined, or a call result. `DefsSound` ranges over the complement; `WellFormed`
bounds the call results to single-use so B1 materialises each exactly once (never via the
`defsOf` recursion). Gas and sload are spilled to memory (Phase B/C), so multi-use of them
re-reads the stashed value (`MLOAD`), never a fresh opcode — they are unrestricted. -/
def NonRecomputable (prog : Program) (t : Tmp) : Prop :=
  isGasDef prog t ∨ isSloadDef prog t ∨ isCallResult prog t ∨ isCreateResult prog t

/-! ## `WellFormed` — the DESIGN DECISION (Phase B: gas is no longer restricted)

Every **call-result** tmp is used **at most once** across the program. (Gas tmps used to
be restricted too — recompute-on-use would re-read a fresh `GAS` value — but **Phase B
spills gas to memory**: a gas read is stashed once at its def-site and reused via `MLOAD`,
so multi-use gas is now safe and is *not* a `WellFormed` obligation.) The predicate stays
*discriminating*, not vacuous: `callIR` satisfies it; a program whose CALL result is
read twice does not. `guardIR` — which reads its first gas value twice (the guard *and* the
`ret`) — is now **`WellFormed`** (gas multi-use is in scope), the demonstration that the
Phase-B spill lifted the former restriction. -/

/-- **The well-formedness condition** (`docs/uniform-spill-alloc-plan.md` §6). Every
**call-result** tmp is used at most once across the program. Gas tmps are unrestricted —
Phase B routes them through the memory spill, so multi-use gas never re-reads a fresh value. -/
def WellFormed (prog : Program) : Prop :=
  ∀ t : Tmp, isCallResult prog t → useCount prog t ≤ 1

/-! ### A decidable surrogate for the concrete sanity check

`WellFormed` quantifies over the infinite `Tmp` domain, so it is not directly
`decide`-able. But the call-result tmps form a **finite, syntactically computable** list.
`WellFormedDec` checks `useCount ≤ 1` over exactly that list, is `Decidable`, and **implies
`WellFormed`** — so a `by decide` on `WellFormedDec prog` discharges `WellFormed prog`. -/

/-- The call-result tmps: every `cs.resultTmp` that is `some`. -/
def callResultTmps (prog : Program) : List Tmp :=
  prog.blocks.toList.flatMap (fun b =>
    b.stmts.filterMap (fun
      | .call cs => cs.resultTmp
      | _        => none))

/-- The decidable surrogate: every call-result tmp is used ≤ once. -/
def WellFormedDec (prog : Program) : Prop :=
  ∀ t ∈ callResultTmps prog, useCount prog t ≤ 1

instance (prog : Program) : Decidable (WellFormedDec prog) := by
  unfold WellFormedDec; infer_instance

/-- Every `isCallResult` tmp is in `callResultTmps`. -/
theorem callResult_mem_dec {prog : Program} {t : Tmp}
    (h : isCallResult prog t) : t ∈ callResultTmps prog := by
  obtain ⟨b, hb, cs, hcsmem, hres⟩ := h
  unfold callResultTmps
  rw [List.mem_flatMap]
  exact ⟨b, hb, by rw [List.mem_filterMap]; exact ⟨.call cs, hcsmem, hres⟩⟩

/-- The decidable surrogate implies the real `WellFormed`. -/
theorem wellFormed_of_dec {prog : Program} (h : WellFormedDec prog) : WellFormed prog :=
  fun t hcr => h t (callResult_mem_dec hcr)

/-! ## `DefsSound` — recompute env agrees with IR locals (B3)

The recompute environment `defsOf prog` agrees with the IR machine's `locals` on the
**recomputable** tmps: for every such `t` with a definition `e`, the local's bound
value equals `e` re-evaluated in the current state. This is exactly the fact B1 needs
at its `.tmp t → defsOf prog t` recursion: materialising `.tmp t` (which expands to
materialising `defsOf prog t`) pushes `evalExpr st e`, and `DefsSound` says that is
`st.locals t` — the value the IR holds.

The **non-recomputable** tmps (`Expr.gas`, call results) are *excluded*: their value is
not a function of `defsOf` (gas is the *consumed* read bound by `assignGas`; a call
result is the dynamic CALL flag bound by the call arm). `WellFormed`'s single-use is
what accounts for them on the bytecode side — B1 materialises each at its unique site,
so the `defsOf` recursion never reaches them. (For a gas-defined `t`, `defsOf prog t =
some .gas`, which `NonRecomputable` excludes; so `DefsSound` makes *no* claim about it,
exactly as intended.)

`obs` is pinned to `0`: a recomputable `e` is non-`gas`, and `evalExpr` reads `obs`
**only** for `.gas`, so the choice is irrelevant for the tmps in range.

We range only over tmps that are **currently assigned** (`st.locals t = some w`). This
is what makes the invariant *vacuous at entry* (empty `locals`) and is exactly the
shape B1 uses: B1 materialises `.tmp t` only when the IR holds a value there, and then
needs `w = evalExpr st 0 e`. (Without the `some w` guard the invariant would be *false*
at entry — `none ≠ evalExpr st 0 (.imm w)` — so the guard is not a weakening of the
useful content, it is the correct content.) -/

/-- **The recompute-soundness invariant** (B3). On every recomputable tmp that the IR
currently holds a value for, that value agrees with re-evaluating the tmp's `defsOf`
expression in the current state. -/
def DefsSound (prog : Program) (st : IRState) : Prop :=
  ∀ (t : Tmp) (e : Expr) (w : Word),
    defsOf prog t = some e →
    ¬ NonRecomputable prog t →
    st.locals t = some w →
    some w = evalExpr st 0 e

/-! ## Entry: `DefsSound` holds with empty locals (vacuous)

At program entry `locals` is everywhere `none`, so the `st.locals t = some w`
hypothesis is unsatisfiable. -/

/-- `DefsSound` holds at the empty-locals entry state for any program/world. -/
theorem defsSound_entry (prog : Program) (w₀ : World) :
    DefsSound prog { locals := fun _ => none, world := w₀ } := by
  intro t e w _ _ hlocal
  simp at hlocal

/-! ## Stability of `evalExpr` under `setLocal` of an unused tmp

`evalExpr` reads only the tmps a (recomputable) expression mentions. If `e` does not
read `t`, rebinding `t` does not change `evalExpr st 0 e`. This is the lemma the
`t₀ ≠ t` case of preservation rests on; the side condition `usesInExpr t e = 0` is
exactly "`e` does not read `t`". The world is untouched by `setLocal`, so `sload`
is fine too. -/

private theorem setLocal_locals_ne {st : IRState} {t t' : Tmp} {w : Word}
    (h : t' ≠ t) : (st.setLocal t w).locals t' = st.locals t' := by
  simp [IRState.setLocal, h]

/-- If `e` does not read `t` (`usesInExpr t e = 0`), evaluating `e` is unchanged by
rebinding `t`. (`obs` is shared, world is shared.) -/
theorem evalExpr_setLocal_of_unused {st : IRState} {t : Tmp} {w obs : Word} :
    ∀ {e : Expr}, usesInExpr t e = 0 →
      evalExpr (st.setLocal t w) obs e = evalExpr st obs e
  | .imm _, _ => rfl
  | .gas,   _ => rfl
  | .slot _, _ => rfl
  | .tmp t', h => by
      simp only [usesInExpr] at h
      have hne : t' ≠ t := by
        intro he; subst he; simp at h
      simp [evalExpr, setLocal_locals_ne hne]
  | .add a b, h => by
      simp only [usesInExpr] at h
      have ha : a ≠ t := by intro he; subst he; simp at h
      have hb : b ≠ t := by intro he; subst he; simp at h
      simp [evalExpr, setLocal_locals_ne ha, setLocal_locals_ne hb]
  | .lt a b, h => by
      simp only [usesInExpr] at h
      have ha : a ≠ t := by intro he; subst he; simp at h
      have hb : b ≠ t := by intro he; subst he; simp at h
      simp [evalExpr, setLocal_locals_ne ha, setLocal_locals_ne hb]
  | .sload k, h => by
      simp only [usesInExpr] at h
      have hk : k ≠ t := by intro he; subst he; simp at h
      simp [evalExpr, IRState.setLocal, hk]

/-! ## Preservation under `EvalStmt`

The interesting step is `EvalStmt.assignPure t e` (the pure-expr `assign`). The other
arms (`sstore`, `assignGas`, `call`) are handled below; for them the subtlety is exactly
the gas/call-recompute coherence the `WellFormed` single-use decision underwrites.

### The clean case: pure-expr `assign`

After `assign t e` (non-gas), `st' = st.setLocal t w` with `w = evalExpr st 0 e`. Three
side conditions, all *honest define-before-use / single-assignment* facts true of the
concrete programs and dischargeable by `decide`:

* **`hself : defsOf prog t = some e`** — the assign being stepped is the one `defsOf`
  records for `t` (single-assignment consistency). Needed for the `t₀ = t` sub-case.
* **`hnoself : usesInExpr t e = 0`** — the RHS does not read its own target (no
  self-reference). Discharges the `t₀ = t` sub-case (the freshly bound value agrees with
  its own recompute).
* **`hscope : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0`**
  — no tmp *already assigned* in `st` has a `defsOf`-expression that reads `t`
  (define-before-use: readers of `t` are defined later, hence not yet bound). Keeps every
  prior agreement stable under the new `setLocal t` (the `t₀ ≠ t` sub-case).

These are precisely the topological-order / SSA content; a program-global `WellScoped`
packaging them is future work (it would discharge `hscope`/`hnoself` once, by an order
argument). Here they are explicit so the lemma is reusable and the proof honest. -/

/-- Reading `t`'s freshly-bound value back: `(st.setLocal t w).locals t = some w`. -/
private theorem setLocal_locals_self {st : IRState} {t : Tmp} {w : Word} :
    (st.setLocal t w).locals t = some w := by
  simp [IRState.setLocal]

/-- **Preservation of `DefsSound` across a pure-expr `assign`.** Given the
single-assignment consistency `hself` and the define-before-use scoping `hscope`,
`DefsSound` is preserved when stepping `EvalStmt.assignPure t e`. -/
theorem defsSound_preserved_assignPure {prog : Program} {st : IRState}
    {t : Tmp} {e : Expr} {w : Word}
    (hv : evalExpr st 0 e = some w)
    (hself : defsOf prog t = some e)
    (hnoself : usesInExpr t e = 0)
    (hscope : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
    (hsound : DefsSound prog st) :
    DefsSound prog (st.setLocal t w) := by
  intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
  by_cases heq : t₀ = t
  · -- t₀ = t : the freshly bound value, and e₀ = e by single-assignment consistency.
    subst heq
    have he : e₀ = e := by rw [hdef₀] at hself; exact Option.some.inj hself
    subst he
    have hw₀ : w₀ = w := by
      rw [setLocal_locals_self] at hlocal₀; exact (Option.some.inj hlocal₀).symm
    subst hw₀
    -- goal: some w₀ = evalExpr (setLocal t₀ w₀) 0 e₀ ; e₀ has no self-reference to t₀.
    rw [evalExpr_setLocal_of_unused hnoself]
    exact hv.symm
  · -- t₀ ≠ t : prior agreement, stable because e₀ does not read t.
    have hl' : st.locals t₀ = some w₀ := by
      rw [setLocal_locals_ne heq] at hlocal₀; exact hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
    have hunused : usesInExpr t e₀ = 0 := hscope t₀ e₀ hdef₀ (by rw [hl']; simp)
    rw [evalExpr_setLocal_of_unused hunused]
    exact hprev

/-! ### `assignGas` — the gas-bound tmp (handled via `NonRecomputable`)

`assign t .gas` binds `t` to the *consumed* gas read (`EvalStmt.assignGas`), giving
`st' = st.setLocal t obs`. The target `t` is gas-defined, so `defsOf prog t = some .gas`
and `NonRecomputable prog t` holds — `DefsSound` makes no claim about `t` (the
`t₀ = t` case is discharged by the `NonRecomputable` exclusion). For `t₀ ≠ t` the
argument is identical to the pure case: rebinding `t` is stable on any prior
agreement, given define-before-use (`hscope`). This is exactly how `WellFormed`'s
single-use accounting lands: the gas value is never recomputed via `defsOf`.

The hypothesis `hgasdef : isGasDef prog t` is the consistency fact that `t` is a gas
definition of the program (`∃ b, assign t .gas ∈ b.stmts`). -/

/-- **Preservation of `DefsSound` across `assign t .gas`.** The gas-bound tmp is
excluded from `DefsSound` (it is `NonRecomputable`); other tmps are stable under
rebinding `t`, given define-before-use. -/
theorem defsSound_preserved_assignGas {prog : Program} {st : IRState}
    {t : Tmp} {obs : Word}
    (hgasdef : isGasDef prog t)
    (hscope : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
    (hsound : DefsSound prog st) :
    DefsSound prog (st.setLocal t obs) := by
  intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
  by_cases heq : t₀ = t
  · -- t₀ = t is gas-defined ⇒ NonRecomputable, contradicting hnr₀.
    subst heq
    exact absurd (Or.inl hgasdef) hnr₀
  · have hl' : st.locals t₀ = some w₀ := by
      rw [setLocal_locals_ne heq] at hlocal₀; exact hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
    have hunused : usesInExpr t e₀ = 0 := hscope t₀ e₀ hdef₀ (by rw [hl']; simp)
    rw [evalExpr_setLocal_of_unused hunused]
    exact hprev

/-! ### `assignSload` — the sload-bound tmp (handled via `NonRecomputable`)

`assign t (.sload k)` fires `EvalStmt.assignPure` (sload is a pure IR expression: it reads
`st.world (st.locals k)`), giving `st' = st.setLocal t w` with `w = evalExpr st 0 (.sload k)`.
After Phase C the target `t` is sload-defined, so `defsOf prog t = some (.slot (slotOf t))`
and `NonRecomputable prog t` holds (`isSloadDef`) — `DefsSound` makes no claim about `t` (the
`t₀ = t` case is discharged by the `NonRecomputable` exclusion, exactly as for gas/call). For
`t₀ ≠ t` the argument is the same stable-rebinding one given define-before-use (`hscope`). The
SLOAD value (and its warmth charge) is never recomputed via `defsOf` — it lives in `slotOf t`,
read once at the def-site stash and reused via `MLOAD`.

The hypothesis `hsloaddef : isSloadDef prog t` is the consistency fact that `t` is an sload
definition of the program (`∃ b k, assign t (.sload k) ∈ b.stmts`). -/

/-- **Preservation of `DefsSound` across `assign t (.sload k)`.** The sload-bound tmp is
excluded from `DefsSound` (it is `NonRecomputable`); other tmps are stable under rebinding `t`,
given define-before-use. -/
theorem defsSound_preserved_assignSload {prog : Program} {st : IRState}
    {t : Tmp} {w : Word}
    (hsloaddef : isSloadDef prog t)
    (hscope : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
    (hsound : DefsSound prog st) :
    DefsSound prog (st.setLocal t w) := by
  intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
  by_cases heq : t₀ = t
  · -- t₀ = t is sload-defined ⇒ NonRecomputable, contradicting hnr₀.
    subst heq
    exact absurd (Or.inr (Or.inl hsloaddef)) hnr₀
  · have hl' : st.locals t₀ = some w₀ := by
      rw [setLocal_locals_ne heq] at hlocal₀; exact hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
    have hunused : usesInExpr t e₀ = 0 := hscope t₀ e₀ hdef₀ (by rw [hl']; simp)
    rw [evalExpr_setLocal_of_unused hunused]
    exact hprev

/-! ### `sstore` — a world write (the `sload`-recompute hazard)

`sstore key value` writes one storage cell: `st' = st.setStorage kw vw`, leaving
`locals` untouched. Recomputing a *pure non-`sload`* expression is stable (it does not
read the world); recomputing an `sload k` whose key equals `kw` would now read the
**new** value — a genuine recompute hazard, the storage analogue of the gas freshness
problem. So preservation needs the honest scoping fact that **no already-assigned
recomputable tmp's definition reads the world at the written key** (`hworld`). On the
concrete programs the SSTORE precedes every dependent SLOAD (so the SLOAD-tmp is not yet
assigned when the SSTORE fires) — `hworld` is then vacuously satisfied there. -/

/-- `evalExpr` is stable under `setStorage k v` for an expression that does not read
the world (`usesWorld e = false`), i.e. is not an `sload`. -/
private theorem evalExpr_setStorage_of_noSload {st : IRState} {k v obs : Word} :
    ∀ {e : Expr}, (∀ key, e ≠ .sload key) →
      evalExpr (st.setStorage k v) obs e = evalExpr st obs e
  | .imm _,   _ => rfl
  | .gas,     _ => rfl
  | .tmp _,   _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _,  _ => rfl
  | .slot _, _ => rfl
  | .sload key, h => absurd rfl (h key)

/-- **Preservation of `DefsSound` across `sstore`.** Given that no already-assigned
recomputable tmp's `defsOf` expression is an `sload` (`hnoSload` — the honest
no-live-sload-across-the-write fact, vacuous on the concrete programs where SSTORE
precedes its readers), `DefsSound` survives the storage write. -/
theorem defsSound_preserved_sstore {prog : Program} {st : IRState} {kw vw : Word}
    (hnoSload : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key)
    (hsound : DefsSound prog st) :
    DefsSound prog (st.setStorage kw vw) := by
  intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
  have hl' : st.locals t₀ = some w₀ := by
    simpa [IRState.setStorage] using hlocal₀
  have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
  have hns : ∀ key, e₀ ≠ .sload key := hnoSload t₀ e₀ hdef₀ hnr₀ (by rw [hl']; simp)
  rw [evalExpr_setStorage_of_noSload hns]
  exact hprev

/-! ### `call` — world replacement + call-result binding (the hardest arm)

`call cs` (`EvalStmt.call`) replaces the whole `world` with the oracle's `world'` and,
if `cs.resultTmp = some t`, binds `t := success`. This is the union of the two hazards
above, taken to their limit:

* **World fully replaced** by an *arbitrary* oracle output ⇒ recomputing **any** live
  `sload`-defined recomputable tmp is unsound (the world bears no relation to its old
  value). So preservation needs the honest *no-live-recomputable-sload-across-the-call*
  fact `hnoSload`, exactly as for `sstore` but unconditional in the key.
* **Call-result binding**: the bound `t = cs.resultTmp` is `isCallResult`, hence
  `NonRecomputable` ⇒ excluded from `DefsSound` (the `t₀ = t` case is vacuous), and
  for `t₀ ≠ t` the rebinding is stable given define-before-use (`hscope`). This is
  precisely where `WellFormed`'s single-use accounting lands for call results.

`evalExpr` over a non-`sload` expression ignores the world, so replacing it is harmless
there; the `setLocal` layer is the same `setLocal_locals_ne` argument as the pure case. -/

/-- `evalExpr` over a non-`sload` expression ignores the world entirely. -/
private theorem evalExpr_world_irrel_of_noSload {locals : Tmp → Option Word}
    {w w' : World} {obs : Word} :
    ∀ {e : Expr}, (∀ key, e ≠ .sload key) →
      evalExpr ⟨locals, w'⟩ obs e = evalExpr ⟨locals, w⟩ obs e
  | .imm _,   _ => rfl
  | .gas,     _ => rfl
  | .tmp _,   _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _,  _ => rfl
  | .slot _, _ => rfl
  | .sload key, h => absurd rfl (h key)

/-- **Preservation of `DefsSound` across `call cs`.** The world is replaced by the
oracle's `world'` and (if present) the call-result tmp is bound to `success`. Given:
`hnoSload` (no live recomputable `sload`-tmp across the call — the world-replacement
hazard), `hisresult` (the bound result tmp is genuinely a call result, hence
`NonRecomputable`), and `hscope` (define-before-use for the result tmp), `DefsSound`
is preserved. Both branches of `cs.resultTmp` are covered. -/
theorem defsSound_preserved_call {prog : Program} {st : IRState} {cs : CallSpec}
    {world' : World} {success : Word}
    (hnoSload : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key)
    (hisresult : ∀ t, cs.resultTmp = some t → isCallResult prog t)
    (hscope : ∀ t, cs.resultTmp = some t →
        ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
    (hsound : DefsSound prog st) :
    DefsSound prog
      (match cs.resultTmp with
        | some t => { st with world := world' }.setLocal t success
        | none   => { st with world := world' }) := by
  -- A reusable fact: DefsSound survives the bare world replacement.
  have hworld : DefsSound prog { st with world := world' } := by
    intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
    have hl' : st.locals t₀ = some w₀ := hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
    have hns : ∀ key, e₀ ≠ .sload key := hnoSload t₀ e₀ hdef₀ hnr₀ (by rw [hl']; simp)
    calc some w₀ = evalExpr st 0 e₀ := hprev
      _ = evalExpr { st with world := world' } 0 e₀ :=
            (evalExpr_world_irrel_of_noSload hns).symm
  cases hrt : cs.resultTmp with
  | none => simpa [hrt] using hworld
  | some t =>
    -- Now the result-tmp binding on top of the world-replaced state.
    intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
    by_cases heq : t₀ = t
    · -- t₀ = t is a call result ⇒ NonRecomputable, contradicting hnr₀.
      subst heq
      exact absurd (Or.inr (Or.inr (Or.inl (hisresult t₀ hrt)))) hnr₀
    · have hl' : ({ st with world := world' }).locals t₀ = some w₀ := by
        rw [setLocal_locals_ne heq] at hlocal₀; exact hlocal₀
      have hprev : some w₀ = evalExpr { st with world := world' } 0 e₀ :=
        hworld t₀ e₀ w₀ hdef₀ hnr₀ hl'
      have hunused : usesInExpr t e₀ = 0 :=
        hscope t hrt t₀ e₀ hdef₀ (by rw [show st.locals t₀ = some w₀ from hl']; simp)
      rw [evalExpr_setLocal_of_unused hunused]
      exact hprev

/-! ### `create` — world replacement + create-result binding (the `call` twin)

`create cs` (`EvalStmt.create`) is structurally the same hazard as `call cs`: the whole
`world` is replaced by the create stream's `world'` and, if `cs.resultTmp = some t`, `t` is
bound to the deployed-address-or-`0` word `addrW`. The preservation argument is *verbatim* the
call one — world-replacement needs `hnoSload` (no live recomputable `sload`-tmp across the
create), and the result binding is excluded because the bound tmp is `isCreateResult`, hence
`NonRecomputable` (the fourth disjunct). The only difference from `defsSound_preserved_call` is
that the result-tmp side condition is `isCreateResult prog t` rather than `isCallResult` (a
CREATE result is not a CALL result). -/

/-- **Preservation of `DefsSound` across `create cs`.** The world is replaced by the create
stream's `world'` and (if present) the create-result tmp is bound to `addrW`. Twin of
`defsSound_preserved_call`; the result-tmp obligation `hisresult` is `isCreateResult prog t`
(the create sibling of `isCallResult`), injecting into `NonRecomputable`'s fourth disjunct. -/
theorem defsSound_preserved_create {prog : Program} {st : IRState} {cs : CreateSpec}
    {world' : World} {addrW : Word}
    (hnoSload : ∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key)
    (hisresult : ∀ t, cs.resultTmp = some t → isCreateResult prog t)
    (hscope : ∀ t, cs.resultTmp = some t →
        ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
    (hsound : DefsSound prog st) :
    DefsSound prog
      (match cs.resultTmp with
        | some t => { st with world := world' }.setLocal t addrW
        | none   => { st with world := world' }) := by
  -- DefsSound survives the bare world replacement (identical to the call case).
  have hworld : DefsSound prog { st with world := world' } := by
    intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
    have hl' : st.locals t₀ = some w₀ := hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
    have hns : ∀ key, e₀ ≠ .sload key := hnoSload t₀ e₀ hdef₀ hnr₀ (by rw [hl']; simp)
    calc some w₀ = evalExpr st 0 e₀ := hprev
      _ = evalExpr { st with world := world' } 0 e₀ :=
            (evalExpr_world_irrel_of_noSload hns).symm
  cases hrt : cs.resultTmp with
  | none => simpa [hrt] using hworld
  | some t =>
    intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
    by_cases heq : t₀ = t
    · -- t₀ = t is a create result ⇒ NonRecomputable (fourth disjunct), contradicting hnr₀.
      subst heq
      exact absurd (Or.inr (Or.inr (Or.inr (hisresult t₀ hrt)))) hnr₀
    · have hl' : ({ st with world := world' }).locals t₀ = some w₀ := by
        rw [setLocal_locals_ne heq] at hlocal₀; exact hlocal₀
      have hprev : some w₀ = evalExpr { st with world := world' } 0 e₀ :=
        hworld t₀ e₀ w₀ hdef₀ hnr₀ hl'
      have hunused : usesInExpr t e₀ = 0 :=
        hscope t hrt t₀ e₀ hdef₀ (by rw [show st.locals t₀ = some w₀ from hl']; simp)
      rw [evalExpr_setLocal_of_unused hunused]
      exact hprev

/-! ### The combined `EvalStmt` preservation

`StepScoped prog st s` bundles the honest, per-step side conditions the four arms need
(define-before-use / single-assignment consistency / no-live-`sload`-across-a-write).
Each is a syntactic/dynamic fact true of the concrete programs and dischargeable there;
a program-global `WellScoped` packaging them once (by a topological-order argument) is
the follow-up. With the bundle, `DefsSound` is preserved by every `EvalStmt` step. -/

/-- The per-step scoping side conditions for `DefsSound` preservation, by statement
shape. (Each arm reuses the precise hypotheses of its dedicated lemma above.) -/
def StepScoped (prog : Program) (st : IRState) : Stmt → Prop
  | .assign t e =>
      (e ≠ .gas → (∀ key, e ≠ .sload key) →
        defsOf prog t = some e ∧ usesInExpr t e = 0 ∧
        (∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0))
      ∧ (e = .gas →
        isGasDef prog t ∧
        (∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0))
      ∧ (∀ key, e = .sload key →
        isSloadDef prog t ∧
        (∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0))
  | .sstore _ _ =>
      ∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key
  | .call cs =>
      (∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key)
      ∧ (∀ t, cs.resultTmp = some t → isCallResult prog t)
      ∧ (∀ t, cs.resultTmp = some t →
          ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)
  | .create cs =>
      -- The `.create` bundle, mirroring `.call` (`docs/create/BUILD-PLAN.md` §2 Step 2):
      -- no live recomputable `sload`-tmp across the world-replacing create; the create-result
      -- tmp is genuinely a create result (`isCreateResult`, the twin of `isCallResult`, hence
      -- `NonRecomputable`); and define-before-use for the result tmp.
      (∀ t₀ e₀, defsOf prog t₀ = some e₀ → ¬ NonRecomputable prog t₀ →
        st.locals t₀ ≠ none → ∀ key, e₀ ≠ .sload key)
      ∧ (∀ t, cs.resultTmp = some t → isCreateResult prog t)
      ∧ (∀ t, cs.resultTmp = some t →
          ∀ t₀ e₀, defsOf prog t₀ = some e₀ → st.locals t₀ ≠ none → usesInExpr t e₀ = 0)

/-- **`DefsSound` is preserved by `EvalStmt`** (the B3 headline preservation), given the
per-step scoping bundle `StepScoped`. Dispatches to the four per-arm lemmas. -/
theorem defsSound_preserved {prog : Program}
    {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream} {s : Stmt}
    (hstep : EvalStmt prog st T C D s st' T' C' D')
    (hsc : StepScoped prog st s)
    (hsound : DefsSound prog st) :
    DefsSound prog st' := by
  cases hstep with
  | assignPure hne hv =>
      rename_i t e w
      obtain ⟨hpure, _, hsload⟩ := hsc
      -- split on whether `e` is a spilled `.sload` (handled via `NonRecomputable`) or a
      -- genuine rematerialised pure expression.
      cases e with
      | sload key =>
          obtain ⟨hsloaddef, hscope⟩ := hsload key rfl
          exact defsSound_preserved_assignSload hsloaddef hscope hsound
      | imm v =>
          obtain ⟨hself, hnoself, hscope⟩ := hpure hne (by nofun)
          exact defsSound_preserved_assignPure hv hself hnoself hscope hsound
      | tmp t' =>
          obtain ⟨hself, hnoself, hscope⟩ := hpure hne (by nofun)
          exact defsSound_preserved_assignPure hv hself hnoself hscope hsound
      | add a b =>
          obtain ⟨hself, hnoself, hscope⟩ := hpure hne (by nofun)
          exact defsSound_preserved_assignPure hv hself hnoself hscope hsound
      | lt a b =>
          obtain ⟨hself, hnoself, hscope⟩ := hpure hne (by nofun)
          exact defsSound_preserved_assignPure hv hself hnoself hscope hsound
      | slot n =>
          obtain ⟨hself, hnoself, hscope⟩ := hpure hne (by nofun)
          exact defsSound_preserved_assignPure hv hself hnoself hscope hsound
      | gas => exact absurd rfl hne
  | assignGas =>
      obtain ⟨_, hgas, _⟩ := hsc
      obtain ⟨hgasdef, hscope⟩ := hgas rfl
      exact defsSound_preserved_assignGas hgasdef hscope hsound
  | sstore hk hv =>
      exact defsSound_preserved_sstore hsc hsound
  | call hcallee hgas =>
      obtain ⟨hnoSload, hisresult, hscope⟩ := hsc
      exact defsSound_preserved_call hnoSload hisresult hscope hsound
  | create hvalue hoff hsize =>
      obtain ⟨hnoSload, hisresult, hscope⟩ := hsc
      exact defsSound_preserved_create hnoSload hisresult hscope hsound

end Lir
