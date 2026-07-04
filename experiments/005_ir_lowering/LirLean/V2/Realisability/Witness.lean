import LirLean.V2.Drive.Headline
import LirLean.Assembly.Acyclic
import LirLean.Decode.BoundaryReach
import LirLean.V2.Realisability.Machinery

/-!
# LirLean v2 — Realisability spec, WITNESS (§6a)

Split out of `RealisabilitySpec.lean` (pure relocation). Holds the concrete non-vacuity
witness `exProg`, the R9 anti-vacuity anchor (`wellLowered_exProg`,
`wellLowered_check_exists`), and its supporting lemmas — sorry-free. Imports `Machinery`. -/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch

/-! ## §6 — the concrete non-vacuity witness (R9's anchor; R12's subject)

`exProg` exercises every interesting feature at once: a gas read feeding a forwarded-gas
CALL (gas introspection coupled to the call channel), a spilled SLOAD, a nonzero SSTORE, an
external CALL (positional, consumed from the `CallStream` — no single-call restriction), and a
genuine CYCLE (block 1 loops on a gas-derived condition until gas drops below the threshold —
the cyclic-driver domain no per-cursor gas function could handle). Block/tmp layout:

* block 0: `t0 := 5; t1 := gas; t2 := sload t0; t3 := 1; sstore t0 t3; t4 := 0x100;`
  `t5 := call(callee := t4, gasFwd := t1); jump L1`
* block 1 (the loop): `t6 := gas; t7 := 1000; t8 := (t6 < t7); branch t8 L2 L1`
* block 2: `stop` -/

/-- The R12 witness program (see the §6 docstring for the layout rationale). REAL
definition — the flagship's antecedent must be machine-checkably TRUE somewhere
(HonestGasTie's replacement role, target-architecture §4.1). -/
def exProg : Program :=
  { blocks := #[
      { stmts := [
          .assign ⟨0⟩ (.imm 5),
          .assign ⟨1⟩ .gas,
          .assign ⟨2⟩ (.sload ⟨0⟩),
          .assign ⟨3⟩ (.imm 1),
          .sstore ⟨0⟩ ⟨3⟩,
          .assign ⟨4⟩ (.imm 0x100),
          .call { callee := ⟨4⟩, gasFwd := ⟨1⟩, resultTmp := some ⟨5⟩ } ],
        term := .jump ⟨1⟩ },
      { stmts := [
          .assign ⟨6⟩ .gas,
          .assign ⟨7⟩ (.imm 1000),
          .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ],
        term := .branch ⟨8⟩ ⟨2⟩ ⟨1⟩ },
      { stmts := [], term := .stop } ],
    entry := ⟨0⟩ }

-- `Block`/`Program` derive only `Repr` in `Spec/IR.lean`; the concrete-witness proofs below
-- (and R9's singleton checker) need decidable equality. Their fields already derive it.
deriving instance DecidableEq for Block
deriving instance DecidableEq for Program

/-- **`defsOf exProg` in closed form.** The two-pass `find?` over the flattened def-pairs
reduces (definitionally) to `find?` over the concrete 9-element pair list: t0↦imm5, t1/t2↦slot
(gas/sload spilled), t3↦imm1, t4↦imm0x100, t5↦slot (call result), t6↦slot (gas spilled),
t7↦imm1000, t8↦lt t6 t7 — the sole reading def. -/
theorem defsOf_exProg_eq : defsOf exProg = fun t =>
    (([ (⟨0⟩, Expr.imm 5), (⟨1⟩, Expr.slot (slotOf ⟨1⟩)), (⟨2⟩, Expr.slot (slotOf ⟨2⟩)),
        (⟨3⟩, Expr.imm 1), (⟨4⟩, Expr.imm 0x100), (⟨5⟩, Expr.slot (slotOf ⟨5⟩)),
        (⟨6⟩, Expr.slot (slotOf ⟨6⟩)), (⟨7⟩, Expr.imm 1000),
        (⟨8⟩, Expr.lt ⟨6⟩ ⟨7⟩) ] : List (Tmp × Expr)).find?
      (fun p => p.1 == t)).map (·.2) := rfl

/-- **The only registered readers in `exProg`.** A `ReadsOf` fact holds iff the reader is `t8`
and the read tmp is `t6` or `t7` (`t8`'s def `lt t6 t7` is the sole def reading any tmp). -/
theorem defsOf_exProg_reads {t t' : Tmp} (h : ReadsOf exProg t t') :
    (t = ⟨6⟩ ∨ t = ⟨7⟩) ∧ t' = ⟨8⟩ := by
  obtain ⟨e', hd, hu⟩ := h
  rw [defsOf_exProg_eq, Option.map_eq_some_iff] at hd
  obtain ⟨p, hfind, hp2⟩ := hd
  have hp1 := List.find?_some hfind
  rw [beq_iff_eq] at hp1
  have hmem := List.mem_of_find?_eq_some hfind
  subst hp2
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (try (exfalso; revert hu; simp only [usesInExpr]; decide))
  -- only the `t8 := lt t6 t7` pair survives; `hp1 : ⟨8⟩ = t'`, `hu : usesInExpr t (lt t6 t7) ≠ 0`.
  refine ⟨?_, hp1.symm⟩
  by_contra hc
  push_neg at hc
  obtain ⟨h6, h7⟩ := hc
  apply hu
  simp only [usesInExpr, if_neg (fun he : (⟨6⟩ : Tmp) = t => h6 he.symm),
    if_neg (fun he : (⟨7⟩ : Tmp) = t => h7 he.symm)]

/-- No `exProg` def reads a tmp other than `t6`/`t7`. -/
theorem not_readsOf_exProg {t : Tmp} (h6 : t ≠ ⟨6⟩) (h7 : t ≠ ⟨7⟩) (t' : Tmp) :
    ¬ ReadsOf exProg t t' := by
  intro h
  rcases (defsOf_exProg_reads h).1 with rfl | rfl
  · exact h6 rfl
  · exact h7 rfl

/-- One `invalStep` over a pure assign whose target has no registered reader (and whose own
expr does not read the target) preserves point-wise falsity of the invalidation set. -/
theorem invalStep_false_assign {I : Tmp → Prop} {t : Tmp} {e : Expr}
    (hI : ∀ t', ¬ I t') (hu : usesInExpr t e = 0)
    (hr : ∀ t', ¬ ReadsOf exProg t t') :
    ∀ t', ¬ invalStep exProg I (.assign t e) t' := by
  intro t' h
  simp only [invalStep] at h
  by_cases hc : t' = t
  · rw [if_pos hc] at h; exact h hu
  · rw [if_neg hc] at h; exact h.elim (hI t') (hr t')

/-- `sstore` transfers the invalidation set unchanged, so it preserves point-wise falsity. -/
theorem invalStep_false_sstore {I : Tmp → Prop} {k v : Tmp}
    (hI : ∀ t', ¬ I t') : ∀ t', ¬ invalStep exProg I (.sstore k v) t' := by
  intro t' h; simp only [invalStep] at h; exact hI t' h

/-- One `invalStep` over a result-bearing call whose result tmp has no registered reader
preserves point-wise falsity. -/
theorem invalStep_false_call {I : Tmp → Prop} {cs : CallSpec} {t : Tmp}
    (hres : cs.resultTmp = some t)
    (hI : ∀ t', ¬ I t') (hr : ∀ t', ¬ ReadsOf exProg t t') :
    ∀ t', ¬ invalStep exProg I (.call cs) t' := by
  intro t' h
  simp only [invalStep, hres] at h
  by_cases hc : t' = t
  · rw [if_pos hc] at h; exact h
  · rw [if_neg hc] at h; exact h.elim (hI t') (hr t')

/-- `exProg` re-validates per block (R0b's static-boundary anchor). The only within-block
invalidation is `t6 := gas` (and the value-coincident `t7 := 1000`) staleing `t8` — its
sole registered reader — healed two statements later by `t8 := lt t6 t7`; no registered
reader of `t8` exists (the branch USE of `t8` is not a registered def), and block 0's
targets have no registered readers at all. TRACKED DEBT (a finite fold evaluation over
`Tmp → Prop`; becomes a `decide` once the R9 checker gives the fold its `List Tmp`
executable twin). -/
theorem revalidatesPerBlock_exProg : RevalidatesPerBlock exProg := by
  rintro ⟨idx⟩ b hL
  rcases idx with _ | _ | _ | n
  · -- block 0: every target has no registered reader; each step preserves falsity.
    have hb : b = Block.mk [ .assign ⟨0⟩ (.imm 5), .assign ⟨1⟩ .gas, .assign ⟨2⟩ (.sload ⟨0⟩),
        .assign ⟨3⟩ (.imm 1), .sstore ⟨0⟩ ⟨3⟩, .assign ⟨4⟩ (.imm 0x100),
        .call ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩ ] (.jump ⟨1⟩) := by
      have hd : blockAt exProg ⟨0⟩ = some (Block.mk [ .assign ⟨0⟩ (.imm 5), .assign ⟨1⟩ .gas,
          .assign ⟨2⟩ (.sload ⟨0⟩), .assign ⟨3⟩ (.imm 1), .sstore ⟨0⟩ ⟨3⟩, .assign ⟨4⟩ (.imm 0x100),
          .call ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩ ] (.jump ⟨1⟩)) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    have h0 : ∀ t', ¬ (fun _ : Tmp => False) t' := fun _ h => h
    have h1 := invalStep_false_assign h0 (show usesInExpr ⟨0⟩ (.imm 5) = 0 by decide)
      (not_readsOf_exProg (t := ⟨0⟩) (by decide) (by decide))
    have h2 := invalStep_false_assign h1 (show usesInExpr ⟨1⟩ Expr.gas = 0 by decide)
      (not_readsOf_exProg (t := ⟨1⟩) (by decide) (by decide))
    have h3 := invalStep_false_assign h2 (show usesInExpr ⟨2⟩ (.sload ⟨0⟩) = 0 by decide)
      (not_readsOf_exProg (t := ⟨2⟩) (by decide) (by decide))
    have h4 := invalStep_false_assign h3 (show usesInExpr ⟨3⟩ (.imm 1) = 0 by decide)
      (not_readsOf_exProg (t := ⟨3⟩) (by decide) (by decide))
    have h5 := invalStep_false_sstore (k := ⟨0⟩) (v := ⟨3⟩) h4
    have h6 := invalStep_false_assign h5 (show usesInExpr ⟨4⟩ (.imm 0x100) = 0 by decide)
      (not_readsOf_exProg (t := ⟨4⟩) (by decide) (by decide))
    have h7 := invalStep_false_call
      (cs := ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩) (t := ⟨5⟩) rfl h6
      (not_readsOf_exProg (t := ⟨5⟩) (by decide) (by decide))
    simpa only [List.foldl_cons, List.foldl_nil] using h7
  · -- block 1 (the loop): the `t6`/`t7` rebinds stale `t8`, healed by the `t8` reassign.
    have hb : b = Block.mk [ .assign ⟨6⟩ .gas, .assign ⟨7⟩ (.imm 1000),
        .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ] (.branch ⟨8⟩ ⟨2⟩ ⟨1⟩) := by
      have hd : blockAt exProg ⟨1⟩ = some (Block.mk [ .assign ⟨6⟩ .gas, .assign ⟨7⟩ (.imm 1000),
          .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ] (.branch ⟨8⟩ ⟨2⟩ ⟨1⟩)) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    intro t'
    simp only [List.foldl_cons, List.foldl_nil, invalStep]
    intro h
    by_cases h8 : t' = ⟨8⟩
    · rw [if_pos h8] at h; revert h; decide
    · rw [if_neg h8] at h
      rcases h with h | h
      · by_cases h7 : t' = ⟨7⟩
        · rw [if_pos h7] at h; revert h; decide
        · rw [if_neg h7] at h
          rcases h with h | h
          · by_cases h6 : t' = ⟨6⟩
            · rw [if_pos h6] at h; revert h; decide
            · rw [if_neg h6] at h
              rcases h with h | h
              · exact h
              · exact h8 (defsOf_exProg_reads h).2
          · exact h8 (defsOf_exProg_reads h).2
      · rcases (defsOf_exProg_reads h).1 with h' | h' <;> exact absurd h' (by decide)
  · -- block 2: no statements, the fold is the empty (false) set.
    have hb : b = Block.mk [] .stop := by
      have hd : blockAt exProg ⟨2⟩ = some (Block.mk [] .stop) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    intro t' h; exact h
  · -- out of bounds: `exProg` has exactly three blocks.
    exfalso
    simp only [blockAt] at hL
    rw [Array.getElem?_eq_none (show exProg.blocks.size ≤ n + 1 + 1 + 1 by
      have h3 : exProg.blocks.size = 3 := by decide
      omega)] at hL
    simp at hL

/-- The lesson-8 stale state: `exProg`'s loop-EXIT iteration, mid-block 1, after the
`t6 := gas` rebind (fresh read `500 < 1000`) and before `t8`'s reassign — `t8` still
holds the previous iteration's `0` (that iteration's gas read was `≥ 1000`). The
`t0`–`t5` bindings are block-0 values (the gas/sload/call-result words chosen
representatively; they are `NonRecomputable`/spilled, so `DefsSound` is silent about
them either way). -/
def staleSt : IRState :=
  { locals := fun t =>
      if t = ⟨0⟩ then some 5 else if t = ⟨1⟩ then some 2000
      else if t = ⟨2⟩ then some 0 else if t = ⟨3⟩ then some 1
      else if t = ⟨4⟩ then some 0x100 else if t = ⟨5⟩ then some 1
      else if t = ⟨6⟩ then some 500 else if t = ⟨7⟩ then some 1000
      else if t = ⟨8⟩ then some 0 else none
    world := fun _ => 0 }

/-- **The machinery finding, machine-checked** (header lesson 8; R0b's motivation): the
un-scoped `DefsSound` — hence `Corr`, whose `defsSound` field it is — is FALSE at the
real mid-block state of `exProg`'s loop-exit iteration: `t8` is bound to the stale `0`
while its registered def `.lt t6 t7` recomputes to `1` under the rebound `t6`. PROVED
(not debt) — the refutation is the point. The scoped invariant is untouched here: `t8`
is exactly the tmp `invalStep` puts in the set at the `t6` rebind. -/
theorem not_defsSound_stale : ¬ Lir.DefsSound exProg staleSt := by
  intro h
  have hnr : ¬ Lir.NonRecomputable exProg ⟨8⟩ := by
    unfold Lir.NonRecomputable Lir.isGasDef Lir.isSloadDef Lir.isCallResult Lir.isCreateResult
    rintro (⟨b, hb, hmem⟩ | ⟨b, hb, k, hmem⟩ | ⟨b, hb, cs, hmem, hres⟩ | ⟨b, hb, cs, hmem, hres⟩) <;>
      (simp [exProg] at hb; rcases hb with rfl | rfl | rfl <;> simp_all)
  exact absurd (h ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) 0 (by decide) hnr (by decide)) (by decide)

/-! ### R9 — the `RunStmts` prefix-binding inversion (the named blocker)

`RunDefinableG`'s three fields quantify over ALL `RunStmts` prefix-runs and demand the
statement's operands be bound at the reached state. The missing brick is a `RunStmts`
binding inversion: a tmp assigned somewhere in the run's statement list is bound at the
run's final state. Two real inductions (no `sorry`/`decide`-escape):

* `runStmts_preserves_bound` — boundness is preserved across a whole `RunStmts` run (every
  `EvalStmt` case only ever `setLocal`s / `setStorage`s, never unbinds);
* `runStmts_binds_assign` — an `assign t e` occurring in the run's list leaves `t` bound at
  the final state (it binds `t` via `setLocal` at its own step, then preservation carries it
  through the suffix). -/

/-- `setLocal` binds its own target: reading back the set tmp yields the set value. -/
private theorem setLocal_self (st : IRState) (t : Tmp) (v : Word) :
    (st.setLocal t v).locals t = some v := by simp [IRState.setLocal]

/-- `setLocal` preserves boundness of any tmp: if `t` was bound in `st`, it is bound in
`st.setLocal t₀ v` (the `t = t₀` branch binds it to `v`, the `t ≠ t₀` branch keeps it). -/
private theorem setLocal_bound {st : IRState} {t t₀ : Tmp} {v : Word}
    (h : ∃ w, st.locals t = some w) : ∃ w', (st.setLocal t₀ v).locals t = some w' := by
  simp only [IRState.setLocal]
  by_cases hc : t = t₀
  · exact ⟨v, by simp [hc]⟩
  · simp only [if_neg hc]; exact h

/-- **Lemma A — boundness preservation across a `RunStmts` run.** Every `EvalStmt` case only
writes locals via `setLocal` (pure/gas assign, call-with-result) or leaves them untouched
(`sstore`, result-free call touch only `world`), so a bound tmp stays bound. Induction on the
run. -/
theorem runStmts_preserves_bound {prog : Program}
    {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {ss : List Stmt} (t : Tmp)
    (h : RunStmts prog st T C D ss st' T' C' D') :
    (∃ w, st.locals t = some w) → ∃ w', st'.locals t = some w' := by
  induction h with
  | nil => exact id
  | @cons st stm st'' T Tm T'' C Cm C'' D Dm D'' s ss hh ht ih =>
    intro hbound
    apply ih
    cases hh with
    | assignPure hne hv => exact setLocal_bound hbound
    | assignGas => exact setLocal_bound hbound
    | sstore hk hv => exact hbound
    | call hcallee hgas =>
      split
      · exact setLocal_bound hbound
      · exact hbound
    | create hvalue hoff hsize =>
      split
      · exact setLocal_bound hbound
      · exact hbound

/-- **Lemma B — an assigned tmp is bound at the run's end.** An `assign t e` occurring
anywhere in the statement list binds `t` (via `setLocal`, both the pure and gas arms) at its
own step; Lemma A then carries that boundness through the remaining suffix. Induction on the
run, splitting the membership at the head. -/
theorem runStmts_binds_assign {prog : Program}
    {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {ss : List Stmt} {t : Tmp} {e : Expr}
    (h : RunStmts prog st T C D ss st' T' C' D') :
    (Stmt.assign t e) ∈ ss → ∃ w, st'.locals t = some w := by
  induction h with
  | nil => intro hmem; simp at hmem
  | @cons st stm st'' T Tm T'' C Cm C'' D Dm D'' s ss hh ht ih =>
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · subst heq
      have hb : ∃ w, stm.locals t = some w := by
        cases hh with
        | assignPure hne hv => exact ⟨_, setLocal_self _ _ _⟩
        | assignGas => exact ⟨_, setLocal_self _ _ _⟩
      exact runStmts_preserves_bound t ht hb
    · exact ih hmem'

/-! ### R9 — `WellLowered exProg` (the anti-vacuity anchor the singleton checker forces)

The three concrete blocks of `exProg`, named for reuse across the `WellLowered` field
discharges. Definitionally the blocks of `exProg` (`decide`-checkable). -/

private def exBlk0 : Block :=
  { stmts := [ .assign ⟨0⟩ (.imm 5), .assign ⟨1⟩ .gas, .assign ⟨2⟩ (.sload ⟨0⟩),
      .assign ⟨3⟩ (.imm 1), .sstore ⟨0⟩ ⟨3⟩, .assign ⟨4⟩ (.imm 0x100),
      .call { callee := ⟨4⟩, gasFwd := ⟨1⟩, resultTmp := some ⟨5⟩ } ],
    term := .jump ⟨1⟩ }

private def exBlk1 : Block :=
  { stmts := [ .assign ⟨6⟩ .gas, .assign ⟨7⟩ (.imm 1000), .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ],
    term := .branch ⟨8⟩ ⟨2⟩ ⟨1⟩ }

private def exBlk2 : Block := { stmts := [], term := .stop }

private theorem blockAt_exProg0 : blockAt exProg ⟨0⟩ = some exBlk0 := by decide
private theorem blockAt_exProg1 : blockAt exProg ⟨1⟩ = some exBlk1 := by decide
private theorem blockAt_exProg2 : blockAt exProg ⟨2⟩ = some exBlk2 := by decide
private theorem toList_exProg0 : exProg.blocks.toList[0]? = some exBlk0 := by decide
private theorem toList_exProg1 : exProg.blocks.toList[1]? = some exBlk1 := by decide
private theorem toList_exProg2 : exProg.blocks.toList[2]? = some exBlk2 := by decide

/-- Invert a present `blockAt exProg ⟨idx⟩`: the label is 0/1/2 with the matching block, or
the index is out of range (contradiction). -/
private theorem blockAt_exProg_inv {idx : Nat} {b : Block}
    (hb : blockAt exProg ⟨idx⟩ = some b) :
    (idx = 0 ∧ b = exBlk0) ∨ (idx = 1 ∧ b = exBlk1) ∨ (idx = 2 ∧ b = exBlk2) := by
  rcases idx with _|_|_|n
  · rw [blockAt_exProg0] at hb; exact Or.inl ⟨rfl, ((Option.some.injEq _ _).mp hb).symm⟩
  · rw [blockAt_exProg1] at hb; exact Or.inr (Or.inl ⟨rfl, ((Option.some.injEq _ _).mp hb).symm⟩)
  · rw [blockAt_exProg2] at hb; exact Or.inr (Or.inr ⟨rfl, ((Option.some.injEq _ _).mp hb).symm⟩)
  · exfalso; simp only [blockAt] at hb
    rw [Array.getElem?_eq_none (show exProg.blocks.size ≤ n + 1 + 1 + 1 by
      have h3 : exProg.blocks.size = 3 := by decide
      omega)] at hb
    simp at hb

/-- The `toList` form of `blockAt_exProg_inv` (`WellFormedLowered`/`AcyclicWellFormed` fields
index via `prog.blocks.toList`). -/
private theorem toList_exProg_inv {idx : Nat} {b : Block}
    (hb : exProg.blocks.toList[idx]? = some b) :
    (idx = 0 ∧ b = exBlk0) ∨ (idx = 1 ∧ b = exBlk1) ∨ (idx = 2 ∧ b = exBlk2) := by
  apply blockAt_exProg_inv (idx := idx)
  rw [blockAt, ← Array.getElem?_toList]; exact hb

/-- The topological rank on `exProg`'s def-graph: `t8 := lt t6 t7` is the sole reading def, so
it ranks above its operands; everything else is a leaf (rank 0). -/
private def rankExProg : Tmp → ℕ := fun t => if t = ⟨8⟩ then 2 else 0

private theorem acyclic_exProg : Lir.Acyclic (defsOf exProg) rankExProg := by
  intro t e hd
  rw [defsOf_exProg_eq, Option.map_eq_some_iff] at hd
  obtain ⟨p, hfind, hp2⟩ := hd
  have hp1 := List.find?_some hfind
  have hmem := List.mem_of_find?_eq_some hfind
  subst hp2
  rw [beq_iff_eq] at hp1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (subst hp1; unfold Lir.ExprRankLt rankExProg <;> decide)

-- `exProg` is `AcyclicWellFormed`: the rank witness above, the fuel slack, and the concrete
-- program-size pc/offset bounds (all `< 2 ^ 32`). The `bound_*` fields `decide` concrete
-- `offsetTable`/`materialiseExpr` byte arithmetic — a deep (structural) reduction, hence the
-- raised `maxRecDepth`.
set_option maxRecDepth 8000 in
private def acyclicWellFormedExProg : Lir.AcyclicWellFormed exProg where
  rank := rankExProg
  acyclic := acyclic_exProg
  rank_lt_fuel := by
    intro t
    have hb : rankExProg t ≤ 2 := by unfold rankExProg; split <;> decide
    have hf : recomputeFuel exProg = 11 := by decide
    omega
  bound_sstore := by
    rintro ⟨idx⟩ b pc key value hb hs
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.sstore.injEq,
        Stmt.assign.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; decide
  bound_sload := by
    rintro ⟨idx⟩ b pc t k hb hs
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq,
        Expr.sload.injEq, and_false, false_and] at hs
    obtain ⟨rfl, rfl⟩ := hs; decide
  bound_ret := by
    rintro ⟨idx⟩ b t hb hterm
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq] at hterm
  bound_stop := by
    rintro ⟨idx⟩ b hb hterm
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq] at hterm
    decide
  bound_jump := by
    rintro ⟨idx⟩ b dst hb hterm
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.jump.injEq] at hterm
    obtain rfl := hterm; decide
  bound_branch := by
    rintro ⟨idx⟩ b cond thenL elseL hb hterm
    rcases toList_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.branch.injEq] at hterm
    obtain ⟨rfl, rfl, rfl⟩ := hterm; decide
  slots_slot := by
    intro tw slot' hd
    rw [defsOf_exProg_eq, Option.map_eq_some_iff] at hd
    obtain ⟨p, hfind, hp2⟩ := hd
    have hp1 := List.find?_some hfind
    have hmem := List.mem_of_find?_eq_some hfind
    rw [beq_iff_eq] at hp1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> subst hp1 <;>
      simp_all [slotOf]

private theorem wellFormedLowered_exProg : Lir.WellFormedLowered exProg :=
  Lir.wellFormedLowered_of_acyclic acyclicWellFormedExProg

/-- `chargeOf`'s LENGTH is independent of the `sloadChg` valuation (each `.sload` contributes
exactly one entry `[sloadChg k]` whatever its value; every other arm is `sloadChg`-free). The
`StackRoomOK` fields quantify `∀ sloadChg`, so this lets them reduce to the concrete
`sloadChg := 0` charge lengths. Induction on the recompute fuel. -/
private theorem chargeOf_length_indep (defs : Tmp → Option Expr) (s1 s2 : Tmp → ℕ) :
    ∀ (f : Nat) (e : Expr),
      (Lir.chargeOf defs s1 f e).length = (Lir.chargeOf defs s2 f e).length := by
  intro f
  induction f with
  | zero => intro e; cases e <;> rfl
  | succ f ih =>
    intro e
    cases e with
    | imm _ => rfl
    | slot _ => rfl
    | gas => rfl
    | tmp t =>
      cases h : defs t with
      | none => rw [Lir.chargeOf_tmp_none _ _ _ _ h, Lir.chargeOf_tmp_none _ _ _ _ h]
      | some e => rw [Lir.chargeOf_tmp_some _ _ _ _ _ h, Lir.chargeOf_tmp_some _ _ _ _ _ h]; exact ih e
    | add a b =>
      rw [Lir.chargeOf_add, Lir.chargeOf_add]; simp only [List.length_append]
      rw [ih (.tmp b), ih (.tmp a)]
    | lt a b =>
      rw [Lir.chargeOf_lt, Lir.chargeOf_lt]; simp only [List.length_append]
      rw [ih (.tmp b), ih (.tmp a)]
    | sload k =>
      rw [Lir.chargeOf_sload, Lir.chargeOf_sload]
      simp only [List.length_append, List.length_cons, List.length_nil, ih (.tmp k)]

-- `exProg` satisfies gas/call-aware run-definability: at every cursor the statement's operands
-- are bound at the reached prefix-run state — discharged from the `runStmts_binds_assign` inversion
-- (the named blocker) + the concrete block layout. The gas/imm cursors are unconditionally
-- definable; the `sload`/`lt`/`sstore`/`call` cursors read tmps assigned earlier in the same block.
set_option maxRecDepth 8000 in
private theorem runDefinableG_exProg : RunDefinableG exProg where
  stmts := by
    intro st st' T T' C C' D D' L b pc s hb hget hrun
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases pc with _|_|_|_|_|_|_|pc <;>
        simp only [exBlk0, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.some.injEq, reduceCtorEq] at hget
      · subst hget; exact Or.inr ⟨_, rfl⟩
      · subst hget; exact Or.inl rfl
      · subst hget
        obtain ⟨w, hw⟩ := runStmts_binds_assign hrun
          (show Stmt.assign ⟨0⟩ (.imm 5) ∈ _ from by decide)
        exact Or.inr ⟨st'.world w, by simp [evalExpr, hw]⟩
      · subst hget; exact Or.inr ⟨_, rfl⟩
      · subst hget
        exact ⟨runStmts_binds_assign hrun (show Stmt.assign ⟨0⟩ (.imm 5) ∈ _ from by decide),
               runStmts_binds_assign hrun (show Stmt.assign ⟨3⟩ (.imm 1) ∈ _ from by decide)⟩
      · subst hget; exact Or.inr ⟨_, rfl⟩
      · subst hget
        exact ⟨runStmts_binds_assign hrun (show Stmt.assign ⟨4⟩ (.imm 0x100) ∈ _ from by decide),
               runStmts_binds_assign hrun (show Stmt.assign ⟨1⟩ Expr.gas ∈ _ from by decide)⟩
    · rcases pc with _|_|_|pc <;>
        simp only [exBlk1, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.some.injEq, reduceCtorEq] at hget
      · subst hget; exact Or.inl rfl
      · subst hget; exact Or.inr ⟨_, rfl⟩
      · subst hget
        obtain ⟨w6, h6⟩ := runStmts_binds_assign hrun
          (show Stmt.assign ⟨6⟩ Expr.gas ∈ _ from by decide)
        obtain ⟨w7, h7⟩ := runStmts_binds_assign hrun
          (show Stmt.assign ⟨7⟩ (.imm 1000) ∈ _ from by decide)
        exact Or.inr ⟨UInt256.lt w6 w7, by simp [evalExpr, h6, h7]⟩
    · simp only [exBlk2, List.getElem?_nil, reduceCtorEq] at hget
  ret_def := by
    intro st st' T T' C C' D D' L b t hb hterm _
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq] at hterm
  branch_def := by
    intro st st' T T' C C' D D' L b cond thenL elseL hb hterm hrun
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.branch.injEq] at hterm
    obtain ⟨rfl, rfl, rfl⟩ := hterm
    exact runStmts_binds_assign hrun (show Stmt.assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ∈ _ from by decide)

-- `exProg` is `DefsConsistent`: every def-site agrees with `defsOf`'s registration
-- (single-assignment ⇒ no shadowing).
set_option maxRecDepth 8000 in
private theorem defsConsistent_exProg : DefsConsistent exProg := by
  intro L b pc hb
  obtain ⟨idx⟩ := L
  refine ⟨fun t e hassign => ?_, fun cs t hcall hres => ?_⟩
  · rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq] at hassign <;>
      (obtain ⟨rfl, rfl⟩ := hassign; decide)
  · rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.call.injEq] at hcall <;>
      (subst hcall; injection hres with hres'; subst hres'; decide)

-- `exProg` has a closed CFG: entry present + bounded, jump/branch targets present, in-bounds,
-- offset-bounded (all concrete).
set_option maxRecDepth 8000 in
private theorem closedCFG_exProg : ClosedCFG exProg where
  entry_present := ⟨exBlk0, blockAt_exProg0⟩
  entry_bound := by decide
  jump_closed := by
    intro L b dst hb hterm
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.jump.injEq] at hterm
    obtain rfl := hterm
    exact ⟨⟨exBlk1, blockAt_exProg1⟩, by decide, by decide⟩
  branch_closed := by
    intro L b cond thenL elseL hb hterm
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.branch.injEq] at hterm
    obtain ⟨rfl, rfl, rfl⟩ := hterm
    exact ⟨⟨⟨exBlk2, blockAt_exProg2⟩, by decide, by decide⟩,
           ⟨exBlk1, blockAt_exProg1⟩, by decide, by decide⟩

-- `exProg` satisfies the static stack-room bounds: every `chargeOf` fold is well under 1024
-- (concrete once `sloadChg` is eliminated via `chargeOf_length_indep`).
set_option maxRecDepth 8000 in
private theorem stackRoomOK_exProg : StackRoomOK exProg where
  branch := by
    intro sloadChg L b cond thenL elseL hb hterm
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq, Term.branch.injEq] at hterm
    obtain ⟨rfl, rfl, rfl⟩ := hterm
    rw [chargeOf_length_indep (defsOf exProg) sloadChg (fun _ => 0)]; decide
  sloadKey := by
    intro sloadChg L b pc t k hb hs
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq, Expr.sload.injEq,
        and_false, false_and] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rw [chargeOf_length_indep (defsOf exProg) sloadChg (fun _ => 0)]; decide
  sstore := by
    intro sloadChg L b pc key value hb hs
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pc with _|_|_|_|_|_|_|pc <;>
      simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.sstore.injEq,
        Stmt.assign.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rw [chargeOf_length_indep (defsOf exProg) sloadChg (fun _ => 0),
        chargeOf_length_indep (defsOf exProg) sloadChg (fun _ => 0)]; decide
  ret := by
    intro sloadChg L b t hb hterm
    obtain ⟨idx⟩ := L
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq] at hterm

-- `exProg` satisfies the gas-stash pc bound at each spilled-`.gas` cursor (`decide` on the
-- concrete `pcOf`, as in `bound_sstore`).
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
private theorem gasBound_exProg : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt exProg L = some b → b.stmts[pc]? = some (.assign t .gas) →
    pcOf exProg L pc + 34 < 2 ^ 32 := by
  rintro ⟨idx⟩ b pc t hb hs
  rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases pc with _|_|_|_|_|_|_|pc <;>
    simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq,
      Expr.imm.injEq, Expr.sload.injEq, Expr.lt.injEq, and_false, false_and, and_true] at hs <;>
    decide

-- `exProg` satisfies spill-slot addressability at each gas/sload cursor.
private theorem slotAddr_exProg : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt exProg L = some b →
    (b.stmts[pc]? = some (.assign t .gas)
      ∨ ∃ k, b.stmts[pc]? = some (.assign t (.sload k))) →
    slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits := by
  have hbig : (2:Nat)^32 ≤ 2 ^ System.Platform.numBits := by
    apply Nat.pow_le_pow_right (by norm_num); cases System.Platform.numBits_eq <;> omega
  rintro ⟨idx⟩ b pc t hb (hs | ⟨k, hs⟩) <;>
    rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases pc with _|_|_|_|_|_|_|pc <;>
    simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq,
      Expr.imm.injEq, Expr.sload.injEq, Expr.lt.injEq, and_false, false_and, and_true] at hs <;>
    first
      | (subst hs; exact ⟨by decide, lt_of_lt_of_le (by decide) hbig⟩)
      | (obtain ⟨rfl, rfl⟩ := hs; exact ⟨by decide, lt_of_lt_of_le (by decide) hbig⟩)

-- `exProg` has no `ret`-terminated block (all blocks jump/branch/stop), so the ret epilogue
-- bound is vacuous.
private theorem retEpilogueBound_exProg : ∀ (L : Label) (b : Block) (t : Tmp),
    blockAt exProg L = some b → b.term = .ret t →
    termOf exProg L
      + (materialiseExpr (defsOf exProg) (recomputeFuel exProg) (.tmp t)).length + 100 < 2 ^ 32 := by
  rintro ⟨idx⟩ b t hb hterm
  rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [exBlk0, exBlk1, exBlk2, reduceCtorEq] at hterm

-- `exProg` has no `.slot`-source assign (no source program writes the lowering-only marker).
set_option linter.unusedSimpArgs false in
private theorem noSlotSource_exProg : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp) (n : Nat),
    blockAt exProg L = some b → b.stmts[pc]? = some (.assign t (.slot n)) → False := by
  rintro ⟨idx⟩ b pc t n hb hs
  rcases blockAt_exProg_inv hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases pc with _|_|_|_|_|_|_|pc <;>
    simp only [exBlk0, exBlk1, exBlk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.some.injEq, reduceCtorEq, Stmt.assign.injEq,
      Expr.slot.injEq, and_false, false_and] at hs

/-- **`WellLowered exProg`** — the anti-vacuity anchor R9's second conjunct forces. Every field
discharged above from the acyclicity core + the concrete `exProg` layout + the `RunStmts`
binding inversion.

(Non-`private` — unlike the other `*_exProg` witness lemmas — because it is the witness
block's exported anchor, consumed by `exProg_nonvacuity` in `RealisabilitySpec.lean` after
the file split.) -/
theorem wellLowered_exProg : WellLowered exProg where
  wf := wellFormedLowered_exProg
  defs := runDefinableG_exProg
  defsCons := defsConsistent_exProg
  entry0 := rfl
  closed := closedCFG_exProg
  stack := stackRoomOK_exProg
  gasBound := gasBound_exProg
  slotAddr := slotAddr_exProg
  retEpilogueBound := retEpilogueBound_exProg
  noSlotSource := noSlotSource_exProg

/-- **R9 — the static checker, stated existentially with a non-vacuity anchor.** A
PREMATURE checker `def` would be worse than debt (a wrong-but-real `lowerCheck` misleads;
a `fun _ => false` checker is the vacuity dual — sound and useless). The obligation is:
some Boolean checker is SOUND for `WellLowered` AND accepts the witness program — the
second conjunct is the anti-vacuity guard (it forces `WellLowered exProg` to actually
hold, `RunDefinableG` included). The checker DEFINITION is the debt. -/
theorem wellLowered_check_exists :
    ∃ check : Program → Bool,
      (∀ prog, check prog = true → WellLowered prog) ∧ check exProg = true := by
  -- The singleton (equality-to-`exProg`) checker: sound because its only accepted program is
  -- `exProg`, which genuinely IS `WellLowered` (`wellLowered_exProg`); the second conjunct
  -- forces that — the anti-vacuity guard. The general checker `def` remains tracked debt.
  refine ⟨fun p => decide (p = exProg), ?_, by decide⟩
  intro prog h
  have : prog = exProg := of_decide_eq_true h
  subst this
  exact wellLowered_exProg


end Lir.V2
