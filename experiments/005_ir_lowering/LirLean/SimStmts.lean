import LirLean.SimStmt

/-!
# LirLean — `sim_stmts` (Layer **D** of the general `lower_conforms` grind)

Statement-list simulation: a whole block's statement list, run by `V2.RunStmts`, is
matched on the bytecode side by the *concatenation* of its per-statement lowered
segments. This is the Layer-D brick that glues Layer C's `sim_stmt` (`SimStmt.lean`,
the `Corr` bundle + `sim_assign`/`sim_sstore_stmt`) along a statement list by
`Runs.trans`, advancing the statement cursor `pc` one position per step and carrying the
`Corr` invariant — crucially its `stack_nil` (M5): recompute-on-use empties the working
stack between statements (each `sim_stmt` arm re-establishes `stack = []`), so `Corr`
threads cleanly from one statement to the next.

## Scope — call-free statement lists

`sim_call_stmt` (`SimStmt.lean` Arm 3) does **not** re-establish `Corr.stack_nil`: the
lowered CALL leaves its 0/1 success flag on the bytecode stack (the documented
lowering-completeness gap — `LirLean/Call.lean` §5, `LirLean/Match.lean`). A block
containing a `Stmt.call` therefore breaks the clean `stack = []` induction. We scope
Layer D to **call-free** statement lists via `CallFree ss := ∀ s ∈ ss, ¬ s.isCall`,
yielding a complete, real theorem over the gas / storage / arithmetic statement blocks.
The call case folds in unchanged once the stack-flag invariant is settled.

## The per-statement simulation hypothesis `SimStmtStep`

The two call-free Layer-C arms (`sim_assign`, `sim_sstore_stmt`) each take a bundle of
honest per-statement structured hypotheses — the `MatDec` decode coverage at the static
cursors, the gas/stack envelopes, the `SstoreRealises` runtime tie, the per-step
`StepScoped` scoping, and the post-state realisability ties. Rather than re-thread all of
those through the list induction (they are per-statement and per-intermediate-state, so
they cannot be stated once up front), Layer D abstracts them into a single structured
hypothesis `SimStmtStep` at exactly the altitude of the Layer-C conclusion: *for every
cursor `pc` in the block holding a non-call statement `s`, any `Corr`-corresponding frame
at `pc` and any `EvalStmt` step of `s` are matched by a `Runs` segment re-establishing
`Corr` at `pc+1` with an empty stack.* This is precisely what `sim_assign` /
`sim_sstore_stmt` deliver; discharging `SimStmtStep` for a concrete program is a
mechanical case split feeding each arm its bundle. (`MatDec`-coverage-as-hypothesis is the
same standard `sim_sstore_stmt` itself adopts — see its `hdv`/`hdk`/`hdop` arguments.)

No `sorry`, no `axiom`, no `native_decide`. Nothing here touches `V2/Machine.lean` /
`V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open BytecodeLayer.Hoare
open Lir.V2

/-! ## Call-free statement lists -/

/-- A statement list is **call-free** when none of its statements is a `Stmt.call`. The
lowered CALL leaves its success flag on the bytecode stack, breaking the `stack = []`
induction `sim_stmts` carries; this predicate scopes Layer D to the clean fragment. -/
def CallFree (ss : List Stmt) : Prop := ∀ s ∈ ss, ¬ s.isCall

theorem callFree_nil : CallFree [] := by intro s hs; exact absurd hs (by simp)

theorem callFree_of_cons {s : Stmt} {ss : List Stmt} (h : CallFree (s :: ss)) :
    ¬ s.isCall ∧ CallFree ss :=
  ⟨h s (by simp), fun s' hs' => h s' (by simp [hs'])⟩

/-! ## The per-statement simulation hypothesis

`SimStmtStep` packages Layer C's call-free conclusion uniformly over the block's cursors:
the union of `sim_assign`'s and `sim_sstore_stmt`'s conclusions, with their per-statement
structured hypotheses (decode coverage, gas/stack envelopes, realisability) discharged
inside. It is what the list induction consumes at each `cons`. -/

/-- **The per-statement simulation step** (Layer C, call-free, abstracted over cursor).
For statement `s` at cursor `(L, pc)` of block `b`, *not* a `Stmt.call`, any frame `fr0`
in `Corr`-correspondence with `st0` at `pc` and any `EvalStmt` step `s : st0 → st0'` are
matched by a `Runs fr0 fr0'` re-establishing `Corr` at `pc+1` with `fr0'.exec.stack = []`.
Discharged for a concrete program by case-splitting `s` and feeding `sim_assign` /
`sim_sstore_stmt` their structured-hypothesis bundles. -/
def SimStmtStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (o : V2.CallOracle)
    (L : Label) (b : Block) : Prop :=
  ∀ (pc : Nat) (s : Stmt) (st0 st0' : V2.IRState) (T0 T0' : Trace) (fr0 : Frame),
    b.stmts[pc]? = some s → ¬ s.isCall →
    Corr prog sloadChg obs st0 fr0 L pc →
    EvalStmt prog o st0 T0 s st0' T0' →
    ∃ fr0', Runs fr0 fr0' ∧ Corr prog sloadChg obs st0' fr0' L (pc + 1)
      ∧ fr0'.exec.stack = []

/-! ## `sim_stmts` — the statement-list glue

Induction on `V2.RunStmts`, generalised over the starting cursor `pc`, the IR state `st`,
the gas trace `T`, and the frame `fr`. The run's statement list is the block suffix
`b.stmts.drop pc`; the `cons` case peels the head statement at cursor `pc` (feeding
`SimStmtStep`), then recurses at `pc+1` on the tail `b.stmts.drop (pc+1)`, gluing the two
`Runs` segments with `Runs.trans`. The `stack = []` re-established by each step is exactly
`Corr.stack_nil` for the next, so the invariant threads. -/

/-- **`sim_stmts` (general suffix form).** From `Corr` at cursor `(L, pc)` and a
`V2.RunStmts` of the block suffix `b.stmts.drop pc` (which must be `CallFree`), running the
lowered bytes of those statements reaches a frame `fr'` in `Corr`-correspondence with the
post-state `st'` at cursor `(L, pc + (b.stmts.drop pc).length)`, with the working stack
back to `[]`. Generic over the per-statement simulation `SimStmtStep`. -/
theorem sim_stmts_drop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    {ss : List Stmt} {st st' : V2.IRState} {T T' : Trace} {pc : Nat} {fr : Frame}
    (hss : ss = b.stmts.drop pc)
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hrun : V2.RunStmts prog o st T ss st' T')
    (hcf : CallFree ss) :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L (pc + ss.length)
      ∧ fr'.exec.stack = [] := by
  induction hrun generalizing pc fr with
  | nil =>
    exact ⟨fr, Runs.refl fr, by simpa using hcorr, hcorr.stack_nil⟩
  | @cons st0 st1 st2 T0 T1 T2 s ss0 hh ht ih =>
    -- the head statement `s` sits at cursor `pc`; the tail `ss0` is `b.stmts.drop (pc+1)`.
    obtain ⟨hnc, hcf0⟩ := callFree_of_cons hcf
    have hdrop : b.stmts.drop pc = s :: ss0 := hss.symm
    have hget : b.stmts[pc]? = some s := by
      have h0 : (b.stmts.drop pc)[0]? = some s := by rw [hdrop]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at h0
    have htail : ss0 = b.stmts.drop (pc + 1) := by
      have hdd : (b.stmts.drop pc).drop 1 = b.stmts.drop (pc + 1) := List.drop_drop ..
      rw [hdrop, List.drop_one, List.tail_cons] at hdd
      exact hdd
    -- Layer C: one step matches a Runs segment re-establishing Corr at pc+1, stack = [].
    obtain ⟨fr1, hruns1, hcorr1, _⟩ := hsim pc s st0 st1 T0 T1 fr hget hnc hcorr hh
    -- recurse on the tail at cursor pc+1.
    obtain ⟨fr2, hruns2, hcorr2, hstk2⟩ := ih htail hcorr1 hcf0
    refine ⟨fr2, hruns1.trans hruns2, ?_, hstk2⟩
    -- cursor arithmetic: pc + (1 + ss0.length) = (pc+1) + ss0.length.
    have hlen : pc + (s :: ss0).length = (pc + 1) + ss0.length := by
      simp only [List.length_cons]; omega
    rwa [hlen]

/-- **`sim_stmts` (block-from-`pc` form).** The Layer-D headline as the plan states it:
from `Corr` at cursor `(L, pc)` and a `V2.RunStmts` of a call-free statement list `ss`
that is exactly the block suffix at `pc`, the lowered bytes compose the per-statement
`sim_stmt` segments into one `Runs fr fr'` re-establishing `Corr` at the end cursor, with
`fr'.exec.stack = []`. (The whole-block case is `pc = 0`, `ss = b.stmts`.) -/
theorem sim_stmts {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {ss : List Stmt}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hrun : V2.RunStmts prog o st T ss st' T')
    (hss : ss = b.stmts.drop pc)
    (hcf : CallFree ss) :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L (pc + ss.length)
      ∧ fr'.exec.stack = [] :=
  sim_stmts_drop hsim hss hcorr hrun hcf

/-- **`sim_stmts` (whole-block form).** The `pc = 0` instance: a whole call-free block
body `b.stmts`, run by `V2.RunStmts` from a `Corr`-corresponding frame at the block's
entry cursor `(L, 0)`, is matched by one `Runs fr fr'` re-establishing `Corr` at the
terminator cursor `(L, b.stmts.length)` with an empty working stack — the frame the block
terminator's lowering (Layer E) consumes. -/
theorem sim_stmts_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace}
    {L : Label} {b : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hcf : CallFree b.stmts) :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L b.stmts.length
      ∧ fr'.exec.stack = [] := by
  have h := sim_stmts_drop hsim (by simp) hcorr hrun hcf
  simpa using h

end Lir

-- Build-enforced axiom-cleanliness guard for the D-layer `sim_stmts` deliverable.
#print axioms Lir.sim_stmts
#print axioms Lir.sim_stmts_block
