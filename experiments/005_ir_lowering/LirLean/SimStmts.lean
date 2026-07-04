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

## Scope — all statements (Route B closed the call gap)

`sim_call_stmt` (`SimStmt.lean` Arm 3, Route B) now re-establishes the full `Corr` —
including `Corr.stack_nil`: the Route-B tail consumes the CALL's 0/1 success flag
(`MSTORE` to the result slot, or `POP`), so a `Stmt.call` no longer breaks the clean
`stack = []` induction. Layer D therefore ranges over **all** statement lists — assign,
sstore, AND call — with no call-free side condition.

## The per-statement simulation hypothesis `SimStmtStep`

The three Layer-C arms (`sim_assign`, `sim_sstore_stmt`, `sim_call_stmt`) each take a
bundle of honest per-statement structured hypotheses — the `MatDec` decode coverage at the
static cursors, the gas/stack envelopes, the `SstoreRealises`/`CallRealises` runtime ties,
the per-step `StepScoped` scoping, and the post-state realisability ties. Rather than
re-thread all of those through the list induction (they are per-statement and
per-intermediate-state, so they cannot be stated once up front), Layer D abstracts them
into a single structured hypothesis `SimStmtStep` at exactly the altitude of the Layer-C
conclusion: *for every cursor `pc` in the block holding a statement `s`, any
`Corr`-corresponding frame at `pc` and any `EvalStmt` step of `s` are matched by a `Runs`
segment re-establishing `Corr` at `pc+1` with an empty stack.* This is precisely what
`sim_assign` / `sim_sstore_stmt` / `sim_call_stmt` deliver; discharging `SimStmtStep` for a
concrete program is a mechanical case split feeding each arm its bundle.
(`MatDec`-coverage-as-hypothesis is the same standard `sim_sstore_stmt` itself adopts — see
its `hdv`/`hdk`/`hdop` arguments.)

No `sorry`, no `axiom`, no `native_decide`. Nothing here touches `V2/Machine.lean` /
`V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open BytecodeLayer.Hoare
open Lir.V2

/-! ## The per-statement simulation hypothesis

`SimStmtStep` packages Layer C's conclusion uniformly over the block's cursors: the union
of `sim_assign`'s, `sim_sstore_stmt`'s and `sim_call_stmt`'s conclusions, with their
per-statement structured hypotheses (decode coverage, gas/stack envelopes, realisability)
discharged inside. It is what the list induction consumes at each `cons`. -/

/-- **The per-statement simulation step** (Layer C, all statements, abstracted over cursor).
For statement `s` at cursor `(L, pc)` of block `b`, any frame `fr0` in
`Corr`-correspondence with `st0` at `pc` that **clean-halts non-exceptionally**
(`CleanHaltsNonException fr0` — the remaining run reaches a `.success`/`.revert` terminal) and
any `EvalStmt` step `s : st0 → st0'` are matched by a `Runs fr0 fr0'` re-establishing `Corr` at
`pc+1` with `fr0'.exec.stack = []`. Discharged for a concrete program by case-splitting `s` and
feeding `sim_assign` / `sim_sstore_stmt` / `sim_call_stmt` their structured-hypothesis bundles —
the per-cursor `CleanHaltsNonException fr0` is what lets the GAS/SLOAD arms DERIVE their runtime
gas/mem envelopes from the §7 extractor (`CleanHaltExtract`) rather than supply them. -/
def SimStmtStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (L : Label) (b : Block) : Prop :=
  ∀ (pc : Nat) (s : Stmt) (st0 st0' : V2.IRState) (T0 T0' : Trace) (C0 C0' : CallStream)
    (fr0 : Frame),
    b.stmts[pc]? = some s →
    Corr prog sloadChg obs st0 fr0 L pc →
    CleanHaltsNonException fr0 →
    EvalStmt prog st0 T0 C0 s st0' T0' C0' →
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
`V2.RunStmts` of the block suffix `b.stmts.drop pc`, running the lowered bytes of those
statements reaches a frame `fr'` in `Corr`-correspondence with the post-state `st'` at
cursor `(L, pc + (b.stmts.drop pc).length)`, with the working stack back to `[]`. Generic
over the per-statement simulation `SimStmtStep`. -/
theorem sim_stmts_drop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {L : Label} {b : Block}
    (hsim : SimStmtStep prog sloadChg obs L b)
    {ss : List Stmt} {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream} {pc : Nat}
    {fr : Frame}
    (hss : ss = b.stmts.drop pc)
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hcs : CleanHaltsNonException fr)
    (hrun : V2.RunStmts prog st T C ss st' T' C') :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L (pc + ss.length)
      ∧ fr'.exec.stack = [] := by
  induction hrun generalizing pc fr with
  | nil =>
    exact ⟨fr, Runs.refl fr, by simpa using hcorr, hcorr.stack_nil⟩
  | @cons st0 st1 st2 T0 T1 T2 C0 C1 C2 s ss0 hh ht ih =>
    -- the head statement `s` sits at cursor `pc`; the tail `ss0` is `b.stmts.drop (pc+1)`.
    have hdrop : b.stmts.drop pc = s :: ss0 := hss.symm
    have hget : b.stmts[pc]? = some s := by
      have h0 : (b.stmts.drop pc)[0]? = some s := by rw [hdrop]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at h0
    have htail : ss0 = b.stmts.drop (pc + 1) := by
      have hdd : (b.stmts.drop pc).drop 1 = b.stmts.drop (pc + 1) := List.drop_drop ..
      rw [hdrop, List.drop_one, List.tail_cons] at hdd
      exact hdd
    -- Layer C: one step matches a Runs segment re-establishing Corr at pc+1, stack = [].
    obtain ⟨fr1, hruns1, hcorr1, _⟩ := hsim pc s st0 st1 T0 T1 C0 C1 fr hget hcorr hcs hh
    -- DERIVE the tail's clean-halt witness from the head's, across the head `Runs` segment.
    have hcs1 : CleanHaltsNonException fr1 := cleanHaltsNonException_forward hcs hruns1
    -- recurse on the tail at cursor pc+1.
    obtain ⟨fr2, hruns2, hcorr2, hstk2⟩ := ih htail hcorr1 hcs1
    refine ⟨fr2, hruns1.trans hruns2, ?_, hstk2⟩
    -- cursor arithmetic: pc + (1 + ss0.length) = (pc+1) + ss0.length.
    have hlen : pc + (s :: ss0).length = (pc + 1) + ss0.length := by
      simp only [List.length_cons]; omega
    rwa [hlen]

/-- **`sim_stmts` (block-from-`pc` form).** The Layer-D headline as the plan states it:
from `Corr` at cursor `(L, pc)` and a `V2.RunStmts` of a statement list `ss` that is
exactly the block suffix at `pc`, the lowered bytes compose the per-statement `sim_stmt`
segments into one `Runs fr fr'` re-establishing `Corr` at the end cursor, with
`fr'.exec.stack = []`. (The whole-block case is `pc = 0`, `ss = b.stmts`.) -/
theorem sim_stmts {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream} {ss : List Stmt}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hcs : CleanHaltsNonException fr)
    (hrun : V2.RunStmts prog st T C ss st' T' C')
    (hss : ss = b.stmts.drop pc) :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L (pc + ss.length)
      ∧ fr'.exec.stack = [] :=
  sim_stmts_drop hsim hss hcorr hcs hrun

/-- **`sim_stmts` (whole-block form).** The `pc = 0` instance: a whole block body
`b.stmts`, run by `V2.RunStmts` from a `Corr`-corresponding frame at the block's entry
cursor `(L, 0)`, is matched by one `Runs fr fr'` re-establishing `Corr` at the terminator
cursor `(L, b.stmts.length)` with an empty working stack — the frame the block
terminator's lowering (Layer E) consumes. -/
theorem sim_stmts_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream}
    {L : Label} {b : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hcs : CleanHaltsNonException fr)
    (hrun : V2.RunStmts prog st T C b.stmts st' T' C') :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L b.stmts.length
      ∧ fr'.exec.stack = [] := by
  have h := sim_stmts_drop hsim (by simp) hcorr hcs hrun
  simpa using h

end Lir

-- Build-enforced axiom-cleanliness guard for the D-layer `sim_stmts` deliverable.
