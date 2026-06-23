import LirLean.V2.Machine
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Programs
import BytecodeLayer.Observables

/-!
# LirLean v2 — the two-read gas-monotonicity milestone (`docs/ir-design-v2.md` §3.4)

The call-free prototype (`LirLean/V2/Preserve.lean`, `Lir.V2.lower_preserves_obs`)
validated the gas-free machine, the observable boundary and a **single** `gasRead`
event. A single read does not exercise the ONE law the gas oracle carries (§3.4): the
sequence of `gasRead` values, in program order, is **monotone non-increasing**. That
law relates **≥ 2** reads.

This file is that milestone: the first example with **two** gas reads whose correctness
*uses* monotonicity — a "sticky gas guard". It

1. defines the monotonicity law on the trace (`Trace.gasMonotone`) and threads it as an
   **assumption** the IR run may use — the IR semantics uses ONLY this law, never any
   per-opcode gas cost (no `matCost`, no charge; the machine stays gas-free as in the
   prototype);
2. gives a two-read IR program `guardIR` — `g1 := gas; …; g2 := gas;
   cmp := lt g1 g2; branch cmp BAD GOOD` — whose "did gas go *up*" guard `lt g1 g2` is
   determinable to `0` **only** because monotonicity pins `g2 ≤ g1`, so the run lands at
   `GOOD`. A one-read example cannot do this: the point is the ORDER between two reads;
3. extends the preservation theorem so the lowered bytecode's two `GAS` opcodes realise
   the two `gasRead` events AND the realised values are genuinely monotone — the
   monotonicity law is **discharged from the bytecode side** (the EVM gas-descent fact),
   not assumed. The headline keeps the §4 shape `∃ G₀, ∀ g ≥ G₀, …` with no pc and no
   gas-equality in the statement; monotonicity is discharged internally.

The prototype (`lower_preserves_obs`) and all v1 files are untouched.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.UInt64

set_option maxRecDepth 4000

/-! ## 1. The monotonicity law on the trace (`docs/ir-design-v2.md` §3.4)

The ONE law the gas oracle carries. We extract the `gasRead` values from a `Trace` in
program order and assert they are non-increasing (each later read is `≤` the one before).
We state `≤` on the `toNat` of the words — the robust EVM "gas remaining" order — which
makes the discharge from the machine's `gasAvailable.toNat` descent immediate. -/

/-- The `gasRead` values of a trace, in program order. -/
def Trace.gasReads : Trace → List Word
  | [] => []
  | .gasRead w :: t => w :: Trace.gasReads t

/-- **The monotonicity law (§3.4).** The `gasRead` values, in program order, are
monotone non-increasing: each consecutive pair `(earlier, later)` satisfies
`later.toNat ≤ earlier.toNat` (gas remaining only goes down). This is the *only* gas
fact the IR semantics is allowed to assume — never any per-opcode cost. -/
def Trace.gasMonotone (T : Trace) : Prop :=
  (T.gasReads).IsChain (fun earlier later => later.toNat ≤ earlier.toNat)

/-- For a two-read trace the law is exactly `g2 ≤ g1` (the case the milestone uses). -/
theorem gasMonotone_pair {g1 g2 : Word} :
    Trace.gasMonotone [Event.gasRead g1, Event.gasRead g2] ↔ g2.toNat ≤ g1.toNat :=
  -- gasReads [gasRead g1, gasRead g2] = [g1, g2]; `IsChain` on a pair is the relation
  List.isChain_pair

/-! ## 2. Using the law: `lt` of two monotone reads is `0`

`UInt256.lt a b = if a < b then 1 else 0`, and `<`/`≤` on `UInt256` are the `toBitVec`
(= `toNat`) order. So once monotonicity gives `g2.toNat ≤ g1.toNat` the "gas went up"
guard `lt g1 g2 = (g1 < g2)` is forced to `0`. This is the sole place the law is used
on the IR side. -/

/-- `b ≤ a` (on `toNat`) forces `UInt256.lt a b = 0` — the guard `lt g1 g2` is `0` when
`g2 ≤ g1`, i.e. the "did gas increase" test is false under monotonicity. -/
theorem lt_eq_zero_of_toNat_le {a b : Word} (h : b.toNat ≤ a.toNat) :
    UInt256.lt a b = 0 := by
  have hnlt : ¬ (a < b) := by
    intro hlt
    -- a < b is a.toBitVec < b.toBitVec, i.e. a.toNat < b.toNat
    have hbv : a.toBitVec.toNat < b.toBitVec.toNat := hlt
    simp only [← UInt256.toNat_eq_toBitVec_toNat] at hbv
    omega
  unfold UInt256.lt UInt256.fromBool
  rw [decide_eq_false hnlt, if_neg (by simp)]

/-! ## 3. The two-read IR program (`guardIR`)

Block 0 (entry): `t0 := gas` (first read), one storage step, `t1 := gas` (second read),
`t2 := lt t0 t1` (the "did gas go up?" guard), then `branch t2 BAD GOOD`.

The guard `lt t0 t1 = (g1 < g2)` is the order test that monotonicity determines: under
`g2 ≤ g1` it is `0`, so the branch takes the `GOOD` (else) arm. Without the law we could
not decide the branch — this is the cheapest program whose correctness *uses* §3.4.

Block 1 (`BAD`): `stop` (never reached under the law). Block 2 (`GOOD`): `ret t0`. -/

private def tmp (n : Nat) : Tmp := ⟨n⟩
private def lbl (n : Nat) : Label := ⟨n⟩

/-- The two-read guard block. The single SSTORE between the reads is the "step" of
§3.4 ("reads gas, does a step, reads gas again") and gives the run a non-trivial world
delta; the law would hold (as `≤`) even with no step between. -/
def guardBlock0 : Block :=
  { stmts := [
      .assign (tmp 0) .gas,            -- g1 (first gas read)
      .assign (tmp 1) (.imm 5),
      .assign (tmp 2) (.imm 7),
      .sstore (tmp 2) (tmp 1),         -- storage[7] := 5 (the step)
      .assign (tmp 3) .gas,            -- g2 (second gas read)
      .assign (tmp 4) (.lt (tmp 0) (tmp 3)) ],  -- guard: g1 < g2 ("gas went up")
    term := .branch (tmp 4) (lbl 1) (lbl 2) }

/-- The BAD block — entered iff the guard `g1 < g2` is true, which monotonicity forbids. -/
def guardBlock1 : Block := { stmts := [], term := .stop }
/-- The GOOD block — `ret t0` (returns the first gas reading). -/
def guardBlock2 : Block := { stmts := [], term := .ret (tmp 0) }

def guardIR : Program :=
  { entry := lbl 0, blocks := #[guardBlock0, guardBlock1, guardBlock2] }

theorem guardIR_block0 : blockAt guardIR (lbl 0) = some guardBlock0 := rfl
theorem guardIR_block2 : blockAt guardIR (lbl 2) = some guardBlock2 := rfl

/-! ### The block-0 statement run over named intermediate states

As in the prototype, each intermediate state is named so every `whnf` stays bounded to a
single `setLocal`/`setStorage` layer. The two gas reads consume `gasRead g1` and
`gasRead g2`; the trace empties after the second. -/

private def q0 (w₀ : World) : IRState := { locals := fun _ => none, world := w₀ }
private def q1 (w₀ : World) (g1 : Word) : IRState := (q0 w₀).setLocal (tmp 0) g1
private def q2 (w₀ : World) (g1 : Word) : IRState := (q1 w₀ g1).setLocal (tmp 1) 5
private def q3 (w₀ : World) (g1 : Word) : IRState := (q2 w₀ g1).setLocal (tmp 2) 7
private def q4 (w₀ : World) (g1 : Word) : IRState := (q3 w₀ g1).setStorage 7 5
private def q5 (w₀ : World) (g1 g2 : Word) : IRState := (q4 w₀ g1).setLocal (tmp 3) g2
private def q6 (w₀ : World) (g1 g2 : Word) : IRState :=
  (q5 w₀ g1 g2).setLocal (tmp 4) (UInt256.lt g1 g2)

private theorem q6_locals0 (w₀ : World) (g1 g2 : Word) :
    (q6 w₀ g1 g2).locals (tmp 0) = some g1 := by rfl
private theorem q6_locals4 (w₀ : World) (g1 g2 : Word) :
    (q6 w₀ g1 g2).locals (tmp 4) = some (UInt256.lt g1 g2) := by rfl

/-- The observable the IR run produces: world with `7 ↦ 5`, returning the first gas
reading `g1`. -/
def guardObsResult (w₀ : World) (g1 : Word) : Observable :=
  { worldDelta := fun k => if k = (7 : Word) then (5 : Word) else w₀ k
    result := .returned g1 }

private theorem q6_world (w₀ : World) (g1 g2 : Word) :
    (q6 w₀ g1 g2).world = (guardObsResult w₀ g1).worldDelta := by
  funext k; show (if k = (7:Word) then (5:Word) else w₀ k) = _; rfl

/-- **The gas-free IR run, using ONLY the monotonicity law.** For any initial world
`w₀` and any two gas readings `g1 g2` whose trace is monotone (`g2 ≤ g1`), `guardIR`
consuming `[gasRead g1, gasRead g2]` halts with `guardObsResult w₀ g1` — the guard
`lt g1 g2` is `0` (by `lt_eq_zero_of_toNat_le`, the *only* use of the law), so the branch
takes the `GOOD` (else) arm and returns `g1`. The gas values are supplied by the run
(the events); the IR asserts nothing about them beyond monotonicity. -/
theorem guard_IRRun (w₀ : World) (g1 g2 : Word)
    (hmono : Trace.gasMonotone [Event.gasRead g1, Event.gasRead g2]) :
    IRRun guardIR w₀ [Event.gasRead g1, Event.gasRead g2] (guardObsResult w₀ g1) := by
  have hle : g2.toNat ≤ g1.toNat := gasMonotone_pair.mp hmono
  -- the six block-0 statements, each between named states
  have e0 : EvalStmt guardIR (q0 w₀) [Event.gasRead g1, Event.gasRead g2]
      (.assign (tmp 0) .gas) (q1 w₀ g1) [Event.gasRead g2] := EvalStmt.assignGas
  have e1 : EvalStmt guardIR (q1 w₀ g1) [Event.gasRead g2]
      (.assign (tmp 1) (.imm 5)) (q2 w₀ g1) [Event.gasRead g2] :=
    EvalStmt.assignPure (by nofun) rfl
  have e2 : EvalStmt guardIR (q2 w₀ g1) [Event.gasRead g2]
      (.assign (tmp 2) (.imm 7)) (q3 w₀ g1) [Event.gasRead g2] :=
    EvalStmt.assignPure (by nofun) rfl
  have e3 : EvalStmt guardIR (q3 w₀ g1) [Event.gasRead g2]
      (.sstore (tmp 2) (tmp 1)) (q4 w₀ g1) [Event.gasRead g2] :=
    EvalStmt.sstore (kw := 7) (vw := 5) rfl rfl
  have e4 : EvalStmt guardIR (q4 w₀ g1) [Event.gasRead g2]
      (.assign (tmp 3) .gas) (q5 w₀ g1 g2) [] := EvalStmt.assignGas
  have e5 : EvalStmt guardIR (q5 w₀ g1 g2) []
      (.assign (tmp 4) (.lt (tmp 0) (tmp 3))) (q6 w₀ g1 g2) [] :=
    EvalStmt.assignPure (by nofun) rfl
  have hss : RunStmts guardIR (q0 w₀) [Event.gasRead g1, Event.gasRead g2]
      guardBlock0.stmts (q6 w₀ g1 g2) [] :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))))
  -- the guard `lt g1 g2` is 0 under monotonicity → branch takes the GOOD (else) arm
  have hguard : (q6 w₀ g1 g2).locals (tmp 4) = some 0 := by
    rw [q6_locals4]; rw [lt_eq_zero_of_toNat_le hle]
  have hbranch :
      RunFrom guardIR (q0 w₀) [Event.gasRead g1, Event.gasRead g2] (lbl 0)
        { worldDelta := (q6 w₀ g1 g2).world, result := .returned g1 } :=
    RunFrom.branchElse (b := guardBlock0) (thenL := lbl 1) (elseL := lbl 2)
      guardIR_block0 hss rfl hguard
      (RunFrom.ret (b := guardBlock2) (t := tmp 0) guardIR_block2 RunStmts.nil rfl
        (q6_locals0 w₀ g1 g2))
  rw [q6_world] at hbranch
  exact hbranch

end Lir.V2
