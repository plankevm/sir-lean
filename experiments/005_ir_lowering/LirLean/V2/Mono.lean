import LirLean.V2.Law
import LirLean.DefsSound
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Hoare.GasMonotone
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Programs
import BytecodeLayer.Observables

/-!
# LirLean v2 — the two-read gas-monotonicity milestone (`docs/ir-design-v2.md` §3.4)

The call-free prototype (`LirLean/V2/Preserve.lean`, `Lir.V2.lower_preserves_obs`)
validated the gas-free machine, the observable boundary and a **single** gas
read. A single read does not exercise the ONE law the gas oracle carries (§3.4): the
sequence of gas reads, in program order, is **monotone non-increasing**. That
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
   the two gas reads AND the realised values are genuinely monotone — the
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

/-! ## 1. The monotonicity law and the guard arithmetic (frame-free, `LirLean/V2/Law.lean`)

The monotonicity law `Trace.gasMonotone` (§3.4), its pair-form
`gasMonotone_pair`, and the guard arithmetic `lt_eq_zero_of_toNat_le` are all frame-free
and live in `LirLean/V2/Law.lean` (imported above). This file uses them; the bytecode-side
discharge of the law (below) is what makes this module the IR↔bytecode bridge for the
two-read milestone. -/

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

/-- `WellFormed` sanity check (B3) — **the discriminating case**. `guardIR`
deliberately *multi-uses* its first gas read `t0`: once in the guard `lt t0 t3` and
again in `ret t0` (`guardBlock2`). `t0` is gas-defined (non-recomputable) yet used
**twice**, so `guardIR` is *not* `WellFormed` — recompute-on-use would re-emit `GAS`
for the `ret`, reading a *fresh* value ≠ the guarded one. This proves the predicate is
genuinely restrictive (not vacuously true), and flags that lifting `guardIR` to the
general lowering needs the future DUP/binding-slot escape hatch noted in the plan. -/
example : ¬ Lir.WellFormed guardIR := by
  intro h
  have hgas : Lir.isGasDef guardIR (tmp 0) := by unfold Lir.isGasDef; decide
  have : Lir.useCount guardIR (tmp 0) ≤ 1 := h (tmp 0) (Or.inl hgas)
  exact absurd this (by decide)

theorem guardIR_block0 : blockAt guardIR (lbl 0) = some guardBlock0 := rfl
theorem guardIR_block2 : blockAt guardIR (lbl 2) = some guardBlock2 := rfl

/-! ### The block-0 statement run over named intermediate states

As in the prototype, each intermediate state is named so every `whnf` stays bounded to a
single `setLocal`/`setStorage` layer. The two gas reads consume `g1` and
`g2`; the stream empties after the second. -/

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
  { world := fun k => if k = (7 : Word) then (5 : Word) else w₀ k
    result := .returned g1 }

private theorem q6_world (w₀ : World) (g1 g2 : Word) :
    (q6 w₀ g1 g2).world = (guardObsResult w₀ g1).world := by
  funext k; show (if k = (7:Word) then (5:Word) else w₀ k) = _; rfl

/-- **The gas-free IR run, using ONLY the monotonicity law.** For any initial world
`w₀` and any two gas readings `g1 g2` whose trace is monotone (`g2 ≤ g1`), `guardIR`
consuming `[g1, g2]` halts with `guardObsResult w₀ g1` — the guard
`lt g1 g2` is `0` (by `lt_eq_zero_of_toNat_le`, the *only* use of the law), so the branch
takes the `GOOD` (else) arm and returns `g1`. The gas values are supplied by the run
(the events); the IR asserts nothing about them beyond monotonicity. -/
theorem guard_IRRun (o : CallOracle) (w₀ : World) (g1 g2 : Word)
    (hmono : Trace.gasMonotone [g1, g2]) :
    IRRun guardIR o w₀ [g1, g2] (guardObsResult w₀ g1) := by
  have hle : g2.toNat ≤ g1.toNat := gasMonotone_pair.mp hmono
  -- the six block-0 statements, each between named states (call-free ⇒ oracle-agnostic)
  have e0 : EvalStmt guardIR o (q0 w₀) [g1, g2]
      (.assign (tmp 0) .gas) (q1 w₀ g1) [g2] := EvalStmt.assignGas
  have e1 : EvalStmt guardIR o (q1 w₀ g1) [g2]
      (.assign (tmp 1) (.imm 5)) (q2 w₀ g1) [g2] :=
    EvalStmt.assignPure (by nofun) rfl
  have e2 : EvalStmt guardIR o (q2 w₀ g1) [g2]
      (.assign (tmp 2) (.imm 7)) (q3 w₀ g1) [g2] :=
    EvalStmt.assignPure (by nofun) rfl
  have e3 : EvalStmt guardIR o (q3 w₀ g1) [g2]
      (.sstore (tmp 2) (tmp 1)) (q4 w₀ g1) [g2] :=
    EvalStmt.sstore (kw := 7) (vw := 5) rfl rfl
  have e4 : EvalStmt guardIR o (q4 w₀ g1) [g2]
      (.assign (tmp 3) .gas) (q5 w₀ g1 g2) [] := EvalStmt.assignGas
  have e5 : EvalStmt guardIR o (q5 w₀ g1 g2) []
      (.assign (tmp 4) (.lt (tmp 0) (tmp 3))) (q6 w₀ g1 g2) [] :=
    EvalStmt.assignPure (by nofun) rfl
  have hss : RunStmts guardIR o (q0 w₀) [g1, g2]
      guardBlock0.stmts (q6 w₀ g1 g2) [] :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))))
  -- the guard `lt g1 g2` is 0 under monotonicity → branch takes the GOOD (else) arm
  have hguard : (q6 w₀ g1 g2).locals (tmp 4) = some 0 := by
    rw [q6_locals4]; rw [lt_eq_zero_of_toNat_le hle]
  have hbranch :
      RunFrom guardIR o (q0 w₀) [g1, g2] (lbl 0)
        { world := (q6 w₀ g1 g2).world, result := .returned g1 } :=
    RunFrom.branchElse (b := guardBlock0) (thenL := lbl 1) (elseL := lbl 2)
      guardIR_block0 hss rfl hguard
      (RunFrom.ret (b := guardBlock2) (t := tmp 0) guardIR_block2 RunStmts.nil rfl
        (q6_locals0 w₀ g1 g2))
  rw [q6_world] at hbranch
  exact hbranch

/-! ## 4. The bytecode witness — two `GAS` opcodes, monotonicity discharged

The internal `Runs` witness, a hand-written PUSH1 bytecode (the prototype's documented
cut — `lower` emits PUSH32, blowing up the decode kernel; the *reasoning* reused is
identical). The two `GAS` opcodes realise the two gas reads; the realised values
are `g1 = ofUInt64 (g − 22108)` and `g2 = ofUInt64 (g − 22110)`, so `g2 ≤ g1` is the
**actual machine gas-descent fact** — that is how we DISCHARGE the §3.4 monotonicity law
from the bytecode side (the same `gasAvailable.toNat` descent the never-OutOfFuel fuel
induction rides; here it is exact `subCharges` arithmetic + `omega`).

```text
pc 0  : PUSH1 5      60 05    value
pc 2  : PUSH1 7      60 07    key
pc 4  : SSTORE       55       storage[7] := 5     (the step between the two reads)
pc 5  : GAS          5a       → g1 (first read)
pc 6  : GAS          5a       → g2 (second read)   [stack: g2 :: g1]
pc 7  : GT           11       → gt g2 g1 = lt g1 g2 (the "did gas go up?" guard)
pc 8  : PUSH1 13     60 0d    JUMPI destination (the BAD block at pc 13)
pc 10 : JUMPI        57       guard = 0 ⇒ fall through to STOP at 11 (GOOD)
pc 11 : STOP         00       (GOOD — the taken fall-through arm)
pc 12 : STOP         00       (padding)
pc 13 : JUMPDEST     5b       (BAD block — never reached under monotonicity)
```
-/
def guardBytecode : ByteArray :=
  ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x5a, 0x5a, 0x11, 0x60,0x0d, 0x57, 0x00, 0x00, 0x5b]⟩

/-- The top-level call running `guardBytecode` in `addrA` (present, default account;
value-free, state-modifying, depth 0) — same world shape as the prototype. -/
def guardParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := (∅ : AccountMap).insert addrA default,
    originalAccounts := ∅, substate := default,
    caller := addrA, origin := addrA, recipient := addrA,
    codeSource := .Code guardBytecode, gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-! ### Decode facts (literal `rfl`, cheap since PUSH1) -/

private def gfr0 (g : UInt64) : Frame := codeFrame (guardParams g) guardBytecode

theorem gdec_0  : decode guardBytecode 0  = some (.Push .PUSH1, some (5, 1))   := by rfl
theorem gdec_2  : decode guardBytecode 2  = some (.Push .PUSH1, some (7, 1))   := by rfl
theorem gdec_4  : decode guardBytecode 4  = some (.Smsf .SSTORE, .none)        := by rfl
theorem gdec_5  : decode guardBytecode 5  = some (.Smsf .GAS, .none)           := by rfl
theorem gdec_6  : decode guardBytecode 6  = some (.Smsf .GAS, .none)           := by rfl
theorem gdec_7  : decode guardBytecode 7  = some (.ArithLogic .GT, .none)      := by rfl
theorem gdec_8  : decode guardBytecode 8  = some (.Push .PUSH1, some (13, 1))  := by rfl
theorem gdec_10 : decode guardBytecode 10 = some (.Smsf .JUMPI, .none)         := by rfl
theorem gdec_11 : decode guardBytecode 11 = some (.System .STOP, .none)        := by rfl

/-! ### The GT opcode rule

There is no `runs_gt` upstream (only `runs_add`/`runs_lt`), so we derive it here. `GT`
dispatches `binOp UInt256.gt exec` — structurally identical to `LT`'s `binOp UInt256.lt`
— so the `stepFrame` characterization is the same proof as the (private) `stepFrame_binOp`
with `op = GT`, landing in the public `binOpPost`. The crucial fact connecting it to the
IR is the definitional `UInt256.gt b a = UInt256.lt a b` (`gt a b = fromBool (a > b)
= fromBool (b < a) = lt b a`). -/

/-- `GT` on `b :: a :: rest` computes `UInt256.gt b a` — definitionally `UInt256.lt a b`
(the order swap). This is what makes the bytecode `GT` realise the IR's `lt g1 g2`. -/
theorem gt_eq_lt_swap (a b : Word) : UInt256.gt b a = UInt256.lt a b := rfl

/-- The post-GT frame (operands `a`/`b` popped, `UInt256.gt a b` pushed). -/
def gtFrame (fr : Frame) (a b : Word) (rest : Stack UInt256) : Frame :=
  { fr with exec := binOpPost fr.exec UInt256.gt a b rest }

/-- The `stepFrame` characterization of `GT` (mirrors the private `stepFrame_binOp`). -/
theorem stepFrame_gt (fr : Frame) (a b : Word) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .GT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (binOpPost fr.exec UInt256.gt a b rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by nofun)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.ArithLogic .GT)
      + stackPushCount (.ArithLogic .GT) > 1024) := by
    simp only [show stackPopCount (.ArithLogic .GT) = 2 from rfl,
               show stackPushCount (.ArithLogic .GT) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  rw [show dispatch (.ArithLogic .GT) .none fr fr.exec = binOp UInt256.gt fr.exec Gverylow from rfl]
  unfold binOp charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  rfl

/-- **The GT `Runs` rule.** One step to `binOpPost fr.exec UInt256.gt a b rest`. -/
theorem runs_gt (fr : Frame) (a b : Word) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .GT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gtFrame fr a b rest) :=
  Runs.single (stepsTo_of_next (stepFrame_gt fr a b rest hdec hstk hsz hgas))

/-! ### The named post-frames (the internal `Runs` witness)

`gf1 … gf6`: PUSH;PUSH;SSTORE;GAS;GAS;GT, then `gf7` pushes the JUMPI destination and the
not-taken JUMPI falls through to the STOP at `gfStop`. -/

private def gf1 (g : UInt64) : Frame := pushFrame (gfr0 g) 5
private def gf2 (g : UInt64) : Frame := pushFrame (gf1 g) 7
private def gf3 (g : UInt64) : Frame := sstoreFrame (gf2 g) 7 5 (gfr0 g).exec.stack
private def gf4 (g : UInt64) : Frame := gasFrame (gf3 g)                       -- g1 read
private def gf5 (g : UInt64) : Frame := gasFrame (gf4 g)                       -- g2 read

/-- The self account is present in the entry world (for the SSTORE lens). -/
private def gSelfAcc (g : UInt64) : Account := (gfr0 g).exec.accounts.find! addrA

private theorem g_self_present (g : UInt64) :
    (gfr0 g).exec.accounts.find? (gfr0 g).exec.executionEnv.address = some (gSelfAcc g) := by rfl

/-- The entry frame's stack is empty. -/
private theorem gfr0_stk (g : UInt64) : (gfr0 g).exec.stack = [] := by rfl

/-! ### The realised gas readings and the monotonicity discharge

`g1Read g = ofUInt64 (gf4.gasAvailable)`, `g2Read g = ofUInt64 (gf5.gasAvailable)` are the
words the two `GAS` opcodes push. The §3.4 monotonicity law `g2.toNat ≤ g1.toNat` is the
**actual gas-descent fact**: `gf5` charged one more `Gbase` than `gf4`, so its gas is
strictly lower. Proved by exact `subCharges` arithmetic + `omega` — the discharge. -/

/-- Charges (execution order) up to the first GAS read: `[3,3,22100,2]`, sum `22108`. -/
private def gchs1 : List ℕ := [3, 3, 22100, 2]
/-- Charges up to the second GAS read: `[3,3,22100,2,2]`, sum `22110`. -/
private def gchs2 : List ℕ := [3, 3, 22100, 2, 2]

private theorem g_gas_f1 (g : UInt64) : (gf1 g).exec.gasAvailable = subCharges g [3] := by
  show (g - UInt64.ofNat Gverylow) = _; rfl
private theorem g_gas_f2 (g : UInt64) : (gf2 g).exec.gasAvailable = subCharges g [3,3] := by
  show ((gf1 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [g_gas_f1]; rfl
private theorem g_gas_f3 (g : UInt64) : (gf3 g).exec.gasAvailable = subCharges g [3,3,22100] := by
  show ((gf2 g).exec.gasAvailable - UInt64.ofNat (sstoreChargeOf (gf2 g).exec 7 5)) = _
  rw [show sstoreChargeOf (gf2 g).exec 7 5 = 22100 from rfl, g_gas_f2]; rfl
private theorem g_gas_f4 (g : UInt64) : (gf4 g).exec.gasAvailable = subCharges g gchs1 := by
  show ((gf3 g).exec.gasAvailable - UInt64.ofNat Gbase) = _; rw [g_gas_f3]; rfl
private theorem g_gas_f5 (g : UInt64) : (gf5 g).exec.gasAvailable = subCharges g gchs2 := by
  show ((gf4 g).exec.gasAvailable - UInt64.ofNat Gbase) = _; rw [g_gas_f4]; rfl

/-- The first GAS read value (the word `gf4`'s GAS opcode pushed). -/
def g1Read (g : UInt64) : Word := UInt256.ofUInt64 (subCharges g gchs1)
/-- The second GAS read value (the word `gf5`'s GAS opcode pushed). -/
def g2Read (g : UInt64) : Word := UInt256.ofUInt64 (subCharges g gchs2)

/-- `UInt256.ofUInt64` preserves `toNat` (the gas word reads back its `UInt64` value).
Limb reconstruction (`toNat_limbs`) of `⟨a.toUInt32, (a>>>32).toUInt32, 0,…⟩`, with the
same `l0`/`l1` simp facts the prototype's `ofUInt64_ne_zero` used. -/
theorem toNat_ofUInt64 (a : UInt64) : (UInt256.ofUInt64 a).toNat = a.toNat := by
  rw [UInt256.toNat_limbs]
  show ((a.toUInt32).toNat + ((a >>> (32:UInt64)).toUInt32).toNat * 2^32
        + 0 * 2^64 + 0 * 2^96 + 0 * 2^128 + 0 * 2^160 + 0 * 2^192 + 0 * 2^224) = a.toNat
  have lt64 : a.toNat < 2^64 := a.toNat_lt
  simp only [UInt64.toUInt32_toNat, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
             show ((32:UInt64).toNat) % 64 = 32 from rfl]
  -- l0 = a.toNat % 2^32, l1 = a.toNat / 2^32 % 2^32, and a.toNat < 2^64
  have dm0 := Nat.div_add_mod a.toNat (2^32)
  have dm1 := Nat.div_add_mod (a.toNat / 2^32) (2^32)
  simp only [show (2:Nat)^64 = 4294967296 * 4294967296 from rfl,
             show (2:Nat)^32 = 4294967296 from rfl] at *
  omega

/-- The realised read words are `ofUInt64` of the GAS-frames' `gasAvailable`, so their
`.toNat` is exactly the machine's `gasAvailable.toNat` at each read (via `toNat_ofUInt64`
and the running-balance facts `g_gas_f4`/`g_gas_f5`). This is the bridge from the read
word's order to the engine's gas order — the quantity `Runs.gasAvailable_le` is monotone
in. -/
private theorem g1Read_toNat (g : UInt64) : (g1Read g).toNat = (gf4 g).exec.gasAvailable.toNat := by
  show (UInt256.ofUInt64 (subCharges g gchs1)).toNat = _
  rw [toNat_ofUInt64, g_gas_f4]
private theorem g2Read_toNat (g : UInt64) : (g2Read g).toNat = (gf5 g).exec.gasAvailable.toNat := by
  show (UInt256.ofUInt64 (subCharges g gchs2)).toNat = _
  rw [toNat_ofUInt64, g_gas_f5]

/-- **The monotonicity law, discharged from the bytecode side — through the engine's
gas-descent lemma, not `subCharges` arithmetic.** The second `GAS` read happens at `gf5`,
reachable from `gf4` (the first read) by one `GAS` step (`Runs (gf4 g) (gf5 g)`), so
`Runs.gasAvailable_le` (`GasMonotone.lean`, the §3.4 "holds across calls" fact) forces
`(gf5 g).gasAvailable.toNat ≤ (gf4 g).gasAvailable.toNat`; via `g1Read_toNat`/`g2Read_toNat`
that is `(g2Read g).toNat ≤ (g1Read g).toNat`. This is the realised
`Trace.gasMonotone [g1Read g, g2Read g]` — monotonicity is a
*consequence of the run*, not assumed. -/
theorem gReads_monotone (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (g2Read g).toNat ≤ (g1Read g).toNat := by
  -- `gf5 = gasFrame (gf4 g)`: one GAS step, the same gate `g_runs` uses for the second read.
  have hrun : Runs (gf4 g) (gf5 g) :=
    runs_gas (gf4 g) gdec_6 (by show (1:ℕ)+1≤1024; omega)
      (by show Gbase ≤ (gf4 g).exec.gasAvailable.toNat
          rw [show Gbase = 2 from rfl, g_gas_f4, toNat_subCharges g gchs1 (by show (22108:ℕ) ≤ g.toNat; omega)]
          show (2:ℕ) ≤ g.toNat - gchs1.sum; show (2:ℕ) ≤ g.toNat - 22108; omega)
  rw [g1Read_toNat, g2Read_toNat]
  exact Runs.gasAvailable_le hrun

/-- The realised two-read trace is `gasMonotone` (the §3.4 law holds on the machine). -/
theorem gReads_gasMonotone (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Trace.gasMonotone [(g1Read g), (g2Read g)] :=
  gasMonotone_pair.mpr (gReads_monotone g hg)

/-! ### The realisability witness, exported for the `Oracle` interface

The milestone trace is *realised* (`LirLean/V2/Oracle.lean`'s `GasRealises`) by two
`Runs`-threaded GAS-frames whose `ofUInt64`-gas words are exactly `g1Read g`/`g2Read g`.
We export that as an existential over frames (the private `gf4`/`gf5`), so `Oracle` can
instantiate its `GasRealises` predicate against this concrete witness without naming the
internal frames. -/

/-- **The milestone trace's realisability data.** There are two frames `a` (first read)
and `b` (second read), `Runs`-threaded (`b` reachable from `a`), whose reported gas words
(`ofUInt64` of `gasAvailable`) are exactly `g1Read g`/`g2Read g`. This is the concrete
witness `Oracle.GasRealises` packages for the two-read milestone. -/
theorem gReads_realisable (g : UInt64) (hg : 30000 ≤ g.toNat) :
    ∃ a b : Frame, Runs a b
      ∧ g1Read g = UInt256.ofUInt64 a.exec.gasAvailable
      ∧ g2Read g = UInt256.ofUInt64 b.exec.gasAvailable :=
  ⟨gf4 g, gf5 g,
    runs_gas (gf4 g) gdec_6 (by show (1:ℕ)+1≤1024; omega)
      (by show Gbase ≤ (gf4 g).exec.gasAvailable.toNat
          rw [show Gbase = 2 from rfl, g_gas_f4, toNat_subCharges g gchs1 (by show (22108:ℕ) ≤ g.toNat; omega)]
          show (2:ℕ) ≤ g.toNat - gchs1.sum; show (2:ℕ) ≤ g.toNat - 22108; omega),
    by show UInt256.ofUInt64 (subCharges g gchs1) = _; rw [g_gas_f4],
    by show UInt256.ofUInt64 (subCharges g gchs2) = _; rw [g_gas_f5]⟩

/-! ### The assembled `Runs` from entry to the STOP halt

`gfr0 → gf5` is the PUSH;PUSH;SSTORE;GAS;GAS prefix; `gf6` is the GT; then PUSH 13 and the
not-taken JUMPI fall through to the STOP at pc 11. The two `GAS` opcodes' pushed words are
`g1Read g`/`g2Read g`; the GT computes the guard, which `gReads_monotone` forces to `0`, so
the JUMPI is **not taken** (fall-through) — the bytecode takes the same arm as the IR. -/

private def gf6 (g : UInt64) : Frame := gtFrame (gf5 g) (g2Read g) (g1Read g) (gfr0 g).exec.stack
private def gf7 (g : UInt64) : Frame := pushFrame (gf6 g) 13
private def gfStop (g : UInt64) : Frame := jumpiFallthroughFrame (gf7 g) (gfr0 g).exec.stack

private theorem g_toNat_prefix (g : UInt64) (hg : 30000 ≤ g.toNat)
    (l : List ℕ) (hle : l.sum ≤ 22223) : (subCharges g l).toNat = g.toNat - l.sum :=
  toNat_subCharges g l (by omega)

/-- The stack at `gf5` (after both GAS reads) is `g2 :: g1 :: rest`, `rest` the entry
stack (empty; SSTORE popped `7`/`5` back to it). -/
private theorem gf5_stk (g : UInt64) :
    (gf5 g).exec.stack = (g2Read g) :: (g1Read g) :: (gfr0 g).exec.stack := by
  show Stack.push (gf4 g).exec.stack (UInt256.ofUInt64 (gf5 g).exec.gasAvailable) = _
  show Stack.push (Stack.push (gf3 g).exec.stack (UInt256.ofUInt64 (gf4 g).exec.gasAvailable))
        (UInt256.ofUInt64 (gf5 g).exec.gasAvailable) = _
  rw [g_gas_f4, g_gas_f5]; rfl

/-- The guard word (top of `gf6`) is `UInt256.lt (g1Read g) (g2Read g)` — `0` under
monotonicity, so the JUMPI falls through. The JUMPI stack at `gf7` is `13 :: guard :: rest`. -/
private theorem gf7_stk (g : UInt64) :
    (gf7 g).exec.stack
      = (13 : Word) :: UInt256.lt (g1Read g) (g2Read g) :: (gfr0 g).exec.stack := by
  show Stack.push (gf6 g).exec.stack 13 = _
  show Stack.push ((BytecodeLayer.Dispatch.binOpPost (gf5 g).exec UInt256.gt (g2Read g) (g1Read g) (gfr0 g).exec.stack).stack) 13 = _
  show Stack.push (Stack.push (gfr0 g).exec.stack (UInt256.gt (g2Read g) (g1Read g))) 13 = _
  rw [gt_eq_lt_swap]; rfl

/-- **The whole good path composes into one `Runs (gfr0 g) (gfStop g)`.**
PUSH;PUSH;SSTORE;GAS;GAS;GT;PUSH;JUMPI(fall-through), glued by `Runs.trans`; each gas gate
threads `g` through `g_gas_f*` + `g_toNat_prefix` then `omega`. -/
private theorem g_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs (gfr0 g) (gfStop g) := by
  refine Runs.trans (runs_push1 (gfr0 g) 5 gdec_0 ?p0 (by show (0:ℕ)+1≤1024; omega))
    (Runs.trans (runs_push1 (gf1 g) 7 gdec_2 ?p1 (by show (1:ℕ)+1≤1024; omega))
    (Runs.trans (runs_sstore (gf2 g) 7 5 (gfr0 g).exec.stack gdec_4 rfl (by show (2:ℕ)≤1024; omega)
        rfl ?stip ?cost)
    (Runs.trans (runs_gas (gf3 g) gdec_5 (by show (0:ℕ)+1≤1024; omega) ?gg1)
    (Runs.trans (runs_gas (gf4 g) gdec_6 (by show (1:ℕ)+1≤1024; omega) ?gg2)
    (Runs.trans (runs_gt (gf5 g) (g2Read g) (g1Read g) (gfr0 g).exec.stack gdec_7 (gf5_stk g) (by rw [gf5_stk]; show (2:ℕ)≤1024; omega) ?ggt)
    (Runs.trans (runs_push1 (gf6 g) 13 gdec_8 ?p13 (by
        show (gf6 g).exec.stack.size + 1 ≤ 1024
        show ((BytecodeLayer.Dispatch.binOpPost (gf5 g).exec UInt256.gt (g2Read g) (g1Read g) (gfr0 g).exec.stack).stack).size + 1 ≤ 1024
        show (Stack.push (gfr0 g).exec.stack (UInt256.gt (g2Read g) (g1Read g))).size + 1 ≤ 1024
        rw [gfr0_stk]; show (0:ℕ) + 1 + 1 ≤ 1024; omega))
      (runs_branch (dest := 13) (cond := UInt256.lt (g1Read g) (g2Read g)) (rest := (gfr0 g).exec.stack)
        gdec_10 (gf7_stk g) (by rw [show (pushFrame (gf6 g) 13) = gf7 g from rfl, gf7_stk]; show (2:ℕ)≤1024; omega) ?ghi
        (Or.inr ⟨lt_eq_zero_of_toNat_le (gReads_monotone g hg), Runs.refl _⟩))))))))
  case p0 => show 3 ≤ (gfr0 g).exec.gasAvailable.toNat; show 3 ≤ g.toNat; omega
  case p1 => rw [g_gas_f1, g_toNat_prefix g hg [3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case stip =>
    show ¬ (gf2 g).exec.gasAvailable.toNat ≤ Gcallstipend
    rw [g_gas_f2, g_toNat_prefix g hg [3,3] (by decide), show Gcallstipend = 2300 from rfl]
    simp only [List.sum_cons, List.sum_nil]; omega
  case cost =>
    rw [show sstoreChargeOf (gf2 g).exec 7 5 = 22100 from rfl, g_gas_f2,
        g_toNat_prefix g hg [3,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case gg1 =>
    show Gbase ≤ (gf3 g).exec.gasAvailable.toNat
    rw [show Gbase = 2 from rfl, g_gas_f3, g_toNat_prefix g hg [3,3,22100] (by decide)]
    simp only [List.sum_cons, List.sum_nil]; omega
  case gg2 =>
    show Gbase ≤ (gf4 g).exec.gasAvailable.toNat
    rw [show Gbase = 2 from rfl, g_gas_f4, g_toNat_prefix g hg gchs1 (by decide)]
    show (2:ℕ) ≤ g.toNat - gchs1.sum; show (2:ℕ) ≤ g.toNat - 22108; omega
  case ggt =>
    show Gverylow ≤ (gf5 g).exec.gasAvailable.toNat
    rw [show Gverylow = 3 from rfl, g_gas_f5, g_toNat_prefix g hg gchs2 (by decide)]
    show (3:ℕ) ≤ g.toNat - gchs2.sum; show (3:ℕ) ≤ g.toNat - 22110; omega
  case p13 =>
    show 3 ≤ (gf6 g).exec.gasAvailable.toNat
    show 3 ≤ (BytecodeLayer.Dispatch.binOpPost (gf5 g).exec UInt256.gt (g2Read g) (g1Read g) []).gasAvailable.toNat
    show 3 ≤ ((gf5 g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
    rw [show Gverylow = 3 from rfl, g_gas_f5]
    rw [toNat_sub_ofNat _ 3 (by rw [g_toNat_prefix g hg gchs2 (by decide)]; show (3:ℕ) ≤ g.toNat - 22110; omega) (by omega),
        g_toNat_prefix g hg gchs2 (by decide)]
    show (3:ℕ) ≤ (g.toNat - gchs2.sum) - 3; show (3:ℕ) ≤ (g.toNat - 22110) - 3; omega
  case ghi =>
    show Ghigh ≤ (gf7 g).exec.gasAvailable.toNat
    show Ghigh ≤ ((gf6 g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
    show Ghigh ≤ ((BytecodeLayer.Dispatch.binOpPost (gf5 g).exec UInt256.gt (g2Read g) (g1Read g) (gfr0 g).exec.stack).gasAvailable - UInt64.ofNat Gverylow).toNat
    show Ghigh ≤ (((gf5 g).exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow).toNat
    have hb : (gf5 g).exec.gasAvailable.toNat = g.toNat - 22110 := by
      rw [g_gas_f5, g_toNat_prefix g hg gchs2 (by decide)]; show g.toNat - gchs2.sum = _; show g.toNat - 22110 = _; rfl
    rw [show Ghigh = 10 from rfl, show Gverylow = 3 from rfl]
    rw [toNat_sub_ofNat _ 3 (by
          rw [toNat_sub_ofNat _ 3 (by rw [hb]; omega) (by omega), hb]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw [hb]; omega) (by omega), hb]; omega

/-! ### The top-level `messageCall` observable

`gfStop` (pc 11) decodes to STOP and halts successfully (empty output); `messageCall`
delivers the assembled run's halt via `messageCall_runs`, leaving `5` at `(addrA, 7)`. -/

/-- The STOP at `gfStop g` halts successfully with empty output. -/
private theorem gfStop_halts (g : UInt64) :
    stepFrame (gfStop g) = .halted (.success (gfStop g).exec .empty) :=
  stepFrame_stop (gfStop g)
    (by show decode (gfStop g).exec.executionEnv.code (gfStop g).exec.pc = _
        show decode guardBytecode 11 = _; exact gdec_11)
    (by show (gfStop g).exec.stack.size ≤ 1024
        show (jumpiFallthroughFrame (gf7 g) (gfr0 g).exec.stack).exec.stack.size ≤ 1024
        show ((BytecodeLayer.Dispatch.jumpiFallthroughPost (gf7 g).exec (gfr0 g).exec.stack).stack).size ≤ 1024
        rw [gfr0_stk]; show (0:ℕ) ≤ 1024; omega)

/-- The halt the assembled run lands on (STOP success, empty output). -/
private def gHalt (g : UInt64) : FrameHalt := .success (gfStop g).exec .empty

/-- **`messageCall` of the witness bytecode** pins to the assembled run's halt. -/
theorem g_messageCall (g : UInt64) (hg : 30000 ≤ g.toNat) :
    messageCall (guardParams g)
      = .ok (FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))) :=
  messageCall_runs (guardParams g)
    (beginCall_code (guardParams g) guardBytecode rfl)
    (g_runs g hg)
    (gfStop_halts g)

/-- The completed call's storage at `(addrA, 7)` is `5` (the SSTORE'd value, preserved by
every later transformer). -/
theorem g_storageAt (g : UInt64) :
    CallResult.storageAt (FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))) addrA 7 = 5 := by
  show ((endFrame (gfStop g) (gHalt g)).toCallResult.accounts.find? addrA
          |>.option 0 (·.lookupStorage 7)) = 5
  have hacc : (endFrame (gfStop g) (gHalt g)).toCallResult.accounts = (gf3 g).exec.accounts := by rfl
  rw [hacc]
  exact sstoreFrame_storage_self (gf2 g) 7 5 (gfr0 g).exec.stack (gSelfAcc g)
    (by show (gf2 g).exec.accounts.find? (gf2 g).exec.executionEnv.address = _; exact g_self_present g)
    (by decide)

/-- The completed call succeeded. -/
theorem g_success (g : UInt64) :
    (FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))).success = true := by rfl

/-! ## 5. The headline (`docs/ir-design-v2.md` §4, two-read monotonicity milestone)

`LoweredRunHasObsMono` is the bytecode-side conclusion: at gas `g`, the witness bytecode (the
internal `Runs` witness) halts with the same observable `O`, **its two `GAS` opcodes
realising the two gas reads** AND the realised values **genuinely monotone**. No
`pc`, no gas-equality appears — only:

* `realises` — the stream is exactly the two machine `GAS` values `[g1Read g, g2Read g]`
  (the §3.4 "reads witnessed by the bytecode" clause, now for TWO reads);
* `monotone` — those realised values satisfy the §3.4 law (`gReads_gasMonotone`),
  **discharged from the EVM gas-descent fact**, not assumed;
* `world` — the completed call's storage agrees with `O.world` at `(addrA, 7)`;
* `success` — the call completed without reverting.

All `Runs`/pc/stack/gas bookkeeping lives *inside* `g_messageCall`'s `Runs` witness. -/
def LoweredRunHasObsMono (g : UInt64) (T : Trace) (O : Observable) : Prop :=
  -- the two gas reads are realised by the two actual GAS opcode values …
  (T = [(g1Read g), (g2Read g)])
  -- … and those realised values are genuinely monotone (the §3.4 law, discharged) …
  ∧ Trace.gasMonotone T
  -- … and the lowered bytecode at gas g completes with O's observable.
  ∧ ∃ out σ,
      Outcome.ofCall (messageCall (guardParams g)) = .completed out σ
      ∧ σ addrA 7 = O.world 7
      ∧ (O.result = .stopped ∨ ∃ w, O.result = .returned w)

/-- **The two-read gas-monotonicity milestone (`docs/ir-design-v2.md` §3.4, §4).**

There is an adequacy floor `G₀` such that for every gas `g ≥ G₀`:

* the gas-free IR run of `guardIR` from `w₀`, consuming the **realised** two-read trace
  `[g1Read g, g2Read g]` **which is `gasMonotone`**, produces the
  observable `O = guardObsResult w₀ (g1Read g)` — the run lands at `GOOD` because the
  guard `lt g1 g2` is forced to `0` by monotonicity (`guard_IRRun`, the IR side using ONLY
  §3.4's law);
* the lowered bytecode at gas `g` halts with that **same** observable `O`, **its two `GAS`
  opcodes realising the two gas reads, and those realised values are monotone**
  (`LoweredRunHasObsMono`) — the monotonicity is **discharged internally** from the bytecode's
  gas descent (`gReads_gasMonotone`), never assumed.

The §4 shape `∃ G₀, ∀ g ≥ G₀, …` is preserved with **no `pc` and no gas-equality** in the
statement; the only gas fact is the envelope `G₀ ≤ g`. The IR and the bytecode take the
same branch precisely because they share the same realised, monotone trace `T`. -/
theorem lower_preserves_obs_mono (o : CallOracle) (w₀ : World) :
    ∃ G₀ : UInt64, ∀ g : UInt64, G₀.toNat ≤ g.toNat →
      IRRun guardIR o w₀ [(g1Read g), (g2Read g)]
        (guardObsResult w₀ (g1Read g))
      ∧ LoweredRunHasObsMono g [(g1Read g), (g2Read g)]
        (guardObsResult w₀ (g1Read g)) := by
  refine ⟨30000, fun g hg => ⟨guard_IRRun o w₀ (g1Read g) (g2Read g) (gReads_gasMonotone g hg), ?_⟩⟩
  refine ⟨rfl, gReads_gasMonotone g hg, ?_⟩
  -- the bytecode observable, from g_messageCall
  refine ⟨(FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))).output,
          CallResult.storageAt (FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))),
          ?_, ?_, ?_⟩
  · -- Outcome.ofCall (messageCall …) = .completed _ σ
    rw [show Outcome.ofCall (messageCall (guardParams g))
          = Outcome.ofResult (FrameResult.toCallResult (endFrame (gfStop g) (gHalt g))) from by
        unfold Outcome.ofCall; rw [g_messageCall g hg]]
    unfold Outcome.ofResult
    rw [if_pos (g_success g)]
  · -- σ addrA 7 = (guardObsResult w₀ (g1Read g)).world 7 = 5
    rw [g_storageAt g]; rfl
  · -- O.result is a return
    exact Or.inr ⟨_, rfl⟩

-- Build-enforced axiom-cleanliness guard: the milestone headline depends only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms lower_preserves_obs_mono

end Lir.V2

