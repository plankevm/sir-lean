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

/-! ## 4. The bytecode witness — two `GAS` opcodes, monotonicity discharged

The internal `Runs` witness, a hand-written PUSH1 bytecode (the prototype's documented
cut — `lower` emits PUSH32, blowing up the decode kernel; the *reasoning* reused is
identical). The two `GAS` opcodes realise the two `gasRead` events; the realised values
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

/-- **The monotonicity law, discharged from the bytecode side.** For `G₀ ≤ g` the actual
gas-descent fact gives `(g2Read g).toNat ≤ (g1Read g).toNat` — the second `GAS` read is
no larger than the first (it charged one more `Gbase`). This is the realised
`Trace.gasMonotone [gasRead (g1Read g), gasRead (g2Read g)]`. -/
theorem gReads_monotone (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (g2Read g).toNat ≤ (g1Read g).toNat := by
  have h1 : (g1Read g).toNat = g.toNat - 22108 := by
    show (UInt256.ofUInt64 (subCharges g gchs1)).toNat = _
    rw [toNat_ofUInt64, toNat_subCharges g gchs1 (by show (22108:ℕ) ≤ g.toNat; omega)]
    show g.toNat - 22108 = _; rfl
  have h2 : (g2Read g).toNat = g.toNat - 22110 := by
    show (UInt256.ofUInt64 (subCharges g gchs2)).toNat = _
    rw [toNat_ofUInt64, toNat_subCharges g gchs2 (by show (22110:ℕ) ≤ g.toNat; omega)]
    show g.toNat - 22110 = _; rfl
  rw [h1, h2]; omega

/-- The realised two-read trace is `gasMonotone` (the §3.4 law holds on the machine). -/
theorem gReads_gasMonotone (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Trace.gasMonotone [Event.gasRead (g1Read g), Event.gasRead (g2Read g)] :=
  gasMonotone_pair.mpr (gReads_monotone g hg)

end Lir.V2

