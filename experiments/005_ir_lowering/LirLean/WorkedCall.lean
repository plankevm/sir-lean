import LirLean.Match
import LirLean.Decode
import BytecodeLayer.Programs
import BytecodeLayer.Hoare.Sequence
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.ExternalCall

/-!
# LirLean — the worked single-call program `Runs` assembly (C3d)

This module assembles the concrete `Runs` for the worked single-call program
`Lir.Decode.workedCall`, running it as a top-level `messageCall` over the
caller/callee world of exp003 (`BytecodeLayer.Programs`, whose `accts` carries the
`0xCA11EE` callee with its `calleeProg` code), and discharges
`lower_preserves` across `messageCall_runs`.

## What is proved here (C3d)

* `wc_begin` — the lowered program enters as code (`EntersAsCode`), giving the
  concrete entry frame `wcFrame g = codeFrame (wcParams g) (lower workedCall)`.
* `wc_prefix_runs` — **the genuine straight-line prefix run**: from the entry frame,
  the lowered opcodes of block 0 up to (and including pushing the seven CALL args)
  `Runs` to the CALL-site frame `wcCallSite g`. This is a real `Runs.trans` chain of
  the exp003 opcode rules (`runs_jumpdest`, `runs_push`, `runs_sstore`) instantiated
  on the concrete `lower workedCall` byte stream — decode at every pc is the
  offset-table address, reduced in the kernel; gas threads through `subCharges`
  exactly as `CallerProgExample.caller_prefix_runs`.
* `wc_call_step` — the CALL step at `wcCallSite g` (`stepFrame_call`).
* `wc_preserves` — **`lower_preserves` for `workedCall`** (the bridge half): given a
  returning external CALL (`CallReturns (wcCallSite g) resumeFr`, the documented
  remainder — a genuine child `drive` run for the `0xCA11EE` callee) and the
  post-CALL `Runs resumeFr last` to a halting `last`, the top-level `messageCall`
  pins to `last`'s halt result. This consumes `lower_preserves_discharge` over the
  assembled prefix + the `Runs.call` node, exactly the
  `Examples.TwoCallExample.twoCall_messageCall` shape, specialised to the single
  worked CALL of `workedCall`.

## The branch terminator — now CLOSED (Track A `validJumpDests` detotalization)

The post-CALL branch terminator is **no longer a remainder**. Track A detotalized
`validJumpDests` (it is now a total, kernel-reducible def with the characterization
lemma `mem_validJumpDests_of_reachable_jumpdest`), so the branch destination obligation
`Frame.get_dest 414 = some 414` is discharged axiom-cleanly here as `wc_get_dest_414`
(via `Frame.get_dest_of_mem` + a `ReachesBoundary (lower workedCall) 0 414` walk,
`wc_reaches_414`). No `native_decide`, no hypothesis. (Previously this was blocked by
`validJumpDests` being a `partial def`, the same wall that forced
`Examples.BranchExample` to build its JUMPI frame with an explicit `validJumps`.)

## The concrete child `CallReturns` — now CLOSED (C3f)

The child `CallReturns` (the C3e documented #1 blocker) is **closed**: `wc_callReturns`
is a genuine, hypothesis-free `CallReturns (wcCallSite g) (wcResumed g)` (for
`g ≥ 50000`). It builds the real child `drive` run of the `0xCA11EE` callee
(`PUSH1 5; PUSH1 7; SSTORE; STOP`) at the 63/64-capped CALL-site gas, over the
**post-SSTORE** parent world. The kernel-cost wall (the call-site `accounts` being the
post-SSTORE world threaded through `sstorePost` over the deep `lower workedCall`
computation) is defeated by the exp003 NAMED-LEMMA pattern: a `g`-independent
`wcStoredAccounts` (built from `callerXfer` + the self write, NO `lower` dependence)
plus `sstore_accounts_congr`, so the post-SSTORE world / SSTORE charge / cold floor are
derived from cheap code-free field facts, never by whole-map reduction. `wc_preserves`
no longer takes `hcall`.

## The one honest remainder (NOT `sorry`)

`wc_preserves` still takes `hpost`/`hhalt` — the **post-CALL run** to a halt. This is
the block-0 branch-condition recompute (`SLOAD; ADD; LT`, the taken `JUMPI` via
`wc_get_dest_414`) then block 1's `RETURN`. Its foundation (`wcResumed_addr/code/pc/
validJumps`) is proved here; the three remaining sub-pieces (the resumed-gas
`allButOneSixtyFourth` lower bound, the `SLOAD` value over the child-committed map, and
a general `RETURN` halt for the materialised `offset/size`) are documented at the
`lower_preserves` section below and in PLAN.md (C3f). NOT stubbed.
-/

namespace Lir.WorkedCall

open Evm Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open BytecodeLayer.UInt64
open BytecodeLayer.ExternalCall
open BytecodeLayer.Interpreter

-- `lower` is a deep computation (PUSH32 literals are 33 bytes each), so the kernel
-- reductions in the decode facts below need a higher recursion limit. The default
-- `maxHeartbeats` suffices: the prefix decode facts are factored into independent
-- `wc_dec_*` lemmas (each reduces one literal pc), which keeps every elaboration
-- under the default budget — no `maxHeartbeats` crank is needed.
set_option maxRecDepth 100000

/-! ## The entry point: `lower workedCall` as a top-level `messageCall` -/

/-- The top-level `CallParams` running `lower workedCall` as code in the
caller/callee world of exp003 (`accts` carries the `0xCA11EE` callee with its
`calleeProg` code). `gas := g` is the only free knob. -/
def wcParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := accts, originalAccounts := ∅, substate := default,
    caller := addrCaller, origin := addrCaller, recipient := addrCaller,
    codeSource := .Code (lower Lir.Decode.workedCall), gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-- The entry frame `beginCall` descends into. -/
def wcFrame (g : UInt64) : Frame := codeFrame (wcParams g) (lower Lir.Decode.workedCall)

theorem wc_begin (g : UInt64) : EntersAsCode (wcParams g) (wcFrame g) :=
  beginCall_code (wcParams g) (lower Lir.Decode.workedCall) rfl

/-! ## The straight-line prefix run to the CALL site

The lowered block 0 of `workedCall` is, byte for byte:
`JUMPDEST` (pc 0) · `PUSH32 5` (pc 1) · `PUSH32 7` (pc 34) · `SSTORE` (pc 67) ·
five `PUSH32 0` (pcs 68,101,134,167,200) · `PUSH32 0xCA11EE` (pc 233) ·
`PUSH32 0xFFFFFFFF` (pc 266) · `CALL` (pc 299).

The `sstore` value/key (5 then 7) are materialised by recompute-on-use, and the
seven CALL args are the value-free, zero-memory `callerProg` order with the callee
and the forwarded gas on top — exactly the stack `stepFrame_call` consumes.

We assemble the run to the CALL-site frame as a `Runs.trans` chain of the exp003
opcode rules; each rule's decode obligation reduces in the kernel at the literal pc,
and the running gas threads through `subCharges`. -/

/-- The gas charges of the prefix, in execution order: `Gjumpdest`, then nine
`Gverylow` (two `PUSH32`s for the SSTORE operands, then SSTORE itself with its own
cost, then the seven CALL-arg `PUSH32`s). We split SSTORE out (its `22100` cost is
world-derived), so the prefix charge list around it is `[1,3,3]` then `[3,3,3,3,3,3,3]`. -/
def preCharges : List ℕ := [GasConstants.Gjumpdest, GasConstants.Gverylow, GasConstants.Gverylow]

/-- The frame after `JUMPDEST; PUSH32 5; PUSH32 7` (the two SSTORE operands on the
stack, gas `g - 1 - 3 - 3`). -/
def wcBeforeSStore (g : UInt64) : Frame :=
  pushFrameW (pushFrameW (jumpdestFrame (wcFrame g)) 5 32) 7 32

/-- The frame at the CALL byte (pc 299), with the seven CALL args on the stack
(gas `0xFFFFFFFF` on top, callee `0xCA11EE` next, five `0`s below) — the shape
`stepFrame_call` consumes. -/
def wcCallSite (g : UInt64) : Frame :=
  pushFrameW (pushFrameW (pushFrameW (pushFrameW (pushFrameW (pushFrameW (pushFrameW
    (sstoreFrame (wcBeforeSStore g) 7 5 [])
      0 32) 0 32) 0 32) 0 32) 0 32) 0xCA11EE 32) 0xFFFFFFFF 32

/-- The full prefix charge list (execution order), SSTORE's `22100` inlined. The
running gas at any prefix step is `subCharges g` of a prefix of this list. -/
def wcCharges : List ℕ :=
  [GasConstants.Gjumpdest, GasConstants.Gverylow, GasConstants.Gverylow, 22100,
   GasConstants.Gverylow, GasConstants.Gverylow, GasConstants.Gverylow, GasConstants.Gverylow,
   GasConstants.Gverylow, GasConstants.Gverylow, GasConstants.Gverylow]

/-- The running gas at the SSTORE frame (after `JUMPDEST; PUSH32; PUSH32`), as a
`subCharges`. -/
theorem wc_gas_atSStore (g : UInt64) :
    (wcBeforeSStore g).exec.gasAvailable = subCharges g [1,3,3] := by
  show (((g - UInt64.ofNat 1) - UInt64.ofNat 3) - UInt64.ofNat 3) = subCharges g [1,3,3]
  simp [subCharges]

/-- The running gas after the SSTORE, as a `subCharges` (SSTORE's `22100` inlined). -/
theorem wc_gas_postSStore (g : UInt64) :
    (sstoreFrame (wcBeforeSStore g) 7 5 []).exec.gasAvailable = subCharges g [1,3,3,22100] := by
  show (wcBeforeSStore g).exec.gasAvailable - UInt64.ofNat (sstoreChargeOf (wcBeforeSStore g).exec 7 5)
      = subCharges g [1,3,3,22100]
  rw [show sstoreChargeOf (wcBeforeSStore g).exec 7 5 = 22100 from rfl, wc_gas_atSStore]
  show subCharges g [1,3,3] - UInt64.ofNat 22100 = subCharges g [1,3,3,22100]
  simp [subCharges]

/-! ### Decode facts at the prefix pcs (each reduced once in the kernel) -/

theorem wc_dec_jumpdest (g : UInt64) :
    decode (wcFrame g).exec.executionEnv.code (wcFrame g).exec.pc = some (.Smsf .JUMPDEST, .none) := by
  show decode (lower Lir.Decode.workedCall) 0 = _; rfl

theorem wc_dec_push5 (g : UInt64) :
    decode (jumpdestFrame (wcFrame g)).exec.executionEnv.code (jumpdestFrame (wcFrame g)).exec.pc
      = some (.Push .PUSH32, some (5, 32)) := by
  show decode (lower Lir.Decode.workedCall) (0 + 1) = _; rfl

theorem wc_dec_push7 (g : UInt64) :
    decode (pushFrameW (jumpdestFrame (wcFrame g)) 5 32).exec.executionEnv.code
        (pushFrameW (jumpdestFrame (wcFrame g)) 5 32).exec.pc
      = some (.Push .PUSH32, some (7, 32)) := by
  show decode (lower Lir.Decode.workedCall) ((0 + 1) + (32 + 1)) = _; rfl

theorem wc_dec_sstore (g : UInt64) :
    decode (wcBeforeSStore g).exec.executionEnv.code (wcBeforeSStore g).exec.pc
      = some (.Smsf .SSTORE, .none) := by
  show decode (lower Lir.Decode.workedCall) (((0 + 1) + (32 + 1)) + (32 + 1)) = _; rfl

theorem wc_stk_sstore (g : UInt64) :
    (wcBeforeSStore g).exec.stack = (7 : Word) :: (5 : Word) :: [] := rfl

/-- **The prefix run up to the SSTORE.** From the entry frame, `JUMPDEST; PUSH32 5;
PUSH32 7; SSTORE` `Runs` to the post-SSTORE frame. A `Runs.trans` chain of
`runs_jumpdest`, two `runs_push`, `runs_sstore`; decode at each literal offset-table
pc reduces in the kernel (the `wc_dec_*` lemmas) and gas threads through `subCharges`. -/
theorem wc_prefix_toSStore (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs (wcFrame g) (sstoreFrame (wcBeforeSStore g) 7 5 []) :=
  Runs.trans (runs_jumpdest (wcFrame g) (wc_dec_jumpdest g) (by show (0:ℕ) ≤ 1024; omega)
      (by show GasConstants.Gjumpdest ≤ g.toNat; show (1:ℕ) ≤ g.toNat; omega))
    (Runs.trans (runs_push _ .PUSH32 5 32 (by nofun) (wc_dec_push5 g) rfl rfl
        (by show 3 ≤ (subCharges g [1]).toNat; rw [toNat_subCharges g [1] (by simp; omega)]; simp; omega)
        (by show (0:ℕ)+1≤1024; omega))
      (Runs.trans (runs_push _ .PUSH32 7 32 (by nofun) (wc_dec_push7 g) rfl rfl
          (by show 3 ≤ (subCharges g [1,3]).toNat
              rw [toNat_subCharges g [1,3] (by simp; omega)]; simp; omega)
          (by show (1:ℕ)+1≤1024; omega))
        (runs_sstore _ 7 5 [] (wc_dec_sstore g) (wc_stk_sstore g) (by show (2:ℕ) ≤ 1024; omega) rfl
            (by show ¬ (wcBeforeSStore g).exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend
                rw [wc_gas_atSStore, toNat_subCharges g [1,3,3] (by simp; omega),
                    show GasConstants.Gcallstipend = 2300 from rfl]
                simp only [List.sum_cons, List.sum_nil]; omega)
            (by show sstoreChargeOf (wcBeforeSStore g).exec 7 5 ≤ (wcBeforeSStore g).exec.gasAvailable.toNat
                rw [show sstoreChargeOf (wcBeforeSStore g).exec 7 5 = 22100 from rfl,
                    wc_gas_atSStore, toNat_subCharges g [1,3,3] (by simp; omega)]
                simp only [List.sum_cons, List.sum_nil]; omega))))

/-! ### The seven CALL-arg pushes (post-SSTORE)

After the SSTORE, block 0 pushes the seven CALL args bottom-to-top: five `PUSH32 0`
(`out_size, out_off, in_size, in_off, value`), then `PUSH32 0xCA11EE` (callee), then
`PUSH32 0xFFFFFFFF` (forwarded gas), at pcs 68/101/134/167/200/233/266 — landing on
the `CALL` at pc 299. Each is a `runs_push`; the running gas threads from
`subCharges g [1,3,3,22100]` (`wc_gas_postSStore`). -/

/-- The running CALL-arg frame after the first `i` of the seven pushes (`i ≤ 7`),
on top of the post-SSTORE frame. -/
def wcCallArgs : UInt64 → Nat → Frame
  | g, 0 => sstoreFrame (wcBeforeSStore g) 7 5 []
  | g, (i+1) =>
    let imm : Word := match i with
      | 5 => 0xCA11EE
      | 6 => 0xFFFFFFFF
      | _ => 0
    pushFrameW (wcCallArgs g i) imm 32

theorem wcCallSite_eq (g : UInt64) : wcCallSite g = wcCallArgs g 7 := rfl

/-- `subCharges` over a snoc: charging `c` last subtracts it last. -/
theorem subCharges_snoc (g : UInt64) (cs : List ℕ) (c : ℕ) :
    subCharges g (cs ++ [c]) = subCharges g cs - UInt64.ofNat c := by
  induction cs generalizing g with
  | nil => rfl
  | cons d cs ih => show subCharges (g - UInt64.ofNat d) (cs ++ [c]) = _; rw [ih]; rfl

/-- `subCharges` over an append: charge `a` then `b`. -/
theorem subCharges_append (g : UInt64) (a b : List ℕ) :
    subCharges g (a ++ b) = subCharges (subCharges g a) b := by
  induction a generalizing g with
  | nil => rfl
  | cons d a ih => show subCharges (g - UInt64.ofNat d) (a ++ b) = _; rw [ih]; rfl

/-- Decode of the `i`-th CALL-arg push (the literal byte at the running pc reduces
in the kernel). Stated per index because the immediate differs (callee/gas). -/
theorem wc_dec_callarg0 (g : UInt64) :
    decode (wcCallArgs g 0).exec.executionEnv.code (wcCallArgs g 0).exec.pc
      = some (.Push .PUSH32, some (0, 32)) := by
  show decode (lower Lir.Decode.workedCall) ((((0+1)+(32+1))+(32+1))+1) = _; rfl
theorem wc_dec_callarg1 (g : UInt64) :
    decode (wcCallArgs g 1).exec.executionEnv.code (wcCallArgs g 1).exec.pc
      = some (.Push .PUSH32, some (0, 32)) := by
  show decode (lower Lir.Decode.workedCall) (((((0+1)+(32+1))+(32+1))+1)+(32+1)) = _; rfl
theorem wc_dec_callarg2 (g : UInt64) :
    decode (wcCallArgs g 2).exec.executionEnv.code (wcCallArgs g 2).exec.pc
      = some (.Push .PUSH32, some (0, 32)) := by
  show decode (lower Lir.Decode.workedCall) ((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1)) = _; rfl
theorem wc_dec_callarg3 (g : UInt64) :
    decode (wcCallArgs g 3).exec.executionEnv.code (wcCallArgs g 3).exec.pc
      = some (.Push .PUSH32, some (0, 32)) := by
  show decode (lower Lir.Decode.workedCall)
    (((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1))+(32+1)) = _; rfl
theorem wc_dec_callarg4 (g : UInt64) :
    decode (wcCallArgs g 4).exec.executionEnv.code (wcCallArgs g 4).exec.pc
      = some (.Push .PUSH32, some (0, 32)) := by
  show decode (lower Lir.Decode.workedCall)
    ((((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1))+(32+1))+(32+1)) = _; rfl
theorem wc_dec_callarg5 (g : UInt64) :
    decode (wcCallArgs g 5).exec.executionEnv.code (wcCallArgs g 5).exec.pc
      = some (.Push .PUSH32, some (0xCA11EE, 32)) := by
  show decode (lower Lir.Decode.workedCall)
    (((((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1))+(32+1))+(32+1))+(32+1)) = _; rfl
theorem wc_dec_callarg6 (g : UInt64) :
    decode (wcCallArgs g 6).exec.executionEnv.code (wcCallArgs g 6).exec.pc
      = some (.Push .PUSH32, some (0xFFFFFFFF, 32)) := by
  show decode (lower Lir.Decode.workedCall)
    ((((((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1))+(32+1))+(32+1))+(32+1))+(32+1)) = _; rfl

/-- Gas at the `i`-th CALL-arg frame: `subCharges g ([1,3,3,22100] ++ List.replicate i 3)`. -/
theorem wc_gas_callarg (g : UInt64) (i : Nat) :
    (wcCallArgs g i).exec.gasAvailable = subCharges g ([1,3,3,22100] ++ List.replicate i 3) := by
  induction i with
  | zero => simpa using wc_gas_postSStore g
  | succ i ih =>
    show (wcCallArgs g i).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
    rw [ih]
    -- subCharges g (xs ++ replicate (i+1) 3) = subCharges g (xs ++ replicate i 3) - 3
    rw [show List.replicate (i+1) 3 = List.replicate i 3 ++ [3] from List.replicate_succ',
        ← List.append_assoc, subCharges_snoc]
    rfl

/-- Stack size at the `i`-th CALL-arg frame is `i` (post-SSTORE stack was empty). -/
theorem wc_stk_callarg (g : UInt64) (i : Nat) :
    (wcCallArgs g i).exec.stack.size = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show ((wcCallArgs g i).exec.stack.push _).size = i + 1
    unfold Stack.size Stack.push at *; rw [List.length_cons, ih]

/-- Each CALL-arg push frame has gas `≥ 3` (for `g ≥ 30000`), via `wc_gas_callarg`.
The total prefix charge `[1,3,3,22100] ++ replicate i 3` is `≤ 22128 ≤ g.toNat`. -/
theorem wc_callarg_gas_ge (g : UInt64) (hg : 30000 ≤ g.toNat) (i : Nat) (hi : i ≤ 7) :
    3 ≤ (wcCallArgs g i).exec.gasAvailable.toNat := by
  rw [wc_gas_callarg, toNat_subCharges _ _ (by
      rw [List.sum_append]
      have : (List.replicate i 3).sum = 3 * i := by
        rw [List.sum_replicate]; ring
      rw [this]; simp only [List.sum_cons, List.sum_nil]; omega)]
  rw [List.sum_append]
  have : (List.replicate i 3).sum = 3 * i := by rw [List.sum_replicate]; ring
  rw [this]; simp only [List.sum_cons, List.sum_nil]; omega

/-- A single CALL-arg push step to the `pushFrameW` post-frame, given the push's
immediate and its decode fact. The gas/stack obligations come from the per-index
lemmas above. -/
theorem wc_callarg_step (g : UInt64) (hg : 30000 ≤ g.toNat) (i : Nat) (hi : i < 7)
    (imm : Word)
    (hdec : decode (wcCallArgs g i).exec.executionEnv.code (wcCallArgs g i).exec.pc
              = some (.Push .PUSH32, some (imm, 32))) :
    Runs (wcCallArgs g i) (pushFrameW (wcCallArgs g i) imm 32) :=
  runs_push _ .PUSH32 imm 32 (by nofun) hdec rfl rfl (wc_callarg_gas_ge g hg i (by omega))
    (by rw [wc_stk_callarg]; omega)

/-- **The full straight-line prefix run.** From the entry frame `wcFrame g`, the
lowered opcodes of block 0 up to and including the seven CALL-arg pushes `Runs` to
the CALL-site frame `wcCallSite g`. The SSTORE prefix (`wc_prefix_toSStore`) glued by
`Runs.trans` with the seven `wc_callarg_step`s; each `pushFrameW` post-frame is
*defeq* to the next `wcCallArgs` (the immediate-`match` reduces at the literal index). -/
theorem wc_prefix_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs (wcFrame g) (wcCallSite g) := by
  rw [wcCallSite_eq]
  refine (wc_prefix_toSStore g hg).trans ?_
  refine (wc_callarg_step g hg 0 (by omega) 0 (wc_dec_callarg0 g)).trans ?_
  refine (wc_callarg_step g hg 1 (by omega) 0 (wc_dec_callarg1 g)).trans ?_
  refine (wc_callarg_step g hg 2 (by omega) 0 (wc_dec_callarg2 g)).trans ?_
  refine (wc_callarg_step g hg 3 (by omega) 0 (wc_dec_callarg3 g)).trans ?_
  refine (wc_callarg_step g hg 4 (by omega) 0 (wc_dec_callarg4 g)).trans ?_
  refine (wc_callarg_step g hg 5 (by omega) 0xCA11EE (wc_dec_callarg5 g)).trans ?_
  exact wc_callarg_step g hg 6 (by omega) 0xFFFFFFFF (wc_dec_callarg6 g)

/-! ## The CALL step at the CALL site -/

theorem wc_dec_call (g : UInt64) :
    decode (wcCallSite g).exec.executionEnv.code (wcCallSite g).exec.pc
      = some (.System .CALL, .none) := by
  show decode (lower Lir.Decode.workedCall)
    (((((((((((0+1)+(32+1))+(32+1))+1)+(32+1))+(32+1))+(32+1))+(32+1))+(32+1))+(32+1))+(32+1)) = _
  rfl

theorem wc_stk_call (g : UInt64) :
    (wcCallSite g).exec.stack
      = (0xFFFFFFFF : Word) :: (0xCA11EE : Word) :: 0 :: 0 :: 0 :: 0 :: 0 :: [] := rfl

/-- Gas at the CALL site = `subCharges g [1,3,3,22100, 3,3,3,3,3,3,3]`. -/
theorem wc_gas_call (g : UInt64) :
    (wcCallSite g).exec.gasAvailable
      = subCharges g ([1,3,3,22100] ++ List.replicate 7 3) := by
  rw [wcCallSite_eq]; exact wc_gas_callarg g 7

/-- **The CALL step.** At the CALL site, `stepFrame` emits `.needsCall` with the
child params/pending for the call to `0xCA11EE` forwarding `0xFFFFFFFF` gas — the
genuine external call of `workedCall`. (`stepFrame_call` on the concrete frame.) -/
theorem wc_call_step (g : UInt64) (hg : 30000 ≤ g.toNat) :
    stepFrame (wcCallSite g)
      = .needsCall (callChildParams (wcCallSite g) 0xCA11EE 0xFFFFFFFF)
          (callPending (wcCallSite g) 0xCA11EE 0xFFFFFFFF) :=
  stepFrame_call (wcCallSite g) 0xFFFFFFFF 0xCA11EE (wc_dec_call g) (wc_stk_call g)
    (by rw [wc_stk_call]; show (7:ℕ) ≤ 1024; omega) rfl (by show (0:ℕ) < 1024; omega)
    (by
      show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
            (wcCallSite g).exec.accounts (wcCallSite g).exec.substate
            ≤ (wcCallSite g).exec.gasAvailable.toNat
      rw [show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
            (wcCallSite g).exec.accounts (wcCallSite g).exec.substate = 2600 from rfl,
          wc_gas_call, toNat_subCharges _ _ (by
            rw [List.sum_append, show (List.replicate 7 3).sum = 21 from rfl]
            simp only [List.sum_cons, List.sum_nil]; omega)]
      rw [List.sum_append, show (List.replicate 7 3).sum = 21 from rfl]
      simp only [List.sum_cons, List.sum_nil]; omega)

/-! ## The concrete child `CallReturns` for the `0xCA11EE` callee (C3f)

The CALL at `wcCallSite g` descends into the `0xCA11EE` callee (`calleeProg =
PUSH1 5; PUSH1 7; SSTORE; STOP`) over the **post-SSTORE** parent world — block 0's
SSTORE wrote slot `7 = 5` in the *caller* (`addrCaller`), so the world threaded into
the child is `callerXfer` with that write applied. We build the genuine child `drive`
run mirroring `Examples.CallerProgExample.caller_callReturns`, transposed onto
`wcCallSite g`.

The kernel-cost wall (PLAN.md C3e) is that `(wcCallSite g).exec.accounts` is the
post-SSTORE world threaded through `sstorePost` over the deep `lower workedCall`
computation; reducing it whole hits "deep recursion". We sidestep that with the
exp003 NAMED-LEMMA pattern: a `g`-independent post-SSTORE world `wcStoredAccounts`
defined from `callerXfer` + the self write (NO dependence on `lower`), and a
congruence lemma (`sstore_accounts_congr`) that derives `(wcCallSite g).exec.accounts
= wcStoredAccounts` from the (cheap, code-free) pre-SSTORE field facts — never
reducing the code field. -/

/-- **SSTORE account congruence.** The account map `State.sstore` produces depends
only on the input `accounts` and the self (`executionEnv.address`); it is otherwise
independent of the exec. This is the brick that lets us read the post-SSTORE world
off the cheap pre-SSTORE field facts instead of reducing the deep `lower workedCall`
frame. -/
theorem sstore_accounts_congr (e1 e2 : ExecutionState) (key v : UInt256)
    (ha : e1.accounts = e2.accounts) (haddr : e1.executionEnv.address = e2.executionEnv.address) :
    (e1.sstore key v).accounts = (e2.sstore key v).accounts := by
  unfold State.sstore
  dsimp only [State.setAccount, State.addAccessedStorageKey, State.lookupAccount]
  rw [ha, haddr]
  cases h : e2.accounts.find? e2.executionEnv.address with
  | none => simp [Option.option]; rw [ha]
  | some acc => simp [Option.option]

/-- A `g`-independent exec carrying the pre-SSTORE caller world (`callerXfer`), self
`addrCaller`. Mirrors the call-site exec on exactly the fields `State.sstore`'s
account map depends on (`accounts`, `executionEnv.address`). -/
def wcPreExec : ExecutionState :=
  { (default : ExecutionState) with
      accounts := callerXfer, originalAccounts := ∅, executionEnv := callerEnv, substate := default }

/-- **The `g`-independent post-SSTORE account map** — `callerXfer` after the caller's
`SSTORE 7 5`. The world threaded into the child CALL. (No `lower` dependence: this is
the analogue of exp003's `childXfer`, built from `callerXfer`.) -/
def wcStoredAccounts : AccountMap := (wcPreExec.sstore 7 5).accounts

/-- The pre-SSTORE call frame's accounts is `callerXfer` (cheap, code-free: the
accounts never depend on `lower workedCall`, only `validJumps`/`code` do). -/
theorem wcBefore_acc (g : UInt64) : (wcBeforeSStore g).exec.accounts = callerXfer := by
  show (wcFrame g).exec.accounts = callerXfer
  unfold wcFrame codeFrame; dsimp only
  unfold codeAccounts wcParams callerXfer accts callerAccount; dsimp only; rfl

/-- **The call-site accounts is the named post-SSTORE world** — derived through
`sstore_accounts_congr` from the cheap pre-SSTORE field facts, NOT by reducing the
deep `lower workedCall` frame. This is the lemma that defeats the kernel-cost wall. -/
theorem wcCallSite_acc (g : UInt64) : (wcCallSite g).exec.accounts = wcStoredAccounts := by
  show (sstoreFrame (wcBeforeSStore g) 7 5 []).exec.accounts = wcStoredAccounts
  unfold sstoreFrame sstorePost
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  show (({ (wcBeforeSStore g).exec with gasAvailable := _ }).toState.sstore 7 5).accounts = wcStoredAccounts
  unfold wcStoredAccounts
  apply sstore_accounts_congr
  · show (wcBeforeSStore g).exec.accounts = wcPreExec.accounts; rw [wcBefore_acc]; rfl
  · show (wcBeforeSStore g).exec.executionEnv.address = wcPreExec.executionEnv.address
    rw [show (wcBeforeSStore g).exec.executionEnv.address = addrCaller from rfl]
    rfl

/-- The call-site substate's accessed-account set is unchanged from the entry
(`default`): SSTORE only adds to `accessedStorageKeys`, never `accessedAccounts`. So
`callExtraCost`'s `accessCost` reads the cold callee either way. -/
theorem wcCallSite_accessedAccounts (g : UInt64) :
    (wcCallSite g).exec.substate.accessedAccounts = (default : Substate).accessedAccounts := by
  show (sstoreFrame (wcBeforeSStore g) 7 5 []).exec.substate.accessedAccounts = _
  unfold sstoreFrame sstorePost State.sstore
  dsimp only [ExecutionState.replaceStackAndIncrPC, State.setAccount, State.addAccessedStorageKey,
    State.lookupAccount, State.addAccessedStorageKey, Substate.addAccessedStorageKey]
  cases (wcBeforeSStore g).exec.accounts.find? (wcBeforeSStore g).exec.executionEnv.address with
  | none => rfl
  | some acc => rfl

/-- `toExecute` on the post-SSTORE world reads the callee's real code: the SSTORE
wrote `addrCaller`, leaving `0xCA11EE`'s `calleeProg` untouched. (`rfl` on the
small literal `wcStoredAccounts` — no `lower` dependence.) -/
theorem wc_toExecute_callee :
    toExecute wcStoredAccounts (AccountAddress.ofUInt256 0xCA11EE) = ToExecute.Code calleeProg := by
  unfold toExecute
  rw [if_neg (by decide)]
  unfold wcStoredAccounts wcPreExec callerXfer accts callerAccount calleeAccount callerEnv
  rfl

/-! ### The child gas and the cold-`SSTORE` floor -/

/-- `callExtraCost` for the cold callee over the post-SSTORE world is `2600`
(`accessCost` cold `2600`, no value transfer, callee already present). Derived
through the named accounts/accessed-account lemmas. -/
theorem wc_callExtraCost (g : UInt64) :
    callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
      (wcCallSite g).exec.accounts (wcCallSite g).exec.substate = 2600 := by
  rw [wcCallSite_acc]
  unfold callExtraCost accessCost
  rw [wcCallSite_accessedAccounts]
  -- transferCost 0 = 0, newAccountCost _ 0 _ = 0 (the `0 != 0` guard fails),
  -- accessCost cold = 2600 (callee not in the default accessed-account set).
  rw [show transferCost (0 : UInt256) = 0 from rfl,
      show newAccountCost (AccountAddress.ofUInt256 0xCA11EE) 0 wcStoredAccounts = 0 from rfl,
      show ((default : Substate).accessedAccounts.contains (AccountAddress.ofUInt256 0xCA11EE)) = false
        from by decide]
  decide

/-- The running gas at the CALL site, as a `subCharges`. -/
theorem wc_gas_call' (g : UInt64) :
    (wcCallSite g).exec.gasAvailable = subCharges g ([1,3,3,22100] ++ List.replicate 7 3) :=
  wc_gas_call g

/-- The forwarded child gas: the 63/64-capped `callGasCap` over the post-SSTORE
world. -/
def wcChildGas (g : UInt64) : ℕ :=
  callGasCap (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0 0xFFFFFFFF
    wcStoredAccounts (wcCallSite g).exec.gasAvailable (wcCallSite g).exec.substate

/-- The total prefix charge before the CALL is `[1,3,3,22100] ++ replicate 7 3`,
summing to `1 + 6 + 22100 + 21 = 22128`. For `g ≥ 50000` the call-site gas clears
both `callExtraCost` and the callee floor with margin. -/
theorem wc_gas_call_toNat (g : UInt64) (hg : 50000 ≤ g.toNat) :
    (wcCallSite g).exec.gasAvailable.toNat = g.toNat - 22128 := by
  rw [wc_gas_call', toNat_subCharges _ _ (by
        rw [List.sum_append, show (List.replicate 7 3).sum = 21 from rfl]
        simp only [List.sum_cons, List.sum_nil]; omega)]
  rw [List.sum_append, show (List.replicate 7 3).sum = 21 from rfl]
  simp only [List.sum_cons, List.sum_nil]; omega

/-- **The cold-`SSTORE` floor clears.** For `g ≥ 50000` the 63/64-capped child gas
clears the callee's `22106` cold-first-write cost — the genuine child run succeeds.
Mirrors `ExternalCall.childGas_lb`, over the post-SSTORE world. -/
theorem wcChildGas_lb (g : UInt64) (hg : 50000 ≤ g.toNat) : 22106 ≤ wcChildGas g := by
  unfold wcChildGas
  rw [← wcCallSite_acc]
  rw [callGasCap, if_pos (by rw [wc_callExtraCost, wc_gas_call_toNat g hg]; omega)]
  rw [wc_callExtraCost, wc_gas_call_toNat g hg]
  refine le_min ?_ (by decide)
  apply Gas.allButOneSixtyFourth_ge_of_liftFloor_le (C := 22106)
  rw [show Gas.liftFloor 22106 = 22457 from rfl]; omega

/-- The child gas fits in `UInt64` (capped by `min … 0xFFFFFFFF`). -/
theorem wcChildGas_ub (g : UInt64) : wcChildGas g < 2^64 := by
  have hgv : ((4294967295:UInt256)).toNat < 2^64 := by decide
  unfold wcChildGas callGasCap
  split
  · exact lt_of_le_of_lt (min_le_right _ _) hgv
  · exact hgv

/-! ### The child world (value-transfer no-op) and the reflexive child frame -/

/-- The callee account map after the (value-0) child transfer: credit callee
`balance+0`, debit caller `balance-0` — a storage no-op over `wcStoredAccounts`. The
analogue of exp003's `childXfer`, over the post-SSTORE world. -/
def wcChildXfer : AccountMap :=
  let m1 := wcStoredAccounts.insert (AccountAddress.ofUInt256 0xCA11EE)
              { calleeAccount with balance := calleeAccount.balance + 0 }
  match m1.find? (AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val)) with
  | none => m1
  | some acc => m1.insert (AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val))
                  { acc with balance := acc.balance - 0 }

/-- The callee's execution env (self `0xCA11EE`, caller `addrCaller`, depth 1). The
parent-derived fields are the caller env's (every prefix transformer preserves the
exec env verbatim, so `(wcCallSite g).exec.executionEnv` agrees with `callerEnv` on
every field but `code` — see `wc_callSite_env_*`). -/
def wcChildEnv : ExecutionEnv :=
  { address := AccountAddress.ofUInt256 0xCA11EE, origin := callerEnv.origin,
    caller := AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val), value := 0,
    calldata := (default : ExecutionState).memory.readWithPadding (UInt256.toNat 0) (UInt256.toNat 0),
    code := calleeProg, gasPrice := (UInt256.ofNat callerEnv.gasPrice).toNat,
    blockHeader := callerEnv.blockHeader, depth := callerEnv.depth + 1,
    canModifyState := callerEnv.canModifyState, blobVersionedHashes := callerEnv.blobVersionedHashes,
    chainId := callerEnv.chainId }

/-- The checkpoint substate of the child frame: the call-site substate (which carries
block 0's SSTORE access `(addrCaller, 7)`) plus the accessed callee account. -/
def wcChildCkptSubstate (g : UInt64) : Substate :=
  ((wcCallSite g).exec |>.addAccessedAccount (AccountAddress.ofUInt256 0xCA11EE)).substate

/-- The reflexive child frame `beginCall (callChildParams …)` produces: code
`calleeProg`, gas `wcChildGas g`, depth `1`, the child value transfer applied. -/
def wcChildFrame (g : UInt64) : Frame :=
  { kind := .call ⟨∅, wcStoredAccounts, wcChildCkptSubstate g⟩,
    validJumps := validJumpDests calleeProg 0,
    exec := { (default : ExecutionState) with
      accounts := wcChildXfer, originalAccounts := ∅, executionEnv := wcChildEnv,
      substate := wcChildCkptSubstate g, createdAccounts := ∅,
      gasAvailable := UInt64.ofNat (wcChildGas g) } }

/-- The child params (the value-free CALL to `0xCA11EE`) enter as code, descending
into `wcChildFrame g`. The `g`-independent world fields are read off the named
`wcCallSite_acc`/`wcCallSite_accessedAccounts` lemmas, not the deep frame. -/
theorem wc_beginCall_child (g : UInt64) :
    beginCall (callChildParams (wcCallSite g) 0xCA11EE 0xFFFFFFFF) = .inl (wcChildFrame g) := by
  unfold callChildParams
  dsimp only [callerCharged]
  rw [wcCallSite_acc]
  unfold beginCall
  dsimp only
  rw [show toExecute wcStoredAccounts (AccountAddress.ofUInt256 0xCA11EE) = ToExecute.Code calleeProg
        from wc_toExecute_callee]
  dsimp only
  rw [show (wcCallSite g).exec.createdAccounts
        = (∅ : Batteries.RBSet AccountAddress compare) from rfl]
  -- Every prefix transformer preserves the exec env verbatim, so the call-site
  -- env agrees with `callerEnv` on every field but `code`; align the parent-derived
  -- env fields the child params read (all cheap `rfl`, no code reduction).
  rw [show (wcCallSite g).exec.executionEnv.address = callerEnv.address from rfl,
      show (wcCallSite g).exec.executionEnv.origin = callerEnv.origin from rfl,
      show (wcCallSite g).exec.executionEnv.gasPrice = callerEnv.gasPrice from rfl,
      show (wcCallSite g).exec.executionEnv.blockHeader = callerEnv.blockHeader from rfl,
      show (wcCallSite g).exec.executionEnv.depth = callerEnv.depth from rfl,
      show (wcCallSite g).exec.executionEnv.canModifyState = callerEnv.canModifyState from rfl,
      show (wcCallSite g).exec.executionEnv.blobVersionedHashes = callerEnv.blobVersionedHashes from rfl,
      show (wcCallSite g).exec.executionEnv.chainId = callerEnv.chainId from rfl]
  unfold wcChildFrame wcChildEnv wcChildXfer wcChildCkptSubstate wcChildGas
  rfl

/-! ### Callee-side decode lemmas (reuse exp003's `calleeProg` facts) -/

/-- The callee exec right after its two `PUSH`es (stack `[7,5]`). -/
def wcChildAfter2Push (g : UInt64) : ExecutionState :=
  { (wcChildFrame g).exec with
    gasAvailable := UInt64.ofNat (wcChildGas g) - UInt64.ofNat 3 - UInt64.ofNat 3,
    pc := (default:ExecutionState).pc + UInt8.toUInt32 2 + UInt8.toUInt32 2, stack := [7,5] }

/-- The child `FrameResult` delivered by the run: the success `endFrame` of the
callee's post-SSTORE state over the empty pending stack. -/
def wcChildFrameRes (g : UInt64) : FrameResult :=
  endFrame (wcChildFrame g) (.success (sstorePost (wcChildAfter2Push g) 7 5 []) .empty)

/-- The child checkpoint substate has **not** accessed the callee's slot `(0xCA11EE,
7)` — block 0's SSTORE only marked `(addrCaller, 7)`, and `addAccessedAccount` does
not touch storage keys. So the callee's first write is cold. Proved through the
named call-site substate facts (no deep frame reduction). -/
theorem wc_ckpt_storageKeys (g : UInt64) :
    (wcChildCkptSubstate g).accessedStorageKeys.contains (AccountAddress.ofUInt256 0xCA11EE, 7)
      = false := by
  unfold wcChildCkptSubstate
  show ((wcCallSite g).exec.substate.addAccessedAccount (AccountAddress.ofUInt256 0xCA11EE)).accessedStorageKeys.contains _ = false
  unfold Substate.addAccessedAccount
  dsimp only
  rw [show (wcCallSite g).exec.substate.accessedStorageKeys
        = (∅ : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp).insert (addrCaller, 7) from by
      show (sstoreFrame (wcBeforeSStore g) 7 5 []).exec.substate.accessedStorageKeys = _
      unfold sstoreFrame sstorePost State.sstore
      dsimp only [ExecutionState.replaceStackAndIncrPC, State.setAccount, State.addAccessedStorageKey,
        State.lookupAccount, Substate.addAccessedStorageKey]
      rw [show (wcBeforeSStore g).exec.accounts.find? (wcBeforeSStore g).exec.executionEnv.address
            = some callerAccount from by
          rw [wcBefore_acc, show (wcBeforeSStore g).exec.executionEnv.address = addrCaller from rfl]
          unfold callerXfer accts callerAccount; rfl]
      show (((wcBeforeSStore g).exec.substate.addAccessedStorageKey (addrCaller, 7)).accessedStorageKeys) = _
      rw [show (wcBeforeSStore g).exec.substate = default from rfl]
      rfl]
  decide

/-- SSTORE's cold first-write cost in the callee is `22100` (its slot `7` starts at
`0` in `wcChildXfer`, and the slot is cold by `wc_ckpt_storageKeys`). Mirrors
`ExternalCall.sstoreChargeOf_child`, over the post-SSTORE parent world. -/
theorem wc_sstoreChargeOf_child (g : UInt64) (exec : ExecutionState)
    (h1 : exec.originalAccounts = ∅) (h2 : exec.accounts = wcChildXfer)
    (h3 : exec.executionEnv.address = AccountAddress.ofUInt256 0xCA11EE)
    (h4 : exec.substate = wcChildCkptSubstate g) : sstoreChargeOf exec 7 5 = 22100 := by
  unfold sstoreChargeOf
  rw [h1, h2, h3, h4, wc_ckpt_storageKeys g]
  rw [show ((∅ : AccountMap).find? (AccountAddress.ofUInt256 0xCA11EE)).option 0
            (fun a => a.storage.findD 7 0) = 0 from rfl,
      show (wcChildXfer.find? (AccountAddress.ofUInt256 0xCA11EE)).option 0
            (fun a => a.storage.findD 7 0) = 0 from by
        unfold wcChildXfer wcStoredAccounts wcPreExec callerXfer accts callerAccount calleeAccount callerEnv
        decide]
  decide

/-- **The child run, empty stack.** Over the empty pending stack, the genuine
driver runs the callee `PUSH;PUSH;SSTORE;STOP` from `wcChildFrame g` to `.ok` of its
success `FrameResult`. 3 opcode steps + the 2-unit halt. Mirrors
`ExternalCall.child_drive`, over the post-SSTORE world. -/
theorem wc_child_drive (g : UInt64) (n : ℕ)
    (hcg : 22106 ≤ wcChildGas g) (hcg2 : wcChildGas g < 2^64) :
    drive (n + 5) [] (.inl (wcChildFrame g)) = .ok (wcChildFrameRes g) := by
  have hofnat : (UInt64.ofNat (wcChildGas g)).toNat = wcChildGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  conv_lhs => dsimp only [wcChildFrame]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 dce0 (by
        show 3 ≤ (UInt64.ofNat (wcChildGas g)).toNat; rw [hofnat]; omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 7 dce2 (by
        show 3 ≤ (UInt64.ofNat (wcChildGas g) - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  have hg6 : ((UInt64.ofNat (wcChildGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = wcChildGas g - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega
  rw [drive_step _ _ _ (stepFrame_sstore _ 7 5 _ dce4 rfl ?hsz rfl ?hstip ?hcost)]
  case hsz => show (2:ℕ) ≤ 1024; omega
  case hstip =>
    show ¬ ((UInt64.ofNat (wcChildGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ GasConstants.Gcallstipend
    rw [hg6, show GasConstants.Gcallstipend = 2300 from rfl]; omega
  case hcost => rw [wc_sstoreChargeOf_child g _ rfl rfl rfl rfl, hg6]; omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  rw [drive_halt _ _ _ (stepFrame_stop _ dce5 (by show (0:ℕ)≤1024; omega))]
  unfold wcChildFrameRes endFrame wcChildAfter2Push wcChildFrame
  rfl

/-! ### The resumed parent and the bundled `CallReturns` -/

/-- The child params' gas is `UInt64.ofNat (wcChildGas g)` (the 63/64 cap over the
post-SSTORE world). -/
theorem wc_child_params_gas (g : UInt64) :
    (callChildParams (wcCallSite g) 0xCA11EE 0xFFFFFFFF).gas = UInt64.ofNat (wcChildGas g) := by
  unfold callChildParams wcChildGas
  dsimp only [callerCharged]
  rw [wcCallSite_acc]

/-- The resumed parent frame (the parent after the child commits and returns). -/
def wcResumed (g : UInt64) : Frame :=
  resumeAfterCall (wcChildFrameRes g).toCallResult (callPending (wcCallSite g) 0xCA11EE 0xFFFFFFFF)

/-- **The bundled `CallReturns` for `workedCall`'s single CALL.** The CALL step, the
child entering as code (`wc_beginCall_child`), the child's genuine terminating run
(`wc_child_drive`), and the resumed parent frame (`wcResumed g` by `rfl`). This
discharges `wc_preserves`'s `hcall` with NO hypothesis (for `g ≥ 50000`). -/
theorem wc_callReturns (g : UInt64) (hg : 50000 ≤ g.toNat) :
    CallReturns (wcCallSite g) (wcResumed g) := by
  have hcg := wcChildGas_lb g hg
  have hcg2 := wcChildGas_ub g
  have hchild :
      drive (seedFuel (callChildParams (wcCallSite g) 0xCA11EE 0xFFFFFFFF).gas) []
          (.inl (wcChildFrame g)) = .ok (wcChildFrameRes g) := by
    rw [wc_child_params_gas g]
    have : seedFuel (UInt64.ofNat (wcChildGas g)) = (seedFuel (UInt64.ofNat (wcChildGas g)) - 5) + 5 := by
      have := two_le_seedFuel (UInt64.ofNat (wcChildGas g)); unfold seedFuel; omega
    rw [this]; exact wc_child_drive g _ hcg hcg2
  exact ⟨_, _, _, _, wc_call_step g (by omega), wc_beginCall_child g, hchild, rfl⟩

/-! ## The post-CALL branch terminator — `get_dest` discharged via `validJumpDests`

After the CALL returns, block 0 recomputes the `lt` condition and runs
`JUMPI`/`JUMP` (pcs 402/413). The taken branch jumps to block 1's `JUMPDEST` at
offset `414`; the `JUMPI` step needs `frame.get_dest 414 = some 414`, i.e.
`(414 : UInt32) ∈ frame.validJumps`.

For the real entry frame `wcFrame g = codeFrame … (lower workedCall)`, `validJumps`
is `validJumpDests (lower workedCall) 0` (set by `codeFrame`), and this is
**preserved** through every prefix transformer (`jumpdestFrame`/`pushFrameW`/
`sstoreFrame` all carry `validJumps` unchanged) and across the CALL
(`resumeAfterCall` rebuilds from the pending parent frame, whose `validJumps` is the
CALL-site frame's). So the same membership fact discharges the branch on the
post-CALL frame.

Track A detotalized `validJumpDests` (it is now a total, kernel-reducible def with a
characterization lemma), so the membership is provable axiom-cleanly — no
`native_decide`. `mem_validJumpDests_of_reachable_jumpdest` needs a `ReachesBoundary
(lower workedCall) 0 414` derivation (walking the instruction stream from the entry
to offset 414) and that offset 414 holds a `JUMPDEST` byte; both are kernel `decide`s
on the concrete lowered bytes. -/

/-- Walking the lowered `workedCall` instruction stream from the entry (pc 0) lands
exactly on block 1's offset `414`: JUMPDEST · 2×PUSH32 · SSTORE · 7×PUSH32 · CALL ·
3×PUSH32 · SLOAD · ADD · LT · PUSH4 · JUMPI · PUSH4 · JUMP. Each step's boundary byte
reduces in the kernel (`by decide`). -/
theorem wc_reaches_414 : ReachesBoundary (lower Lir.Decode.workedCall) 0 414 :=
      (.step (byte := 0x5b) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x55) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0xf1) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x7f) (by decide)
      (.step (byte := 0x54) (by decide)
      (.step (byte := 0x01) (by decide)
      (.step (byte := 0x10) (by decide)
      (.step (byte := 0x63) (by decide)
      (.step (byte := 0x57) (by decide)
      (.step (byte := 0x63) (by decide)
      (.step (byte := 0x56) (by decide)
      (.refl 414)))))))))))))))))))))))

/-- Block 1's offset `414` is a valid jump destination of `lower workedCall`: it
holds a `JUMPDEST` byte reachable from the start, so the detotalized
`validJumpDests` records it. -/
theorem wc_414_mem_validJumps :
    (414 : UInt32) ∈ validJumpDests (lower Lir.Decode.workedCall) 0 :=
  mem_validJumpDests_of_reachable_jumpdest (lower Lir.Decode.workedCall)
    wc_reaches_414 (byte := 0x5b) (by decide) (by decide)

/-- **The branch destination resolves.** For any frame `fr` whose `validJumps` is the
lowered program's (`validJumpDests (lower workedCall) 0`) — the entry frame and every
prefix/post-CALL frame derived from it — the branch operand `414` resolves to the
real `JUMPDEST` at pc 414. This is the post-CALL branch-terminator obligation,
discharged through Track A's `Frame.get_dest_of_mem` + the membership fact (no
`native_decide`, no hypothesis). -/
theorem wc_get_dest_414 (fr : Frame)
    (hvj : fr.validJumps = validJumpDests (lower Lir.Decode.workedCall) 0) :
    fr.get_dest 414 = some 414 :=
  Frame.get_dest_of_mem fr (d := 414) (by decide) (hvj ▸ wc_414_mem_validJumps)

/-- The entry frame's `validJumps` is the lowered program's table (by `codeFrame`),
so `wc_get_dest_414` applies to it and any frame that preserves `validJumps`. -/
theorem wcFrame_validJumps (g : UInt64) :
    (wcFrame g).validJumps = validJumpDests (lower Lir.Decode.workedCall) 0 := rfl

/-! ## The resumed parent frame fields (post-CALL run foundation)

After `wc_callReturns`, `wcResumed g` is the genuine resumed frame the post-CALL run
starts from. Its observable fields project cleanly off `resumeAfterCall` (no deep
`lower` reduction): the code is still the lowered program, `validJumps` is still its
jump table (so `wc_get_dest_414` applies to the post-CALL JUMPI), and the pc is the
byte after the CALL (300) — block 0's branch-condition recompute. These are the bricks
the post-CALL `Runs` chain (the documented remainder below) threads. -/

/-- The resumed frame's self is still `addrCaller`. -/
theorem wcResumed_addr (g : UInt64) : (wcResumed g).exec.executionEnv.address = addrCaller := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; rfl

/-- The resumed frame's code is still the lowered program. -/
theorem wcResumed_code (g : UInt64) :
    (wcResumed g).exec.executionEnv.code = lower Lir.Decode.workedCall := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; rfl

/-- The resumed frame's pc is the byte after the CALL (300) — block 0's post-CALL
branch-condition recompute. -/
theorem wcResumed_pc (g : UInt64) : (wcResumed g).exec.pc = 300 := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; rfl

/-- The resumed frame's `validJumps` is still the lowered program's jump table — so
`wc_get_dest_414` discharges the post-CALL taken `JUMPI` to block 1. -/
theorem wcResumed_validJumps (g : UInt64) :
    (wcResumed g).validJumps = validJumpDests (lower Lir.Decode.workedCall) 0 := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; rfl

/-! ## Resumed-frame facts: stack, accounts, substate (post-CALL run foundation)

The post-CALL run starts from `wcResumed g` (pc 300, the block-0 branch recompute).
Beyond the `wcResumed_addr/code/pc/validJumps` fields above, the run needs the
resumed **stack** (`[1]` — the CALL success flag), the resumed **accounts** (the
child-committed map, where the caller's slot 7 is still 5), and the resumed
**substate** (warm `(addrCaller, 7)`). These are all `g`-independent (gas is the only
`g`-carrying field), so we read them off named `g`-free maps via `resumeAfterCall` /
`endCall` projections — no deep `lower` reduction. -/

/-- The child call returned success (the callee `PUSH;PUSH;SSTORE;STOP` halts with
`.success`, and `endCall .success` keeps the non-empty child accounts → `success`). -/
theorem wcChildResult_success (g : UInt64) :
    (wcChildFrameRes g).toCallResult.success = true := by
  unfold wcChildFrameRes endFrame
  dsimp only [wcChildFrame, FrameResult.toCallResult, endCall]

/-- The caller's self balance is `≥ 0` (always), so the "insufficient funds" guard
in `resumeAfterCall` is false; with a successful child and caller depth `0 ≠ 1024`,
the pushed success flag is `1`. -/
theorem wcResumed_stack (g : UInt64) : (wcResumed g).exec.stack = [1] := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  rw [wcChildResult_success g]
  rw [if_neg (by
    rw [show ((callerCharged (wcCallSite g).exec 0xCA11EE 0xFFFFFFFF).executionEnv.depth == 1024)
          = false from by
        rw [show (callerCharged (wcCallSite g).exec 0xCA11EE 0xFFFFFFFF).executionEnv.depth
              = (wcCallSite g).exec.executionEnv.depth from rfl,
            show (wcCallSite g).exec.executionEnv.depth = 0 from rfl]; rfl]
    simp only [Bool.not_true, Bool.false_or, Bool.or_false, decide_eq_true_eq, gt_iff_lt]
    exact not_lt_of_ge (UInt256.zero_le _))]
  rfl

/-- A `g`-independent exec carrying the child's pre-SSTORE world (`wcChildXfer`), self
`0xCA11EE`. Mirrors `wcChildAfter2Push` on exactly the fields `State.sstore`'s account
map depends on (`accounts`, `executionEnv.address`) — the analogue of `wcPreExec`. -/
def wcChildPreExec : ExecutionState :=
  { (default : ExecutionState) with
      accounts := wcChildXfer, originalAccounts := ∅, executionEnv := wcChildEnv }

/-- **The `g`-independent child post-SSTORE account map** — `wcChildXfer` after the
callee's `SSTORE 7 5` (writing `0xCA11EE`'s slot 7). This is the map committed back
to the parent on return (the resumed frame's accounts). -/
def wcResumedAccounts : AccountMap := (wcChildPreExec.sstore 7 5).accounts

/-- The resumed frame's accounts is the named child post-SSTORE world — derived
through `sstore_accounts_congr` from the cheap field facts (`wcChildAfter2Push`'s
accounts is `wcChildXfer`, self `0xCA11EE`), NOT by deep reduction. The `endCall`
non-empty branch keeps the child's accounts (it is not `∅`). -/
theorem wcResumed_acc (g : UInt64) : (wcResumed g).exec.accounts = wcResumedAccounts := by
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  show (wcChildFrameRes g).toCallResult.accounts = wcResumedAccounts
  unfold wcChildFrameRes endFrame
  dsimp only [wcChildFrame, FrameResult.toCallResult, endCall]
  rw [if_neg (by
    -- the child post-SSTORE accounts is non-empty (it inserts `0xCA11EE`)
    show ¬ ((sstorePost (wcChildAfter2Push g) 7 5 []).accounts == ∅) = true
    rw [show (sstorePost (wcChildAfter2Push g) 7 5 []).accounts = wcResumedAccounts from by
        unfold sstorePost
        dsimp only [ExecutionState.replaceStackAndIncrPC]
        show ((wcChildAfter2Push g).toState.sstore 7 5).accounts = wcResumedAccounts
        unfold wcResumedAccounts
        apply sstore_accounts_congr
        · show (wcChildAfter2Push g).accounts = wcChildPreExec.accounts
          show (wcChildFrame g).exec.accounts = wcChildPreExec.accounts; rfl
        · show (wcChildAfter2Push g).executionEnv.address = wcChildPreExec.executionEnv.address; rfl]
    decide)]
  unfold sstorePost
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  show ((wcChildAfter2Push g).toState.sstore 7 5).accounts = wcResumedAccounts
  unfold wcResumedAccounts
  apply sstore_accounts_congr
  · show (wcChildAfter2Push g).accounts = wcChildPreExec.accounts; rfl
  · show (wcChildAfter2Push g).executionEnv.address = wcChildPreExec.executionEnv.address; rfl

/-- **The caller's slot 7 survives the child CALL = 5.** In the child-committed map,
the caller (`addrCaller`) slot 7 is still `5` (block 0 wrote it; the child wrote
`0xCA11EE`'s slot 7, a different account). This is the SLOAD value the block-0/block-1
`lt` recompute reads. (`decide` on the small literal `wcResumedAccounts`.) -/
theorem wcResumed_sload7 (g : UInt64) :
    ((wcResumed g).exec.accounts.find? addrCaller).option 0 (·.lookupStorage 7) = 5 := by
  rw [wcResumed_acc]
  unfold wcResumedAccounts wcChildPreExec wcChildXfer wcStoredAccounts wcPreExec
    callerXfer accts callerAccount calleeAccount callerEnv wcChildEnv
  decide

/-! ### The resumed gas

The resumed frame's gas is `machineWithOutput.gasAvailable + result.gasRemaining`
(`resumeAfterCall`): the caller's post-CALL-charge gas (`callerCharged`, which keeps
`g − 22128 − (callGasCap + 2600)`) plus the child's leftover
(`wcChildGas − 22106 = callGasCap − 22106`). The `callGasCap` **cancels**, leaving
`g − 22128 − 2600 − 22106 = g − 46834` — independent of the (large) forwarded gas.
We prove the lower bound `46834 + N ≤ g → N ≤ resumed gas` over UInt64 (no
intermediate wraparound for `g` in range), giving the post-CALL run its gas. -/

/-- The child's leftover gas equals `wcChildGas g − 22106` (3+3 for the two pushes,
22100 for the cold SSTORE, 0 for STOP). -/
theorem wcChildResult_gasRemaining (g : UInt64) (hg : 50000 ≤ g.toNat) :
    (wcChildFrameRes g).toCallResult.gasRemaining.toNat = wcChildGas g - 22106 := by
  have hcg := wcChildGas_lb g hg
  have hcg2 := wcChildGas_ub g
  have hofnat : (UInt64.ofNat (wcChildGas g)).toNat = wcChildGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  unfold wcChildFrameRes endFrame
  dsimp only [wcChildFrame, FrameResult.toCallResult, endCall]
  show ((sstorePost (wcChildAfter2Push g) 7 5 []).gasAvailable).toNat = _
  rw [show (sstorePost (wcChildAfter2Push g) 7 5 []).gasAvailable
        = (wcChildAfter2Push g).gasAvailable - UInt64.ofNat (sstoreChargeOf (wcChildAfter2Push g) 7 5)
        from rfl]
  rw [show sstoreChargeOf (wcChildAfter2Push g) 7 5 = 22100 from
      wc_sstoreChargeOf_child g (wcChildAfter2Push g) rfl rfl rfl rfl]
  show ((UInt64.ofNat (wcChildGas g) - UInt64.ofNat 3 - UInt64.ofNat 3) - UInt64.ofNat 22100).toNat = _
  rw [toNat_sub_ofNat _ 22100 (by
        rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega) (by omega),
            toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega) (by omega),
      toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega) (by omega),
      toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]
  omega

/-- The caller's post-CALL-charge gas (`callerCharged`), in `toNat`:
`g − 22128 − (callGasCap + 2600)`, with `callGasCap = wcChildGas g`. -/
theorem wc_callerCharged_gas (g : UInt64) (hg : 50000 ≤ g.toNat) :
    (callerCharged (wcCallSite g).exec 0xCA11EE 0xFFFFFFFF).gasAvailable.toNat
      = (g.toNat - 22128) - (wcChildGas g + 2600) := by
  unfold callerCharged
  dsimp only
  rw [show callGasCap (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0 0xFFFFFFFF
          (wcCallSite g).exec.accounts (wcCallSite g).exec.gasAvailable (wcCallSite g).exec.substate
        = wcChildGas g from by unfold wcChildGas; rw [← wcCallSite_acc],
      wc_callExtraCost g]
  -- callGasCap ≤ allButOneSixtyFourth (callSiteGas − 2600) ≤ callSiteGas − 2600 ≤ g − 24728
  have hcap : wcChildGas g ≤ (g.toNat - 22128) - 2600 := by
    unfold wcChildGas
    rw [← wcCallSite_acc, callGasCap]
    rw [if_pos (by rw [wc_callExtraCost, wc_gas_call_toNat g hg]; omega)]
    rw [wc_callExtraCost, wc_gas_call_toNat g hg]
    exact le_trans (min_le_left _ _) (Nat.sub_le _ _)
  have hglt : g.toNat < 2 ^ 64 := g.toNat_lt
  rw [toNat_sub_ofNat _ _ (by rw [wc_gas_call_toNat g hg]; omega) (by omega)]
  rw [wc_gas_call_toNat g hg]

/-- **The resumed gas, exact.** `callGasCap` cancels between the caller's post-CALL
charge and the child's leftover, leaving `g − 46834` (`= g − 22128 − 2600 − 22106`).
For `g ≥ 50000` this is `≥ 3166`. -/
theorem wcResumed_gas (g : UInt64) (hg : 50000 ≤ g.toNat) :
    (wcResumed g).exec.gasAvailable.toNat = g.toNat - 46834 := by
  have hcc := wc_callerCharged_gas g hg
  have hgr := wcChildResult_gasRemaining g hg
  have hcglb := wcChildGas_lb g hg
  have hglt : g.toNat < 2 ^ 64 := g.toNat_lt
  -- callGasCap upper bound (so the gas pieces stay in range)
  have hcap : wcChildGas g ≤ (g.toNat - 22128) - 2600 := by
    unfold wcChildGas
    rw [← wcCallSite_acc, callGasCap]
    rw [if_pos (by rw [wc_callExtraCost, wc_gas_call_toNat g hg]; omega)]
    rw [wc_callExtraCost, wc_gas_call_toNat g hg]
    exact le_trans (min_le_left _ _) (Nat.sub_le _ _)
  unfold wcResumed resumeAfterCall
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  -- gasAfterReturn = machineWithOutput.gasAvailable + result.gasRemaining; the
  -- machine's gas is the callerCharged gas (writeBytes preserves gas).
  show ((callerCharged (wcCallSite g).exec 0xCA11EE 0xFFFFFFFF).gasAvailable
          + (wcChildFrameRes g).toCallResult.gasRemaining).toNat = _
  rw [UInt64.toNat_add, hcc, hgr]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Slot 7 of self is WARM in the resumed frame.** Block 0's `SSTORE 7 5` marked
`(addrCaller, 7)` accessed; that survives the CALL (threaded into the child
checkpoint) and the child's own `SSTORE` (which adds `(0xCA11EE, 7)`, keeping the
caller's key). So the post-CALL `SLOAD 7` of self is warm (cost 100). -/
theorem wcResumed_warm7 (g : UInt64) :
    (wcResumed g).exec.substate.accessedStorageKeys.contains (addrCaller, 7) = true := by
  rw [show (wcResumed g).exec.substate = (sstorePost (wcChildAfter2Push g) 7 5 []).substate from by
      unfold wcResumed resumeAfterCall callPending
      dsimp only [ExecutionState.replaceStackAndIncrPC]
      show (wcChildFrameRes g).toCallResult.substate = _
      unfold wcChildFrameRes endFrame
      dsimp only [wcChildFrame, FrameResult.toCallResult, endCall]
      rw [if_neg (by
        show ¬ ((sstorePost (wcChildAfter2Push g) 7 5 []).accounts == ∅) = true
        rw [show (sstorePost (wcChildAfter2Push g) 7 5 []).accounts = wcResumedAccounts from by
            unfold sstorePost; dsimp only [ExecutionState.replaceStackAndIncrPC]
            show ((wcChildAfter2Push g).toState.sstore 7 5).accounts = wcResumedAccounts
            unfold wcResumedAccounts
            apply sstore_accounts_congr
            · show (wcChildAfter2Push g).accounts = wcChildPreExec.accounts; rfl
            · show (wcChildAfter2Push g).executionEnv.address = wcChildPreExec.executionEnv.address; rfl]
        decide)]]
  -- The child SSTORE adds `(0xCA11EE, 7)` to the child checkpoint's accessed keys
  -- (which already carry `(addrCaller, 7)` from block 0); membership of `(addrCaller, 7)`
  -- survives. Reduce only the `accessedStorageKeys` field (never the refund).
  unfold sstorePost State.sstore
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  rw [show (wcChildAfter2Push g).toState.lookupAccount (wcChildAfter2Push g).executionEnv.address
        = some calleeAccount from by
      show wcChildXfer.find? (AccountAddress.ofUInt256 0xCA11EE) = some calleeAccount
      unfold wcChildXfer wcStoredAccounts wcPreExec callerXfer accts callerAccount calleeAccount callerEnv
      rfl]
  dsimp only [Option.option, State.setAccount, State.addAccessedStorageKey,
    Substate.addAccessedStorageKey]
  rw [show (wcChildAfter2Push g).substate.accessedStorageKeys
        = (∅ : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp).insert (addrCaller, 7) from by
      show (wcChildCkptSubstate g).accessedStorageKeys = _
      unfold wcChildCkptSubstate State.addAccessedAccount Substate.addAccessedAccount
      dsimp only
      show (wcCallSite g).exec.substate.accessedStorageKeys = _
      show (sstoreFrame (wcBeforeSStore g) 7 5 []).exec.substate.accessedStorageKeys = _
      unfold sstoreFrame sstorePost State.sstore
      dsimp only [ExecutionState.replaceStackAndIncrPC, State.setAccount, State.addAccessedStorageKey,
        State.lookupAccount, Substate.addAccessedStorageKey]
      rw [show (wcBeforeSStore g).exec.accounts.find? (wcBeforeSStore g).exec.executionEnv.address
            = some callerAccount from by
          rw [wcBefore_acc, show (wcBeforeSStore g).exec.executionEnv.address = addrCaller from rfl]
          unfold callerXfer accts callerAccount; rfl]
      show (((wcBeforeSStore g).exec.substate.addAccessedStorageKey (addrCaller, 7)).accessedStorageKeys) = _
      rw [show (wcBeforeSStore g).exec.substate = default from rfl]
      rfl]
  rw [show (wcChildAfter2Push g).executionEnv.address = AccountAddress.ofUInt256 0xCA11EE from rfl]
  decide

/-! ## The general `RETURN` halt (materialised return window)

The lowering's `ret t` emits `materialise t ++ [RETURN]`, so the `RETURN` consumes
the materialised value as `offset` and the value below it as `size` — NOT the `0,0`
that exp003's `stepFrame_return_empty` (and `Match.halt_ret`) need. We prove the
**general** `RETURN` halt here: at any frame decoding to `RETURN` with
`offset :: size :: rest` on the stack, if the memory-expansion charge succeeds
(`chargeMemExpansion fr.exec offset size = .ok ec`, i.e. enough gas), then
`stepFrame fr` halts. The bridge (`lower_preserves_discharge`) only needs the halt
to *exist*, so we deliver `∃ halt, stepFrame fr = .halted halt`. The proof mirrors
`stepFrame_return_empty` but routes through the genuine `chargeMemExpansion` success
instead of the size-0 short-circuit. -/

/-- **The general `RETURN` halt.** A frame decoding to `RETURN` with
`offset :: size :: rest`, whose memory-expansion charge succeeds, halts. (Existence
form: the bridge needs only `∃ halt, stepFrame fr = .halted halt`.) -/
theorem stepFrame_return_halts (fr : Frame) (offset size : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .RETURN, .none))
    (hstk : fr.exec.stack = offset :: size :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (ec : ExecutionState)
    (hmem : chargeMemExpansion fr.exec offset size = .ok ec) :
    ∃ halt, stepFrame fr = .halted halt := by
  have hstep : stepFrame fr
      = .halted (.success
          (ExecutionState.replaceStackAndIncrPC
            { ec with toMachineState :=
                { ec.toMachineState with
                    activeWords := MachineState.M ec.activeWords offset.toUInt64 size.toUInt64 } }
            rest)
          (ec.memory.readWithPadding offset.toNat size.toNat)) := by
    unfold stepFrame
    simp only [hdec]
    dsimp only [Option.getD]
    rw [if_neg (by decide)]
    have hov : ¬ (fr.exec.stack.size - stackPopCount (.System .RETURN)
        + stackPushCount (.System .RETURN) > 1024) := by
      simp only [show stackPopCount (.System .RETURN) = 2 from rfl,
                 show stackPushCount (.System .RETURN) = 0 from rfl]
      have := hsz; omega
    rw [if_neg hov]
    dsimp only [dispatch, systemOp, haltOp, returnOrRevertOp]
    rw [hstk]
    dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
      Except.bind, pure, Except.pure]
    rw [hmem]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [if_neg (by decide)]
  exact ⟨_, hstep⟩

/-! ## The post-CALL run (block-0 recompute → taken JUMPI → block-1 RETURN)

From the resumed frame `wcResumed g` (pc 300, stack `[1]`, accounts the child-committed
map, gas `g − 46834`), block 0 recomputes the `lt` branch condition
(`PUSH 100; PUSH 9; PUSH 7; SLOAD; ADD; LT`), pushes the then-target and takes the
`JUMPI` to block 1 (offset 414), then block 1 recomputes the same condition and
`RETURN`s the result. We assemble this as a `Runs.trans` chain of the exp003 opcode
rules, threading the running gas through `subCharges` and reading the SLOAD value
(`5`, `wcResumed_sload7`), the warm cost (`wcResumed_warm7`), and the taken branch
(`wc_get_dest_414`). The terminal `RETURN` halts via `stepFrame_return_halts`. -/

/-- The post-CALL charge list (execution order), block-0 recompute through block-1's
last `LT` (the `RETURN`'s memory charge is handled separately). Sum `= 247`. -/
def wcPostCharges : List ℕ :=
  [3,3,3,100,3,3,3,10,   -- block 0: 3×PUSH32, SLOAD(warm), ADD, LT, PUSH4, JUMPI
   1,3,3,3,100,3,3]      -- block 1: JUMPDEST, 3×PUSH32, SLOAD(warm), ADD, LT

/-- The block-0 recompute frame after `PUSH 100; PUSH 9; PUSH 7` (three operands on
the stack), on top of the resumed frame. -/
def wcRec0Push3 (g : UInt64) : Frame :=
  pushFrameW (pushFrameW (pushFrameW (wcResumed g) 100 32) 9 32) 7 32

/-- The frame after the block-0 `SLOAD` (key 7 popped, value 5 pushed). -/
def wcRec0Sload (g : UInt64) : Frame :=
  sloadFrame (wcRec0Push3 g) 7 [9, 100, 1]

/-- The frame after the block-0 `ADD` (`5 + 9 = 14`). -/
def wcRec0Add (g : UInt64) : Frame :=
  addFrame (wcRec0Sload g) 5 9 [100, 1]

/-- The frame after the block-0 `LT` (`14 < 100 = 1`). -/
def wcRec0Lt (g : UInt64) : Frame :=
  ltFrame (wcRec0Add g) 14 100 [1]

/-- The frame after `PUSH4 414` (the then-target on top of the `lt` result). -/
def wcRec0PushDest (g : UInt64) : Frame :=
  pushFrameW (wcRec0Lt g) 414 4

/-- The frame after the taken `JUMPI` to block 1 (pc 414, stack `[1]`). -/
def wcBlock1 (g : UInt64) : Frame :=
  jumpFrame (wcRec0PushDest g) GasConstants.Ghigh 414 [1]

/-- The frame after block 1's `JUMPDEST`. -/
def wcBlock1Jd (g : UInt64) : Frame := jumpdestFrame (wcBlock1 g)

/-- The frame after block 1's `PUSH 100; PUSH 9; PUSH 7`. -/
def wcRec1Push3 (g : UInt64) : Frame :=
  pushFrameW (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32) 7 32

/-- The frame after block 1's `SLOAD`. -/
def wcRec1Sload (g : UInt64) : Frame :=
  sloadFrame (wcRec1Push3 g) 7 [9, 100, 1]

/-- The frame after block 1's `ADD`. -/
def wcRec1Add (g : UInt64) : Frame :=
  addFrame (wcRec1Sload g) 5 9 [100, 1]

/-- The frame after block 1's `LT` — the `RETURN` frame (stack `[1, 1]`: the `lt`
result `1` on top, the residual CALL flag `1` below; pc 517). -/
def wcRetFrame (g : UInt64) : Frame :=
  ltFrame (wcRec1Add g) 14 100 [1]

/-! ### Resumed-frame base facts threaded into the chain -/

/-- The resumed frame's accounts equal the named child-committed map (alias of
`wcResumed_acc`, used to read the SLOAD value). -/
theorem wcResumed_self_sload (g : UInt64) :
    ((wcResumed g).exec.accounts.find? (wcResumed g).exec.executionEnv.address).option 0
        (·.lookupStorage 7) = 5 := by
  rw [wcResumed_addr]; exact wcResumed_sload7 g

/-! ### Decode facts at the post-CALL pcs

Every chain frame preserves `executionEnv.code` (= the resumed code = `lower
workedCall`) and threads the pc from `wcResumed_pc = 300`. So each decode reduces to
`decode (lower workedCall) <pc> = …`, a kernel `rfl` at the literal offset-table pc. -/

theorem wcd_300 (g : UInt64) :
    decode (wcResumed g).exec.executionEnv.code (wcResumed g).exec.pc
      = some (.Push .PUSH32, some (100, 32)) := by
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_333 (g : UInt64) :
    decode (pushFrameW (wcResumed g) 100 32).exec.executionEnv.code
        (pushFrameW (wcResumed g) 100 32).exec.pc
      = some (.Push .PUSH32, some (9, 32)) := by
  show decode (wcResumed g).exec.executionEnv.code ((wcResumed g).exec.pc + (32 + 1)) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_366 (g : UInt64) :
    decode (pushFrameW (pushFrameW (wcResumed g) 100 32) 9 32).exec.executionEnv.code
        (pushFrameW (pushFrameW (wcResumed g) 100 32) 9 32).exec.pc
      = some (.Push .PUSH32, some (7, 32)) := by
  show decode (wcResumed g).exec.executionEnv.code (((wcResumed g).exec.pc + (32 + 1)) + (32 + 1)) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_399 (g : UInt64) :
    decode (wcRec0Push3 g).exec.executionEnv.code (wcRec0Push3 g).exec.pc
      = some (.Smsf .SLOAD, .none) := by
  show decode (wcResumed g).exec.executionEnv.code ((((wcResumed g).exec.pc + (32+1)) + (32+1)) + (32+1)) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_400 (g : UInt64) :
    decode (wcRec0Sload g).exec.executionEnv.code (wcRec0Sload g).exec.pc
      = some (.ArithLogic .ADD, .none) := by
  show decode (wcResumed g).exec.executionEnv.code (((((wcResumed g).exec.pc + (32+1)) + (32+1)) + (32+1)) + 1) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_401 (g : UInt64) :
    decode (wcRec0Add g).exec.executionEnv.code (wcRec0Add g).exec.pc
      = some (.ArithLogic .LT, .none) := by
  show decode (wcResumed g).exec.executionEnv.code ((((((wcResumed g).exec.pc + (32+1)) + (32+1)) + (32+1)) + 1) + 1) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_402 (g : UInt64) :
    decode (wcRec0Lt g).exec.executionEnv.code (wcRec0Lt g).exec.pc
      = some (.Push .PUSH4, some (414, 4)) := by
  show decode (wcResumed g).exec.executionEnv.code (((((((wcResumed g).exec.pc + (32+1)) + (32+1)) + (32+1)) + 1) + 1) + 1) = _
  rw [wcResumed_code, wcResumed_pc]; rfl
theorem wcd_407 (g : UInt64) :
    decode (wcRec0PushDest g).exec.executionEnv.code (wcRec0PushDest g).exec.pc
      = some (.Smsf .JUMPI, .none) := by
  show decode (wcResumed g).exec.executionEnv.code ((((((((wcResumed g).exec.pc + (32+1)) + (32+1)) + (32+1)) + 1) + 1) + 1) + (4+1)) = _
  rw [wcResumed_code, wcResumed_pc]; rfl

-- Block 1: the taken JUMPI set pc := 414 (jumpPost), so block-1 pcs are absolute.
theorem wcd_414 (g : UInt64) :
    decode (wcBlock1 g).exec.executionEnv.code (wcBlock1 g).exec.pc
      = some (.Smsf .JUMPDEST, .none) := by
  show decode (wcResumed g).exec.executionEnv.code 414 = _
  rw [wcResumed_code]; rfl
theorem wcd_415 (g : UInt64) :
    decode (wcBlock1Jd g).exec.executionEnv.code (wcBlock1Jd g).exec.pc
      = some (.Push .PUSH32, some (100, 32)) := by
  show decode (wcResumed g).exec.executionEnv.code (414 + 1) = _
  rw [wcResumed_code]; rfl
theorem wcd_448 (g : UInt64) :
    decode (pushFrameW (wcBlock1Jd g) 100 32).exec.executionEnv.code
        (pushFrameW (wcBlock1Jd g) 100 32).exec.pc
      = some (.Push .PUSH32, some (9, 32)) := by
  show decode (wcResumed g).exec.executionEnv.code ((414 + 1) + (32+1)) = _
  rw [wcResumed_code]; rfl
theorem wcd_481 (g : UInt64) :
    decode (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.executionEnv.code
        (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.pc
      = some (.Push .PUSH32, some (7, 32)) := by
  show decode (wcResumed g).exec.executionEnv.code (((414 + 1) + (32+1)) + (32+1)) = _
  rw [wcResumed_code]; rfl
theorem wcd_514 (g : UInt64) :
    decode (wcRec1Push3 g).exec.executionEnv.code (wcRec1Push3 g).exec.pc
      = some (.Smsf .SLOAD, .none) := by
  show decode (wcResumed g).exec.executionEnv.code ((((414 + 1) + (32+1)) + (32+1)) + (32+1)) = _
  rw [wcResumed_code]; rfl
theorem wcd_515 (g : UInt64) :
    decode (wcRec1Sload g).exec.executionEnv.code (wcRec1Sload g).exec.pc
      = some (.ArithLogic .ADD, .none) := by
  show decode (wcResumed g).exec.executionEnv.code (((((414 + 1) + (32+1)) + (32+1)) + (32+1)) + 1) = _
  rw [wcResumed_code]; rfl
theorem wcd_516 (g : UInt64) :
    decode (wcRec1Add g).exec.executionEnv.code (wcRec1Add g).exec.pc
      = some (.ArithLogic .LT, .none) := by
  show decode (wcResumed g).exec.executionEnv.code ((((((414 + 1) + (32+1)) + (32+1)) + (32+1)) + 1) + 1) = _
  rw [wcResumed_code]; rfl
theorem wcd_517 (g : UInt64) :
    decode (wcRetFrame g).exec.executionEnv.code (wcRetFrame g).exec.pc
      = some (.System .RETURN, .none) := by
  show decode (wcResumed g).exec.executionEnv.code (((((((414 + 1) + (32+1)) + (32+1)) + (32+1)) + 1) + 1) + 1) = _
  rw [wcResumed_code]; rfl

/-! ### Gas threading along the post-CALL chain

Every chain frame's gas is `subCharges (wcResumed g).exec.gasAvailable [prefix]` (each
transformer subtracts its `ofNat cost`). The SLOAD charge reduces to `100` (warm,
`wcResumed_warm7`). With `wcResumed_gas = g − 46834 ≥ 3166` (for `g ≥ 50000`) and the
total charges `≤ 244`, every step's gas bound holds with margin. -/

/-- The block-0 SLOAD's warm charge is `100` — its frame's substate/address are the
resumed frame's (the three pushes preserve both), where slot 7 of self is warm. -/
theorem wcRec0_sloadCost (g : UInt64) :
    Evm.sloadCost ((wcRec0Push3 g).exec.substate.accessedStorageKeys.contains
        ((wcRec0Push3 g).exec.executionEnv.address, 7)) = 100 := by
  rw [show (wcRec0Push3 g).exec.substate = (wcResumed g).exec.substate from rfl,
      show (wcRec0Push3 g).exec.executionEnv.address = (wcResumed g).exec.executionEnv.address from rfl,
      wcResumed_addr, wcResumed_warm7]; rfl

/-- The block-1 SLOAD's warm charge is `100` (same self/slot, threaded through the
taken JUMPI + block-1 pushes, which preserve substate/address). -/
theorem wcRec1_sloadCost (g : UInt64) :
    Evm.sloadCost ((wcRec1Push3 g).exec.substate.accessedStorageKeys.contains
        ((wcRec1Push3 g).exec.executionEnv.address, 7)) = 100 := by
  rw [show (wcRec1Push3 g).exec.substate = (wcResumed g).exec.substate from rfl,
      show (wcRec1Push3 g).exec.executionEnv.address = (wcResumed g).exec.executionEnv.address from rfl,
      wcResumed_addr, wcResumed_warm7]; rfl

/-- The gas at the `RETURN` frame, threaded through the whole chain, as a
`subCharges` of the resumed gas over `wcPostCharges`. -/
theorem wcChain_gas (g : UInt64) :
    (wcRetFrame g).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable wcPostCharges := by
  unfold wcRetFrame wcRec1Add wcRec1Sload wcRec1Push3 wcBlock1Jd wcBlock1
    wcRec0PushDest wcRec0Lt wcRec0Add wcRec0Sload wcRec0Push3
    ltFrame addFrame sloadFrame jumpdestFrame jumpFrame pushFrameW
  dsimp only [BytecodeLayer.Dispatch.binOpPost, BytecodeLayer.Dispatch.sloadPost,
    BytecodeLayer.Dispatch.jumpdestPost, BytecodeLayer.Dispatch.jumpPost,
    ExecutionState.replaceStackAndIncrPC, ExecutionState.incrPC]
  rw [show Evm.sloadCost ((wcResumed g).exec.substate.accessedStorageKeys.contains
            ((wcResumed g).exec.executionEnv.address, 7)) = 100 from by
      rw [wcResumed_addr, wcResumed_warm7]; rfl]
  rfl

/-- Every step's running gas equals `resumed − prefix-sum`; in particular the gas at
the `RETURN` frame is `resumed − 244 ≥ 2922` (for `g ≥ 50000`). -/
theorem wcChain_gas_toNat (g : UInt64) (hg : 50000 ≤ g.toNat) :
    (subCharges (wcResumed g).exec.gasAvailable wcPostCharges).toNat
      = (wcResumed g).exec.gasAvailable.toNat - 244 := by
  rw [toNat_subCharges _ _ (by
        rw [wcResumed_gas g hg]
        show wcPostCharges.sum ≤ g.toNat - 46834
        unfold wcPostCharges; simp only [List.sum_cons, List.sum_nil]; omega)]
  show (wcResumed g).exec.gasAvailable.toNat - wcPostCharges.sum = _
  rw [show wcPostCharges.sum = 244 from by unfold wcPostCharges; decide]

/-! ### Per-frame gas lower bounds (each step's charge clears its running gas)

Each chain frame's gas is `resumed − (its prefix of wcPostCharges)`. The gas at each
frame a `runs_*` consumes is `≥ resumed − 244 ≥ 2922` (for `g ≥ 50000`), so every
per-step gas bound (max charge `100`) holds. The frame gas is read as a `subCharges`
(each transformer subtracts `ofNat c`), the SLOAD charge reduced to `100`. -/

/-- The resumed gas lower bound used at every step: `≥ 2922` for `g ≥ 50000`. -/
theorem wcResumed_gas_ge (g : UInt64) (hg : 50000 ≤ g.toNat) :
    2922 ≤ (wcResumed g).exec.gasAvailable.toNat := by
  rw [wcResumed_gas g hg]; omega

/-- A frame whose gas is `subCharges resumed cs` (`cs.sum ≤ 244`) has gas `≥ 2678`
(`= 2922 − 244`), clearing every per-step charge (max `100`). -/
theorem wcSub_gas_ge (g : UInt64) (hg : 50000 ≤ g.toNat) (cs : List ℕ) (hcs : cs.sum ≤ 244) :
    2678 ≤ (subCharges (wcResumed g).exec.gasAvailable cs).toNat := by
  rw [toNat_subCharges _ _ (by have := wcResumed_gas_ge g hg; omega)]
  have := wcResumed_gas_ge g hg; omega

/-- The `wcRec0Sload`-frame gas as a constant-charge `subCharges` (SLOAD = 100). -/
theorem wcRec0Sload_gas (g : UInt64) :
    (wcRec0Sload g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100] := by
  show (wcRec0Push3 g).exec.gasAvailable - UInt64.ofNat
        (Evm.sloadCost ((wcRec0Push3 g).exec.substate.accessedStorageKeys.contains
          ((wcRec0Push3 g).exec.executionEnv.address, 7))) = _
  rw [wcRec0_sloadCost]; rfl

/-- The block-1 SLOAD-frame gas as a constant-charge `subCharges` (SLOAD = 100). -/
theorem wcRec1Sload_gas (g : UInt64) :
    (wcRec1Sload g).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable ([3,3,3,100] ++ [3,3,3,10,1,3,3,3,100]) := by
  rw [subCharges_append, ← wcRec0Sload_gas]
  show (wcRec1Push3 g).exec.gasAvailable - UInt64.ofNat
        (Evm.sloadCost ((wcRec1Push3 g).exec.substate.accessedStorageKeys.contains
          ((wcRec1Push3 g).exec.executionEnv.address, 7))) = _
  rw [wcRec1_sloadCost]
  show (wcRec1Push3 g).exec.gasAvailable - UInt64.ofNat 100
    = subCharges (wcRec0Sload g).exec.gasAvailable [3,3,3,10,1,3,3,3,100]
  rfl

/-! ### Stack facts (the SLOADs push the value `5`) -/

/-- The block-0 SLOAD pushes `5` (caller slot 7), so its frame's stack is
`5 :: 9 :: 100 :: 1 :: []` — the shape the following `ADD` consumes. -/
theorem wcRec0Sload_stack (g : UInt64) :
    (wcRec0Sload g).exec.stack = (5 : Word) :: 9 :: 100 :: 1 :: [] := by
  show ((BytecodeLayer.Dispatch.sloadPost (wcRec0Push3 g).exec 7 [9,100,1]).stack) = _
  unfold BytecodeLayer.Dispatch.sloadPost
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  rw [show ((wcRec0Push3 g).exec.toState.sload 7).2 = 5 from by
      show (((wcRec0Push3 g).exec.accounts.find? (wcRec0Push3 g).exec.executionEnv.address).option 0
            (Account.lookupStorage (k := 7))) = 5
      rw [show (wcRec0Push3 g).exec.accounts = (wcResumed g).exec.accounts from rfl,
          show (wcRec0Push3 g).exec.executionEnv.address = (wcResumed g).exec.executionEnv.address from rfl]
      exact wcResumed_self_sload g]
  rfl

/-- The block-1 SLOAD pushes `5` likewise. -/
theorem wcRec1Sload_stack (g : UInt64) :
    (wcRec1Sload g).exec.stack = (5 : Word) :: 9 :: 100 :: 1 :: [] := by
  show ((BytecodeLayer.Dispatch.sloadPost (wcRec1Push3 g).exec 7 [9,100,1]).stack) = _
  unfold BytecodeLayer.Dispatch.sloadPost
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  rw [show ((wcRec1Push3 g).exec.toState.sload 7).2 = 5 from by
      show (((wcRec1Push3 g).exec.accounts.find? (wcRec1Push3 g).exec.executionEnv.address).option 0
            (Account.lookupStorage (k := 7))) = 5
      rw [show (wcRec1Push3 g).exec.accounts = (wcResumed g).exec.accounts from rfl,
          show (wcRec1Push3 g).exec.executionEnv.address = (wcResumed g).exec.executionEnv.address from rfl]
      exact wcResumed_self_sload g]
  rfl

/-! ### Block-1 cumulative gas equations (push frames after the JUMPDEST) -/

/-- Gas at `wcBlock1Jd` as a `subCharges` (block-0 charges + JUMPI + JUMPDEST). -/
theorem wcBlock1Jd_gas (g : UInt64) :
    (wcBlock1Jd g).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1] := by
  show (wcBlock1 g).exec.gasAvailable - UInt64.ofNat GasConstants.Gjumpdest = _
  rw [show (wcBlock1 g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10] from by
      show (wcRec0PushDest g).exec.gasAvailable - UInt64.ofNat GasConstants.Ghigh = _
      rw [show (wcRec0PushDest g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3] from by
          show (wcRec0Lt g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
          rw [show (wcRec0Lt g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3] from by
              show (wcRec0Add g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
              rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
                  show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                  rw [wcRec0Sload_gas]; rfl]; rfl]; rfl]; rfl]; rfl

theorem wcRec1_g10 (g : UInt64) :
    (pushFrameW (wcBlock1Jd g) 100 32).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3] := by
  show (wcBlock1Jd g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
  rw [wcBlock1Jd_gas]; rfl

theorem wcRec1_g11 (g : UInt64) :
    (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3,3] := by
  show (pushFrameW (wcBlock1Jd g) 100 32).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
  rw [wcRec1_g10]; rfl

theorem wcRec1_g12 (g : UInt64) :
    (wcRec1Push3 g).exec.gasAvailable
      = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3,3,3] := by
  show (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
  rw [wcRec1_g11]; rfl

/-! ### Stack-shape facts threaded into the chain -/

theorem wcRec0Push3_stack (g : UInt64) :
    (wcRec0Push3 g).exec.stack = (7 : Word) :: 9 :: 100 :: 1 :: [] := by
  show Stack.push (Stack.push (Stack.push (wcResumed g).exec.stack 100) 9) 7 = _
  rw [wcResumed_stack]; rfl

theorem wcBlock1Jd_stack (g : UInt64) : (wcBlock1Jd g).exec.stack = (1 : Word) :: [] := rfl

theorem wcRec1Push3_stack (g : UInt64) :
    (wcRec1Push3 g).exec.stack = (7 : Word) :: 9 :: 100 :: 1 :: [] := rfl

/-! ### The assembled post-CALL run

`wcResumed g → … → wcRetFrame g` (pc 517, `RETURN`) as one `Runs`, a `Runs.trans`
chain of the exp003 opcode rules over the post-CALL frames. Decode at each pc
(`wcd_*`), gas via the `subCharges`/`wcSub_gas_ge` bounds (warm SLOAD = 100), SLOAD
value `5` (`wcRec*Sload_stack`), the taken `JUMPI` to block 1 (`wc_get_dest_414` on
`wcResumed_validJumps`). For `g ≥ 50000`. -/
theorem wcPostRun (g : UInt64) (hg : 50000 ≤ g.toNat) :
    Runs (wcResumed g) (wcRetFrame g) := by
  -- block 0 recompute: PUSH 100; PUSH 9; PUSH 7
  refine (runs_push (wcResumed g) .PUSH32 100 32 (by nofun) (wcd_300 g) rfl rfl
      (by show 3 ≤ (subCharges (wcResumed g).exec.gasAvailable []).toNat
          have := wcSub_gas_ge g hg [] (by simp); omega)
      (by rw [wcResumed_stack]; decide)).trans ?_
  refine (runs_push _ .PUSH32 9 32 (by nofun) (wcd_333 g) rfl rfl
      (by show 3 ≤ (subCharges (wcResumed g).exec.gasAvailable [3]).toNat
          have := wcSub_gas_ge g hg [3] (by simp); omega)
      (by rw [show (pushFrameW (wcResumed g) 100 32).exec.stack = (100:Word) :: 1 :: [] from by
              show Stack.push (wcResumed g).exec.stack 100 = _; rw [wcResumed_stack]; rfl]
          decide)).trans ?_
  refine (runs_push _ .PUSH32 7 32 (by nofun) (wcd_366 g) rfl rfl
      (by show 3 ≤ (subCharges (wcResumed g).exec.gasAvailable [3,3]).toNat
          have := wcSub_gas_ge g hg [3,3] (by simp); omega)
      (by rw [show (pushFrameW (pushFrameW (wcResumed g) 100 32) 9 32).exec.stack = (9:Word) :: 100 :: 1 :: [] from by
              show Stack.push (Stack.push (wcResumed g).exec.stack 100) 9 = _; rw [wcResumed_stack]; rfl]
          decide)).trans ?_
  -- SLOAD 7 (warm, value 5)
  refine (runs_sload (wcRec0Push3 g) 7 [9,100,1] (wcd_399 g) (wcRec0Push3_stack g)
      (by rw [wcRec0Push3_stack]; decide)
      (by rw [show Evm.sloadCost ((wcRec0Push3 g).exec.substate.accessedStorageKeys.contains
              ((wcRec0Push3 g).exec.executionEnv.address, 7)) = 100 from wcRec0_sloadCost g]
          show 100 ≤ (subCharges (wcResumed g).exec.gasAvailable [3,3,3]).toNat
          have := wcSub_gas_ge g hg [3,3,3] (by simp); omega)).trans ?_
  -- ADD (5 + 9 = 14)
  refine (runs_add (wcRec0Sload g) 5 9 [100,1] (wcd_400 g) (wcRec0Sload_stack g)
      (by rw [wcRec0Sload_stack]; decide)
      (by rw [wcRec0Sload_gas]; have := wcSub_gas_ge g hg [3,3,3,100] (by simp)
          show (3:ℕ) ≤ _; omega)).trans ?_
  -- LT (14 < 100 = 1)
  refine (runs_lt (wcRec0Add g) 14 100 [1] (wcd_401 g) rfl
      (by rw [show (wcRec0Add g).exec.stack = (14:Word) :: 100 :: 1 :: [] from rfl]; decide)
      (by show (3:ℕ) ≤ (wcRec0Add g).exec.gasAvailable.toNat
          rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
              show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
              rw [wcRec0Sload_gas]; rfl]
          have := wcSub_gas_ge g hg [3,3,3,100,3] (by simp); omega)).trans ?_
  -- PUSH4 414 (then-target)
  refine (runs_push _ .PUSH4 414 4 (by nofun) (wcd_402 g) rfl rfl
      (by show 3 ≤ (wcRec0Lt g).exec.gasAvailable.toNat
          rw [show (wcRec0Lt g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3] from by
              show (wcRec0Add g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
              rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
                  show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                  rw [wcRec0Sload_gas]; rfl]; rfl]
          have := wcSub_gas_ge g hg [3,3,3,100,3,3] (by simp); omega)
      (by show (wcRec0Lt g).exec.stack.size + 1 ≤ 1024
          rw [show (wcRec0Lt g).exec.stack = (1:Word) :: 1 :: [] from rfl]
          decide)).trans ?_
  -- JUMPI taken to block 1 (cond = lt result = 1 ≠ 0, dest 414)
  refine (runs_jumpi_taken (wcRec0PushDest g) 414 1 414 [1] (wcd_407 g) rfl
      (by show (wcRec0PushDest g).exec.stack.size ≤ 1024
          rw [show (wcRec0PushDest g).exec.stack = (414:Word) :: 1 :: 1 :: [] from rfl]
          decide)
      (by show (10:ℕ) ≤ (wcRec0PushDest g).exec.gasAvailable.toNat
          rw [show (wcRec0PushDest g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3] from by
              show (wcRec0Lt g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
              rw [show (wcRec0Lt g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3] from by
                  show (wcRec0Add g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                  rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
                      show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                      rw [wcRec0Sload_gas]; rfl]; rfl]; rfl]
          have := wcSub_gas_ge g hg [3,3,3,100,3,3,3] (by simp); omega)
      (by decide)
      (wc_get_dest_414 (wcRec0PushDest g) (by
          show (wcRec0PushDest g).validJumps = validJumpDests (lower Lir.Decode.workedCall) 0
          show (wcResumed g).validJumps = _; exact wcResumed_validJumps g))).trans ?_
  -- block 1: JUMPDEST
  refine (runs_jumpdest (wcBlock1 g) (wcd_414 g)
      (by rw [show (wcBlock1 g).exec.stack = (1:Word) :: [] from rfl]; decide)
      (by show (1:ℕ) ≤ (wcBlock1 g).exec.gasAvailable.toNat
          rw [show (wcBlock1 g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10] from by
              show (wcRec0PushDest g).exec.gasAvailable - UInt64.ofNat GasConstants.Ghigh = _
              rw [show (wcRec0PushDest g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3] from by
                  show (wcRec0Lt g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                  rw [show (wcRec0Lt g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3] from by
                      show (wcRec0Add g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                      rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
                          show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                          rw [wcRec0Sload_gas]; rfl]; rfl]; rfl]; rfl]
          have := wcSub_gas_ge g hg [3,3,3,100,3,3,3,10] (by simp); show 1 ≤ _; omega)).trans ?_
  -- block 1 recompute: PUSH 100; PUSH 9; PUSH 7
  refine (runs_push (wcBlock1Jd g) .PUSH32 100 32 (by nofun) (wcd_415 g) rfl rfl
      (by show 3 ≤ (wcBlock1Jd g).exec.gasAvailable.toNat
          rw [show (wcBlock1Jd g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1] from by
              show (wcBlock1 g).exec.gasAvailable - UInt64.ofNat GasConstants.Gjumpdest = _
              rw [show (wcBlock1 g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10] from by
                  show (wcRec0PushDest g).exec.gasAvailable - UInt64.ofNat GasConstants.Ghigh = _
                  rw [show (wcRec0PushDest g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3] from by
                      show (wcRec0Lt g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                      rw [show (wcRec0Lt g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3] from by
                          show (wcRec0Add g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                          rw [show (wcRec0Add g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3] from by
                              show (wcRec0Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
                              rw [wcRec0Sload_gas]; rfl]; rfl]; rfl]; rfl]; rfl]
          have := wcSub_gas_ge g hg [3,3,3,100,3,3,3,10,1] (by simp); omega)
      (by rw [wcBlock1Jd_stack]; decide)).trans ?_
  refine (runs_push _ .PUSH32 9 32 (by nofun) (wcd_448 g) rfl rfl
      (by have := wcSub_gas_ge g hg [3,3,3,100,3,3,3,10,1,3] (by simp)
          show 3 ≤ (pushFrameW (wcBlock1Jd g) 100 32).exec.gasAvailable.toNat
          rw [show (pushFrameW (wcBlock1Jd g) 100 32).exec.gasAvailable
                = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3] from
              wcRec1_g10 g]; omega)
      (by rw [show (pushFrameW (wcBlock1Jd g) 100 32).exec.stack = (100:Word) :: 1 :: [] from by
              show Stack.push (wcBlock1Jd g).exec.stack 100 = _; rw [wcBlock1Jd_stack]; rfl]
          decide)).trans ?_
  refine (runs_push _ .PUSH32 7 32 (by nofun) (wcd_481 g) rfl rfl
      (by have := wcSub_gas_ge g hg [3,3,3,100,3,3,3,10,1,3,3] (by simp)
          show 3 ≤ (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.gasAvailable.toNat
          rw [show (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.gasAvailable
                = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3,3] from wcRec1_g11 g]; omega)
      (by rw [show (pushFrameW (pushFrameW (wcBlock1Jd g) 100 32) 9 32).exec.stack = (9:Word) :: 100 :: 1 :: [] from by
              show Stack.push (Stack.push (wcBlock1Jd g).exec.stack 100) 9 = _; rw [wcBlock1Jd_stack]; rfl]
          decide)).trans ?_
  -- block 1 SLOAD (warm, value 5)
  refine (runs_sload (wcRec1Push3 g) 7 [9,100,1] (wcd_514 g) (wcRec1Push3_stack g)
      (by rw [wcRec1Push3_stack]; decide)
      (by rw [show Evm.sloadCost ((wcRec1Push3 g).exec.substate.accessedStorageKeys.contains
              ((wcRec1Push3 g).exec.executionEnv.address, 7)) = 100 from wcRec1_sloadCost g]
          have := wcSub_gas_ge g hg [3,3,3,100,3,3,3,10,1,3,3,3] (by simp)
          rw [show (wcRec1Push3 g).exec.gasAvailable
                = subCharges (wcResumed g).exec.gasAvailable [3,3,3,100,3,3,3,10,1,3,3,3] from wcRec1_g12 g]; omega)).trans ?_
  -- block 1 ADD (5 + 9 = 14)
  refine (runs_add (wcRec1Sload g) 5 9 [100,1] (wcd_515 g) (wcRec1Sload_stack g)
      (by rw [wcRec1Sload_stack]; decide)
      (by rw [wcRec1Sload_gas]; have := wcSub_gas_ge g hg ([3,3,3,100] ++ [3,3,3,10,1,3,3,3,100]) (by simp)
          show (3:ℕ) ≤ _; omega)).trans ?_
  -- block 1 LT (14 < 100 = 1) — the RETURN frame
  exact runs_lt (wcRec1Add g) 14 100 [1] (wcd_516 g) rfl
      (by rw [show (wcRec1Add g).exec.stack = (14:Word) :: 100 :: 1 :: [] from rfl]; decide)
      (by show (3:ℕ) ≤ (wcRec1Add g).exec.gasAvailable.toNat
          rw [show (wcRec1Add g).exec.gasAvailable
                = subCharges (wcResumed g).exec.gasAvailable ([3,3,3,100] ++ [3,3,3,10,1,3,3,3,100,3]) from by
              show (wcRec1Sload g).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow = _
              rw [wcRec1Sload_gas]; rfl]
          have := wcSub_gas_ge g hg ([3,3,3,100] ++ [3,3,3,10,1,3,3,3,100,3]) (by simp); omega)

/-! ### The terminal `RETURN` halt

The `RETURN` frame `wcRetFrame g` (pc 517) has stack `[1, 1]` (the `lt` result on top
as `offset`, the residual CALL flag below as `size`). Its memory-expansion charge for
`offset = size = 1` is `Cₘ 1 − Cₘ 0 = 3`, which the running gas (`≥ 2678`) covers, so
`RETURN` halts (`stepFrame_return_halts`). -/

/-- The `RETURN` frame's active words are `0` (default; every transformer and
`resumeAfterCall`'s zero in/out windows leave them untouched). -/
theorem wcRetFrame_activeWords (g : UInt64) : (wcRetFrame g).exec.activeWords = 0 := by
  show (wcResumed g).exec.activeWords = 0
  unfold wcResumed resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; rfl

/-- The `RETURN` frame's stack is `[1, 1]` (the `lt` result `1` on top, the residual
CALL success flag `1` below). -/
theorem wcRetFrame_stack (g : UInt64) : (wcRetFrame g).exec.stack = (1 : Word) :: 1 :: [] := rfl

/-- **The `RETURN` halts.** At `wcRetFrame g` (pc 517, stack `[1,1]`), the
memory-expansion charge for `offset = size = 1` succeeds (cost `3`, gas `≥ 2678`), so
`stepFrame` halts. -/
theorem wcRetFrame_halts (g : UInt64) (hg : 50000 ≤ g.toNat) :
    ∃ halt, stepFrame (wcRetFrame g) = .halted halt := by
  have hgas : (wcRetFrame g).exec.gasAvailable.toNat = (wcResumed g).exec.gasAvailable.toNat - 244 := by
    rw [show (wcRetFrame g).exec.gasAvailable = subCharges (wcResumed g).exec.gasAvailable wcPostCharges
          from wcChain_gas g]
    exact wcChain_gas_toNat g hg
  have hge : 3 ≤ (wcRetFrame g).exec.gasAvailable.toNat := by
    rw [hgas]; have := wcResumed_gas_ge g hg; omega
  -- chargeMemExpansion succeeds: M 0 1 1 = 1, charge Cₘ 1 − Cₘ 0 = 3 ≤ gas.
  have hmem : chargeMemExpansion (wcRetFrame g).exec 1 1
      = .ok { (wcRetFrame g).exec with gasAvailable := (wcRetFrame g).exec.gasAvailable - UInt64.ofNat 3 } := by
    unfold chargeMemExpansion
    rw [show Evm.memoryExpansionWords? (wcRetFrame g).exec.activeWords 1 1
          = some (MachineState.M (wcRetFrame g).exec.activeWords 1 1) from by
        rw [wcRetFrame_activeWords]; rfl]
    show charge (Evm.Cₘ (MachineState.M (wcRetFrame g).exec.activeWords 1 1)
        - Evm.Cₘ (wcRetFrame g).exec.activeWords) (wcRetFrame g).exec = _
    rw [wcRetFrame_activeWords]
    rw [show Evm.Cₘ (MachineState.M 0 1 1) - Evm.Cₘ 0 = 3 from by decide]
    unfold charge
    rw [if_neg (by have := hge; omega)]
  exact stepFrame_return_halts (wcRetFrame g) 1 1 [] (wcd_517 g) (wcRetFrame_stack g)
    (by rw [wcRetFrame_stack]; decide) _ hmem

/-! ## `lower_preserves` for `workedCall` (the bridge half)

The full execution of `workedCall` as one `Runs (wcFrame g) last`:

```
  wcFrame g  --wc_prefix_runs-->  wcCallSite g       (the genuine straight-line prefix)
             --Runs.call (wc_callReturns)-->  wcResumed g   (the CONCRETE external CALL,
                                                              now closed — child drive run)
             --hpost : Runs (wcResumed g) last-->  last      (block-0 branch recompute, then
                                                              block 1's RETURN)
             --halts (stepFrame last = .halted halt)
```

`wc_prefix_runs` (proved above) is the real prefix; the CALL is a `Runs.call` node
carrying the **concrete** `wc_callReturns` witness (no longer assumed); only the
post-CALL run `hpost` and its halt `hhalt` remain hypotheses, discharged through the
bridge with `lower_preserves_discharge`. The result holds for **any** assembled
post-CALL run — and because the bridge composes any number of `Runs.call` nodes, a
≥2-call worked program closes the same way (C4).

**The documented post-CALL remainder** (NOT stubbed). To make `wc_preserves`
*fully* hypothesis-free, `hpost`/`hhalt` must be the genuine block-0 recompute run:
from `wcResumed g` (pc 300, stack `[1]` — the CALL success flag — with the
`wcResumed_*` fields above), run `PUSH32 100; PUSH32 9; PUSH32 7; SLOAD; ADD; LT;
PUSH4 414; JUMPI` (the `lt` condition `(sload 7 + 9) < 100 = 1`, so the JUMPI is
taken via `wc_get_dest_414`), then block 1's `JUMPDEST; PUSH32 100; PUSH32 9;
PUSH32 7; SLOAD; ADD; LT; RETURN`. Three honest sub-pieces remain:
1. **The resumed-gas lower bound.** The resumed gas is `callerCharged.gasAvailable +
   childRemaining`; `callerCharged` retains `~1/64` of the pre-call gas
   (`allButOneSixtyFourth`), so it is large for big `g`, but the bound requires the
   `allButOneSixtyFourth` arithmetic over `callGasCap`.
2. **The SLOAD value over the child-committed map.** `wcResumed g`'s accounts are the
   child's committed map (`sstorePost (wcChildAfter2Push g) 7 5`); the caller's slot
   `7` there is still `5` (block 0 wrote it; the child wrote `0xCA11EE`'s slot), so
   `sload 7 = 5` and the recomputed `lt` is `1`. Needs a named storage-lens lemma over
   that map.
3. **A general `RETURN` halt.** The lowering's `ret t` materialises the value, so the
   `RETURN` consumes `offset = 1, size = 1` (not the `0,0` of exp003's
   `stepFrame_return_empty`); the halt needs a general `RETURN` step
   (`∃ halt, stepFrame fr = .halted halt` from `chargeMemExpansion` succeeding),
   provable in this layer but left as the documented next step. -/

/-- **`lower_preserves` for `workedCall` — FULLY HYPOTHESIS-FREE.** Every piece is
now concrete and supplied internally: the straight-line prefix (`wc_prefix_runs`), the
single external CALL (`wc_callReturns` — the genuine child `drive`), the post-CALL
block-0 recompute → taken `JUMPI` → block-1 recompute (`wcPostRun`), and the terminal
`RETURN` halt (`wcRetFrame_halts`). For `g ≥ 50000` the top-level
`messageCall (wcParams g)` delivers the `RETURN` frame's halt result. The `hcall` AND
the `hpost`/`hhalt` hypotheses of the C3d–C3f shape are **all gone** — `wc_preserves`
takes only the program (implicit) and the gas knob `g`. -/
theorem wc_preserves (g : UInt64) (hg : 50000 ≤ g.toNat) :
    ∃ halt, messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame (wcRetFrame g) halt)) := by
  obtain ⟨halt, hhalt⟩ := wcRetFrame_halts g hg
  refine ⟨halt, ?_⟩
  have hruns : Runs (wcFrame g) (wcRetFrame g) :=
    (wc_prefix_runs g (by omega)).trans (Runs.call (wc_callReturns g hg) (wcPostRun g hg))
  exact lower_preserves_discharge Lir.Decode.workedCall (wcParams g)
    (wc_begin g) rfl hruns hhalt

/-- **C4 — multi-call corollary (shape).** Because `lower_preserves_discharge` crosses
the bridge for *any* assembled `Runs` (any number of `Runs.call` nodes), a worked
program with two returning external CALLs closes by the same discharge: glue the prefix,
the first call node, the middle run, the second call node, and the suffix into one
`Runs`, then cross once. This is `wc_preserves` generalised to two calls — the bridge
needs nothing more (cf. `Examples.TwoCallExample.twoCall_messageCall`).

This stays a *shape* lemma (it takes the two-call assembly as hypotheses) because
`workedCall` itself has exactly **one** external CALL — there is no concrete two-call
program here to instantiate the pieces from. The single concrete deliverable,
`wc_preserves`, is fully hypothesis-free; `wc_preserves_twoCall` records that the same
discharge composes any number of concrete `CallReturns` nodes (each closeable exactly
like `wc_callReturns`), so a genuine two-call program closes with no extra theory. -/
theorem wc_preserves_twoCall (g : UInt64)
    {fr₀ callFr₁ resumeFr₁ callFr₂ resumeFr₂ last : Frame} {halt : FrameHalt}
    (hbegin  : EntersAsCode (wcParams g) fr₀)
    (hcode   : fr₀.exec.executionEnv.code = lower Lir.Decode.workedCall)
    (hpre    : Runs fr₀ callFr₁)
    (hcall₁  : CallReturns callFr₁ resumeFr₁)
    (hmiddle : Runs resumeFr₁ callFr₂)
    (hcall₂  : CallReturns callFr₂ resumeFr₂)
    (hpost   : Runs resumeFr₂ last)
    (hhalt   : stepFrame last = .halted halt) :
    messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  lower_preserves_discharge Lir.Decode.workedCall (wcParams g) hbegin hcode
    (hpre.trans (Runs.call hcall₁ (hmiddle.trans (Runs.call hcall₂ hpost)))) hhalt

end Lir.WorkedCall
