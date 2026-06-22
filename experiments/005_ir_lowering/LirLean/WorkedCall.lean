import LirLean.Match
import LirLean.Decode
import BytecodeLayer.Programs
import BytecodeLayer.Hoare.Sequence
import BytecodeLayer.Semantics.UInt64

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

## The two honest remainders (NOT `sorry`)

A *fully self-contained* `workedCall` closure — `wc_preserves` with **no**
hypotheses, all the way to a literal `STOP`/`RETURN` halt — is blocked on two
concrete pieces, kept as honest hypotheses of `wc_preserves` (verified feasible,
not stubbed):

1. **The concrete child `CallReturns`.** `wc_call_step` already pins the CALL step;
   what remains is the child `drive` run of the `0xCA11EE` callee
   (`PUSH1 5; PUSH1 7; SSTORE; STOP`) at the 63/64-capped CALL-site gas, in the
   post-SSTORE world — the `CallerProgExample.caller_callReturns` shape transposed
   onto `wcCallSite g`. Confirmed feasible: `toExecute (wcCallSite g).accounts
   0xCA11EE = .Code calleeProg` (`rfl`) and the forwarded child gas clears the
   callee's `22106` cold-SSTORE floor (e.g. `g = 1_000_000`, `by decide`).

2. **The post-CALL branch terminator.** After the CALL returns, block 0 recomputes
   the `lt` condition and runs `JUMPI`/`JUMP`. `Frame.get_dest` reads the frame's
   `validJumps`, which for the real entry frame `codeFrame … (lower workedCall)` is
   `validJumpDests (lower workedCall) 0` — a `partial def`, so it cannot be reduced
   in a proof without `native_decide` (which would break the axiom-clean bar; the same
   reason `Examples.BranchExample` builds its JUMPI frame with an *explicit*
   `validJumps` rather than via `codeFrame`). Closing the branch axiom-cleanly needs a
   `validJumpDests`-characterization lemma on `lower prog`, tracked in `PLAN.md`.

Both are external to the bridge half proved here; see `PLAN.md` (C3d log).
-/

namespace Lir.WorkedCall

open Evm Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open BytecodeLayer.UInt64

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

/-! ## `lower_preserves` for `workedCall` (the bridge half)

The full execution of `workedCall` as one `Runs (wcFrame g) last`:

```
  wcFrame g  --wc_prefix_runs-->  wcCallSite g
             --Runs.call (CallReturns)-->  resumeFr      (the single external CALL)
             --Runs resumeFr last-->  last               (block-0 branch recompute, then
                                                          ret/stop in the taken block)
             --halts (stepFrame last = .halted halt)
```

`wc_prefix_runs` (proved above) is the real prefix; the CALL is a `Runs.call` node
carrying a `CallReturns (wcCallSite g) resumeFr` witness; the post-CALL run and the
terminating halt are the remaining concrete pieces. We state `lower_preserves` taking
exactly those as hypotheses (the `Examples.TwoCallExample.twoCall_messageCall` shape),
and discharge it through the bridge with `lower_preserves_discharge`. The result holds
for **any** assembled post-CALL run — so once the concrete child `CallReturns` and the
branch-block post-run land, this closes `workedCall` end-to-end; and because the bridge
composes any number of `Runs.call` nodes, a ≥2-call worked program closes the same way
(C4). -/

/-- **`lower_preserves` for `workedCall`.** Given the single returning external CALL
(`CallReturns (wcCallSite g) resumeFr`) and the post-CALL run to a halting `last`, the
top-level `messageCall (wcParams g)` delivers `last`'s halt result. The prefix run to
the CALL site (`wc_prefix_runs`) is genuine; the call node and post-run are the
documented concrete remainder (see `PLAN.md`). -/
theorem wc_preserves (g : UInt64) (hg : 30000 ≤ g.toNat)
    {resumeFr last : Frame} {halt : FrameHalt}
    (hcall : CallReturns (wcCallSite g) resumeFr)
    (hpost : Runs resumeFr last)
    (hhalt : stepFrame last = .halted halt) :
    messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  have hruns : Runs (wcFrame g) last :=
    (wc_prefix_runs g hg).trans (Runs.call hcall hpost)
  exact lower_preserves_discharge Lir.Decode.workedCall (wcParams g)
    (wc_begin g) rfl hruns hhalt

/-- **C4 — multi-call corollary (shape).** Because `lower_preserves_discharge` crosses
the bridge for *any* assembled `Runs` (any number of `Runs.call` nodes), a worked
program with two returning external CALLs closes by the same discharge: glue the prefix,
the first call node, the middle run, the second call node, and the suffix into one
`Runs`, then cross once. This is `wc_preserves` generalised to two calls — the bridge
needs nothing more (cf. `Examples.TwoCallExample.twoCall_messageCall`). -/
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
