import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.UInt256
import BytecodeLayer.Examples.ProgramDecode
import BytecodeLayer.Programs

/-!
# Demonstration — `sstoreProgram` proven by composing opcode rules

The headline `messageCall_sstore_storageAt` in `Proof/StraightlineInstances.lean`
proves the same program by writing out `sstoreF1`, `sstoreF2`, `sstoreF3` (the
execution trace) with their gas arithmetic and chaining them by hand. Here we
reprove it **compositionally**: glue `runs_push1 5`, `runs_push1 7`, `runs_sstore`
with `Runs.trans` (the sequencing rule), and read the result through the SSTORE
effect/frame projection lemmas. No intermediate frame is named in the theorem and
the stored value `5` is **derived** from the composition (the `newValue` operand
of `runs_sstore`), not asserted.

The two conclusions:
* **effect** — the run completes leaving `5` at cell `(addrA, 7)`;
* **frame** — the same run leaves cell `(addrA, 8)` untouched (still `0`).
-/

namespace BytecodeLayer.Examples
open Evm
open GasConstants
open BytecodeLayer.UInt256
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Hoare

set_option maxRecDepth 4000

/-- The frame `sstoreProgram` is sitting on when it `STOP`s, obtained by composing
the three opcode rules — never written out as a literal frame in any statement.
`fr₀` is the initial code frame; the pushes leave `[7, 5]` on the stack, then
SSTORE writes. -/
private def fr₀ (g : UInt64) : Frame := codeFrame (paramsSStore g) sstoreProgram

/-- The self address `addrA`. -/
private theorem self_addr (g : UInt64) : (fr₀ g).exec.executionEnv.address = addrA := rfl

/-- The self account present in the initial world (`addrA`). Named as the
concrete `find!` entry; its storage is empty (proved on demand by `rfl`). -/
private def selfAcc (g : UInt64) : Account := (fr₀ g).exec.accounts.find! addrA

private theorem self_present (g : UInt64) :
    (fr₀ g).exec.accounts.find? (fr₀ g).exec.executionEnv.address = some (selfAcc g) := by
  rw [self_addr]; rfl

set_option maxHeartbeats 1000000 in
/-- **The composed run.** From the initial frame, `Runs 3` to the post-SSTORE
frame `last`, built by `Runs.trans` of the three opcode rules. The value `5` and
slot `7` enter only as the `runs_sstore` operands; the intermediate frames live
inside the `Runs` proof. -/
private theorem sstore_runs (g : UInt64) (hg : 22106 ≤ g.toNat) :
    Runs 3 (fr₀ g)
      (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  have hg0 : (fr₀ g).exec.gasAvailable.toNat = g.toNat := rfl
  -- gas after the two pushes is g - 6
  have hg1 : ((fr₀ g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat = g.toNat - 3 := by
    rw [gv]; show (g - UInt64.ofNat 3).toNat = g.toNat - 3
    rw [toNat_sub_ofNat g 3 (by omega) (by omega)]
  have hg1' : ((fr₀ g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat = g.toNat - 3 := hg1
  have hg2 : ((pushFrame (fr₀ g) 5).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
      = g.toNat - 6 := by
    show (((fr₀ g).exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow).toNat
        = g.toNat - 6
    rw [gv, toNat_sub_ofNat _ 3 (by rw [show GasConstants.Gverylow = 3 from rfl] at hg1'; omega) (by omega)]
    rw [show GasConstants.Gverylow = 3 from rfl] at hg1'; omega
  -- compose: push 5, push 7, sstore  (3 = 1 + (1 + 1))
  refine Runs.trans (runs_push1 (fr₀ g) 5 decode_sstore_0 (by rw [hg0]; omega) (by show (0:ℕ)+1 ≤ 1024; omega))
    (Runs.trans (runs_push1 (pushFrame (fr₀ g) 5) 7 decode_sstore_2 ?_ (by show (1:ℕ)+1 ≤ 1024; omega))
      (runs_sstore (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack
        decode_sstore_4 rfl (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_))
  · -- gas ≥ 3 after first push
    show 3 ≤ ((fr₀ g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
    rw [hg1]; omega
  · -- stipend gate after two pushes (the frame's own gas is the twice-charged value)
    show ¬ ((pushFrame (fr₀ g) 5).exec.gasAvailable - UInt64.ofNat Gverylow).toNat ≤ Gcallstipend
    rw [hg2, show Gcallstipend = 2300 from rfl]; omega
  · -- store cost ≤ remaining gas
    rw [show sstoreChargeOf (pushFrame (pushFrame (fr₀ g) 5) 7).exec 7 5 = 22100 from rfl]
    show (22100:ℕ) ≤ ((pushFrame (fr₀ g) 5).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
    rw [hg2]; omega

set_option maxHeartbeats 1000000 in
/-- The post-SSTORE frame halts on `STOP` (pc 5) with empty output. -/
private theorem sstore_halt (g : UInt64) :
    stepFrame (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack)
      = Signal.halted (.success
          (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack).exec .empty) :=
  stepFrame_stop _ decode_sstore_5 (by show (0:ℕ) ≤ 1024; omega)

set_option maxHeartbeats 1000000 in
/-- `messageCall` of `sstoreProgram` equals the success result of the composed
run's final frame — derived through `messageCall_runs`, with the fuel obligation
`3 + 2 ≤ seedFuel g` discharged from the gas. -/
private theorem sstore_messageCall (g : UInt64) (hg : 22106 ≤ g.toNat) :
    messageCall (paramsSStore g)
      = .ok (FrameResult.toCallResult (endFrame
          (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack)
          (.success
            (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack).exec .empty))) :=
  messageCall_runs (paramsSStore g) (fr₀ g) _
    (beginCall_code (paramsSStore g) sstoreProgram rfl)
    (sstore_runs g hg) _ (sstore_halt g)
    (by show (3:ℕ) + 2 ≤ seedFuel g; unfold seedFuel; omega)

/-- The SSTORE-stepping frame's account self-lookup, lifted from `fr₀` through the
two pushes (which preserve accounts and the execution env). Stated at the frame's
own `executionEnv.address` (definitionally `addrA`). -/
private theorem step_self_present (g : UInt64) :
    (pushFrame (pushFrame (fr₀ g) 5) 7).exec.accounts.find?
        (pushFrame (pushFrame (fr₀ g) 5) 7).exec.executionEnv.address
      = some (selfAcc g) := self_present g

/-- Abbreviation for the success result of the composed run, used to keep the
demonstration statement readable. -/
private def demoResult (g : UInt64) : CallResult :=
  FrameResult.toCallResult (endFrame
    (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack)
    (.success (sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack).exec .empty))

/-- The written cell holds the **derived** `5`. -/
private theorem demo_effect (g : UInt64) :
    CallResult.storageAt (demoResult g) addrA 7 = 5 := by
  show ((sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack).exec.accounts.find?
          addrA |>.option 0 (·.lookupStorage 7)) = 5
  exact sstoreFrame_storage_self (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack
    (selfAcc g) (step_self_present g) (by decide)

/-- The other cell `(addrA, 8)` is left untouched at `0` — the framing fact. -/
private theorem demo_frame (g : UInt64) :
    CallResult.storageAt (demoResult g) addrA 8 = 0 := by
  show ((sstoreFrame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack).exec.accounts.find?
          addrA |>.option 0 (·.lookupStorage 8)) = 0
  rw [sstoreFrame_storage_frame (pushFrame (pushFrame (fr₀ g) 5) 7) 7 5 (fr₀ g).exec.stack
    (selfAcc g) (step_self_present g) (by decide) addrA 8 (Or.inr (by decide))]
  rfl

set_option maxHeartbeats 1000000 in
/-- The success outcome of the message call decodes to `completed`, with its
queryable storage being `storageAt (demoResult g)`. -/
private theorem demo_outcome (g : UInt64) (hg : 22106 ≤ g.toNat) :
    Outcome.ofCall (messageCall (paramsSStore g))
      = .completed .empty (CallResult.storageAt (demoResult g)) := by
  rw [sstore_messageCall g hg]
  show Outcome.ofResult (demoResult g) = _
  rw [Outcome.ofResult, if_pos (show (demoResult g).success = true from rfl)]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The demonstration theorem.** Running `sstoreProgram` at `addrA` (under its
exact gas cost) completes leaving `5` at cell `(addrA, 7)` — the `5` **derived**
by composing `runs_push1`/`runs_sstore`, not assumed — **and** leaves cell
`(addrA, 8)` untouched at `0` (the framing fact). Stated entirely through the
`Outcome` lens: no `Frame`, pc, stack, gas counter, or fuel, and no execution
trace in the statement or in any hypothesis (the only hypothesis is the semantic
gas bound `22106 ≤ g`). -/
theorem hoare_demo (g : UInt64) (hg : 22106 ≤ g.toNat) :
    Outcome.completedWith (Outcome.ofCall (messageCall (paramsSStore g))) addrA 7 5
    ∧ (∀ out σ, Outcome.ofCall (messageCall (paramsSStore g)) = .completed out σ → σ addrA 8 = 0) := by
  refine ⟨⟨.empty, _, demo_outcome g hg, demo_effect g⟩, ?_⟩
  intro out σ hc
  rw [demo_outcome g hg] at hc
  cases hc
  exact demo_frame g

end BytecodeLayer.Examples
