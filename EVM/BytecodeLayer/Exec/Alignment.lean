import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Exec.RecorderLemmas

namespace BytecodeLayer.Exec.Invariants

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.Exec.Recorder

/-- A recorded GAS word is the read exposed by the post-charge GAS frame. -/
theorem gasRecord_eq_gasReadOf (current : Frame) {exec : ExecutionState}
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    UInt256.ofUInt64 exec.gasAvailable = gasReadOf (gasFrame current) := by
  have hforced : stepFrame current = .next (Dispatch.gasPost current.exec) :=
    BytecodeLayer.Dispatch.stepFrame_gas current hdec hsz hgas
  rw [hstep] at hforced
  have hexec : exec = Dispatch.gasPost current.exec := (Signal.next.injEq _ _).mp hforced
  subst hexec
  rfl

/-- `gasReadOf` at the GAS post-frame is the pre-frame's post-charge gas word. -/
theorem gasReadOf_gasFrame_eq_obs (fr : Frame) :
    gasReadOf (gasFrame fr)
      = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) := by
  rfl

/-- A recorded gas accumulator aligned with its reachable GAS frames. -/
def GasLogAligned (gasAcc : List Word) (frs : List Frame) : Prop :=
  gasAcc = frs.map gasReadOf ∧ FramesRun frs

theorem gasLogAligned_nil : GasLogAligned [] [] := ⟨rfl, trivial⟩

/-- Appending a reachable frame preserves a `FramesRun` chain. -/
theorem FramesRun.snoc :
    ∀ {frs : List Frame} {last g : Frame},
      FramesRun frs → frs.getLast? = some last → Runs last g → FramesRun (frs ++ [g])
  | [], _, _, _, hlast, _ => by simp at hlast
  | [a], last, g, _, hlast, hrun => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    exact ⟨hrun, trivial⟩
  | a :: b :: rest, last, g, h, hlast, hrun => by
    obtain ⟨hab, htl⟩ := h
    have hlast' : (b :: rest).getLast? = some last := by
      rw [List.getLast?_cons_cons] at hlast
      exact hlast
    exact ⟨hab, FramesRun.snoc htl hlast' hrun⟩

/-- A top-level GAS record extends the gas/frame alignment in lockstep. -/
theorem gasLogAligned_step_gas {gasAcc : List Word} {frs : List Frame} {current : Frame}
    {exec : ExecutionState} {last : Frame}
    (halign : GasLogAligned gasAcc frs)
    (hlast : frs.getLast? = some last)
    (hreach : Runs last (gasFrame current))
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    GasLogAligned (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) (frs ++ [gasFrame current]) := by
  obtain ⟨hreads, hrun⟩ := halign
  refine ⟨?_, FramesRun.snoc hrun hlast hreach⟩
  rw [List.map_append, ← hreads]
  simp only [List.map_cons, List.map_nil]
  rw [gasRecord_eq_gasReadOf current hdec hsz hgas hstep]

theorem gasLogAligned_step_norecord {gasAcc : List Word} {frs : List Frame}
    (halign : GasLogAligned gasAcc frs) :
    GasLogAligned gasAcc frs := halign

/-- Select the gas observation paired with a witness frame. -/
theorem aligned_read_eq_obs {gasAcc : List Word} {frs : List Frame} {i : Nat} {fr : Frame}
    (halign : GasLogAligned gasAcc frs)
    (hwit : frs[i]? = some (gasFrame fr)) :
    gasAcc[i]? = some (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) := by
  obtain ⟨hreads, _⟩ := halign
  rw [hreads, List.getElem?_map, hwit]
  simp only [Option.map_some]
  rw [gasReadOf_gasFrame_eq_obs]

end BytecodeLayer.Exec.Invariants
