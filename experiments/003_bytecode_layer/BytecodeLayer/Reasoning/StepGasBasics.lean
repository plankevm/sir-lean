import Evm

/-!
# Gas-charging foundations for the per-step gas-decrease theorem

Low-level `UInt64`/`charge` facts underpinning `Reasoning/StepGas.lean`:
`charge cost` strictly decreases `gasAvailable.toNat` when `cost ≥ 1` (and never
increases it), and the pc/stack rewrap `replaceStackAndIncrPC` preserves gas.
-/

namespace BytecodeLayer
open Evm
open GasConstants

-- charge with cost ≥ 1 strictly decreases gasAvailable.toNat
theorem charge_lt {cost : ℕ} {exec exec' : ExecutionState}
    (hc : 1 ≤ cost) (h : charge cost exec = .ok exec') :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · rename_i hge
    have hge' : cost ≤ exec.gasAvailable.toNat := Nat.not_lt.mp hge
    injection h with h
    subst h
    have hlt : cost < 2 ^ 64 := Nat.lt_of_le_of_lt hge' exec.gasAvailable.toNat_lt
    have hofNat : (UInt64.ofNat cost).toNat = cost := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    have hble : (UInt64.ofNat cost) ≤ exec.gasAvailable := by
      rw [UInt64.le_iff_toNat_le, hofNat]; exact hge'
    dsimp only
    rw [UInt64.toNat_sub_of_le _ _ hble, hofNat]
    omega

-- charge never increases gas (cost ≥ 0)
theorem charge_le {cost : ℕ} {exec exec' : ExecutionState}
    (h : charge cost exec = .ok exec') :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · rename_i hge
    have hge' : cost ≤ exec.gasAvailable.toNat := Nat.not_lt.mp hge
    injection h with h
    subst h
    have hlt : cost < 2 ^ 64 := Nat.lt_of_le_of_lt hge' exec.gasAvailable.toNat_lt
    have hofNat : (UInt64.ofNat cost).toNat = cost := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    have hble : (UInt64.ofNat cost) ≤ exec.gasAvailable := by
      rw [UInt64.le_iff_toNat_le, hofNat]; exact hge'
    dsimp only
    rw [UInt64.toNat_sub_of_le _ _ hble, hofNat]
    omega

-- replaceStackAndIncrPC / incrPC preserve gas
theorem gas_replaceStackAndIncrPC (exec : ExecutionState) (s : Stack UInt256) (d : UInt8) :
    (exec.replaceStackAndIncrPC s d).gasAvailable = exec.gasAvailable := rfl

theorem gasNat_replaceStackAndIncrPC (exec : ExecutionState) (s : Stack UInt256) (d : UInt8) :
    (exec.replaceStackAndIncrPC s d).gasAvailable.toNat = exec.gasAvailable.toNat :=
  congrArg UInt64.toNat (gas_replaceStackAndIncrPC exec s d)

-- A `charge cost exec = .ok exec'` step bridged through replaceStackAndIncrPC.
theorem binOp_lt {f exec cost exec'}
    (hc : 1 ≤ cost) (h : binOp f exec cost = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  unfold binOp at h
  cases hch : charge cost exec with
  | error e => rw [hch] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hch] at h
    simp only [bind, Except.bind] at h
    cases hp : ec.stack.pop2 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, a, b⟩ := v
      rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option, continueWith,
        Except.ok.injEq, Signal.next.injEq] at h
      rw [← h]
      have : ec.gasAvailable.toNat < exec.gasAvailable.toNat := charge_lt hc hch
      simpa [gas_replaceStackAndIncrPC] using this

end BytecodeLayer
