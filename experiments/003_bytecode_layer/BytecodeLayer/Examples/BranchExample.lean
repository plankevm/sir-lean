import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.UInt64

/-!
# Worked example: a program with one conditional branch (`BranchExample`)

The acceptance check for the CFG / conditional-control-flow combinator. We lower a
tiny program whose single instruction of interest is a `JUMPI` through the new
control-flow `Runs` rules and compose **both arms** into one `Runs` value with the
branching helper `runs_branch` — exactly the way Track C's branch lowering will,
case-splitting on the runtime value of the condition.

```text
pc 0 : JUMPI        (57)      if cond ≠ 0 jump to pc 3, else fall through to pc 1
pc 1 : STOP         (00)      fall-through arm halts here
pc 2 : STOP         (00)      (padding so pc 3 is reachable)
pc 3 : JUMPDEST     (5b)      taken arm lands here …
pc 4 : STOP         (00)      … and halts here
```

The initial frame is the `JUMPI` frame with an **arbitrary** condition `cond` and
the destination `3` already on the stack (`[3, cond]`) — the branch point itself,
which is precisely what the combinator reasons about. For any `cond` and enough
gas, `branchRuns` produces one `Runs` from the JUMPI frame to a halting `STOP`
frame:

* taken arm (`cond ≠ 0`): `runs_jumpi_taken`/`runs_branch` jumps to the
  `JUMPDEST` at pc 3, then `runs_jumpdest` steps over it to the `STOP` at pc 4;
* fall-through arm (`cond = 0`): `runs_branch` advances to the `STOP` at pc 1.

The frame is built directly with an explicit `validJumps := #[3]`, so
`get_dest 3 = some 3` reduces in the kernel (`codeFrame` would route through the
`partial def validJumpDests`, which is opaque). No execution trace is named, and
the example is axiom-clean (no `native_decide`).
-/

namespace BytecodeLayer.Examples
open Evm
open GasConstants
open BytecodeLayer.Dispatch
open BytecodeLayer.Hoare
open BytecodeLayer.UInt64

/-- The branch program: `JUMPI ; STOP ; STOP ; JUMPDEST ; STOP`. -/
def branchProgram : ByteArray := ⟨#[0x57, 0x00, 0x00, 0x5b, 0x00]⟩

/-- The `JUMPI` frame: pc 0, stack `[3, cond]` (destination on top, condition
below), `g` gas, explicit `validJumps := #[3]` (pc 3 is the only `JUMPDEST`). -/
def jumpiFrame (cond : UInt256) (g : UInt64) : Frame :=
  { kind := .call ⟨∅, ∅, default⟩
    validJumps := #[3]
    exec :=
      { (default : ExecutionState) with
          executionEnv := { (default : ExecutionEnv) with code := branchProgram }
          stack := (3 : UInt256) :: cond :: []
          gasAvailable := g } }

theorem decode_branch_0 : decode branchProgram 0 = some (.Smsf .JUMPI, .none) := by rfl
theorem decode_branch_1 : decode branchProgram 1 = some (.System .STOP, .none) := by rfl
theorem decode_branch_3 : decode branchProgram 3 = some (.Smsf .JUMPDEST, .none) := by rfl

/-- The destination operand `3` resolves to the valid jump target pc 3. -/
theorem jumpiFrame_get_dest (cond : UInt256) (g : UInt64) :
    (jumpiFrame cond g).get_dest 3 = some 3 := by rfl

/-- **The branch program composes into one `Runs`.** For any condition `cond` and
enough gas, there is a `Runs` from the `JUMPI` frame to *some* frame that decodes
to `STOP` (the per-arm halt site) — built by `runs_branch` (case-split on `cond`),
the taken arm threading one `runs_jumpdest` past its landing pad. -/
theorem branchRuns (cond : UInt256) (g : UInt64) (hg : 11 ≤ g.toNat) :
    ∃ fr', Runs (jumpiFrame cond g) fr'
      ∧ decode fr'.exec.executionEnv.code fr'.exec.pc = some (.System .STOP, .none) := by
  have hg0 : (jumpiFrame cond g).exec.gasAvailable.toNat = g.toNat := rfl
  have hsz : (jumpiFrame cond g).exec.stack.size ≤ 1024 := by show (2:ℕ) ≤ 1024; omega
  have hghi : GasConstants.Ghigh ≤ (jumpiFrame cond g).exec.gasAvailable.toNat := by
    rw [hg0, show GasConstants.Ghigh = 10 from rfl]; omega
  have hstk : (jumpiFrame cond g).exec.stack = (3 : UInt256) :: cond :: [] := rfl
  by_cases hc : cond = 0
  · -- fall-through arm: advance to pc 1, STOP
    refine ⟨jumpiFallthroughFrame (jumpiFrame cond g) [], ?_, by rfl⟩
    exact runs_branch (dest := 3) (cond := cond) (rest := []) decode_branch_0 hstk hsz hghi
      (Or.inr ⟨hc, Runs.refl _⟩)
  · -- taken arm: jump to pc 3 (JUMPDEST), step over it, STOP at pc 4
    have hgJ : (jumpFrame (jumpiFrame cond g) GasConstants.Ghigh 3 []).exec.gasAvailable.toNat
        = g.toNat - 10 := by
      show ((jumpiFrame cond g).exec.gasAvailable - UInt64.ofNat GasConstants.Ghigh).toNat = _
      rw [show GasConstants.Ghigh = 10 from rfl,
          toNat_sub_ofNat _ 10 (by rw [hg0]; omega) (by omega), hg0]
    refine ⟨jumpdestFrame (jumpFrame (jumpiFrame cond g) GasConstants.Ghigh 3 []), ?_, by rfl⟩
    exact runs_branch (dest := 3) (cond := cond) (rest := []) decode_branch_0 hstk hsz hghi
      (Or.inl ⟨3, hc, jumpiFrame_get_dest cond g,
        runs_jumpdest (jumpFrame (jumpiFrame cond g) GasConstants.Ghigh 3 [])
          decode_branch_3 (by show (0:ℕ) ≤ 1024; omega)
          (by show GasConstants.Gjumpdest ≤ _;
              rw [hgJ, show GasConstants.Gjumpdest = 1 from rfl]; omega)⟩)

end BytecodeLayer.Examples
