import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.UInt64

/-!
# Worked example: arithmetic + storage-read + introspection (`ArithStorageExample`)

The acceptance check for the new opcode `Runs` rules `runs_add` / `runs_lt` /
`runs_gas` / `runs_sload`. We lower a tiny straight-line program through all four
and compose them into one `Runs` value with `Runs.trans` — exactly the way Track
C's expression lowering threads them.

```text
pc 0 : ADD     (01)   pop a,b ; push a+b
pc 1 : LT      (10)   pop (a+b),k ; push lt(a+b,k)
pc 2 : GAS     (5a)   push ofUInt64 gasAvailable (post-charge)
pc 3 : SLOAD   (54)   pop that gas word as key ; push self storage @ key
```

The initial frame has `[a, b, k]` on the stack and `g` gas (with no accessed
storage keys, so SLOAD is *cold* → `Gcoldsload = 2100`). For enough gas,
`arithStorageRuns` produces one `Runs` from the ADD frame to the post-SLOAD frame,
threading each rule's post-frame into the next via `Runs.trans`. No execution
trace is named, and the example is axiom-clean (no `native_decide`).
-/

namespace BytecodeLayer.Examples
open Evm
open GasConstants
open BytecodeLayer.Dispatch
open BytecodeLayer.Hoare
open BytecodeLayer.UInt64

/-- The program: `ADD ; LT ; GAS ; SLOAD`. -/
def arithStorageProgram : ByteArray := ⟨#[0x01, 0x10, 0x5a, 0x54]⟩

/-- The starting frame: pc 0, stack `[a, b, k]`, `g` gas, empty accessed-keys set
(so SLOAD is cold). -/
def arithFrame (a b k : UInt256) (g : UInt64) : Frame :=
  { kind := .call ⟨∅, ∅, default⟩
    validJumps := #[]
    exec :=
      { (default : ExecutionState) with
          executionEnv := { (default : ExecutionEnv) with code := arithStorageProgram }
          stack := a :: b :: k :: []
          gasAvailable := g } }

/-- **The four rules compose into one `Runs`.** From the ADD frame, with enough gas,
`runs_add` → `runs_lt` → `runs_gas` → `runs_sload` thread their post-frames through
`Runs.trans` into a single `Runs` reaching the post-SLOAD frame. -/
theorem arithStorageRuns (a b k : UInt256) (g : UInt64) (hg : 2200 ≤ g.toNat) :
    ∃ fr', Runs (arithFrame a b k g) fr' := by
  set fr0 := arithFrame a b k g with hfr0
  -- pc 0 : ADD
  have hg0 : fr0.exec.gasAvailable.toNat = g.toNat := rfl
  have hstk0 : fr0.exec.stack = a :: b :: (k :: []) := rfl
  have hsz0 : fr0.exec.stack.size ≤ 1024 := by show (3 : ℕ) ≤ 1024; omega
  have hadd : Runs fr0 (addFrame fr0 a b (k :: [])) :=
    runs_add fr0 a b (k :: []) rfl hstk0 hsz0 (by rw [hg0, show Gverylow = 3 from rfl]; omega)
  -- pc 1 : LT
  set fr1 := addFrame fr0 a b (k :: []) with hfr1
  have hg1 : fr1.exec.gasAvailable.toNat = g.toNat - 3 := by
    show ((fr0.exec.gasAvailable - UInt64.ofNat Gverylow).toNat) = _
    rw [show Gverylow = 3 from rfl, toNat_sub_ofNat _ 3 (by rw [hg0]; omega) (by omega), hg0]
  have hstk1 : fr1.exec.stack = (a + b) :: k :: [] := rfl
  have hsz1 : fr1.exec.stack.size ≤ 1024 := by show (2 : ℕ) ≤ 1024; omega
  have hlt : Runs fr1 (ltFrame fr1 (a + b) k []) :=
    runs_lt fr1 (a + b) k [] rfl hstk1 hsz1 (by rw [hg1, show Gverylow = 3 from rfl]; omega)
  -- pc 2 : GAS
  set fr2 := ltFrame fr1 (a + b) k [] with hfr2
  have hg2 : fr2.exec.gasAvailable.toNat = g.toNat - 6 := by
    show ((fr1.exec.gasAvailable - UInt64.ofNat Gverylow).toNat) = _
    rw [show Gverylow = 3 from rfl, toNat_sub_ofNat _ 3 (by rw [hg1]; omega) (by omega), hg1]
    omega
  have hsz2 : fr2.exec.stack.size + 1 ≤ 1024 := by show (1 : ℕ) + 1 ≤ 1024; omega
  have hgas : Runs fr2 (gasFrame fr2) :=
    runs_gas fr2 rfl hsz2 (by rw [hg2, show Gbase = 2 from rfl]; omega)
  -- pc 3 : SLOAD (cold: accessedStorageKeys is empty)
  set fr3 := gasFrame fr2 with hfr3
  have hg3 : fr3.exec.gasAvailable.toNat = g.toNat - 8 := by
    show ((fr2.exec.gasAvailable - UInt64.ofNat Gbase).toNat) = _
    rw [show Gbase = 2 from rfl, toNat_sub_ofNat _ 2 (by rw [hg2]; omega) (by omega), hg2]
    omega
  have hstk3 : fr3.exec.stack
      = (UInt256.ofUInt64 fr3.exec.gasAvailable) :: ((UInt256.lt (a + b) k) :: []) := rfl
  have hsz3 : fr3.exec.stack.size ≤ 1024 := by show (2 : ℕ) ≤ 1024; omega
  have hcold : fr3.exec.substate.accessedStorageKeys.contains
      (fr3.exec.executionEnv.address, UInt256.ofUInt64 fr3.exec.gasAvailable) = false := rfl
  have hsload : Runs fr3
      (sloadFrame fr3 (UInt256.ofUInt64 fr3.exec.gasAvailable) (UInt256.lt (a + b) k :: [])) :=
    runs_sload fr3 (UInt256.ofUInt64 fr3.exec.gasAvailable) (UInt256.lt (a + b) k :: [])
      rfl hstk3 hsz3 (by
      rw [hcold, show sloadCost false = Gcoldsload from rfl, show Gcoldsload = 2100 from rfl,
          hg3]; omega)
  exact ⟨_, hadd.trans (hlt.trans (hgas.trans hsload))⟩

end BytecodeLayer.Examples
