import EvmYul.EVM.Semantics
import Mathlib.Tactic.FinCases

/-!
# Nested never-`OutOfFuel` (Milestone B2) — WIP, always-green

Goal (mirrors exp003's flat `messageCall_never_outOfFuel`, but over the genuinely
mutual fuel-passing recursion `EvmYul.EVM.{X, Ξ, Θ, call, step}`):

> If `fuel` is instantiated at a gas-derived bound (`seedFuel`), top-level message
> execution (`Θ`) never returns `.error .OutOfFuel`.

## Status / spine

The proof is a measure argument over the mutual recursion. The measure is *gas*:
out-of-gas is itself a halt, so the gas held by a frame bounds the number of `X`
loop iterations it can run, and the gas forwarded to a child is carved out of the
parent's gas (`Ccallgas ≤ parent gas`), with call depth additionally capped at
`1024`. Hence a fuel budget that is a fixed multiple of the available gas (plus a
depth term) always suffices.

This file is grown bottom-up; every theorem below is *fully proved* (no `sorry`,
no axiom). What is established so far:

* **Fuel-`0` base cases** for all five layers — the only places `OutOfFuel` is
  emitted directly (everything else propagates it). These pin where the bound bites.
* **Per-step gas positivity** (`C'_pos_of_runnable`): every opcode that lets the
  `X` loop *continue* burns `≥ 1` gas. The only `C' = 0` opcodes are
  `Wzero = [STOP, RETURN, REVERT]` (all halt the loop via `H`) and `INVALID`
  (whose `step` immediately errors — never `OutOfFuel`). This is the cornerstone
  that makes gas a genuine decreasing measure.

What remains (see PLAN.md for the precise obligations) is the measure assembly:
the gas-decrement lemma threading `C'` through `Z`/`step`, the child-gas/depth
conservation across `call`/`Θ`/`Ξ`, and the final mutual induction. Those are
documented, not faked.
-/

namespace EvmYul.EVM.NeverOutOfFuel

open EvmYul EvmYul.EVM
open GasConstants InstructionGasGroups

/-! ## Fuel-`0` base cases

Each of the five mutually-recursive layers pattern-matches `fuel` first and emits
`.error .OutOfFuel` exactly on `0`. These are the *only* syntactic occurrences of
`OutOfFuel` produced directly by a layer; every other `OutOfFuel` is propagated
from a recursive call. So the fuel bound only has to guarantee none of these `0`
cases is reached. -/

@[simp] theorem X_zero (validJumps : Array UInt256) (s : State) :
    X 0 validJumps s = .error .OutOfFuel := rfl

@[simp] theorem step_zero (gasCost : ℕ) (instr : Option (Operation × Option (UInt256 × Nat)))
    (s : State) :
    step 0 gasCost instr s = .error .OutOfFuel := rfl

@[simp] theorem call_zero (gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (s : State) :
    call 0 gasCost bvh gas source recipient t value value' inOffset inSize outOffset outSize
      permission s = .error .OutOfFuel := rfl

@[simp] theorem Ξ_zero
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ 0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfFuel := rfl

@[simp] theorem Θ_zero (bvh : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (H : BlockHeader) (w : Bool) :
    Θ 0 bvh createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c g p v v' d e H w
      = .error .OutOfFuel := rfl

/-! ## Positivity of the special cost helpers

The non-constant arms of `C'` (`SSTORE`, `SLOAD`, the `CALL` family, account
access, …) route through these helpers. Each is `≥ 1` because it is dominated by a
positive gas constant (`Gwarmaccess = 100`, `Gselfdestruct = 5000`, …). These feed
the `C'` master positivity lemma below. -/

theorem Caccess_pos (a : AccountAddress) (A : Substate) : 1 ≤ Caccess a A := by
  unfold Caccess; split <;> decide

theorem Csstore_pos (s : State) : 1 ≤ Csstore s := by
  -- `loadComponent + storeComponent`, with `storeComponent ∈ {100, 20000, 2900}`.
  unfold Csstore
  dsimp only [Gwarmaccess, Gsset, Gsreset, Gcoldsload]
  repeat' split
  all_goals omega

theorem Csload_pos (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv) :
    1 ≤ Csload μₛ A I := by
  unfold Csload; split <;> decide

theorem Cselfdestruct_pos (s : State) : 1 ≤ Cselfdestruct s := by
  unfold Cselfdestruct
  simp only [Gselfdestruct]
  split <;> split <;> omega

theorem Ccall_pos (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) : 1 ≤ Ccall t r val g σ μ A := by
  -- `Ccall = Cgascap + Cextra` and `Cextra = Caccess + Cxfer + Cnew ≥ Caccess ≥ 1`.
  unfold Ccall Cextra
  have := Caccess_pos t A
  omega

/-! ## Per-step gas positivity — the cornerstone

`C' s w ≥ 1` for every opcode `w` that keeps the `X` loop running. The runnable
opcodes are exactly those outside `Wzero ∪ {INVALID}`:

* `Wzero = [STOP, RETURN, REVERT]` and `SELFDESTRUCT` *halt* the loop (`H` returns
  `some`), so they never need fuel for a successor iteration;
* `INVALID`'s `step` returns `.error .InvalidInstruction`, halting with an error
  that is *not* `OutOfFuel`.

We prove positivity for *every* runnable opcode in one `cases`-sweep
(`C'_pos_of_runnable`): the constant-cost groups collapse under the membership
`decide`, and the special arms (`SSTORE`/`SLOAD`/account-access/the `CALL` family)
are discharged by the helper lemmas above. -/

/-! ## The runnable set and the master positivity lemma

`runnable w` holds for every opcode that, on success, makes `X` recurse — i.e. all
opcodes outside the halting set `{STOP, RETURN, REVERT, SELFDESTRUCT}` and the
self-erroring `INVALID`. (`H` returns `some` exactly on the first four; `INVALID`'s
`step` errors with `.InvalidInstruction`.) For these, `C' s w ≥ 1`. -/

def runnable (w : Operation) : Prop :=
  w ≠ .STOP ∧ w ≠ .RETURN ∧ w ≠ .REVERT ∧ w ≠ .SELFDESTRUCT ∧ w ≠ .INVALID

/-- Closer for one `C'` arm: unfold `C'`, decide the (state-free) membership guards
and the named gas constants, expand any surviving `if`s, then discharge by `omega`
(which uses the `C*`-atom lower-bound hypotheses in context). -/
local macro "c'_close" : tactic =>
  `(tactic|
    (simp (config := { decide := true }) only
      [C', Wcopy, Wextaccount, Wzero, Wbase, Wverylow, Wlow, Wmid, Whigh,
       Gbase, Gverylow, Glow, Gmid, Ghigh, Gexp, Gexpbyte, Gcopy, Gjumpdest,
       Gkeccak256, Gkeccak256word, Gcreate, Gblockhash, HASH_OPCODE_GAS,
       Ctstore, Ctload, Gwarmaccess, Glog, Glogtopic,
       if_true, if_false, reduceIte] <;> (repeat' split) <;> omega))

set_option maxHeartbeats 8000000 in
set_option linter.unnecessarySeqFocus false in
/-- **Per-step gas positivity (cornerstone).** Every runnable opcode burns `≥ 1`
gas. Combined with the `Z`/`step` gas-decrement (remaining work), this makes gas a
strictly decreasing measure on the `X` loop. -/
theorem C'_pos_of_runnable (s : State) (w : Operation) (hw : runnable w) : 1 ≤ C' s w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  -- The non-constant arms route through the helper positivity lemmas; everything
  -- else is a positive constant evaluated by `decide` after the membership guards
  -- (which only mention `w`, never `s`) reduce.
  -- Lower bounds for every non-constant `C'` atom, given to `omega` as hypotheses.
  -- omega treats each `C*`/`Caccess` call as an opaque atom and uses these `≥ 1`
  -- facts to close `1 ≤ atom + …` after the arithmetic/`if` structure is exposed.
  have hsstore := Csstore_pos s
  have hself := Cselfdestruct_pos s
  have hsload := Csload_pos s.stack s.substate s.executionEnv
  have hacc0 := Caccess_pos (AccountAddress.ofUInt256 s.stack[0]!) s.substate
  have hcall : ∀ t r val g, 1 ≤ Ccall t r val g s.accountMap s.toMachineState s.substate :=
    fun t r val g => Ccall_pos t r val g _ _ _
  -- The uniform closer: unfold `C'`, decide the (state-free) membership guards,
  -- expand the surviving `if`s, then discharge by `omega` with the atom bounds.
  cases w with
  | StopArith o => cases o <;> first | exact absurd rfl h1 | c'_close
  | CompBit o => cases o <;> c'_close
  | Keccak o => cases o <;> c'_close
  | Env o => cases o <;>
      first
      | c'_close
      | -- EXTCODECOPY: `Caccess (…) A + Gcopy * …`; defeq folds the `A` projection.
        (simp only [C']; exact le_trans hacc0 (Nat.le_add_right _ _))
  | Block o => cases o <;> c'_close
  | StackMemFlow o => cases o <;> first | exact hsstore | exact hsload | c'_close
  | Push o => cases o <;> c'_close
  | Dup o => cases o <;> c'_close
  | Exchange o => cases o <;> c'_close
  | Log o => cases o <;> c'_close
  | System o => cases o <;>
      first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact absurd rfl h3
      | exact absurd rfl h4
      | exact absurd rfl h5
      | c'_close
      | (simp only [C']; exact hcall _ _ _ _)

/-! ## Fuel bound and the headline target

### The bound

Each `X` loop iteration burns `≥ 1` gas (cornerstone above, threaded through
`Z`/`step`); the gas forwarded to a child is carved out of the parent
(`Ccallgas ≤ parent gas`); and the call depth is capped at `1024`. So the *total*
number of `{X, Ξ, Θ, call, step}` fuel decrements across the whole call tree is
bounded by a fixed multiple of the available gas. We take the conservative bound

  `seedFuel g = 4 * (g + 1)`

(one decrement for the `X` step, plus the `call`/`Θ`/`Ξ` hops per descent; the `+1`
covers a frame that halts immediately on its first instruction). Any larger
multiple works; the constant `4` is the per-instruction worst-case hop count.

### The headline (target of the measure assembly — not yet closed)

The goal, mirroring exp003's `messageCall_never_outOfFuel`, is:

```
theorem Θ_never_outOfFuel
    (bvh) (cA) (gh) (blocks) (σ σ₀) (A) (s o r) (c) (g p v v' : UInt256)
    (d) (e) (H) (w)
    (hfuel : seedFuel g.toNat ≤ fuel) :
    Θ fuel bvh cA gh blocks σ σ₀ A s o r c g p v v' d e H w ≠ .error .OutOfFuel
```

This is the unconditional never-`OutOfFuel`. It is *documented*, not asserted: the
remaining obligations (see PLAN.md) are the measure-decrement chain
`C'_pos_of_runnable → Z → step → X` and the cross-layer gas/depth conservation for
`call`/`Θ`/`Ξ`, then a mutual induction on `fuel`. -/

/-- The gas-derived fuel bound (analogue of exp003's flat `seedFuel gas`). -/
def seedFuel (g : ℕ) : ℕ := 4 * (g + 1)

end EvmYul.EVM.NeverOutOfFuel
