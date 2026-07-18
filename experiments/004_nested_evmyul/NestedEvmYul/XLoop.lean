import NestedEvmYul.NeverOutOfFuel
import NestedEvmYul.Refinement

/-!
# T1 — X-loop program logic: nested per-opcode rules, branch combinator,
# and the sequencing/decomposition theorem

This file colonizes the "logic-free zone" diagnosed by the B3 shape study
(ObservableTriple.lean §Findings (c)): nested-native analogs of the flat
`runs_*` per-opcode rules, built directly over the vendored
`EvmYul.EVM.{X, Z, step}` / `EvmYul.step` semantics. **Everything here is
sorry-free** (house proof-first rule); nothing below imports or extends the
study's stated-only `IterStep`/`Iters` seed vocabulary (see the
reconciliation note at the bottom).

## The load-bearing technique (dispatcher equations)

`EVM.step`'s fuel parameter appears only in the succ-pattern and the recursive
CALL/CREATE-family arms; every other arm routes to the fuel-free shared
`EvmYul.step` via the default arm at EVMYulLean/EvmYul/EVM/Semantics.lean:424,
*after* the unconditional `execLength + 1` bump at :234. So for each concrete
non-call/create opcode the equation

  `EVM.step (f+1) cost (some (op, arg)) s = EvmYul.step op arg (debit s cost)`

closes by `rfl`: unification reduces the 140-arm dispatch match through the one
concrete-constructor arm without re-elaborating it (the `gas_EvmYul_step`
technique — never `simp only [EvmYul.step]`/`unfold` the whole match). The RHS
never mentions `f`, so every per-opcode rule below is **∀-fuel for free** — no
fuel-irrelevance keystone anywhere in this file.

The shared-arm forward lemmas reduce `EvmYul.step <op>` on a stack of the
op's required shape by `obtain`-destructuring the state, `subst`-ing the stack
hypothesis, and closing by `rfl` (concrete cons-cells let `pop`/`pop2`/`pop7`
iota-reduce).

## Layer map

1. `debit`/`bump` + `step_eq_shared_*` — dispatcher equations (`rfl` each),
   incl. `step_call_eq` (the CALL-arm equation, consumed by T4's endgame).
2. `shared_step_*` — shared-arm forward lemmas (`.ok` successor shapes).
3. `X_iter`/`X_iter_halt` — one `X`-loop iteration, consumer-style `Z`.
4. `X_push1`/`X_push0`/`X_sstore`/`X_jump`/`X_jumpi_*` — the flat `runs_*`
   analogs: `∀ f, X (f+2) vj s = X (f+1) vj s'` with `s'` explicit.
5. `X_branch` — the branch combinator (flat `runs_branch` analog).
6. `IterStepU`/`IterHaltU`/`ItersN` + `ItersN_X`/`X_decompose` — the
   sequencing/decomposition theorem (flat `Runs.trans`/`drive_reconcile`
   analog), with **∀-fuel step clauses** (dischargeable by the per-opcode
   intro rules `IterStepU.*`/`IterHaltU.*`), killing the study's `∃ f`
   fuel-transport trap. Fuel arithmetic is pure `Nat`-offset bookkeeping.
7. `Z_ok_toState`/`X_call_iter`/`stopHaltState`/`X_stop_halt` — the T4
   endgame ingredients: the (necessarily cofinal) `CALL` iteration and the
   explicit-successor halting iteration. Plus `step_fuel_irrelevant` in §1:
   the keystone post-mortem's salvaged true fragment (every non-CALL/CREATE
   arm is fuel-irrelevant).

Decode hypotheses are phrased through `.getD (.STOP, .none)` — exactly `X`'s
own read (undecodable bytes ARE `STOP`; the study's `decode = some` phrasing
was a recorded fidelity gap).
-/

namespace NestedEvmYul.XLoop

open EvmYul EvmYul.EVM

/-- `UInt256`'s derived `BEq` compares the wrapped `Fin`s, whose `BEq` is
lawful; lift that to a `LawfulBEq UInt256` instance (needed to route `JUMPI`'s
`μ₁ != ⟨0⟩` guard through `bne_iff_ne`/`beq_eq_false_iff_ne`). -/
instance : LawfulBEq UInt256 where
  eq_of_beq {a b} h := by
    obtain ⟨av⟩ := a; obtain ⟨bv⟩ := b
    exact congrArg UInt256.mk (eq_of_beq (show (av == bv) = true from h))
  rfl {a} := by
    obtain ⟨av⟩ := a
    exact (show (av == av) = true from beq_self_eq_true av)

/-! ## 1. Dispatcher equation lemmas -/

/-- The state `EVM.step`'s default (non-CALL/CREATE-family) arm hands to the
shared interpreter `EvmYul.step`: the unconditional `execLength + 1` bump
(EVMYulLean/EvmYul/EVM/Semantics.lean:234) followed by the `gasCost` debit
(the default arm at :424). -/
def debit (s : EVM.State) (cost : ℕ) : EVM.State :=
  { s with execLength := s.execLength + 1,
           gasAvailable := s.gasAvailable - UInt256.ofNat cost }

/-- The state `EVM.step`'s CALL-family arms hand to `call`: only the
`execLength + 1` bump — the CALL arms do **not** pre-debit `gasCost`
(it is passed down into `call` instead). -/
def bump (s : EVM.State) : EVM.State := { s with execLength := s.execLength + 1 }

theorem step_eq_shared_push1 (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.PUSH1, arg)) s = EvmYul.step .PUSH1 arg (debit s cost) := rfl

theorem step_eq_shared_push0 (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.PUSH0, arg)) s = EvmYul.step .PUSH0 arg (debit s cost) := rfl

theorem step_eq_shared_sstore (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.SSTORE, arg)) s = EvmYul.step .SSTORE arg (debit s cost) := rfl

theorem step_eq_shared_jump (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.JUMP, arg)) s = EvmYul.step .JUMP arg (debit s cost) := rfl

theorem step_eq_shared_jumpi (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.JUMPI, arg)) s = EvmYul.step .JUMPI arg (debit s cost) := rfl

theorem step_eq_shared_stop (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f+1) cost (some (.STOP, arg)) s = EvmYul.step .STOP arg (debit s cost) := rfl

/-- **The CALL-arm dispatcher equation** (consumed by T4's endgame, not here):
on a 7-deep stack, `EVM.step (f+1)` on `CALL` is `call f gasCost …` on the
**bumped** state (`execLength + 1`, *no* gas pre-debit), followed by
`replaceStackAndIncrPC (rest.push x)` on the call's output state. This is the
tie the study proved impossible to state consistently at the raw-`call` level
(the `execLength` bump refutation): the successor is the *post-processed*
call output, never the raw one. -/
theorem step_call_eq (f cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (g t v io isz oo osz : UInt256) (rest : Stack UInt256)
    (hstk : s.stack = g :: t :: v :: io :: isz :: oo :: osz :: rest) :
    EVM.step (f+1) cost (some (.CALL, arg)) s
      = (call f cost s.executionEnv.blobVersionedHashes g (.ofNat s.executionEnv.codeOwner)
          t t v v io isz oo osz s.executionEnv.perm (bump s)).bind
          (fun p => .ok (p.2.replaceStackAndIncrPC (rest.push p.1))) := by
  obtain ⟨sh, pc, stk, el⟩ := s
  dsimp only at hstk
  subst hstk
  rfl

set_option maxHeartbeats 8000000 in
/-- **The general fuel-irrelevance sweep** (the keystone post-mortem's TRUE
fragment, salvaged): for every opcode outside the recursive CALL/CREATE
families, `EVM.step` at positive fuel is the same function at EVERY positive
fuel — each of the ~130 non-recursive dispatcher arms routes to the fuel-free
shared `EvmYul.step`, so each leaf closes by `rfl` (the dispatcher-equation
technique, sweeping the two-level `Operation` sum). The six excluded arms are
excluded *correctly*: CALL-family arms recurse into `call` (honest fuel
consumption), and CREATE/CREATE2 absorb an inner `Lambda` `OutOfFuel`
(the leak that makes the full result-stability keystone FALSE — see
ThetaRuns.lean's keystone post-mortem).

Heartbeats cranked per-theorem (8M, ~2min): the ~140-leaf `rfl` sweep
whnf-instantiates the full dispatcher body once per leaf, as for the
`gas_EvmYul_step` sweep. -/
theorem step_fuel_irrelevant (op : Operation)
    (hcall : op.isCall = false) (hcreate : op.isCreate = false)
    (f f' cost : ℕ) (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EVM.step (f + 1) cost (some (op, arg)) s
      = EVM.step (f' + 1) cost (some (op, arg)) s := by
  cases op <;> rename_i o <;> cases o <;>
    first
      | rfl
      | exact Bool.noConfusion hcall
      | exact Bool.noConfusion hcreate

/-! ## 2. Shared-arm forward lemmas -/

theorem shared_step_push1 (v : UInt256) (n : ℕ) (s : EVM.State) :
    EvmYul.step .PUSH1 (some (v, n)) s
      = .ok (s.replaceStackAndIncrPC (s.stack.push v) (pcΔ := n+1)) := rfl

theorem shared_step_push0 (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EvmYul.step .PUSH0 arg s
      = .ok (s.replaceStackAndIncrPC (s.stack.push ⟨0⟩)) := rfl

theorem shared_step_stop (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EvmYul.step .STOP arg s
      = .ok { s with toMachineState := s.toMachineState.setReturnData .empty } := rfl

/-- `SSTORE` through `dispatchBinaryStateOp`/`State.sstore`: pops `key :: val`,
stores, `replaceStackAndIncrPC` on the rest. -/
theorem shared_step_sstore (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (key val : UInt256) (rest : Stack UInt256) (hstk : s.stack = key :: val :: rest) :
    EvmYul.step .SSTORE arg s
      = .ok ({ s with toState := s.toState.sstore key val }.replaceStackAndIncrPC rest) := by
  obtain ⟨sh, pc, stk, el⟩ := s
  dsimp only at hstk
  subst hstk
  rfl

theorem shared_step_jump (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (dest : UInt256) (rest : Stack UInt256) (hstk : s.stack = dest :: rest) :
    EvmYul.step .JUMP arg s = .ok { s with pc := dest, stack := rest } := by
  obtain ⟨sh, pc, stk, el⟩ := s
  dsimp only at hstk
  subst hstk
  rfl

/-- `JUMPI`, both arms at once: the new `pc` is the branch `if` itself.
(The two directed corollaries below reduce the `if`.) -/
theorem shared_step_jumpi (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (dest cond : UInt256) (rest : Stack UInt256)
    (hstk : s.stack = dest :: cond :: rest) :
    EvmYul.step .JUMPI arg s
      = .ok { s with pc := if cond != ⟨0⟩ then dest else s.pc + ⟨1⟩, stack := rest } := by
  obtain ⟨sh, pc, stk, el⟩ := s
  dsimp only at hstk
  subst hstk
  rfl

theorem shared_step_jumpi_taken (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (dest cond : UInt256) (rest : Stack UInt256)
    (hstk : s.stack = dest :: cond :: rest) (hcond : cond ≠ ⟨0⟩) :
    EvmYul.step .JUMPI arg s = .ok { s with pc := dest, stack := rest } := by
  rw [shared_step_jumpi arg s dest cond rest hstk]
  simp only [bne_iff_ne.mpr hcond, if_true]

theorem shared_step_jumpi_fallthrough (arg : Option (UInt256 × Nat)) (s : EVM.State)
    (dest : UInt256) (rest : Stack UInt256)
    (hstk : s.stack = dest :: (⟨0⟩ : UInt256) :: rest) :
    EvmYul.step .JUMPI arg s = .ok { s with pc := s.pc + ⟨1⟩, stack := rest } := by
  obtain ⟨sh, pc, stk, el⟩ := s
  dsimp only at hstk
  subst hstk
  rfl

/-! ## 3. X one-iteration lemmas

Consumer-style `Z` (hypothesis `Z vj op s = .ok (s₁, cost)`); the decode
hypothesis goes through `X`'s own `.getD (.STOP, .none)` read. -/

/-- One non-halting `X`-loop iteration: decode → gate → step → `H = none`,
so `X (f+1)` recurses as `X f` on the step successor. -/
theorem X_iter (f : ℕ) (vj : Array UInt256) (s s₁ s' : EVM.State)
    (op : Operation) (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg))
    (hZ : Z vj op s = .ok (s₁, cost))
    (hstep : EVM.step f cost (some (op, arg)) s₁ = .ok s')
    (hH : H s'.toMachineState op = none) :
    X (f+1) vj s = X f vj s' := by
  conv_lhs => unfold X
  simp only [bind, Except.bind]
  rw [hdec]
  simp only []
  rw [hZ]
  simp only []
  rw [hstep]
  simp only []
  rw [hH]

/-- The halting sibling: `H = some o` on a non-`REVERT` opcode packages
`.ok (.success s' o)`. -/
theorem X_iter_halt (f : ℕ) (vj : Array UInt256) (s s₁ s' : EVM.State)
    (op : Operation) (arg : Option (UInt256 × Nat)) (cost : ℕ) (o : ByteArray)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg))
    (hZ : Z vj op s = .ok (s₁, cost))
    (hstep : EVM.step f cost (some (op, arg)) s₁ = .ok s')
    (hH : H s'.toMachineState op = some o)
    (hrev : op ≠ .REVERT) :
    X (f+1) vj s = .ok (.success s' o) := by
  conv_lhs => unfold X
  simp only [bind, Except.bind]
  rw [hdec]
  simp only []
  rw [hZ]
  simp only []
  rw [hstep]
  simp only []
  rw [hH]
  simp only [beq_eq_false_iff_ne.mpr hrev, Bool.false_eq_true, if_false]

/-! ## 4. Per-opcode nested runs rules (the flat `runs_*` analogs)

Each rule is `∀ f, X (f+2) vj s = X (f+1) vj s'` with `s'` **explicit** — the
`f+2`/`f+1` offsets because `X (f+1)` runs `step f` and `step` needs positive
fuel. The `∀ f` is free: the dispatcher RHS never mentions `f` (per-opcode
fuel-irrelevance without any keystone). -/

/-- `PUSH1 v` (arg width `n`): push `v`, `pc += n+1`. -/
theorem X_push1 (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (v : UInt256) (n : ℕ) (cost : ℕ)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.PUSH1, some (v, n)))
    (hZ : Z vj .PUSH1 s = .ok (s₁, cost)) :
    X (f+2) vj s
      = X (f+1) vj
          ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push v) (pcΔ := n+1)) :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_push1 f cost _ s₁).trans (shared_step_push1 v n (debit s₁ cost))) rfl

/-- `PUSH0`: push `0`, `pc += 1`. -/
theorem X_push0 (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.PUSH0, arg))
    (hZ : Z vj .PUSH0 s = .ok (s₁, cost)) :
    X (f+2) vj s
      = X (f+1) vj
          ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push ⟨0⟩)) :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_push0 f cost arg s₁).trans (shared_step_push0 arg (debit s₁ cost))) rfl

/-- `SSTORE`: pop `key :: val`, store into the code owner's storage, `pc += 1`.
The stack-shape hypothesis is on the post-`Z` state `s₁` (`Z` only touches
`gasAvailable`). -/
theorem X_sstore (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (key val : UInt256) (rest : Stack UInt256)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.SSTORE, arg))
    (hZ : Z vj .SSTORE s = .ok (s₁, cost))
    (hstk : s₁.stack = key :: val :: rest) :
    X (f+2) vj s
      = X (f+1) vj
          ({ debit s₁ cost with
              toState := s₁.toState.sstore key val }.replaceStackAndIncrPC rest) :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_sstore f cost arg s₁).trans
      (shared_step_sstore arg (debit s₁ cost) key val rest hstk)) rfl

/-- `JUMP`: pop the destination, set `pc` to it. (`Z`'s `BadJumpDestination`
gate already passed — its success is the hypothesis.) -/
theorem X_jump (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (dest : UInt256) (rest : Stack UInt256)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMP, arg))
    (hZ : Z vj .JUMP s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: rest) :
    X (f+2) vj s = X (f+1) vj { debit s₁ cost with pc := dest, stack := rest } :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_jump f cost arg s₁).trans
      (shared_step_jump arg (debit s₁ cost) dest rest hstk)) rfl

/-- `JUMPI`, taken arm (`cond ≠ 0`): pop `dest :: cond`, jump to `dest`. -/
theorem X_jumpi_taken (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (dest cond : UInt256) (rest : Stack UInt256)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: cond :: rest)
    (hcond : cond ≠ ⟨0⟩) :
    X (f+2) vj s = X (f+1) vj { debit s₁ cost with pc := dest, stack := rest } :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_taken arg (debit s₁ cost) dest cond rest hstk hcond)) rfl

/-- `JUMPI`, fallthrough arm (`cond = 0`): pop `dest :: 0`, `pc += 1`.
NB the successor's `pc` is `(debit s₁ cost).pc + 1 = s₁.pc + 1` — `debit`
does not move the `pc`. -/
theorem X_jumpi_fallthrough (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (dest : UInt256) (rest : Stack UInt256)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: (⟨0⟩ : UInt256) :: rest) :
    X (f+2) vj s
      = X (f+1) vj
          { debit s₁ cost with pc := (debit s₁ cost).pc + ⟨1⟩, stack := rest } :=
  X_iter (f+1) vj s s₁ _ _ _ cost hdec hZ
    ((step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_fallthrough arg (debit s₁ cost) dest rest hstk)) rfl

/-! ## 5. The branch combinator -/

/-- **Branch combinator** (flat `runs_branch` analog): to establish any
property of the `X`-run through a `JUMPI`, provide it on both arms — the taken
successor under `cond ≠ 0` and the fallthrough successor under `cond = 0`. -/
theorem X_branch (f : ℕ) (vj : Array UInt256) (s s₁ : EVM.State)
    (arg : Option (UInt256 × Nat)) (cost : ℕ)
    (dest cond : UInt256) (rest : Stack UInt256)
    (motive : Except EVM.ExecutionException (ExecutionResult EVM.State) → Prop)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: cond :: rest)
    (htaken : cond ≠ ⟨0⟩ →
      motive (X (f+1) vj { debit s₁ cost with pc := dest, stack := rest }))
    (hfall : cond = ⟨0⟩ →
      motive (X (f+1) vj
        { debit s₁ cost with pc := (debit s₁ cost).pc + ⟨1⟩, stack := rest })) :
    motive (X (f+2) vj s) := by
  by_cases hc : cond = ⟨0⟩
  · subst hc
    rw [X_jumpi_fallthrough f vj s s₁ arg cost dest rest hdec hZ hstk]
    exact hfall rfl
  · rw [X_jumpi_taken f vj s s₁ arg cost dest cond rest hdec hZ hstk hc]
    exact htaken hc

/-! ## 6. Sequencing / decomposition

The lemma-backed successor vocabulary. Unlike the study's stated-only
`IterStep` (ObservableTriple.lean), the `step` clause is **∀-fuel** — exactly
what the per-opcode rules discharge (the dispatcher RHS is fuel-free), so no
fuel transport is ever needed. Decode goes through `.getD` (the study's
`decode = some` was a fidelity gap: undecodable bytes ARE `STOP`). -/

/-- One non-halting `X`-loop iteration from `s` to `s'`, with a fuel-universal
`step` clause. Populated by the `IterStepU.*` intro rules below. -/
def IterStepU (vj : Array UInt256) (s s' : EVM.State) : Prop :=
  ∃ (cost : ℕ) (op : Operation) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg) ∧
    Z vj op s = .ok (s₁, cost) ∧
    (∀ f, EVM.step (f+1) cost (some (op, arg)) s₁ = .ok s') ∧
    H s'.toMachineState op = none

/-- The halting sibling: the iteration's `H` fires with output `o` on a
non-`REVERT` opcode (`X` packages `.ok (.success s' o)`). -/
def IterHaltU (vj : Array UInt256) (s s' : EVM.State) (o : ByteArray) : Prop :=
  ∃ (cost : ℕ) (op : Operation) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg) ∧
    Z vj op s = .ok (s₁, cost) ∧
    (∀ f, EVM.step (f+1) cost (some (op, arg)) s₁ = .ok s') ∧
    H s'.toMachineState op = some o ∧
    op ≠ .REVERT

/-- `n`-indexed straight-line runs: the length-indexed reflexive-transitive
closure of `IterStepU` (refl + tail). The index makes the fuel bookkeeping in
`X_decompose` pure `Nat`-offset arithmetic. -/
inductive ItersN (vj : Array UInt256) : ℕ → EVM.State → EVM.State → Prop
  | refl (s : EVM.State) : ItersN vj 0 s s
  | tail {n : ℕ} {s s' s'' : EVM.State} :
      ItersN vj n s s' → IterStepU vj s' s'' → ItersN vj (n+1) s s''

/-- A single `IterStepU` is a length-1 chain. -/
theorem ItersN.single {vj : Array UInt256} {s s' : EVM.State}
    (h : IterStepU vj s s') : ItersN vj 1 s s' :=
  (ItersN.refl s).tail h

/-- Chains concatenate (lengths add). -/
theorem ItersN.trans {vj : Array UInt256} {m n : ℕ} {s s' s'' : EVM.State}
    (h₁ : ItersN vj m s s') (h₂ : ItersN vj n s' s'') :
    ItersN vj (m + n) s s'' := by
  induction h₂ with
  | refl _ => exact h₁
  | tail hc hstep ih => exact (ih h₁).tail hstep

/-- One `IterStepU` advances `X` by exactly one fuel tick, at every
sufficient fuel. -/
theorem IterStepU_X {vj : Array UInt256} {s s' : EVM.State}
    (h : IterStepU vj s s') (f : ℕ) : X (f+2) vj s = X (f+1) vj s' := by
  obtain ⟨cost, op, arg, s₁, hdec, hZ, hstep, hH⟩ := h
  exact X_iter (f+1) vj s s₁ s' op arg cost hdec hZ (hstep f) hH

/-- **Chain transport**: an `n`-chain advances `X` by exactly `n` fuel ticks,
at every sufficient fuel — pure `Nat`-offset bookkeeping, no fuel transport. -/
theorem ItersN_X {vj : Array UInt256} {n : ℕ} {s s' : EVM.State}
    (h : ItersN vj n s s') : ∀ f, X (f + n + 2) vj s = X (f + 2) vj s' := by
  induction h with
  | refl s => intro f; rfl
  | @tail k _ _ _ hc hstep ih =>
    intro f
    have harith : f + (k + 1) + 2 = (f + 1) + k + 2 := by omega
    rw [harith, ih (f + 1), IterStepU_X hstep (f + 1)]

/-- **The sequencing/decomposition theorem** (flat `Runs.trans` +
`drive_reconcile` analog): a straight-line chain into `sEnd` followed by a
halting iteration yields the `X`-run's success outcome, at **every**
sufficient fuel (`f + n + 2`: `n` chain ticks + the halting iteration, whose
`step` needs positive fuel). No fuel transport anywhere: every `step` clause
is ∀-fuel. -/
theorem X_decompose {vj : Array UInt256} {n : ℕ} {s sEnd sHalt : EVM.State}
    {out : ByteArray}
    (hchain : ItersN vj n s sEnd) (hhalt : IterHaltU vj sEnd sHalt out) :
    ∀ f, X (f + n + 2) vj s = .ok (.success sHalt out) := by
  intro f
  rw [ItersN_X hchain f]
  obtain ⟨cost, op, arg, s₁, hdec, hZ, hstep, hH, hrev⟩ := hhalt
  exact X_iter_halt (f+1) vj sEnd s₁ sHalt op arg cost out hdec hZ (hstep f) hH hrev

/-! ### Per-opcode `IterStepU`/`IterHaltU` intro rules

These discharge the ∀-fuel step clause via the dispatcher equations — the
per-opcode rules above, repackaged as chain links. -/

theorem IterStepU.push1 {vj : Array UInt256} {s s₁ : EVM.State}
    {v : UInt256} {n cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.PUSH1, some (v, n)))
    (hZ : Z vj .PUSH1 s = .ok (s₁, cost)) :
    IterStepU vj s
      ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push v) (pcΔ := n+1)) :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_push1 f cost _ s₁).trans (shared_step_push1 v n _), rfl⟩

theorem IterStepU.push0 {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.PUSH0, arg))
    (hZ : Z vj .PUSH0 s = .ok (s₁, cost)) :
    IterStepU vj s
      ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push ⟨0⟩)) :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_push0 f cost arg s₁).trans (shared_step_push0 arg _), rfl⟩

theorem IterStepU.sstore {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {key val : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.SSTORE, arg))
    (hZ : Z vj .SSTORE s = .ok (s₁, cost))
    (hstk : s₁.stack = key :: val :: rest) :
    IterStepU vj s
      ({ debit s₁ cost with toState := s₁.toState.sstore key val }.replaceStackAndIncrPC rest) :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_sstore f cost arg s₁).trans
      (shared_step_sstore arg (debit s₁ cost) key val rest hstk), rfl⟩

theorem IterStepU.jump {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMP, arg))
    (hZ : Z vj .JUMP s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: rest) :
    IterStepU vj s { debit s₁ cost with pc := dest, stack := rest } :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_jump f cost arg s₁).trans
      (shared_step_jump arg (debit s₁ cost) dest rest hstk), rfl⟩

theorem IterStepU.jumpi_taken {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest cond : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: cond :: rest)
    (hcond : cond ≠ ⟨0⟩) :
    IterStepU vj s { debit s₁ cost with pc := dest, stack := rest } :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_taken arg (debit s₁ cost) dest cond rest hstk hcond), rfl⟩

theorem IterStepU.jumpi_fallthrough {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: (⟨0⟩ : UInt256) :: rest) :
    IterStepU vj s
      { debit s₁ cost with pc := (debit s₁ cost).pc + ⟨1⟩, stack := rest } :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_fallthrough arg (debit s₁ cost) dest rest hstk), rfl⟩

/-- The canonical halting link: `STOP` (also what undecodable bytes decode to,
via `.getD`). Output is empty; the machine state's `returnData` is cleared. -/
theorem IterHaltU.stop {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.STOP, arg))
    (hZ : Z vj .STOP s = .ok (s₁, cost)) :
    IterHaltU vj s
      { debit s₁ cost with
          toMachineState := (debit s₁ cost).toMachineState.setReturnData .empty }
      .empty :=
  ⟨cost, _, _, s₁, hdec, hZ,
    fun f => (step_eq_shared_stop f cost arg s₁).trans (shared_step_stop arg _),
    rfl, by intro h; exact absurd h (by decide)⟩

/-! ## 7. CALL-site and halting-iteration lemmas (the endgame's ingredients)

The two iteration shapes the straight-line rules above cannot cover: a `CALL`
iteration (whose `step` clause recurses into `call`, so it is only
**cofinally** fuel-universal — `∀ f, call (f + k) … = .ok …` — never bare
∀-fuel), and the halting `STOP` iteration with an *explicit* successor
(`stopHaltState`), so the final state's map can be chased back to the `call`
output by `rfl` + `Z_ok_toState`. -/

set_option maxHeartbeats 2000000 in
/-- A successful `Z` only rewrites `gasAvailable` (a `MachineState` field), so
the `toState` projection (accountMap / substate / createdAccounts /
executionEnv) passes through untouched. Same inversion recipe (and heartbeat
crank) as `NeverOutOfFuel.Z_ok_code_pc`. -/
theorem Z_ok_toState {vj : Array UInt256} {op : Operation} {s s' : EVM.State} {c : ℕ}
    (h : Z vj op s = .ok (s', c)) : s'.toState = s.toState := by
  unfold Z at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  generalize hm : memoryExpansionCost s op = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact absurd h (by simp)
  · rw [if_neg hg1] at h
    generalize hcc : C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } op = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } : EVM.State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact absurd h (by simp)
    · rw [if_neg hg2] at h
      have hs' : s' = { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } := by
        revert h
        split_ifs <;> intro h <;>
          first
          | (have hp := Except.ok.inj h; rw [Prod.mk.injEq] at hp
             obtain ⟨rfl, _⟩ := hp; rfl)
          | exact absurd h (by simp)
      rw [hs']

/-- **The CALL iteration** (the study's "unstateable" call-site tie, stated and
proved): if the code at `s.pc` decodes to `CALL`, the `Z` gate passes to `sZ`,
and the recursive `call` — on the **bumped** state, with the exact operand
plumbing `step_call_eq` exposes — succeeds cofinally above offset `k` with
output state `evR`, then one `X` iteration advances `s` to the *post-processed*
successor `evR.replaceStackAndIncrPC (rest.push ⟨1⟩)`, at every fuel of the
form `f + k + 2`. The cofinal (`∀ f, call (f + k) …`) rather than ∀-fuel call
clause is forced: `call` recurses into `Θ`, so it genuinely consumes fuel —
this is the one iteration shape whose fuel clause cannot be bare-universal. -/
theorem X_call_iter {vj : Array UInt256} {s sZ evR : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost k : ℕ}
    {g t v io isz oo osz : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.CALL, arg))
    (hZ : Z vj .CALL s = .ok (sZ, cost))
    (hstk : sZ.stack = g :: t :: v :: io :: isz :: oo :: osz :: rest)
    (hcall : ∀ f, call (f + k) cost sZ.executionEnv.blobVersionedHashes g
      (.ofNat sZ.executionEnv.codeOwner) t t v v io isz oo osz
      sZ.executionEnv.perm (bump sZ) = .ok (⟨1⟩, evR)) (f : ℕ) :
    X (f + k + 2) vj s
      = X (f + k + 1) vj (evR.replaceStackAndIncrPC (rest.push ⟨1⟩)) := by
  refine X_iter (f + k + 1) vj s sZ _ .CALL arg cost hdec hZ ?_ rfl
  rw [step_call_eq (f + k) cost arg sZ g t v io isz oo osz rest hstk, hcall f]
  rfl

/-- The explicit successor of a halting `STOP` iteration entered at post-`Z`
state `sZ` with gate cost `cost` (the `IterHaltU.stop` successor shape, named
so consumers can chase its fields: `accountMap`/`substate`/`createdAccounts`
are `sZ`'s by `rfl`). -/
def stopHaltState (sZ : EVM.State) (cost : ℕ) : EVM.State :=
  { debit sZ cost with
      toMachineState := (debit sZ cost).toMachineState.setReturnData .empty }

/-- **The halting `STOP` iteration with explicit successor**: `X` packages
`.ok (.success (stopHaltState sZ cost) .empty)` at every fuel `f + 2`.
(No stack hypothesis: `Z`'s success is taken as a hypothesis, so this works at
any stack — unlike `Refinement.Z_stop`, which needs `stack = []`.) -/
theorem X_stop_halt {vj : Array UInt256} {s sZ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.STOP, arg))
    (hZ : Z vj .STOP s = .ok (sZ, cost)) (f : ℕ) :
    X (f + 2) vj s = .ok (.success (stopHaltState sZ cost) .empty) :=
  X_iter_halt (f+1) vj s sZ _ .STOP arg cost .empty hdec hZ
    ((step_eq_shared_stop f cost arg sZ).trans (shared_step_stop arg _)) rfl
    (fun h => nomatch h)

/-! ## 8. Reconciliation with the study's seed vocabulary

The study's stated-only seeds (`IterStep`/`IterCallStep`/`IterHalt`/`Iters`,
formerly in ObservableTriple.lean — no lemmas, `∃ f` fuel clause, `decode =
some` fidelity gap) were RETIRED by T4 when the endgame statement was rebuilt
on this file's lemma-backed vocabulary (`IterStepU`/`IterHaltU`/`ItersN` +
`X_call_iter`/`X_stop_halt`, ∀-fuel or cofinal, `.getD`-faithful). The
retirement record — including the study's refutability finding about the naive
call-site tie — lives in the endgame's docstring
(ObservableTriple.`nested_twoCall_completedWith`). -/

end NestedEvmYul.XLoop
