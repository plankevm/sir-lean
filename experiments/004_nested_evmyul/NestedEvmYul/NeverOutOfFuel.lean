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
* **Item 1 — `Z → step → X` gas-decrement chain** (DONE):
  - `gas_EvmYul_step`: the shared per-opcode interpreter preserves `gasAvailable`
    on `.ok` (a full per-opcode sweep over the grouped `Operation`, every arm closed
    by definitional unfolding to a combinator/inline gas lemma — no re-elaboration of
    the 140-arm `match`). Stated for every opcode the shared step actually handles
    (the `CREATE`/`CALL` family is special-cased earlier and never routed here).
  - `gas_EVM_step_default`: the nested `EVM.step` default arm debits *exactly*
    `gasCost`, so `s'.gasAvailable = s.gasAvailable - gasCost`.
  - `Z_ok_cost_le_gas`: a successful `Z` returns `(s', c)` with `c = C' s' w` and
    `c ≤ s'.gasAvailable.toNat` (the `cost₂` guard).
* **Item 2 — `X` measure descent** (DONE): `X_iter_gas_lt` — a non-halting `X`
  iteration (`Z` ok, `step` ok on a non-call/create opcode, `H = none`) lands in a
  state with *strictly less* `gasAvailable.toNat`. Built from `C'_pos_of_runnable`
  (positivity), `Z_ok_cost_le_gas` (cost ≤ gas), `gas_EVM_step_default` (the debit),
  and `gas_sub_lt` (`UInt256` subtraction of a positive non-underflowing cost drops
  `.toNat`). So gas is a genuine well-founded measure on the loop.
* **Item 3 — child gas ≤ parent gas** (down-payment): `Cgascap_le_gas` — the gas a
  frame forwards to a child is bounded by the parent's own gas (or capped at `g`).

What remains (see PLAN.md) is the cross-layer threading of item 3 through the
`call`/`Θ`/`Ξ` arms (incl. the `Gcallstipend` top-up and the `depth ≤ 1024` cap) and
**item 4**, the final mutual `fuel` induction over `X`/`Ξ`/`Θ`/`call`/`step` closing
`Θ_never_outOfFuel`. Those are documented, not faked.
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

This is the unconditional never-`OutOfFuel`. It is *documented*, not asserted. The
measure-decrement chain `C'_pos_of_runnable → Z → step → X` and the `X` measure
descent are now **proved** (`gas_EvmYul_step`, `gas_EVM_step_default`,
`Z_ok_cost_le_gas`, `X_iter_gas_lt` below). The remaining obligations (see PLAN.md)
are the cross-layer gas/depth conservation for `call`/`Θ`/`Ξ` (item-3 down-payment:
`Cgascap_le_gas`) and the final mutual `fuel` induction over the five layers. -/

/-- The gas-derived fuel bound (analogue of exp003's flat `seedFuel gas`). -/
def seedFuel (g : ℕ) : ℕ := 4 * (g + 1)

/-! ## Item 1a — `EvmYul.step` preserves `gasAvailable`

The shared per-opcode interpreter `EvmYul.step` (the one called on the *default*
arm of `EVM.step`, i.e. for every non-`CREATE`/`CALL`-family opcode) never reads
or writes `gasAvailable`: a `grep` confirms the field is mentioned nowhere in
`EvmYul/Semantics.lean`. Every result it can produce is built either as
`s.replaceStackAndIncrPC …` or `{s with toMachineState/toState/toSharedState := …}`,
none of which touch `gasAvailable`. We make that precise: on any `.ok` result the
`gasAvailable` field is unchanged. This is the gas-preservation half of the
`Z → step → X` chain. -/

/-- `replaceStackAndIncrPC` preserves `gasAvailable` (it only rewrites `stack`/`pc`). -/
@[simp] theorem gasAvailable_replaceStackAndIncrPC (s : State) (st : Stack UInt256) (d : ℕ) :
    (s.replaceStackAndIncrPC st d).gasAvailable = s.gasAvailable := rfl

@[simp] theorem gasAvailable_incrPC (s : State) (d : ℕ) :
    (s.incrPC d).gasAvailable = s.gasAvailable := rfl

/-- Closer for a primop-combinator gas-preservation goal: unfold the combinator,
case-split on the stack-pop guard, discharge the `.ok` arm by `injection`/`rfl`
(the result is `replaceStackAndIncrPC` of a gas-preserving update) and the
underflow arm by contradiction. -/
local macro "gas_comb" defn:ident hyp:ident : tactic =>
  `(tactic|
    (unfold $defn at $hyp:ident
     split at $hyp:ident <;>
       first
       | (simp only [Id.run] at $hyp:ident; injection $hyp:ident with $hyp:ident
          subst $hyp:ident; rfl)
       | (exfalso; exact absurd $hyp:ident (by simp))))

/-- Closer for the guard-free combinators (`machineStateOp`/`stateOp`/
`executionEnvOp`): no stack-pop split — they always return
`.ok (replaceStackAndIncrPC …)`. -/
local macro "gas_comb0" defn:ident hyp:ident : tactic =>
  `(tactic|
    (unfold $defn at $hyp:ident
     simp only [Id.run] at $hyp:ident; injection $hyp:ident with $hyp:ident
     subst $hyp:ident; rfl))

theorem gas_execUnOp (f : Primop.Unary) (s s' : State) (h : EVM.execUnOp f s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.execUnOp h

theorem gas_execBinOp (f : Primop.Binary) (s s' : State) (h : EVM.execBinOp f s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.execBinOp h

theorem gas_execTriOp (f : Primop.Ternary) (s s' : State) (h : EVM.execTriOp f s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.execTriOp h

theorem gas_execQuadOp (f : Primop.Quaternary) (s s' : State) (h : EVM.execQuadOp f s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.execQuadOp h

theorem gas_executionEnvOp (op : ExecutionEnv → UInt256) (s s' : State)
    (h : EVM.executionEnvOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  gas_comb0 EVM.executionEnvOp h

theorem gas_unaryExecutionEnvOp (op : ExecutionEnv → UInt256 → UInt256) (s s' : State)
    (h : EVM.unaryExecutionEnvOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  gas_comb EVM.unaryExecutionEnvOp h

theorem gas_machineStateOp (op : MachineState → UInt256) (s s' : State)
    (h : EVM.machineStateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  gas_comb0 EVM.machineStateOp h

theorem gas_stateOp (op : EvmYul.State → UInt256) (s s' : State)
    (h : EVM.stateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  gas_comb0 EVM.stateOp h

/-! The combinators that update the *machine* part carry the op's gas behaviour as
a hypothesis (`hop`): all the concrete ops used by `step` rebuild the machine state
as `{ self with … }` without touching `gasAvailable`, so `hop` is discharged by
`rfl` at each use site. The ones that update the pure `EvmYul.State` / `SharedState`
part preserve `gasAvailable` definitionally — except `SharedState`, which *contains*
`gasAvailable`, so those copy ops also carry an `hop`. -/

theorem gas_binaryMachineStateOp (op : MachineState → UInt256 → UInt256 → MachineState)
    (hop : ∀ m a b, (op m a b).gasAvailable = m.gasAvailable) (s s' : State)
    (h : EVM.binaryMachineStateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.binaryMachineStateOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h
    simp only [gasAvailable_replaceStackAndIncrPC]; exact hop _ _ _
  · exfalso; exact absurd h (by simp)

theorem gas_binaryMachineStateOp' (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    (hop : ∀ m a b, (op m a b).2.gasAvailable = m.gasAvailable) (s s' : State)
    (h : EVM.binaryMachineStateOp' op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.binaryMachineStateOp' at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h
    simp only [gasAvailable_replaceStackAndIncrPC]; exact hop _ _ _
  · exfalso; exact absurd h (by simp)

theorem gas_ternaryMachineStateOp (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    (hop : ∀ m a b c, (op m a b c).gasAvailable = m.gasAvailable) (s s' : State)
    (h : EVM.ternaryMachineStateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.ternaryMachineStateOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h
    simp only [gasAvailable_replaceStackAndIncrPC]; exact hop _ _ _ _
  · exfalso; exact absurd h (by simp)

theorem gas_binaryStateOp (op : EvmYul.State → UInt256 → UInt256 → EvmYul.State) (s s' : State)
    (h : EVM.binaryStateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.binaryStateOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h; rfl
  · exfalso; exact absurd h (by simp)

theorem gas_unaryStateOp (op : EvmYul.State → UInt256 → EvmYul.State × UInt256) (s s' : State)
    (h : EVM.unaryStateOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.unaryStateOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h; rfl
  · exfalso; exact absurd h (by simp)

theorem gas_ternaryCopyOp (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState)
    (hop : ∀ ss a b c, (op ss a b c).gasAvailable = ss.gasAvailable) (s s' : State)
    (h : EVM.ternaryCopyOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.ternaryCopyOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h
    simp only [gasAvailable_replaceStackAndIncrPC]; exact hop _ _ _ _
  · exfalso; exact absurd h (by simp)

theorem gas_quaternaryCopyOp (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState)
    (hop : ∀ ss a b c d, (op ss a b c d).gasAvailable = ss.gasAvailable) (s s' : State)
    (h : EVM.quaternaryCopyOp op s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  unfold EVM.quaternaryCopyOp at h
  split at h
  · simp only [Id.run] at h; injection h with h; subst h
    simp only [gasAvailable_replaceStackAndIncrPC]; exact hop _ _ _ _ _
  · exfalso; exact absurd h (by simp)

/-! ### Concrete machine/shared-state op gas-preservation facts (all `rfl`)

Each opcode-level op rebuilds its target as `{ self with … }` without naming
`gasAvailable`, so gas is preserved definitionally. These are the `hop` arguments
for the combinator lemmas above. -/

theorem gas_mstore (m : MachineState) (a b : UInt256) :
    (MachineState.mstore m a b).gasAvailable = m.gasAvailable := rfl
theorem gas_mstore8 (m : MachineState) (a b : UInt256) :
    (MachineState.mstore8 m a b).gasAvailable = m.gasAvailable := rfl
theorem gas_mload (m : MachineState) (a : UInt256) :
    (MachineState.mload m a).2.gasAvailable = m.gasAvailable := rfl
theorem gas_keccak256 (m : MachineState) (a b : UInt256) :
    (MachineState.keccak256 m a b).2.gasAvailable = m.gasAvailable := rfl
theorem gas_evmReturn (m : MachineState) (a b : UInt256) :
    (MachineState.evmReturn m a b).gasAvailable = m.gasAvailable := rfl
theorem gas_evmRevert (m : MachineState) (a b : UInt256) :
    (MachineState.evmRevert m a b).gasAvailable = m.gasAvailable := rfl
theorem gas_mcopy (m : MachineState) (a b c : UInt256) :
    (MachineState.mcopy m a b c).gasAvailable = m.gasAvailable := rfl
theorem gas_returndatacopy (m : MachineState) (a b c : UInt256) :
    (MachineState.returndatacopy m a b c).gasAvailable = m.gasAvailable := rfl
theorem gas_calldatacopy (ss : SharedState) (a b c : UInt256) :
    (SharedState.calldatacopy ss a b c).gasAvailable = ss.gasAvailable := rfl
theorem gas_codeCopy (ss : SharedState) (a b c : UInt256) :
    (SharedState.codeCopy ss a b c).gasAvailable = ss.gasAvailable := rfl
theorem gas_extCodeCopy' (ss : SharedState) (acc a b c : UInt256) :
    (SharedState.extCodeCopy' ss acc a b c).gasAvailable = ss.gasAvailable := rfl
theorem gas_logOp' (μ₀ μ₁ : UInt256) (t : Array UInt256) (ss : SharedState) :
    (SharedState.logOp μ₀ μ₁ t ss).gasAvailable = ss.gasAvailable := rfl

theorem gas_log0Op (s s' : State) (h : EVM.log0Op s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.log0Op h
theorem gas_log1Op (s s' : State) (h : EVM.log1Op s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.log1Op h
theorem gas_log2Op (s s' : State) (h : EVM.log2Op s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.log2Op h
theorem gas_log3Op (s s' : State) (h : EVM.log3Op s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.log3Op h
theorem gas_log4Op (s s' : State) (h : EVM.log4Op s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by gas_comb EVM.log4Op h

/-! ### Gas-preservation for the *inline* `EvmYul.step` arms

These are the opcode arms whose body is written inline in `EvmYul.step` rather than
via a dispatch combinator. Each is proved about the underlying raw function so it
can be applied to a concrete `EvmYul.step <op>` hypothesis by definitional
unfolding (exactly as the combinator lemmas are). -/

theorem gas_dup (n : ℕ) (s s' : State) (h : EvmYul.dup n s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by
  simp only [EvmYul.dup] at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

theorem gas_swap (n : ℕ) (s s' : State) (h : EvmYul.swap n s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by
  simp only [EvmYul.swap] at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- STOP arm body. -/
theorem gas_inl_stop (s s' : State)
    (h : (.ok {s with toMachineState := s.toMachineState.setReturnData .empty}
          : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := by injection h with h; subst h; rfl

/-- POP arm body. -/
theorem gas_inl_pop (s s' : State)
    (h : (match s.stack.pop with
          | some ⟨st, _⟩ => (.ok (s.replaceStackAndIncrPC st) : Except EVM.ExecutionException State)
          | _ => .error .StackUnderflow) = .ok s') : s'.gasAvailable = s.gasAvailable := by
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- PC arm body (unconditional push). -/
theorem gas_inl_replaceStack (s s' : State) (st : Stack UInt256)
    (h : (.ok (s.replaceStackAndIncrPC st) : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := by injection h with h; subst h; rfl

/-- JUMPDEST arm body (unconditional `incrPC`). -/
theorem gas_inl_incrPC (s s' : State)
    (h : (.ok s.incrPC : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := by injection h with h; subst h; rfl

/-- JUMP/JUMPI arm bodies set `pc`/`stack` only. -/
theorem gas_inl_setPcStack (s s' : State) (pc : UInt256) (st : Stack UInt256)
    (h : (.ok {s with pc := pc, stack := st} : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := by injection h with h; subst h; rfl

/-- JUMP arm: stated about `EvmYul.step` directly (so the `do`/`match` shape need not
be guessed); peel the `pop` guard, each `.ok` leaf sets only `pc`/`stack`. -/
theorem gas_inl_jump (arg : Option (UInt256 × Nat)) (s s' : State)
    (h : EvmYul.step (.StackMemFlow .JUMP) arg s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  have h2 : (match s.stack.pop with
              | some ⟨st, μ₀⟩ => (.ok {s with pc := μ₀, stack := st} : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .ok s' := h
  split at h2
  · injection h2 with h2; subst h2; rfl
  · exact absurd h2 (by simp)

/-- JUMPI arm: stated about `EvmYul.step` directly. -/
theorem gas_inl_jumpi (arg : Option (UInt256 × Nat)) (s s' : State)
    (h : EvmYul.step (.StackMemFlow .JUMPI) arg s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  have h2 : (match s.stack.pop2 with
              | some ⟨st, μ₀, μ₁⟩ =>
                (.ok {s with pc := if μ₁ != (⟨0⟩ : UInt256) then μ₀ else s.pc + (⟨1⟩ : UInt256),
                              stack := st} : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .ok s' := h
  split at h2
  · injection h2 with h2; subst h2; rfl
  · exact absurd h2 (by simp)

/-- Push arm (non-`PUSH0`): the immediate-argument `arg` is matched, then
`replaceStackAndIncrPC (stack.push arg) (argWidth+1)`; gas-preserving regardless. -/
theorem gas_inl_push (po : Operation.POp) (arg : Option (UInt256 × Nat)) (s s' : State)
    (h : EvmYul.step (.Push po) arg s = .ok s') : s'.gasAvailable = s.gasAvailable := by
  cases po with
  | PUSH0 => exact gas_inl_replaceStack _ _ _ h
  | _ =>
    all_goals (
      -- `cases arg` lets `EvmYul.step .PUSHn (some _) s` / `… none s` reduce by defeq.
      cases arg with
      | none =>
        exact absurd (show (.error .StackUnderflow : Except EVM.ExecutionException State) = .ok s'
                       from h) (by simp)
      | some p =>
        obtain ⟨a, w⟩ := p
        have h2 : (.ok (s.replaceStackAndIncrPC (s.stack.push a) w.succ)
                    : Except EVM.ExecutionException State) = .ok s' := h
        injection h2 with h2; subst h2; rw [gasAvailable_replaceStackAndIncrPC])

/-- INVALID arm body (`dispatchInvalid` = constant error): no `.ok` result, so the
goal follows vacuously. -/
theorem gas_inl_error (s s' : State) (e : EVM.ExecutionException)
    (h : (.error e : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := absurd h (by simp)

/-- General inline closer: `.ok` of `replaceStackAndIncrPC t st` with `t` a
gas-preserving rebuild of `s` (the `hgas` side condition is `rfl` at each use). -/
theorem gas_inl_replaceStackOf (s t s' : State) (st : Stack UInt256) (d : ℕ)
    (hgas : t.gasAvailable = s.gasAvailable)
    (h : (.ok (t.replaceStackAndIncrPC st d) : Except EVM.ExecutionException State) = .ok s') :
    s'.gasAvailable = s.gasAvailable := by
  injection h with h; subst h; rw [gasAvailable_replaceStackAndIncrPC]; exact hgas

/-- MLOAD arm body: pop, push the loaded word onto a machine-updated state. -/
theorem gas_inl_mload (s s' : State)
    (h : (match s.stack.pop with
          | some ⟨st, μ₀⟩ =>
            (.ok (({s with toMachineState := (s.toMachineState.mload μ₀).2}).replaceStackAndIncrPC
                    (st.push (s.toMachineState.mload μ₀).1)) : Except EVM.ExecutionException State)
          | _ => .error .StackUnderflow) = .ok s') : s'.gasAvailable = s.gasAvailable := by
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- RETURNDATACOPY arm body: pop3, machine-update, replace stack. -/
theorem gas_inl_returndatacopy (s s' : State)
    (h : (match s.stack.pop3 with
          | some ⟨st, μ₀, μ₁, μ₂⟩ =>
            (.ok (({s with toMachineState := s.toMachineState.returndatacopy μ₀ μ₁ μ₂}).replaceStackAndIncrPC
                    st) : Except EVM.ExecutionException State)
          | _ => .error .StackUnderflow) = .ok s') : s'.gasAvailable = s.gasAvailable := by
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-! ### `EvmYul.step` preserves `gasAvailable` (the full per-opcode sweep)

The shared interpreter is invoked on `EVM.step`'s default arm with the already
gas-debited state; we show it leaves `gasAvailable` untouched on any `.ok`. The
proof is one `cases`-sweep over the grouped `Operation`: after peeling the
`dbg_trace`/`Id.run` wrapper, each arm is exactly one of the combinators proved
above (discharged by `step_arm`), or an inline `replaceStackAndIncrPC`/`incrPC`
result (the `Push`/`POP`/`MLOAD`/`PC`/`JUMPDEST`/`JUMP`/`JUMPI`/`RETURNDATACOPY`/
`SELFDESTRUCT`/`STOP`/`dup`/`swap` arms, discharged by `step_inline`). -/

/-- Closer for a combinator arm: try every proved combinator gas lemma. -/
local macro "step_arm" hyp:ident : tactic =>
  `(tactic|
    first
    | exact gas_execUnOp _ _ _ $hyp
    | exact gas_execBinOp _ _ _ $hyp
    | exact gas_execTriOp _ _ _ $hyp
    | exact gas_execQuadOp _ _ _ $hyp
    | exact gas_executionEnvOp _ _ _ $hyp
    | exact gas_unaryExecutionEnvOp _ _ _ $hyp
    | exact gas_machineStateOp _ _ _ $hyp
    | exact gas_stateOp _ _ _ $hyp
    -- `unaryStateOp`/`binaryStateOp` ops need a concrete op so `EvmYul.step` reduces:
    | exact gas_unaryStateOp EvmYul.State.balance _ _ $hyp
    | exact gas_unaryStateOp EvmYul.State.extCodeSize _ _ $hyp
    | exact gas_unaryStateOp EvmYul.State.extCodeHash _ _ $hyp
    | exact gas_unaryStateOp EvmYul.State.sload _ _ $hyp
    | exact gas_unaryStateOp EvmYul.State.tload _ _ $hyp
    | exact gas_unaryStateOp (fun s v ↦ (s, EvmYul.State.calldataload s v)) _ _ $hyp
    | exact gas_unaryStateOp (fun s v ↦ (s, EvmYul.State.blockHash s v)) _ _ $hyp
    | exact gas_binaryStateOp EvmYul.State.sstore _ _ $hyp
    | exact gas_binaryStateOp EvmYul.State.tstore _ _ $hyp
    -- machine/shared-state-rebuilding ops: the op must be supplied concretely so
    -- that `EvmYul.step <op>` reduces by defeq; the `hop` side goal is then `rfl`.
    | exact gas_binaryMachineStateOp MachineState.mstore (fun _ _ _ => rfl) _ _ $hyp
    | exact gas_binaryMachineStateOp MachineState.mstore8 (fun _ _ _ => rfl) _ _ $hyp
    | exact gas_binaryMachineStateOp MachineState.evmReturn (fun _ _ _ => rfl) _ _ $hyp
    | exact gas_binaryMachineStateOp MachineState.evmRevert (fun _ _ _ => rfl) _ _ $hyp
    | exact gas_binaryMachineStateOp' MachineState.keccak256 (fun _ _ _ => rfl) _ _ $hyp
    | exact gas_ternaryMachineStateOp MachineState.mcopy (fun _ _ _ _ => rfl) _ _ $hyp
    | exact gas_ternaryCopyOp SharedState.calldatacopy (fun _ _ _ _ => rfl) _ _ $hyp
    | exact gas_ternaryCopyOp SharedState.codeCopy (fun _ _ _ _ => rfl) _ _ $hyp
    | exact gas_quaternaryCopyOp SharedState.extCodeCopy' (fun _ _ _ _ _ => rfl) _ _ $hyp
    | exact gas_log0Op _ _ $hyp
    | exact gas_log1Op _ _ $hyp
    | exact gas_log2Op _ _ $hyp
    | exact gas_log3Op _ _ $hyp
    | exact gas_log4Op _ _ $hyp)

/-- Closer for an inline arm: apply the matching defeq-applicable raw lemma. The
side conditions on the `…Of`/machine variants are `rfl` (the rebuild does not touch
`gasAvailable`). For `dup`/`swap`/STOP-shape arms a `split`/`injection` cleanup is
attempted last. -/
local macro "step_inline" hyp:ident : tactic =>
  `(tactic|
    first
    | exact gas_dup _ _ _ $hyp
    | exact gas_swap _ _ _ $hyp
    | exact gas_inl_stop _ _ $hyp
    | exact gas_inl_pop _ _ $hyp
    | exact gas_inl_mload _ _ $hyp
    | exact gas_inl_returndatacopy _ _ $hyp
    | exact gas_inl_incrPC _ _ $hyp
    | exact gas_inl_replaceStack _ _ _ $hyp
    | exact gas_inl_replaceStackOf _ _ _ _ _ rfl $hyp
    | exact gas_inl_setPcStack _ _ _ _ $hyp
    | exact gas_inl_jump _ _ _ $hyp
    | exact gas_inl_jumpi _ _ _ $hyp
    | exact gas_inl_selfdestruct _ _ _ $hyp
    | exact gas_inl_error _ _ _ $hyp)

-- SELFDESTRUCT arm body: pop, then (across both EIP-6780 branches and all the
-- account-map sub-cases) the result is `replaceStackAndIncrPC` of a state that only
-- rewrites `accountMap`/`substate` — both in the gas-free `toState` part. We discharge
-- it by peeling the `pop` guard and every nested `if`/`match`, each leaf being
-- `replaceStackAndIncrPC` of a gas-preserving rebuild (`rfl`).
set_option maxHeartbeats 1000000 in
theorem gas_inl_selfdestruct (arg : Option (UInt256 × Nat)) (s s' : State)
    (h : EvmYul.step (.System .SELFDESTRUCT) arg s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by
  -- Body shape with all `let`s inlined (the `let`s are what block `split`); every
  -- non-error leaf is `.ok ({s with accountMap := _, substate := _}.replaceStackAndIncrPC st)`,
  -- and `accountMap`/`substate` are in the gas-free `toState` part, so each closes by `rfl`.
  have h2 : (match s.stack.pop with
      | some ⟨st, μ₁⟩ =>
        if s.createdAccounts.contains s.executionEnv.codeOwner then
          (.ok (({s with
              accountMap :=
                match s.lookupAccount s.executionEnv.codeOwner with
                  | none => s.accountMap
                  | some σ_Iₐ =>
                    match s.lookupAccount (AccountAddress.ofUInt256 μ₁) with
                      | none =>
                        if σ_Iₐ.balance == (⟨0⟩ : UInt256) then s.accountMap
                        else s.accountMap.insert (AccountAddress.ofUInt256 μ₁)
                                {(default : Account) with balance := σ_Iₐ.balance}
                                |>.insert s.executionEnv.codeOwner {σ_Iₐ with balance := (⟨0⟩ : UInt256)}
                      | some σ_r =>
                        if (AccountAddress.ofUInt256 μ₁) ≠ s.executionEnv.codeOwner then
                          s.accountMap.insert (AccountAddress.ofUInt256 μ₁)
                              {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                            |>.insert s.executionEnv.codeOwner {σ_Iₐ with balance := (⟨0⟩ : UInt256)}
                        else s.accountMap.insert (AccountAddress.ofUInt256 μ₁) {σ_r with balance := (⟨0⟩ : UInt256)}
                                |>.insert s.executionEnv.codeOwner {σ_Iₐ with balance := (⟨0⟩ : UInt256)}
              substate :=
                { s.substate with
                    selfDestructSet := s.substate.selfDestructSet.insert s.executionEnv.codeOwner
                    accessedAccounts := s.substate.accessedAccounts.insert (AccountAddress.ofUInt256 μ₁) }
              }).replaceStackAndIncrPC st) : Except EVM.ExecutionException State)
        else
          (.ok (({s with
              accountMap :=
                match s.lookupAccount s.executionEnv.codeOwner with
                  | none => s.accountMap
                  | some σ_Iₐ =>
                    match s.lookupAccount (AccountAddress.ofUInt256 μ₁) with
                      | none =>
                        if σ_Iₐ.balance == (⟨0⟩ : UInt256) then s.accountMap
                        else s.accountMap.insert (AccountAddress.ofUInt256 μ₁)
                                {(default : Account) with balance := σ_Iₐ.balance}
                                |>.insert s.executionEnv.codeOwner {σ_Iₐ with balance := (⟨0⟩ : UInt256)}
                      | some σ_r =>
                        if (AccountAddress.ofUInt256 μ₁) ≠ s.executionEnv.codeOwner then
                          s.accountMap.insert (AccountAddress.ofUInt256 μ₁)
                              {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                            |>.insert s.executionEnv.codeOwner {σ_Iₐ with balance := (⟨0⟩ : UInt256)}
                        else s.accountMap
              substate :=
                { s.substate with accessedAccounts := s.substate.accessedAccounts.insert (AccountAddress.ofUInt256 μ₁) }
              }).replaceStackAndIncrPC st) : Except EVM.ExecutionException State)
      | _ => .error .StackUnderflow) = .ok s' := h
  clear h
  -- Peel the pop-match and the EIP-6780 `if`; each non-error leaf is
  -- `.ok ({s with accountMap := _, substate := _}.replaceStackAndIncrPC st)` — the
  -- `accountMap`/`substate` matches are *inside* a field and need not be split, since
  -- `replaceStackAndIncrPC` preserves gas for any field values.
  split at h2
  · split at h2 <;>
      (repeat' first
        | (injection h2 with h2; subst h2; rw [gasAvailable_replaceStackAndIncrPC])
        | split at h2)
  · exact absurd h2 (by simp)

/-- The opcodes the *shared* `EvmYul.step` does not actually interpret: the
`CREATE`/`CALL` family. In the nested `EVM.step` these never reach `EvmYul.step`
(they are special-cased earlier), and in the shared interpreter they fall through to
the `_ => default` arm — which returns `.ok default`, *not* gas-preserving. So the
gas-preservation theorem is stated for every *other* opcode. -/
def isCallCreate (w : Operation) : Prop :=
  w = .CREATE ∨ w = .CREATE2 ∨ w = .CALL ∨ w = .CALLCODE ∨
  w = .DELEGATECALL ∨ w = .STATICCALL

set_option maxHeartbeats 4000000 in
/-- **`EvmYul.step` gas-preservation.** For every opcode the shared interpreter
actually handles (i.e. not the `CREATE`/`CALL` family, which `EVM.step` special-cases
and never routes here), a successful shared-step leaves `gasAvailable` unchanged.
(Gas is debited *before* `EvmYul.step` is reached, in `EVM.step`'s default arm.) Each
arm is discharged by definitional unfolding to the matching combinator lemma
(`step_arm`) or inline raw lemma (`step_inline`); nothing re-elaborates the full
`match`. -/
theorem gas_EvmYul_step (op : Operation) (arg : Option (UInt256 × Nat)) (s s' : State)
    (hop : ¬ isCallCreate op) (h : EvmYul.step op arg s = .ok s') :
    s'.gasAvailable = s.gasAvailable := by
  unfold isCallCreate at hop
  push_neg at hop
  cases op with
  | StopArith o => cases o <;> first | step_arm h | step_inline h
  | CompBit o => cases o <;> first | step_arm h | step_inline h
  | Keccak o => cases o <;>
      exact gas_binaryMachineStateOp' MachineState.keccak256 (fun _ _ _ => rfl) _ _ h
  | Env o => cases o <;> first | step_arm h | step_inline h
  | Block o => cases o <;> first | step_arm h | step_inline h
  | StackMemFlow o => cases o <;> first | step_arm h | step_inline h
  | Push o => exact gas_inl_push o _ _ _ h
  | Dup o => cases o <;> exact gas_dup _ _ _ h
  | Exchange o => cases o <;> exact gas_swap _ _ _ h
  | Log o => cases o <;>
      first | exact gas_log0Op _ _ h | exact gas_log1Op _ _ h | exact gas_log2Op _ _ h
            | exact gas_log3Op _ _ h | exact gas_log4Op _ _ h
  | System o =>
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hop
      cases o <;>
        first
        | exact absurd rfl hc1   -- CREATE
        | exact absurd rfl hc2   -- CREATE2
        | exact absurd rfl hc3   -- CALL
        | exact absurd rfl hc4   -- CALLCODE
        | exact absurd rfl hc5   -- DELEGATECALL
        | exact absurd rfl hc6   -- STATICCALL
        | exact gas_inl_selfdestruct _ _ _ h
        | step_arm h
        | step_inline h

/-! ## Item 1b — `EVM.step` debits exactly `gasCost` on the default arm

`EVM.step (f+1) cost (some (w, a)) s`, for any `w` outside the `CREATE`/`CALL`
family, takes the *default* arm: it bumps `execLength`, debits `gasCost` from
`gasAvailable`, and hands off to `EvmYul.step` — which preserves gas
(`gas_EvmYul_step`). Hence the resulting `gasAvailable` is exactly
`s.gasAvailable - gasCost`. This is the `step` half of the `Z → step → X`
gas-decrement chain. -/

set_option maxHeartbeats 4000000 in
theorem gas_EVM_step_default (f : ℕ) (cost : ℕ) (w : Operation) (a : Option (UInt256 × Nat))
    (s s' : State) (hop : ¬ isCallCreate w)
    (h : step (f+1) cost (some (w, a)) s = .ok s') :
    s'.gasAvailable = s.gasAvailable - UInt256.ofNat cost := by
  -- On the default arm, `EVM.step` reduces to
  --   `EvmYul.step w a {s with execLength := s.execLength+1, gasAvailable := s.gasAvailable - cost}`.
  -- We expose that by defeq (`cases w`, excluding the special arms) and apply
  -- `gas_EvmYul_step`; the `execLength` bump and the `- cost` debit are the only state
  -- changes, and `EvmYul.step` keeps `gasAvailable`.
  unfold isCallCreate at hop
  push_neg at hop
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hop
  -- the post-debit state handed to `EvmYul.step`
  set t : State :=
    { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat cost }
    with ht
  have key : ∀ (w' : Operation), ¬ isCallCreate w' →
      EvmYul.step w' a t = .ok s' → s'.gasAvailable = s.gasAvailable - UInt256.ofNat cost := by
    intro w' hw' he
    have := gas_EvmYul_step w' a t s' hw' he
    rw [this, ht]
  -- For every non-call/create `w`, `step (f+1) cost (some (w,a)) s` is defeq to
  -- `EvmYul.step w a t`. We hand `h` to `key` after that defeq coercion.
  apply key w (by unfold isCallCreate; push_neg; exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩)
  -- the defeq: only valid because `w` is not in the special set; `cases w` to let it reduce.
  cases w with
  | StopArith o => cases o <;> exact h
  | CompBit o => cases o <;> exact h
  | Keccak o => cases o <;> exact h
  | Env o => cases o <;> exact h
  | Block o => cases o <;> exact h
  | StackMemFlow o => cases o <;> exact h
  | Push o => cases o <;> exact h
  | Dup o => cases o <;> exact h
  | Exchange o => cases o <;> exact h
  | Log o => cases o <;> exact h
  | System o =>
      cases o <;>
        first
        | exact absurd rfl hc1 | exact absurd rfl hc2 | exact absurd rfl hc3
        | exact absurd rfl hc4 | exact absurd rfl hc5 | exact absurd rfl hc6
        | exact h

/-! ## Item 1c — `Z` gas inversion

`Z` debits the memory-expansion cost `cost₁` (guarded so it cannot underflow), forms
`cost₂ := C'` of the debited state, *guards* `gasAvailable ≥ cost₂`, then (after a
sequence of `if … then .error` validity checks) returns the debited state paired with
`cost₂`. So on a successful `Z`:

* the returned state `s'` is `s` with `gasAvailable` reduced by `cost₁` (hence
  `s'.gasAvailable.toNat ≤ s.gasAvailable.toNat`);
* the returned cost `c` satisfies `c ≤ s'.gasAvailable.toNat` (the `cost₂` guard).

These two facts are exactly what the `X` measure descent needs: after `Z`, the frame
still holds at least `c` gas, and `c = C' s' w ≥ 1` for runnable `w`. -/

set_option maxHeartbeats 1000000 in
theorem Z_ok_cost_le_gas (validJumps : Array UInt256) (w : Operation) (s s' : State) (c : ℕ)
    (h : Z validJumps w s = .ok (s', c)) :
    c ≤ s'.gasAvailable.toNat ∧ c = C' s' w := by
  unfold Z at h
  -- `Z`'s `do` desugars to nested `if guard then throw … else …` over `Except`. The
  -- guards mention the *huge* `memoryExpansionCost`/`C'` terms, which make `split`/`simp`
  -- on the discriminants blow up. We therefore `generalize` the memory-expansion cost to
  -- an opaque `m₁` first; the `C'` term is exposed only after the `cost₁` branch, where we
  -- `generalize` it to `c₂` before splitting on its guard.
  simp only [bind, Except.bind] at h
  -- Make the two heavy discriminants (`memoryExpansionCost`, `C'`) opaque, and decide the
  -- two gas guards with `by_cases` + `simp only [if_pos/if_neg]` (so we never invoke
  -- `split`/`split_ifs`' discriminant-simp, which blows up on those terms). The `cost₁`
  -- guard must be true→`.error` (contradiction) so we are in its `else`; likewise `cost₂`.
  generalize hm : memoryExpansionCost s w = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact Except.noConfusion h
  · rw [if_neg hg1] at h
    generalize hc : C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } w = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } : State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact Except.noConfusion h
    · rw [if_neg hg2] at h
      -- `h` now runs through the remaining validity `if`s to `.ok (s_debited, c₂)`.
      repeat' first
        | (have hp := Except.ok.inj h
           rw [Prod.mk.injEq] at hp
           obtain ⟨rfl, rfl⟩ := hp
           exact ⟨Nat.le_of_not_lt hg2, hc.symm⟩)
        | exact Except.noConfusion h
        | split at h

/-! ## Item 2 — `X` measure descent

Subtracting a positive cost `c ≤ g.toNat` from a `UInt256` gas word strictly lowers
its `.toNat` (no wraparound, since `c ≤ g.toNat`). Then a non-halting `X` iteration —
which runs a runnable opcode (`H = none` ⇒ not `STOP`/`RETURN`/`REVERT`/`SELFDESTRUCT`,
and `step` succeeding ⇒ not `INVALID`), debiting `cost₂ = C' s₁ w ≥ 1` — lands in a
state with strictly less gas. Hence gas is a genuine well-founded measure on the loop. -/

/-- `UInt256` subtraction of a positive, non-underflowing cost strictly drops `.toNat`. -/
theorem gas_sub_lt (g : UInt256) (c : ℕ) (hle : c ≤ g.toNat) (hpos : 1 ≤ c) (hc : c < UInt256.size) :
    (g - UInt256.ofNat c).toNat < g.toNat := by
  have hgsz : g.val.val < UInt256.size := g.val.isLt
  have hle' : c ≤ g.val.val := hle
  have hcmod : (Fin.ofNat UInt256.size c).val = c := by
    simp only [Fin.ofNat, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hc
  have hsub : (g - UInt256.ofNat c).toNat = g.toNat - c := by
    show ((g.val - (Fin.ofNat _ c))).val = g.val.val - c
    rw [Fin.sub_def, hcmod]
    -- the surviving expression is `(size - c + g.val.val) % size`; it equals
    -- `((g.val.val - c) + size) % size = (g.val.val - c) % size = g.val.val - c`.
    show (UInt256.size - c + g.val.val) % UInt256.size = g.val.val - c
    have hrw : UInt256.size - c + g.val.val = (g.val.val - c) + UInt256.size := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hsub]; omega

/-- `H` returns `none` (the recursing branch of `X`) exactly off the halting set
`{STOP, RETURN, REVERT, SELFDESTRUCT}`. -/
theorem H_none_not_halt (μ : MachineState) (w : Operation) (h : H μ w = none) :
    w ≠ .STOP ∧ w ≠ .RETURN ∧ w ≠ .REVERT ∧ w ≠ .SELFDESTRUCT := by
  unfold H at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rintro rfl; simp_all)

/-- `INVALID`'s `EVM.step` (default arm) errors, so a successful `step` rules it out. -/
theorem step_invalid_error (f cost : ℕ) (a : Option (UInt256 × Nat)) (s s' : State)
    (h : step (f+1) cost (some (.INVALID, a)) s = .ok s') : False := by
  -- defeq: `step (f+1) cost (some (.INVALID,a)) s = EvmYul.step .INVALID a {…} = .error _`.
  have h2 : (.error .InvalidInstruction : Except EVM.ExecutionException State) = .ok s' := h
  exact absurd h2 (by simp)

/-- **`X` measure descent (item 2).** A non-halting `X (f+1)` iteration — `Z` succeeds
with cost `cost₂`, `step` (default arm, `w` not in the `CREATE`/`CALL` family) succeeds,
and `H = none` (so the loop recurses) — lands in a state with *strictly less* gas. The
cornerstone `C'_pos_of_runnable` supplies `1 ≤ cost₂`; `Z_ok_cost_le_gas` supplies
`cost₂ ≤ s₁.gasAvailable.toNat`; `gas_EVM_step_default` + `gas_sub_lt` close it. -/
theorem X_iter_gas_lt (f cost₂ : ℕ) (validJumps : Array UInt256) (w : Operation)
    (a : Option (UInt256 × Nat)) (s s₁ s₂ : State)
    (hw : ¬ isCallCreate w)
    (hZ : Z validJumps w s = .ok (s₁, cost₂))
    (hstep : step (f+1) cost₂ (some (w, a)) s₁ = .ok s₂)
    (hH : H s₂.toMachineState w = none) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  -- `w` is runnable: `H = none` ⇒ not STOP/RETURN/REVERT/SELFDESTRUCT; `step` succeeds
  -- ⇒ not INVALID.
  obtain ⟨h1, h2, h3, h4⟩ := H_none_not_halt s₂.toMachineState w hH
  have h5 : w ≠ .INVALID := by rintro rfl; exact step_invalid_error f cost₂ a s₁ s₂ hstep
  have hrun : runnable w := ⟨h1, h2, h3, h4, h5⟩
  -- `cost₂ = C' s₁ w ≥ 1`, and `cost₂ ≤ s₁.gas`.
  obtain ⟨hle, hcost⟩ := Z_ok_cost_le_gas validJumps w s s₁ cost₂ hZ
  have hpos : 1 ≤ cost₂ := by rw [hcost]; exact C'_pos_of_runnable s₁ w hrun
  -- `step` debits exactly `cost₂`.
  have hgas : s₂.gasAvailable = s₁.gasAvailable - UInt256.ofNat cost₂ :=
    gas_EVM_step_default f cost₂ w a s₁ s₂ hw hstep
  rw [hgas]
  exact gas_sub_lt s₁.gasAvailable cost₂ hle hpos
    (Nat.lt_of_le_of_lt hle s₁.gasAvailable.val.isLt)

/-! ## Item 3 (down-payment) — child gas is carved from the parent

The gas a frame forwards to a child (`Ccallgas`) is bounded by the parent's own gas.
The core inequality is `Cgascap ≤ parent gas`: in the branch where the parent can
cover the call's `Cextra`, `Cgascap = min (L (gas − extra)) g ≤ L (gas − extra)
≤ gas − extra ≤ gas`. This is the genuinely-nested analogue of exp003's flat
`gasFundsDescent`. (The full cross-layer threading through the `call`/`Θ`/`Ξ` arms —
including the `Gcallstipend` top-up and the `depth e+1 ≤ 1024` cap — is the remaining
item-3 work, documented in PLAN.md.) -/

theorem L_le (n : ℕ) : L n ≤ n := by unfold L; omega

theorem Cgascap_le_gas (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    Cgascap t r val g σ μ A ≤ μ.gasAvailable.toNat ∨ Cgascap t r val g σ μ A ≤ g.toNat := by
  unfold Cgascap
  split
  · rename_i hge
    left
    calc min (L (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat
        ≤ L (μ.gasAvailable.toNat - Cextra t r val σ A) := min_le_left _ _
      _ ≤ μ.gasAvailable.toNat - Cextra t r val σ A := L_le _
      _ ≤ μ.gasAvailable.toNat := Nat.sub_le _ _
  · right; exact le_refl _

/-- `Cgascap ≤ g.toNat` always (both branches cap at `g`). The forwarded gas is also
bounded by the cap `g` passed to the call (= the `gas` stack argument, already an
`UInt256` so `< UInt256.size`). -/
theorem Cgascap_le_cap (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    Cgascap t r val g σ μ A ≤ g.toNat := by
  unfold Cgascap
  split
  · exact min_le_right _ _
  · exact le_refl _

/-! ### Item 3 — child gas is bounded by the parent's available gas (with the stipend)

The gas a `CALL`-family frame forwards to its child is `Ccallgas`, which is
`Cgascap` plus (when `val ≠ 0`) the `Gcallstipend` top-up. The stipend is only ever
added when value is transferred, and the value-transfer cost `Cxfer = Gcallvalue =
9000` (paid out of the parent's gas as part of `Cextra ≤` the parent's gas in the
`Cgascap` branch) dominates the stipend `2300`. Hence the child's forwarded gas is
bounded by the parent's available gas (`Cgascap` branch) — the genuinely-nested
analogue of exp003's flat `gasFundsDescent`. -/

/-- When the stipend is added (`val ≠ 0`), the parent paid `Cxfer = Gcallvalue` as
part of `Cextra`; that cost dominates the stipend. So even with the stipend,
`Ccallgas ≤ μ.gasAvailable.toNat` in the branch where the parent can cover `Cextra`. -/
theorem Ccallgas_le_gas_of_cover (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate)
    (hcover : μ.gasAvailable.toNat ≥ Cextra t r val σ A) :
    Ccallgas t r val g σ μ A ≤ μ.gasAvailable.toNat := by
  -- `Cgascap` (in the cover branch) `= min (L (gas - Cextra)) g ≤ gas - Cextra`.
  have hcap : Cgascap t r val g σ μ A ≤ μ.gasAvailable.toNat - Cextra t r val σ A := by
    unfold Cgascap; rw [if_pos hcover]
    exact le_trans (min_le_left _ _) (L_le _)
  -- `Cextra ≥ Cxfer`.
  have hextra_xfer : Cxfer val ≤ Cextra t r val σ A := by unfold Cextra; omega
  -- Case on the `Fin` value of `val`, which simultaneously decides the `Ccallgas`
  -- `⟨0⟩`-match and the `Cxfer` `!=`-guard (both reduce to `val.val == 0`).
  obtain ⟨⟨n, hn⟩⟩ := val
  cases n with
  | zero =>
    -- val = ⟨0⟩: `Ccallgas = Cgascap ≤ gas - Cextra ≤ gas`.
    show Cgascap t r _ g σ μ A ≤ μ.gasAvailable.toNat
    exact le_trans hcap (Nat.sub_le _ _)
  | succ k =>
    -- val ≠ 0: `Ccallgas = Cgascap + Gcallstipend`; `Cxfer val = Gcallvalue = 9000 ≥
    -- Gcallstipend = 2300`, with `Cgascap ≤ gas - Cextra ≤ gas - Cxfer`.
    -- The `!=`/match both reduce to the underlying `Nat.beq (k+1) 0 = false` (`rfl`).
    have hxfer : Cxfer ⟨⟨k+1, hn⟩⟩ = Gcallvalue := rfl
    have hstip : Gcallstipend ≤ Cxfer ⟨⟨k+1, hn⟩⟩ := by rw [hxfer]; decide
    have hcgcap : Cgascap t r ⟨⟨k+1, hn⟩⟩ g σ μ A ≤ μ.gasAvailable.toNat - Cxfer ⟨⟨k+1, hn⟩⟩ :=
      le_trans hcap (Nat.sub_le_sub_left hextra_xfer _)
    -- goal: `Ccallgas … = Cgascap … + Gcallstipend ≤ gas`.
    show Cgascap t r _ g σ μ A + Gcallstipend ≤ μ.gasAvailable.toNat
    omega

/-- The depth bound: `call`'s recursion into `Θ` is gated by `Iₑ < 1024`, so the
child's depth `e = Iₑ + 1 ≤ 1024`. (Structural fact about the `call` guard — the
descent never increases depth beyond `1024`.) -/
theorem call_depth_bound (Iₑ : ℕ) (h : Iₑ < 1024) : Iₑ + 1 ≤ 1024 := h

/-! ## Item 4 (setup) — the cross-layer propagation lemmas

`OutOfFuel` is emitted *directly* only at the five fuel-`0` base cases (proved
above). At a successor `fuel`, each layer either returns without recursing (never
`OutOfFuel`) or hands off to a sub-layer; in every such hand-off the `OutOfFuel`
case is *propagated*, never created. These propagation lemmas reduce each layer's
non-`OutOfFuel`-ness at `fuel+1` to that of the sub-layers it calls — the inductive
step skeleton for the final mutual induction. -/

/-- `Ξ (f+1)` propagates `OutOfFuel` only from its inner `X f`. If that `X f` is not
`OutOfFuel`, neither is `Ξ (f+1)`. (The post-processing match on `X`'s
`.success`/`.revert` result never emits `OutOfFuel`.) -/
theorem Ξ_outOfFuel_of (f : ℕ)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hX : ∀ s : State, X f (D_J I.code ⟨0⟩) s ≠ .error .OutOfFuel) :
    Ξ (f+1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I ≠ .error .OutOfFuel := by
  unfold Ξ
  simp only []
  -- the freshly-built child state
  set s0 : EVM.State := _ with hs0
  -- `Ξ (f+1) = do let result ← X f …; match result …`. Case on `X f`.
  cases hr : X f (D_J I.code ⟨0⟩) s0 with
  | error e =>
    -- propagated error: it equals `e`, and `e ≠ OutOfFuel` by `hX`.
    intro hc
    have : e = EVM.ExecutionException.OutOfFuel := by
      simp only [hr, bind, Except.bind] at hc
      exact (Except.error.inj hc)
    exact hX s0 (by rw [hr, this])
  | ok r =>
    -- success: the trailing match yields `.ok …` in both `.success`/`.revert` arms.
    simp only [hr, bind, Except.bind]
    cases r <;> simp

/-- `Θ (fuel+1)` on a **`Code`** call propagates `OutOfFuel` only from its inner
`Ξ fuel` (the explicit `if e == .OutOfFuel then throw .OutOfFuel` re-throw): any
other `Ξ`-error is swallowed into a `pure`, and on success the trailing `.ok` makes
`Θ` an `.ok`. So if `Ξ fuel … ≠ OutOfFuel`, neither is `Θ (fuel+1)`.

The **precompiled** path (`c = .Precompiled _`) never recurses and never emits
`OutOfFuel` — every arm of the 10-way numeric match is `.ok`, and the `_ => default`
fallthrough is `.ok default` (the `Inhabited (Except ε α)` instance is `.ok default`).
That case is a separate, non-recursive obligation: it is term-size-heavy (the
`Θ.eq` equation lemmas for `.Precompiled` are enormous) and the literal-pattern
`match pc with | 1 => … | 10 => …` makes `split` generate unprovable
`pc = n → False` exhaustiveness side-goals. It is documented in PLAN.md, not faked. -/
theorem Θ_outOfFuel_of (fuel : ℕ) (bvh : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (code : ByteArray)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (hΞ : ∀ (σ₁ : AccountMap) (I : ExecutionEnv),
      Ξ fuel createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I ≠ .error .OutOfFuel) :
    Θ (fuel+1) bvh createdAccounts genesisBlockHeader blocks σ σ₀ A s o r (.Code code)
        g p v v' d e Hd w ≠ .error .OutOfFuel := by
  -- The `Code` path's bound value comes from matching `Ξ fuel …`; an `OutOfFuel`
  -- there is re-thrown, any other error is swallowed into `pure`, and on success the
  -- trailing `.ok` makes `Θ` an `.ok`. (See `Θ_precompiled_never_outOfFuel` for the
  -- non-recursive precompiled path.)
  simp only [Θ, bind, Except.bind]
  set I : ExecutionEnv := _ with hI
  set σ₁ : AccountMap := _ with hσ₁
  cases hr : Ξ fuel createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I with
  | error ee =>
    -- `if ee == OutOfFuel then throw OutOfFuel else pure …`. If we ended at
    -- OutOfFuel, then `ee = OutOfFuel`, contradicting `hΞ`.
    by_cases hee : ee = EVM.ExecutionException.OutOfFuel
    · exact absurd (hee ▸ hr) (hΞ σ₁ I)
    · -- ee ≠ OutOfFuel ⇒ the `if` takes the `else` (`pure`), so result is `.ok`.
      have hb : (ee == EVM.ExecutionException.OutOfFuel) = false := by
        cases ee <;> first | rfl | exact absurd rfl hee
      simp only [hb, if_false, Bool.false_eq_true]
      intro hc; exact Except.noConfusion hc
  | ok res =>
    -- success/revert both `pure`, then trailing `.ok`.
    rcases res with ⟨g', o⟩ | ⟨⟨⟨a, b⟩, cc, dd⟩, o⟩ <;>
      (intro hc; exact Except.noConfusion hc)

end EvmYul.EVM.NeverOutOfFuel
