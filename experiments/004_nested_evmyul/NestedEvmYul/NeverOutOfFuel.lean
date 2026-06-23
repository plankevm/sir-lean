import EvmYul.EVM.Semantics
import Mathlib.Tactic.FinCases
import NestedEvmYul.GasArith
import NestedEvmYul.PrecompileGas

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


-- `gas_sub_le` (UInt256 subtraction of a non-underflowing cost does not increase `.toNat`,
-- the `≤` companion of `gas_sub_lt`) now lives in `NestedEvmYul.GasArith` (shared with the
-- precompile gas bricks), imported above.

set_option maxHeartbeats 2000000 in
/-- A successful `Z` returns a state whose gas does not exceed the input's: `Z`
debits the (non-underflowing) memory-expansion cost `cost₁` and leaves `gasAvailable`
otherwise untouched. This is the non-strict gas bound the `X`-loop induction needs to
chain `ev.gas ≤ s.gas` with the strict per-iteration drop (`X_iter_gas_lt`). -/
theorem Z_ok_state (vj : Array UInt256) (w : Operation) (s s' : State) (c : ℕ)
    (h : Z vj w s = .ok (s', c)) :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  unfold Z at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  generalize hm : memoryExpansionCost s w = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact absurd h (by simp)
  · rw [if_neg hg1] at h
    generalize hcc : C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } w = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } : State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact absurd h (by simp)
    · rw [if_neg hg2] at h
      have hs' : s'.gasAvailable = s.gasAvailable - UInt256.ofNat m₁ := by
        revert h
        split_ifs <;> intro h <;>
          first
          | (have hp := Except.ok.inj h; rw [Prod.mk.injEq] at hp
             obtain ⟨rfl, _⟩ := hp; rfl)
          | exact absurd h (by simp)
      rw [hs']
      exact gas_sub_le s.gasAvailable m₁ (Nat.le_of_not_lt hg1)
        (Nat.lt_of_le_of_lt (Nat.le_of_not_lt hg1) s.gasAvailable.val.isLt)

set_option maxHeartbeats 2000000 in
/-- A successful `Z` preserves `pc` and the execution-env `code` (it only rewrites
`gasAvailable`). Needed so the `X` loop's decoded opcode (decoded from the pre-`Z`
state) is also the opcode at the post-`Z` step-state. -/
theorem Z_ok_code_pc (vj : Array UInt256) (w : Operation) (s s' : State) (c : ℕ)
    (h : Z vj w s = .ok (s', c)) :
    s'.toState.executionEnv.code = s.toState.executionEnv.code ∧ s'.pc = s.pc := by
  unfold Z at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  generalize hm : memoryExpansionCost s w = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact absurd h (by simp)
  · rw [if_neg hg1] at h
    generalize hcc : C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } w = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } : State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact absurd h (by simp)
    · rw [if_neg hg2] at h
      have hs' : s' = { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } := by
        revert h
        split_ifs <;> intro h <;>
          first
          | (have hp := Except.ok.inj h; rw [Prod.mk.injEq] at hp
             obtain ⟨rfl, _⟩ := hp; rfl)
          | exact absurd h (by simp)
      rw [hs']; exact ⟨rfl, rfl⟩

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

set_option maxHeartbeats 2000000 in
/-- `Z` never emits `OutOfFuel`: every error arm is `OutOfGass`/`InvalidInstruction`/
`StackUnderflow`/`BadJumpDestination`/`InvalidMemoryAccess`/`StackOverflow`/
`StaticModeViolation`, and the final result is `.ok`. (We `generalize` the heavy
`memoryExpansionCost`/`C'` discriminants opaque so `split` does not blow up — the same
technique as `Z_ok_cost_le_gas`.) -/
theorem Z_never_outOfFuel (vj : Array UInt256) (w : Operation) (s : State)
    (h : Z vj w s = .error .OutOfFuel) : False := by
  unfold Z at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  generalize memoryExpansionCost s w = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact absurd h (by simp)
  · rw [if_neg hg1] at h
    generalize C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } w = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } : State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact absurd h (by simp)
    · rw [if_neg hg2] at h
      split_ifs at h <;> exact absurd h (by simp)

/-- **`X` propagation skeleton.** `X (f+1) vj s` emits `OutOfFuel` only from the
per-instruction `step f …` or the loop tail `X f …`: the decode/`Z` prelude never
emits `OutOfFuel` (`Z_never_outOfFuel`), the `H = some` halts are `.ok`. So if every
`step f …` and every `X f …` is not `OutOfFuel`, neither is `X (f+1)`. (This is the
*propagation* half; the inner loop-induction that discharges `hX` from gas is
`X_no_outOfFuel` below.) -/
theorem X_outOfFuel_of (f : ℕ) (vj : Array UInt256) (s : State)
    (hstep : ∀ (w : Operation) (arg) (cost : ℕ) (s2 : State),
       step f cost (some (w, arg)) s2 ≠ .error .OutOfFuel)
    (hX : ∀ s2 : State, X f vj s2 ≠ .error .OutOfFuel) :
    X (f+1) vj s ≠ .error .OutOfFuel := by
  unfold X
  simp only [bind, Except.bind]
  set instr := decode s.toState.executionEnv.code s.pc |>.getD (.STOP, .none) with hinstr
  cases hZ : Z vj instr.1 s with
  | error e =>
    intro hc
    have : e = EVM.ExecutionException.OutOfFuel := by
      revert hc; simp only [hZ]; intro hc; exact Except.error.inj hc
    exact Z_never_outOfFuel vj instr.1 s (by rw [hZ, this])
  | ok p =>
    obtain ⟨ev, cost₂⟩ := p
    simp only [hZ]
    cases hs : step f cost₂ instr ev with
    | error e =>
      intro hc
      have he : e = EVM.ExecutionException.OutOfFuel := by
        revert hc; simp only [hs]; intro hc; exact Except.error.inj hc
      rw [he] at hs
      exact hstep instr.1 instr.2 cost₂ ev hs
    | ok ev' =>
      simp only [hs]
      cases hH : H ev'.toMachineState instr.1 with
      | none => exact hX ev'
      | some o =>
        by_cases hrev : (instr.1 == Operation.REVERT) = true
        · rw [hrev]; intro hc; nomatch hc
        · simp only [hrev, Bool.false_eq_true, if_false]
          intro hc; nomatch hc

/-! ### The `X` inner loop-induction (the genuinely hard piece — DONE for
non-call/create frames)

`X` is the only layer whose recursion is a *loop* over its own fuel (the loop tail
`X f vj ev'` reuses the frame). Propagation alone (`X_outOfFuel_of`) is not enough:
it reduces `X (f+1)` to `X f` on a *successor* state, so a naive fuel induction never
bottoms out. The measure that does bottom out is **gas**: every non-halting
iteration burns `≥ 1` gas (`X_iter_gas_lt`, via the cornerstone `C'_pos_of_runnable`),
and `Z` never increases gas (`Z_ok_state`). So once `fuel > gasAvailable`, the loop
*must* halt (or error non-`OutOfFuel`) before fuel runs out.

`X_loop_noncallcreate` proves exactly this for a frame whose code never decodes to a
`CREATE`/`CALL`-family opcode (the hypothesis `hnc`) — i.e. a *single* frame with no
nested descent. The induction is on `fuel`; at `fuel = f+1` with `gas < f+1` (so
`gas ≤ f`), one iteration lands at `ev'` with `ev'.gas < ev.gas ≤ s.gas ≤ f`, so the
IH at `f` applies (the successor's gas is `< f`). This is the complete inner
loop-induction; the only thing it assumes about the rest of the recursion is
`hstep` (every `step f` is non-`OutOfFuel`), which the final mutual induction
supplies. For frames that *do* call/create, the same gas measure works (a call
iteration still strictly burns `Cextra ≥ 1` net, since the child returns
`g' ≤ Cgascap = cost₂ − Cextra`), but threading that through the mutual
`call`/`Θ`/`Ξ` descent is the remaining assembly work (see end of file). -/
theorem X_loop_noncallcreate (vj : Array UInt256)
    (hnc : ∀ (s2 : State),
      ¬ isCallCreate (decode s2.toState.executionEnv.code s2.pc |>.getD (.STOP, .none)).1)
    (hstep : ∀ (f : ℕ) (w : Operation) (arg) (cost : ℕ) (s2 : State),
       ¬ isCallCreate w → step (f+1) cost (some (w, arg)) s2 ≠ .error .OutOfFuel) :
    ∀ (fuel : ℕ) (s : State), s.gasAvailable.toNat + 1 < fuel → X fuel vj s ≠ .error .OutOfFuel := by
  intro fuel
  induction fuel with
  | zero => intro s hlt; omega
  | succ f ih =>
    intro s hlt
    -- `gas + 1 < f + 1` ⇒ `gas < f`, so `f ≥ 1`: write `f = f'+1`.
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    unfold X
    simp only [bind, Except.bind]
    set instr := decode s.toState.executionEnv.code s.pc |>.getD (.STOP, .none) with hinstr
    have hncs : ¬ isCallCreate instr.1 := hnc s
    cases hZ : Z vj instr.1 s with
    | error e =>
      intro hc
      have : e = EVM.ExecutionException.OutOfFuel := by
        revert hc; simp only [hZ]; intro hc; exact Except.error.inj hc
      exact Z_never_outOfFuel vj instr.1 s (by rw [hZ, this])
    | ok p =>
      obtain ⟨ev, cost₂⟩ := p
      simp only [hZ]
      have hevle : ev.gasAvailable.toNat ≤ s.gasAvailable.toNat := Z_ok_state vj instr.1 s ev cost₂ hZ
      -- the per-instruction step is at fuel `f'+1 ≥ 1`, so it never `OutOfFuel`s.
      cases hs : step (f'+1) cost₂ instr ev with
      | error e =>
        intro hc
        have he : e = EVM.ExecutionException.OutOfFuel := by
          revert hc; simp only [hs]; intro hc; exact Except.error.inj hc
        rw [he] at hs; exact hstep f' instr.1 instr.2 cost₂ ev hncs hs
      | ok ev' =>
        simp only [hs]
        cases hH : H ev'.toMachineState instr.1 with
        | none =>
          -- recurse `X (f'+1) vj ev'`; the loop tail's fuel is `f'+1` and the
          -- successor's gas strictly dropped, so `ev'.gas + 1 < f'+1`.
          have hlt2 : ev'.gasAvailable.toNat < ev.gasAvailable.toNat :=
            X_iter_gas_lt f' cost₂ vj instr.1 instr.2 s ev ev' hncs hZ hs hH
          apply ih ev'
          omega
        | some o =>
          by_cases hrev : (instr.1 == Operation.REVERT) = true
          · rw [hrev]; intro hc; nomatch hc
          · simp only [hrev, Bool.false_eq_true, if_false]; intro hc; nomatch hc

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

/-- Gas-aware refinement of `Ξ_outOfFuel_of`: the inner `X` is only ever run on the
freshly-built child state, whose `gasAvailable` is exactly `g`. So it suffices to know
`X f` is not `OutOfFuel` on states with `gasAvailable = g` (not all states). This is
what lets the gas bound thread through the descent. -/
theorem Ξ_outOfFuel_of_gas (f : ℕ)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hX : ∀ s : State, s.gasAvailable = g → X f (D_J I.code ⟨0⟩) s ≠ .error .OutOfFuel) :
    Ξ (f+1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I ≠ .error .OutOfFuel := by
  unfold Ξ
  simp only []
  cases hr : X f (D_J I.code ⟨0⟩) ({ (default : EVM.State) with accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A, createdAccounts := createdAccounts, gasAvailable := g, blocks := blocks, genesisBlockHeader := genesisBlockHeader }) with
  | error e =>
    intro hc
    have : e = EVM.ExecutionException.OutOfFuel := by
      simp only [hr, bind, Except.bind] at hc
      exact (Except.error.inj hc)
    exact hX _ rfl (by rw [hr, this])
  | ok r =>
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

set_option maxHeartbeats 8000000 in
/-- **The precompiled `Θ`-arm (DONE).** `Θ (fuel+1) … (.Precompiled pc) …` is
non-recursive and never `OutOfFuel`: every arm of the 10-way numeric match is `.ok`
(each precompile returns a numeric result), and the `_ => default` fallthrough is
`.ok default`. The `Θ.eq` equation lemmas for `.Precompiled` are enormous (so
`simp only [Θ]` deep-recurses; we use `dsimp only [Θ]`), and the literal-pattern
`match pc with | 1 … | 10 …` makes a naive `split` emit unprovable `pc = n → False`
exhaustiveness side-goals. The bespoke reduction keeps `hc` in scope across the
`split` (no `revert`) and drills nested `if`/`match` with `repeat' split at hc`,
closing every `.ok …`-headed leaf by `nomatch hc`. -/
theorem Θ_precompiled_never_outOfFuel (fuel : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (pc : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool) :
    Θ (fuel+1) bvh cA gh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e Hd w
      ≠ .error .OutOfFuel := by
  intro hc
  dsimp only [Θ] at hc
  simp only [pure, Except.pure, bind, Except.bind] at hc
  split at hc <;> (repeat' first | nomatch hc | split at hc)

/-- `call (f+1)` emits `OutOfFuel` only via its inner `Θ f` (taken in the
balance/depth `if`-branch). The `else` branch and all the post-call state assembly
are pure `.ok`. So if every `Θ f …` (for whatever `c = toExecute σ t` the call
forms) is not `OutOfFuel`, neither is `call (f+1)`. -/
theorem call_outOfFuel_of (f : ℕ) (gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (s : EVM.State)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (g p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool),
          Θ f bvh cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c g p vv vv' dd e Hd w
            ≠ .error .OutOfFuel) :
    call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize outOffset outSize
      permission s ≠ .error .OutOfFuel := by
  simp only [call, bind, Except.bind]
  split
  · -- if-branch (can transfer value, depth < 1024): matches `Θ f …`.
    split
    · -- `Θ f = .error err`: the bind makes `call = .error err`. If `err = OutOfFuel`
      -- that contradicts `hΘ`; so `err ≠ OutOfFuel`.
      rename_i err heq
      intro hc
      have herr : err = EVM.ExecutionException.OutOfFuel := Except.error.inj hc
      exact (hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (herr ▸ heq)
    · intro hc; exact Except.noConfusion hc
  · -- else-branch: the call result is assembled as `.ok …`.
    intro hc; exact Except.noConfusion hc

/-- `Lambda (f+1)` (contract creation, `CREATE`/`CREATE2`) emits `OutOfFuel` only
via its inner `Ξ f` re-throw (same `if e == .OutOfFuel then throw .OutOfFuel` shape
as `Θ`'s `Code` arm). The leading `L_A` address-derivation lift only ever errors as
`.StackUnderflow` (the `MonadLift Option (Except …)` instance), and on `Ξ` success
the result is assembled as `.ok`. So if `Ξ f … ≠ OutOfFuel`, neither is
`Lambda (f+1)`. -/
theorem Lambda_outOfFuel_of (f : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress) (g p v : UInt256)
    (i : ByteArray) (e : UInt256) (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool)
    (hΞ : ∀ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (As : Substate)
            (I : ExecutionEnv),
          Ξ f cA' gh blocks σ' σ₀ g As I ≠ .error .OutOfFuel) :
    Lambda (f+1) bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w ≠ .error .OutOfFuel := by
  simp only [Lambda, bind, Except.bind]
  -- case on the `L_A` address lift: `none` ⇒ the lift is `.error StackUnderflow`.
  cases hla : Lambda.L_A s (Option.option (⟨0⟩ : UInt256) (·.nonce) (σ.find? s) - ⟨1⟩) ζ i with
  | none => intro hc; exact absurd (Except.error.inj hc) (fun h => by cases h)
  | some lₐ =>
    split
    · -- lift `.error`: impossible since `liftM (some lₐ) = .ok lₐ`.
      rename_i heqx; exact absurd heqx (fun h => by cases h)
    · -- lift `.ok`: split the `Ξ f` result (`.error` re-throw / `.revert` / `.success`).
      split
      · rename_i err heq
        by_cases hee : err = EVM.ExecutionException.OutOfFuel
        · exact absurd (hee ▸ heq) (hΞ _ _ _ _)
        · have hb : (err == EVM.ExecutionException.OutOfFuel) = false := by
            cases err <;> first | rfl | exact absurd rfl hee
          simp only [hb, if_false, Bool.false_eq_true]
          intro hc; exact Except.noConfusion hc
      -- `Ξ = .ok (.revert …)` and `Ξ = .ok (.success …)`: both assemble to `.ok …`.
      all_goals (intro hc; exact Except.noConfusion hc)

/-! ## Item 4a — `EvmYul.step` never emits `OutOfFuel`

The shared interpreter `EvmYul.step` mentions `OutOfFuel` nowhere (a `grep` over
`EvmYul/Semantics.lean` returns zero hits): every arm returns `.ok …`, `.error
.StackUnderflow`, or `.error .InvalidInstruction`, and even the `_ => default`
fallthrough is `.ok default` (the `Inhabited (Except ε α)` instance is `.ok`). We
make that precise with a per-opcode sweep mirroring `gas_EvmYul_step` (no
re-elaboration of the 140-arm `match`; each arm is closed by defeq to a combinator
or inline `noOOF` lemma). This is the `EvmYul.step` base fact for the `step`
skeleton's default arm. -/

local macro "nooof_comb" defn:ident : tactic =>
  `(tactic| (unfold $defn; first | (split <;> simp [Id.run]) | simp [Id.run]))

theorem noOOF_execUnOp (f : Primop.Unary) (s : State) : EVM.execUnOp f s ≠ .error .OutOfFuel := by nooof_comb EVM.execUnOp
theorem noOOF_execBinOp (f : Primop.Binary) (s : State) : EVM.execBinOp f s ≠ .error .OutOfFuel := by nooof_comb EVM.execBinOp
theorem noOOF_execTriOp (f : Primop.Ternary) (s : State) : EVM.execTriOp f s ≠ .error .OutOfFuel := by nooof_comb EVM.execTriOp
theorem noOOF_execQuadOp (f : Primop.Quaternary) (s : State) : EVM.execQuadOp f s ≠ .error .OutOfFuel := by nooof_comb EVM.execQuadOp
theorem noOOF_executionEnvOp (op) (s : State) : EVM.executionEnvOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.executionEnvOp
theorem noOOF_unaryExecutionEnvOp (op) (s : State) : EVM.unaryExecutionEnvOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.unaryExecutionEnvOp
theorem noOOF_machineStateOp (op) (s : State) : EVM.machineStateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.machineStateOp
theorem noOOF_stateOp (op) (s : State) : EVM.stateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.stateOp
theorem noOOF_unaryStateOp (op) (s : State) : EVM.unaryStateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.unaryStateOp
theorem noOOF_binaryStateOp (op) (s : State) : EVM.binaryStateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.binaryStateOp
theorem noOOF_binaryMachineStateOp (op) (s : State) : EVM.binaryMachineStateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.binaryMachineStateOp
theorem noOOF_binaryMachineStateOp' (op) (s : State) : EVM.binaryMachineStateOp' op s ≠ .error .OutOfFuel := by nooof_comb EVM.binaryMachineStateOp'
theorem noOOF_ternaryMachineStateOp (op) (s : State) : EVM.ternaryMachineStateOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.ternaryMachineStateOp
theorem noOOF_ternaryCopyOp (op) (s : State) : EVM.ternaryCopyOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.ternaryCopyOp
theorem noOOF_quaternaryCopyOp (op) (s : State) : EVM.quaternaryCopyOp op s ≠ .error .OutOfFuel := by nooof_comb EVM.quaternaryCopyOp
theorem noOOF_log0Op (s : State) : EVM.log0Op s ≠ .error .OutOfFuel := by nooof_comb EVM.log0Op
theorem noOOF_log1Op (s : State) : EVM.log1Op s ≠ .error .OutOfFuel := by nooof_comb EVM.log1Op
theorem noOOF_log2Op (s : State) : EVM.log2Op s ≠ .error .OutOfFuel := by nooof_comb EVM.log2Op
theorem noOOF_log3Op (s : State) : EVM.log3Op s ≠ .error .OutOfFuel := by nooof_comb EVM.log3Op
theorem noOOF_log4Op (s : State) : EVM.log4Op s ≠ .error .OutOfFuel := by nooof_comb EVM.log4Op
theorem noOOF_dup (n : ℕ) (s : State) : EvmYul.dup n s ≠ .error .OutOfFuel := by
  unfold EvmYul.dup; simp only []; split <;> simp
theorem noOOF_swap (n : ℕ) (s : State) : EvmYul.swap n s ≠ .error .OutOfFuel := by
  unfold EvmYul.swap; simp only []; split <;> simp

theorem noOOF_push (op : Operation.POp) (arg) (s : State) :
    EvmYul.step (.Push op) arg s ≠ .error .OutOfFuel := by
  cases op with
  | PUSH0 =>
    intro h
    have h2 : (.ok (s.replaceStackAndIncrPC (s.stack.push ⟨0⟩)) : Except EVM.ExecutionException State)
              = .error .OutOfFuel := h
    exact Except.noConfusion h2
  | _ =>
    all_goals (
      cases arg with
      | none =>
        intro h
        have h2 : (.error .StackUnderflow : Except EVM.ExecutionException State) = .error .OutOfFuel := h
        exact absurd h2 (by simp)
      | some p =>
        obtain ⟨a, w⟩ := p; intro h
        have h2 : (.ok (s.replaceStackAndIncrPC (s.stack.push a) w.succ)
                    : Except EVM.ExecutionException State) = .error .OutOfFuel := h
        exact Except.noConfusion h2)

theorem noOOF_inl_pop (arg) (s : State) : EvmYul.step (.StackMemFlow .POP) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (match s.stack.pop with
              | some ⟨st, _⟩ => (.ok (s.replaceStackAndIncrPC st) : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  revert h2; split <;> (intro h2; exact absurd h2 (by simp))

theorem noOOF_inl_mload (arg) (s : State) : EvmYul.step (.StackMemFlow .MLOAD) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (match s.stack.pop with
              | some ⟨st, μ₀⟩ =>
                (.ok (({s with toMachineState := (s.toMachineState.mload μ₀).2}).replaceStackAndIncrPC
                        (st.push (s.toMachineState.mload μ₀).1)) : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  revert h2; split <;> (intro h2; exact absurd h2 (by simp))

theorem noOOF_inl_returndatacopy (arg) (s : State) :
    EvmYul.step (.Env .RETURNDATACOPY) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (match s.stack.pop3 with
              | some ⟨st, μ₀, μ₁, μ₂⟩ =>
                (.ok (({s with toMachineState := s.toMachineState.returndatacopy μ₀ μ₁ μ₂}).replaceStackAndIncrPC
                        st) : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  revert h2; split <;> (intro h2; exact absurd h2 (by simp))

theorem noOOF_inl_jump (arg) (s : State) : EvmYul.step (.StackMemFlow .JUMP) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (match s.stack.pop with
              | some ⟨st, μ₀⟩ => (.ok {s with pc := μ₀, stack := st} : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  revert h2; split <;> (intro h2; exact absurd h2 (by simp))

theorem noOOF_inl_jumpi (arg) (s : State) : EvmYul.step (.StackMemFlow .JUMPI) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (match s.stack.pop2 with
              | some ⟨st, μ₀, μ₁⟩ =>
                (.ok {s with pc := if μ₁ != (⟨0⟩ : UInt256) then μ₀ else s.pc + (⟨1⟩ : UInt256),
                              stack := st} : Except EVM.ExecutionException State)
              | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  revert h2; split <;> (intro h2; exact absurd h2 (by simp))

theorem noOOF_inl_invalid (arg) (s : State) : EvmYul.step (.System .INVALID) arg s ≠ .error .OutOfFuel := by
  intro h
  have h2 : (.error .InvalidInstruction : Except EVM.ExecutionException State) = .error .OutOfFuel := h
  exact absurd h2 (by simp)

set_option maxHeartbeats 1000000 in
theorem noOOF_inl_selfdestruct (arg) (s : State) :
    EvmYul.step (.System .SELFDESTRUCT) arg s ≠ .error .OutOfFuel := by
  intro h
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
      | _ => .error .StackUnderflow) = .error .OutOfFuel := h
  clear h
  revert h2
  split
  · split <;>
      (repeat' first
        | (intro h2; exact absurd h2 (by simp))
        | split)
  · intro h2; exact absurd h2 (by simp)

local macro "noOOF_arm" hyp:ident : tactic =>
  `(tactic|
    first
    | exact noOOF_execUnOp _ _ $hyp
    | exact noOOF_execBinOp _ _ $hyp
    | exact noOOF_execTriOp _ _ $hyp
    | exact noOOF_execQuadOp _ _ $hyp
    | exact noOOF_executionEnvOp _ _ $hyp
    | exact noOOF_unaryExecutionEnvOp _ _ $hyp
    | exact noOOF_machineStateOp _ _ $hyp
    | exact noOOF_stateOp _ _ $hyp
    | exact noOOF_unaryStateOp EvmYul.State.balance _ $hyp
    | exact noOOF_unaryStateOp EvmYul.State.extCodeSize _ $hyp
    | exact noOOF_unaryStateOp EvmYul.State.extCodeHash _ $hyp
    | exact noOOF_unaryStateOp EvmYul.State.sload _ $hyp
    | exact noOOF_unaryStateOp EvmYul.State.tload _ $hyp
    | exact noOOF_unaryStateOp (fun s v ↦ (s, EvmYul.State.calldataload s v)) _ $hyp
    | exact noOOF_unaryStateOp (fun s v ↦ (s, EvmYul.State.blockHash s v)) _ $hyp
    | exact noOOF_binaryStateOp EvmYul.State.sstore _ $hyp
    | exact noOOF_binaryStateOp EvmYul.State.tstore _ $hyp
    | exact noOOF_binaryMachineStateOp MachineState.mstore _ $hyp
    | exact noOOF_binaryMachineStateOp MachineState.mstore8 _ $hyp
    | exact noOOF_binaryMachineStateOp MachineState.evmReturn _ $hyp
    | exact noOOF_binaryMachineStateOp MachineState.evmRevert _ $hyp
    | exact noOOF_binaryMachineStateOp' MachineState.keccak256 _ $hyp
    | exact noOOF_ternaryMachineStateOp MachineState.mcopy _ $hyp
    | exact noOOF_ternaryCopyOp SharedState.calldatacopy _ $hyp
    | exact noOOF_ternaryCopyOp SharedState.codeCopy _ $hyp
    | exact noOOF_quaternaryCopyOp SharedState.extCodeCopy' _ $hyp
    | exact noOOF_log0Op _ $hyp
    | exact noOOF_log1Op _ $hyp
    | exact noOOF_log2Op _ $hyp
    | exact noOOF_log3Op _ $hyp
    | exact noOOF_log4Op _ $hyp)

local macro "noOOF_inline" hyp:ident : tactic =>
  `(tactic|
    first
    | exact absurd $hyp (by intro hc; exact Except.noConfusion hc)
    | exact noOOF_inl_pop _ _ $hyp
    | exact noOOF_inl_mload _ _ $hyp
    | exact noOOF_inl_returndatacopy _ _ $hyp
    | exact noOOF_inl_jump _ _ $hyp
    | exact noOOF_inl_jumpi _ _ $hyp
    | exact noOOF_inl_invalid _ _ $hyp
    | exact noOOF_inl_selfdestruct _ _ $hyp)

set_option maxHeartbeats 8000000 in
/-- **`EvmYul.step` never `OutOfFuel`.** The shared interpreter emits only `.ok`,
`.StackUnderflow`, `.InvalidInstruction`, or `.ok default` — never `OutOfFuel`. -/
theorem noOOF_EvmYul_step (op : Operation) (arg : Option (UInt256 × Nat)) (s : State) :
    EvmYul.step op arg s ≠ .error .OutOfFuel := by
  intro h
  cases op with
  | StopArith o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)
  | CompBit o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)
  | Keccak o => cases o <;> exact noOOF_binaryMachineStateOp' MachineState.keccak256 _ h
  | Env o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)
  | Block o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)
  | StackMemFlow o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)
  | Push o => exact noOOF_push o arg s h
  | Dup o => cases o <;> exact noOOF_dup _ _ h
  | Exchange o => cases o <;> exact noOOF_swap _ _ h
  | Log o => cases o <;>
      first | exact noOOF_log0Op _ h | exact noOOF_log1Op _ h | exact noOOF_log2Op _ h
            | exact noOOF_log3Op _ h | exact noOOF_log4Op _ h
  | System o => cases o <;> first | (noOOF_arm h) | (noOOF_inline h)

/-! ## Item 4b — the `step` skeleton (DONE)

`step (f+1) cost (some (w,a)) s ≠ OutOfFuel` routes:
* `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL` → `call f` (`noOOF_step_call*`, using
  the `call f` non-`OutOfFuel` hypothesis);
* `CREATE`/`CREATE2` → these *swallow* `Lambda`'s result into a tuple (the `match Λ
  with | .ok … | _ => default` discards the error), so they are unconditionally
  non-`OutOfFuel` — they never even need the `Lambda` hypothesis;
* every other opcode → `EvmYul.step` on the gas-debited state (`noOOF_EvmYul_step`).

`noOOF_step` assembles all three; the routing is the `cases w` defeq-coercion to
the per-arm body (mirroring `gas_EVM_step_default`). -/

/-- Generic call-arm body: `pop … >>= call f … >>= .ok (assemble)` propagates
`OutOfFuel` only from `call f`. -/
theorem noOOF_call_arm_body {X : Type}
    (popv : Option X)
    (callOf : X → Except EVM.ExecutionException (UInt256 × State))
    (assemble : X → UInt256 × State → State)
    (hcall : ∀ x, callOf x ≠ .error .OutOfFuel)
    (h : (do
      let r ← Option.option (Except.error ExecutionException.StackUnderflow) Except.ok popv
      let p ← callOf r
      Except.ok (assemble r p) : Except EVM.ExecutionException State) = .error .OutOfFuel) : False := by
  revert h
  simp only [bind, Except.bind]
  cases hp : popv with
  | none => simp [Option.option]
  | some r =>
    simp only [Option.option]
    cases hr : callOf r with
    | error e => intro h; injection h with h; exact hcall r (hr.trans (by rw [h]))
    | ok p => intro h; simp at h

theorem noOOF_step_call (f cost : ℕ) (a) (s : State)
    (hcall : ∀ g src rcpt t v v' io is oo os perm s2,
      call f cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2
        ≠ .error .OutOfFuel) :
    step (f+1) cost (some (.System .CALL, a)) s ≠ .error .OutOfFuel := by
  intro h; exact noOOF_call_arm_body _ _ _ (fun _ => hcall _ _ _ _ _ _ _ _ _ _ _ _) h

theorem noOOF_step_callcode (f cost : ℕ) (a) (s : State)
    (hcall : ∀ g src rcpt t v v' io is oo os perm s2,
      call f cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2
        ≠ .error .OutOfFuel) :
    step (f+1) cost (some (.System .CALLCODE, a)) s ≠ .error .OutOfFuel := by
  intro h; exact noOOF_call_arm_body _ _ _ (fun _ => hcall _ _ _ _ _ _ _ _ _ _ _ _) h

theorem noOOF_step_delegatecall (f cost : ℕ) (a) (s : State)
    (hcall : ∀ g src rcpt t v v' io is oo os perm s2,
      call f cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2
        ≠ .error .OutOfFuel) :
    step (f+1) cost (some (.System .DELEGATECALL, a)) s ≠ .error .OutOfFuel := by
  intro h; exact noOOF_call_arm_body _ _ _ (fun _ => hcall _ _ _ _ _ _ _ _ _ _ _ _) h

theorem noOOF_step_staticcall (f cost : ℕ) (a) (s : State)
    (hcall : ∀ g src rcpt t v v' io is oo os perm s2,
      call f cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2
        ≠ .error .OutOfFuel) :
    step (f+1) cost (some (.System .STATICCALL, a)) s ≠ .error .OutOfFuel := by
  intro h; exact noOOF_call_arm_body _ _ _ (fun _ => hcall _ _ _ _ _ _ _ _ _ _ _ _) h

set_option maxHeartbeats 8000000 in
theorem noOOF_step_create (f cost : ℕ) (a) (s : State) :
    step (f+1) cost (some (.System .CREATE, a)) s ≠ .error .OutOfFuel := by
  intro h
  dsimp only [step] at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  repeat' first | split at h | (exact absurd h (by simp))

set_option maxHeartbeats 8000000 in
theorem noOOF_step_create2 (f cost : ℕ) (a) (s : State) :
    step (f+1) cost (some (.System .CREATE2, a)) s ≠ .error .OutOfFuel := by
  intro h
  dsimp only [step] at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  repeat' first | split at h | (exact absurd h (by simp))

set_option maxHeartbeats 4000000 in
/-- The `step` default arm (`¬ isCallCreate w`) hands off to `EvmYul.step` on the
gas-debited state, which never errors `OutOfFuel` (`noOOF_EvmYul_step`). -/
theorem noOOF_step_default (f cost : ℕ) (w : Operation) (a) (s : State) (hop : ¬ isCallCreate w) :
    step (f+1) cost (some (w, a)) s ≠ .error .OutOfFuel := by
  intro h
  unfold isCallCreate at hop; push_neg at hop
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hop
  set t : State := { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat cost } with ht
  have key : ∀ (w' : Operation), EvmYul.step w' a t = .error .OutOfFuel → False :=
    fun w' he => noOOF_EvmYul_step w' a t he
  apply key w
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

/-- **The `step` skeleton (DONE).** `step (f+1) …` is never `OutOfFuel` provided
every `call f …` (with `s`'s genesis/blocks) is not `OutOfFuel`. CREATE/CREATE2 are
unconditional; the default arm goes through `noOOF_EvmYul_step`. -/
theorem noOOF_step (f cost : ℕ) (w : Operation) (a) (s : State)
    (hcall : ∀ g src rcpt t v v' io is oo os perm s2,
      call f cost s.executionEnv.blobVersionedHashes g src rcpt t v v' io is oo os perm s2
        ≠ .error .OutOfFuel) :
    step (f+1) cost (some (w, a)) s ≠ .error .OutOfFuel := by
  by_cases hcc : isCallCreate w
  · -- one of the six call/create opcodes
    unfold isCallCreate at hcc
    rcases hcc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact noOOF_step_create f cost a s
    · exact noOOF_step_create2 f cost a s
    · exact noOOF_step_call f cost a s hcall
    · exact noOOF_step_callcode f cost a s hcall
    · exact noOOF_step_delegatecall f cost a s hcall
    · exact noOOF_step_staticcall f cost a s hcall
  · exact noOOF_step_default f cost w a s hcc

/-! ## Item 4c — end-to-end leaf-frame never-`OutOfFuel` (DONE, unconditional)

For a frame whose code contains **no** `CREATE`/`CALL`-family opcode (a *leaf* in the
call tree), the never-`OutOfFuel` property is now fully closed *unconditionally* by
chaining the proved pieces: `noOOF_step_default` (the `step` never `OutOfFuel`s on a
non-call/create arm) discharges the `hstep` of `X_loop_noncallcreate`, which closes
`X` (`X_leaf_noOOF`), which closes `Ξ` (`Ξ_leaf_noOOF`, via the gas-aware
`Ξ_outOfFuel_of_gas`) and `Θ` on a `Code` leaf (`Θ_leaf_noOOF`). This is the genuine
bake-off deliverable for non-nesting execution; the headline `Θ_never_outOfFuel` for
the *nested* case needs the same chain with the call/create iterations' fuel supplied
by the mutual IH (see the closing note). -/

/-- **Leaf-frame `X` never `OutOfFuel` (unconditional).** If the executing code never
decodes to a `CREATE`/`CALL`-family opcode, then `X fuel vj s ≠ OutOfFuel` whenever
`fuel > gasAvailable + 1` — the loop halts (gas measure) before fuel runs out, and
every per-instruction `step` is a non-call/create arm (never `OutOfFuel`). -/
theorem X_leaf_noOOF (vj : Array UInt256)
    (hnc : ∀ (s2 : State),
      ¬ isCallCreate (decode s2.toState.executionEnv.code s2.pc |>.getD (.STOP, .none)).1)
    (fuel : ℕ) (s : State) (hlt : s.gasAvailable.toNat + 1 < fuel) :
    X fuel vj s ≠ .error .OutOfFuel := by
  apply X_loop_noncallcreate vj hnc _ fuel s hlt
  intro f w arg cost s2 hw
  exact noOOF_step_default f cost w arg s2 hw

/-- **Leaf-frame `Ξ` never `OutOfFuel` (unconditional).** For a child whose `code`
contains no `CREATE`/`CALL`-family opcode, `Ξ (f+1)` is never `OutOfFuel` when the
forwarded gas `g` satisfies `g + 1 < f`. -/
theorem Ξ_leaf_noOOF (f : ℕ)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hnc : ∀ (s2 : State),
      ¬ isCallCreate (decode s2.toState.executionEnv.code s2.pc |>.getD (.STOP, .none)).1)
    (hf : g.toNat + 1 < f) :
    Ξ (f+1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I ≠ .error .OutOfFuel := by
  apply Ξ_outOfFuel_of_gas f createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  intro s hsg
  exact X_leaf_noOOF (D_J I.code ⟨0⟩) hnc f s (by rw [hsg]; exact hf)

/-- **Leaf-frame `Θ` (a `Code` call to call-free code) never `OutOfFuel`
(unconditional).** Chains `Θ_outOfFuel_of` (the `Code`-path skeleton) with the leaf
`Ξ`. Requires the called code to contain no `CREATE`/`CALL`-family opcode and the
forwarded gas `g` to satisfy `g + 2 < fuel` (the `+2` covers the `Θ → Ξ → X`
fuel hops above the `X`-loop's own `gas + 1` budget). This is the genuine end-to-end
deliverable for a single (non-nesting) message call. -/
theorem Θ_leaf_noOOF (fuel : ℕ) (bvh : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (code : ByteArray)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (hnc : ∀ (s2 : State),
      ¬ isCallCreate (decode s2.toState.executionEnv.code s2.pc |>.getD (.STOP, .none)).1)
    (hf : g.toNat + 2 < fuel) :
    Θ (fuel+1) bvh createdAccounts genesisBlockHeader blocks σ σ₀ A s o r (.Code code)
        g p v v' d e Hd w ≠ .error .OutOfFuel := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  apply Θ_outOfFuel_of (f'+1) bvh createdAccounts genesisBlockHeader blocks σ σ₀ A s o r code
    g p v v' d e Hd w
  intro σ₁ I
  exact Ξ_leaf_noOOF f' createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I hnc (by omega)

/-! ## Item 1 (gas monotonicity) — the `X` loop never raises gas

`resultGas` reads the gas held by an `X`/`Ξ`-style result (`evmState'.gasAvailable`
on `.success`, the explicit `g'` on `.revert`). The loop-monotonicity lemma
`X_loop_gas_le` shows a successful `X fuel vj s` returns a result whose `resultGas`
is `≤ s.gasAvailable.toNat`, *provided* every per-instruction `step` lands at gas
`≤` its input (the hypothesis `hstep`, which both the non-call/create gas-debit and
the call-arm accounting satisfy). This is the gas-monotonicity half threaded through
the mutual induction; combined with `Ccallgas ≤ Ccall` it bottoms out the loop. -/

/-- Gas held by an `X` result: the running state's gas on success, the explicit
leftover on revert. -/
def resultGas (r : ExecutionResult State) : ℕ :=
  match r with
  | .success s _ => s.gasAvailable.toNat
  | .revert g _ => g.toNat

set_option maxHeartbeats 1000000 in
/-- **`X` loop gas-monotonicity.** If every per-instruction `step f cost (w,arg) s'`
that succeeds lands at gas `≤ s'.gasAvailable.toNat`, then a successful
`X fuel vj s = .ok r` has `resultGas r ≤ s.gasAvailable.toNat`. (`Z` never raises gas
— `Z_ok_state`; the halting arms read the post-`step` gas directly.) -/
theorem X_loop_gas_le (vj : Array UInt256)
    (hstep : ∀ (f cost : ℕ) (w : Operation) (arg) (s' s'' : State),
       (w, arg) = (decode s'.toState.executionEnv.code s'.pc |>.getD (.STOP, .none)) →
       cost ≤ s'.gasAvailable.toNat →
       step f cost (some (w, arg)) s' = .ok s'' →
       s''.gasAvailable.toNat ≤ s'.gasAvailable.toNat) :
    ∀ (fuel : ℕ) (s : State) (r : ExecutionResult State),
      X fuel vj s = .ok r → resultGas r ≤ s.gasAvailable.toNat := by
  intro fuel
  induction fuel with
  | zero => intro s r hX; exact absurd hX (by simp [X])
  | succ f ih =>
    intro s r hX
    unfold X at hX
    simp only [bind, Except.bind] at hX
    set instr := decode s.toState.executionEnv.code s.pc |>.getD (.STOP, .none) with hinstr
    cases hZ : Z vj instr.1 s with
    | error e => rw [hZ] at hX; exact absurd hX (by simp)
    | ok p =>
      obtain ⟨ev, cost₂⟩ := p
      rw [hZ] at hX
      simp only at hX
      have hevle : ev.gasAvailable.toNat ≤ s.gasAvailable.toNat := Z_ok_state vj instr.1 s ev cost₂ hZ
      have hcodepc : ev.toState.executionEnv.code = s.toState.executionEnv.code ∧ ev.pc = s.pc :=
        Z_ok_code_pc vj instr.1 s ev cost₂ hZ
      cases hs : step f cost₂ instr ev with
      | error e => rw [hs] at hX; exact absurd hX (by simp)
      | ok ev' =>
        rw [hs] at hX
        simp only at hX
        have hcle : cost₂ ≤ ev.gasAvailable.toNat := (Z_ok_cost_le_gas vj instr.1 s ev cost₂ hZ).1
        have hdec : (instr.1, instr.2) = (decode ev.toState.executionEnv.code ev.pc |>.getD (.STOP, .none)) := by
          rw [hcodepc.1, hcodepc.2, ← hinstr]
        have hsle : ev'.gasAvailable.toNat ≤ ev.gasAvailable.toNat :=
          hstep f cost₂ instr.1 instr.2 ev ev' hdec hcle hs
        cases hH : H ev'.toMachineState instr.1 with
        | none =>
          rw [hH] at hX
          simp only at hX
          exact le_trans (ih ev' r hX) (le_trans hsle hevle)
        | some o =>
          rw [hH] at hX
          simp only at hX
          by_cases hrev : (instr.1 == Operation.REVERT) = true
          · rw [if_pos hrev] at hX
            have : r = ExecutionResult.revert ev'.gasAvailable o := Except.ok.inj hX |>.symm
            rw [this]; exact le_trans hsle hevle
          · rw [if_neg (by simpa using hrev)] at hX
            have : r = ExecutionResult.success ev' o := Except.ok.inj hX |>.symm
            rw [this]; exact le_trans hsle hevle

/-! ## Item 1 (foundation) — CALL-iteration gas accounting

A `CALL`-family iteration of the `X` loop runs `step f cost₂ (w, arg) ev`, whose
`CALL` arm calls `call f cost₂ … ev`. That `call`:
  * debits `cost₂` from `ev` (`evmState.gasAvailable - ofNat gasCost`),
  * runs the child `Θ` at forwarded gas `Ccallgas …`, which returns leftover `g'`,
  * rebuilds the result with `gasAvailable := (ev.gas - cost₂) + g'`.
So the post-`step` state has gas `(ev.gas - cost₂) + g'`. To bottom out the loop we
need this `< ev.gas`, i.e. `g' < cost₂`. Since the child never raises gas above the
forwarded `Ccallgas` (`Θ_result_gas_le`, the gas-monotonicity half of the mutual
induction) and `Ccallgas ≤ Ccall = cost₂` with `cost₂ = C' ev .CALL ≥ Cextra ≥ 1`,
the strict drop follows. We start with the pure-arithmetic `Ccallgas ≤ Ccall`. -/

/-- `Ccallgas ≤ Ccall`: the gas forwarded to the child is at most the call's total
cost. When `val = 0`, `Ccallgas = Cgascap ≤ Cgascap + Cextra = Ccall`. When `val ≠ 0`,
the stipend `Gcallstipend = 2300` is dominated by `Cxfer = Gcallvalue = 9000 ≤ Cextra`,
so `Ccallgas = Cgascap + 2300 ≤ Cgascap + Cextra = Ccall`. -/
theorem Ccallgas_le_Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    Ccallgas t r val g σ μ A ≤ Ccall t r val g σ μ A := by
  have hac := Caccess_pos t A
  obtain ⟨⟨n, hn⟩⟩ := val
  cases n with
  | zero =>
    show Cgascap t r _ g σ μ A ≤ Cgascap t r _ g σ μ A + Cextra t r _ σ A
    omega
  | succ k =>
    have hxfer : Cxfer ⟨⟨k+1, hn⟩⟩ = Gcallvalue := rfl
    have hstip : Gcallstipend ≤ Cxfer ⟨⟨k+1, hn⟩⟩ := by rw [hxfer]; decide
    have hxe : Cxfer ⟨⟨k+1, hn⟩⟩ ≤ Cextra t r ⟨⟨k+1, hn⟩⟩ σ A := by unfold Cextra; omega
    show Cgascap t r _ g σ μ A + Gcallstipend ≤ Cgascap t r _ g σ μ A + Cextra t r _ σ A
    omega

/-- **CALL-arm stack arg-matching.** A successful `pop7` exposes the top three stack
words as `s[0]!`, `s[1]!`, `s[2]!` — exactly the entries `C'`'s `CALL`/`CALLCODE`/… arms
read via `μₛ[i]!`. This is what reconciles the `Ccallgas` `call` forwards (from `pop7`)
with the `Ccall` that `C'` charges (from `μₛ[i]!`). -/
theorem pop7_stack_index {α} [Inhabited α] (s tl : Stack α) (a b c d e f g : α)
    (h : s.pop7 = some (tl, a, b, c, d, e, f, g)) :
    s[0]! = a ∧ s[1]! = b ∧ s[2]! = c := by
  unfold Stack.pop7 at h
  split at h
  · rename_i hd hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ tl'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl, rfl, _⟩ := h
    refine ⟨?_, ?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

/-- **Strict** `Ccallgas < Ccall`: the forwarded gas is *strictly* less than the
call's total cost, since `Cextra ≥ Caccess ≥ 1` (val = 0 case) and
`Cextra ≥ Cxfer = 9000 > 2300 = Gcallstipend` (val ≠ 0 case). This gives the strict
per-iteration gas drop a CALL iteration needs to bottom out the `X` loop. -/
theorem Ccallgas_lt_Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    Ccallgas t r val g σ μ A < Ccall t r val g σ μ A := by
  have hac := Caccess_pos t A
  obtain ⟨⟨n, hn⟩⟩ := val
  cases n with
  | zero =>
    show Cgascap t r _ g σ μ A < Cgascap t r _ g σ μ A + Cextra t r _ σ A
    unfold Cextra; omega
  | succ k =>
    have hxfer : Cxfer ⟨⟨k+1, hn⟩⟩ = Gcallvalue := rfl
    have hxe : Cxfer ⟨⟨k+1, hn⟩⟩ ≤ Cextra t r ⟨⟨k+1, hn⟩⟩ σ A := by unfold Cextra; omega
    have : Gcallstipend < Cxfer ⟨⟨k+1, hn⟩⟩ := by rw [hxfer]; decide
    show Cgascap t r _ g σ μ A + Gcallstipend < Cgascap t r _ g σ μ A + Cextra t r _ σ A
    omega

/-- `(a - ofNat c) + b` (UInt256) has `.toNat ≤ a.toNat` whenever `c ≤ a.toNat`,
`c < size`, and `b.toNat ≤ c` (no wraparound: the sum `= a.toNat - c + b.toNat ≤ a.toNat`).
This is the UInt256-arithmetic core of the call-result gas bound (`result.gas =
(ev.gas - cost) + g'`). -/
theorem gas_add_sub_le (a b : UInt256) (c : ℕ) (hca : c ≤ a.toNat) (hcs : c < UInt256.size)
    (hbc : b.toNat ≤ c) : ((a - UInt256.ofNat c) + b).toNat ≤ a.toNat := by
  have hsub : (a - UInt256.ofNat c).toNat = a.toNat - c := by
    have htn : a.toNat = a.val.val := rfl
    have hcmod : (Fin.ofNat UInt256.size c).val = c := by
      simp only [Fin.ofNat, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hcs
    show ((a.val - (Fin.ofNat _ c))).val = a.val.val - c
    rw [Fin.sub_def, hcmod]
    show (UInt256.size - c + a.val.val) % UInt256.size = a.val.val - c
    have hle' : c ≤ a.val.val := by rw [← htn]; exact hca
    have hrw : UInt256.size - c + a.val.val = (a.val.val - c) + UInt256.size := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- the sum: `((a-c).toNat + b.toNat) % size`, and `(a-c).toNat + b.toNat ≤ a.toNat < size`.
  have hbsz : b.toNat < UInt256.size := b.val.isLt
  have hsum : ((a - UInt256.ofNat c) + b).toNat = ((a - UInt256.ofNat c).toNat + b.toNat) % UInt256.size := by
    show (((a - UInt256.ofNat c).val + b.val)).val = _
    rw [Fin.add_def]; rfl
  rw [hsum, hsub]
  have hbound : (a.toNat - c) + b.toNat ≤ a.toNat := by omega
  have : (a.toNat - c) + b.toNat < UInt256.size :=
    Nat.lt_of_le_of_lt hbound (a.val.isLt)
  rw [Nat.mod_eq_of_lt this]; exact hbound

set_option maxHeartbeats 2000000 in
/-- **`call` result gas bound.** A successful `call (f+1) cost … ev = .ok (x, result)`
returns `result.gasAvailable.toNat ≤ ev.gasAvailable.toNat`, *provided* the child `Θ`
never returns more than the forwarded gas (`hΘ`) and the call's `cost` covers the
forwarded `callgas` (`hccg : Ccallgas … ≤ cost`) with `cost ≤ ev.gas.toNat`. The
result gas is `(ev.gas - cost) + g'` (UInt256), and `g'.toNat ≤ callgas ≤ cost`
rules out wraparound (`gas_add_sub_le`). The two `g'` sources — the child `Θ` (cover
branch) and the `.ofNat callgas` fallback (else branch) — both satisfy
`g'.toNat ≤ callgas`. -/
theorem call_result_gas_le (f cost : ℕ) (bvh : List ByteArray)
    (gas source recipient t value value' io is oo os : UInt256) (perm : Bool) (ev : State)
    (x : UInt256) (result : State)
    (hcle : cost ≤ ev.gasAvailable.toNat)
    (hccg : Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
              ev.accountMap ev.toMachineState ev.substate ≤ cost)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : call (f+1) cost bvh gas source recipient t value value' io is oo os perm ev
          = .ok (x, result)) :
    result.gasAvailable.toNat ≤ ev.gasAvailable.toNat := by
  -- abbreviations matching `call`'s `let`s
  set tA := AccountAddress.ofUInt256 t with htA
  set rA := AccountAddress.ofUInt256 recipient with hrA
  set callgas := Ccallgas tA rA value gas ev.accountMap ev.toMachineState ev.substate with hcg
  -- the forwarded-gas word is `.ofNat callgas`; its `.toNat = callgas` since `callgas < size`.
  have hcgsz : callgas < UInt256.size :=
    Nat.lt_of_le_of_lt (le_trans hccg hcle) ev.gasAvailable.val.isLt
  have hcgtoNat : (UInt256.ofNat callgas).toNat = callgas := by
    show (Fin.ofNat _ callgas).val = callgas
    simp only [Fin.ofNat, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hcgsz
  have hcostsz : cost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  -- the debited machine-gas = ev.gas - ofNat cost
  simp only [call, bind, Except.bind] at h
  -- the inner `g'` comes from either the Θ-branch or the `.ofNat callgas` else-branch;
  -- in both cases `g'.toNat ≤ callgas`, and `result.gas = (ev.gas - ofNat cost) + g'`.
  -- We expose `g'` by casing the `if value ≤ … ∧ Iₑ < 1024`.
  split at h
  · -- cover branch: g' comes from Θ
    split at h
    · exact absurd h (by simp)
    · rename_i res hΘeq
      have hg' : res.2.2.1.toNat ≤ (UInt256.ofNat callgas).toNat :=
        hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res hΘeq
      have hresgas : result.gasAvailable
          = (ev.gasAvailable - UInt256.ofNat cost) + res.2.2.1 := by
        have := Except.ok.inj h; rw [Prod.mk.injEq] at this; rw [← this.2]; rfl
      rw [hresgas]
      rw [hcgtoNat] at hg'
      exact gas_add_sub_le ev.gasAvailable res.2.2.1 cost hcle hcostsz (le_trans hg' hccg)
  · -- else branch: g' = .ofNat callgas
    have hresgas : result.gasAvailable
        = (ev.gasAvailable - UInt256.ofNat cost) + UInt256.ofNat callgas := by
      have := Except.ok.inj h; rw [Prod.mk.injEq] at this; rw [← this.2]; rfl
    rw [hresgas]
    exact gas_add_sub_le ev.gasAvailable (UInt256.ofNat callgas) cost hcle hcostsz
      (by rw [hcgtoNat]; exact hccg)

/-- Strict companion of `gas_add_sub_le`: `((a - ofNat c) + b).toNat < a.toNat` when
`c ≤ a.toNat`, `c < size`, and `b.toNat < c`. -/
theorem gas_add_sub_lt (a b : UInt256) (c : ℕ) (hca : c ≤ a.toNat) (hcs : c < UInt256.size)
    (hbc : b.toNat < c) : ((a - UInt256.ofNat c) + b).toNat < a.toNat := by
  have hsub : (a - UInt256.ofNat c).toNat = a.toNat - c := by
    have htn : a.toNat = a.val.val := rfl
    have hcmod : (Fin.ofNat UInt256.size c).val = c := by
      simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hcs
    show ((a.val - (Fin.ofNat _ c))).val = a.val.val - c
    rw [Fin.sub_def, hcmod]
    show (UInt256.size - c + a.val.val) % UInt256.size = a.val.val - c
    have hle' : c ≤ a.val.val := by rw [← htn]; exact hca
    have hrw : UInt256.size - c + a.val.val = (a.val.val - c) + UInt256.size := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hsum : ((a - UInt256.ofNat c) + b).toNat = ((a - UInt256.ofNat c).toNat + b.toNat) % UInt256.size := by
    show (((a - UInt256.ofNat c).val + b.val)).val = _
    rw [Fin.add_def]; rfl
  rw [hsum, hsub]
  have hbound : (a.toNat - c) + b.toNat < a.toNat := by omega
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hbound a.val.isLt)]; exact hbound

set_option maxHeartbeats 2000000 in
/-- **`call` result gas STRICT bound.** Strict companion of `call_result_gas_le`:
when `Ccallgas … < cost` (always true, `Ccallgas_lt_Ccall`, with `cost = Ccall`),
a successful `call` lands at *strictly* less gas. This is what bottoms out the `X`
loop on a CALL iteration. -/
theorem call_result_gas_lt (f cost : ℕ) (bvh : List ByteArray)
    (gas source recipient t value value' io is oo os : UInt256) (perm : Bool) (ev : State)
    (x : UInt256) (result : State)
    (hcle : cost ≤ ev.gasAvailable.toNat)
    (hccg : Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
              ev.accountMap ev.toMachineState ev.substate < cost)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : call (f+1) cost bvh gas source recipient t value value' io is oo os perm ev
          = .ok (x, result)) :
    result.gasAvailable.toNat < ev.gasAvailable.toNat := by
  set callgas := Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
              ev.accountMap ev.toMachineState ev.substate with hcg
  have hcgsz : callgas < UInt256.size :=
    Nat.lt_of_le_of_lt (le_of_lt (Nat.lt_of_lt_of_le hccg hcle)) ev.gasAvailable.val.isLt
  have hcgtoNat : (UInt256.ofNat callgas).toNat = callgas := by
    show (Fin.ofNat _ callgas).val = callgas
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hcgsz
  have hcostsz : cost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  simp only [call, bind, Except.bind] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i res hΘeq
      have hg' : res.2.2.1.toNat ≤ (UInt256.ofNat callgas).toNat :=
        hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res hΘeq
      have hresgas : result.gasAvailable
          = (ev.gasAvailable - UInt256.ofNat cost) + res.2.2.1 := by
        have := Except.ok.inj h; rw [Prod.mk.injEq] at this; rw [← this.2]; rfl
      rw [hresgas, hcgtoNat] at *
      exact gas_add_sub_lt ev.gasAvailable res.2.2.1 cost hcle hcostsz
        (Nat.lt_of_le_of_lt hg' hccg)
  · rename_i hne
    have hresgas : result.gasAvailable
        = (ev.gasAvailable - UInt256.ofNat cost) + UInt256.ofNat callgas := by
      have := Except.ok.inj h; rw [Prod.mk.injEq] at this; rw [← this.2]; rfl
    rw [hresgas]
    exact gas_add_sub_lt ev.gasAvailable (UInt256.ofNat callgas) cost hcle hcostsz
      (by rw [hcgtoNat]; exact hccg)

/-- **Default-arm `step` gas bound** in the `X_loop_gas_le` `hstep` shape: a successful
non-call/create `step (f+1)` debits `cost` (so lands at `gas - cost ≤ gas`, using
`cost ≤ s.gas.toNat` to rule out wraparound). -/
theorem step_default_gas_le (f cost : ℕ) (w : Operation) (arg) (s s' : State)
    (hop : ¬ isCallCreate w) (hcle : cost ≤ s.gasAvailable.toNat)
    (h : step f cost (some (w, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  cases f with
  | zero => exact absurd h (by simp [step])
  | succ f =>
    have hg : s'.gasAvailable = s.gasAvailable - UInt256.ofNat cost :=
      gas_EVM_step_default f cost w arg s s' hop h
    rw [hg]
    exact gas_sub_le s.gasAvailable cost hcle
      (Nat.lt_of_le_of_lt hcle s.gasAvailable.val.isLt)

/-- **Leaf-frame `X` gas-monotonicity (unconditional).** For a frame whose code never
decodes to a CREATE/CALL opcode, a successful `X fuel vj s = .ok r` returns
`resultGas r ≤ s.gasAvailable.toNat`. This is the gas-monotonicity companion of
`X_leaf_noOOF`, discharging `X_loop_gas_le`'s `hstep` via `step_default_gas_le`. -/
theorem X_leaf_gas_le (vj : Array UInt256)
    (hnc : ∀ (s2 : State),
      ¬ isCallCreate (decode s2.toState.executionEnv.code s2.pc |>.getD (.STOP, .none)).1)
    (fuel : ℕ) (s : State) (r : ExecutionResult State)
    (hX : X fuel vj s = .ok r) :
    resultGas r ≤ s.gasAvailable.toNat := by
  refine X_loop_gas_le vj ?_ fuel s r hX
  intro f cost w arg s' s'' hdec hcle hs
  -- the stepped `(w,arg)` is the decoded opcode at `s'`; `hnc s'` rules out call/create.
  have hwnc : ¬ isCallCreate w := by
    have := hnc s'
    rw [← hdec] at this; exact this
  exact step_default_gas_le f cost w arg s' s'' hwnc hcle hs

/-! ## Item 1 (CREATE-side) — CREATE/CREATE2/`Lambda` gas descent (B2g)

The CREATE/CREATE2 arms of `step` have a *different* result-gas shape than CALL's
wrapping `UInt256` sum. Reading the vendored `EVM.step` `.CREATE`/`.CREATE2` arms:
the gas is first debited (`evmState.gasAvailable := evmState.gasAvailable - ofNat
gasCost` — call this debited word `gd`), then a child `Lambda f … (forwarded gas =
.ofNat (L gd.toNat)) …` runs returning a leftover `g'`, and the result state's gas is

  `gasAvailable := .ofNat <| gd.toNat - L (gd.toNat) + g'.toNat`

a **`Nat`-shaped** (not `UInt256`-wrapping) expression wrapped once by `.ofNat`,
where `L n = n - n/64` is the create gas cap (the 63/64 reservation). The forwarded
gas is exactly `.ofNat (L gd.toNat)`, so the create analogue of `Θ_result_gas_le` is
`g'.toNat ≤ L gd.toNat`. Across the three `(a, evmState', g', z, o)` branches:
  * nonce-overflow (`σ_Iₐ.nonce ≥ 2^64-1`):  `g' = .ofNat (L gd.toNat)`  → `= L gd.toNat`;
  * else (insufficient funds / depth = 1024 / init-code too big): same `.ofNat (L gd.toNat)`;
  * the `Lambda` branch: `g'` is `Lambda`'s 4th result component on `.ok`, else `⟨0⟩`.
So `g'.toNat ≤ L gd.toNat` reduces to the single child-`Lambda`-result hypothesis,
exactly as `call_result_gas_le` reduced to the child-`Θ` hypothesis.

The `Nat` no-wrap core `create_gas_arith{,_lt}` then gives `gd.toNat − L + g' ≤ gd.toNat`
(`< gd.toNat` is impossible — equality holds when `g' = L`; the strict drop comes
from the *debit*: `gd.toNat < ev.gas.toNat` since `Gcreate = 32000 > 0`). -/

/-- `C' s .CREATE ≥ 1`: the create base cost `Gcreate = 32000` dominates. This
discharges the `1 ≤ gasCost` (`hpos`) hypothesis of `create_result_gas_lt` when the
assembly takes `gasCost = C' ev .CREATE`. -/
theorem C'_create_pos (s : State) : 1 ≤ C' s .CREATE := by
  show 1 ≤ Gcreate + _; simp only [Gcreate]; omega

/-- `C' s .CREATE2 ≥ 1`: same, `Gcreate = 32000` dominates. -/
theorem C'_create2_pos (s : State) : 1 ≤ C' s .CREATE2 := by
  show 1 ≤ Gcreate + _ + _; simp only [Gcreate]; omega

/-- **CREATE-arm stack arg-matching.** A successful `pop3` exposes the top three
words as `s[0]!`, `s[1]!`, `s[2]!` — the entries `C' .CREATE` reads via `μₛ[i]!`. The
create analogue of `pop7_stack_index` (CREATE pops 3). -/
theorem pop3_stack_index {α} [Inhabited α] (s tl : Stack α) (a b c : α)
    (h : s.pop3 = some (tl, a, b, c)) :
    s[0]! = a ∧ s[1]! = b ∧ s[2]! = c := by
  unfold Stack.pop3 at h
  split at h
  · rename_i hd hd₁ hd₂ tl'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

/-- **CREATE2-arm stack arg-matching.** A successful `pop4` exposes the top four
words; the gas-relevant `μₛ[2]!` is the third. (CREATE2 pops 4: gas/salt + the three
CREATE words.) -/
theorem pop4_stack_index {α} [Inhabited α] (s tl : Stack α) (a b c d : α)
    (h : s.pop4 = some (tl, a, b, c, d)) :
    s[0]! = a ∧ s[1]! = b ∧ s[2]! = c ∧ s[3]! = d := by
  unfold Stack.pop4 at h
  split at h
  · rename_i hd hd₁ hd₂ hd₃ tl'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

/-- **CREATE `Nat` no-wrap core (≤).** Given `g' ≤ L gd` (the child returns no more
than the create cap) and `gd ≤ G` (the debited gas does not exceed the input), the
`.ofNat`-wrapped create result gas `gd − L gd + g'` has `.toNat ≤ G`. The single
`.ofNat` does not wrap because `gd − L gd + g' ≤ gd ≤ G < size`. -/
theorem create_gas_arith (gd G g' : ℕ) (hg' : g' ≤ L gd) (hgd : gd ≤ G) (hG : G < UInt256.size) :
    (UInt256.ofNat (gd - L gd + g')).toNat ≤ G := by
  have hLle : L gd ≤ gd := L_le gd
  have hinner : gd - L gd + g' ≤ gd := by omega
  have hlt : gd - L gd + g' < UInt256.size := Nat.lt_of_le_of_lt (le_trans hinner hgd) hG
  have htoNat : (UInt256.ofNat (gd - L gd + g')).toNat = gd - L gd + g' := by
    show (Fin.ofNat _ _).val = _
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hlt
  rw [htoNat]; omega

/-- **CREATE `Nat` no-wrap core (strict <).** Same as `create_gas_arith` but with a
*strict* debit `gd < G` (which the positive create base cost `Gcreate = 32000`
guarantees), yielding `.toNat < G`. -/
theorem create_gas_arith_lt (gd G g' : ℕ) (hg' : g' ≤ L gd) (hgd : gd < G) (hG : G < UInt256.size) :
    (UInt256.ofNat (gd - L gd + g')).toNat < G := by
  have hLle : L gd ≤ gd := L_le gd
  have hinner : gd - L gd + g' ≤ gd := by omega
  have hlt : gd - L gd + g' < UInt256.size := Nat.lt_of_le_of_lt (le_of_lt (Nat.lt_of_le_of_lt hinner hgd)) hG
  have htoNat : (UInt256.ofNat (gd - L gd + g')).toNat = gd - L gd + g' := by
    show (Fin.ofNat _ _).val = _
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hlt
  rw [htoNat]; omega

set_option maxHeartbeats 4000000 in
/-- **CREATE result-gas bound.** A successful CREATE step
`step (f+1) gasCost (some (.CREATE, arg)) ev = .ok s'` lands at
`s'.gasAvailable.toNat ≤ ev.gasAvailable.toNat`, provided the debit does not wrap
(`gasCost ≤ ev.gasAvailable.toNat`) and the child `Lambda` returns no more than the
forwarded create cap (`hΛ`). The result gas is `.ofNat (gd.toNat − L gd.toNat + g'.toNat)`
where `gd = ev.gas − ofNat gasCost`; `create_gas_arith` rules out the single `.ofNat`
wrap. The `g'` across the three branches (nonce-overflow / `Lambda` / else) all satisfy
`g'.toNat ≤ L gd.toNat`. -/
theorem create_result_gas_le (f gasCost : ℕ) (arg : Option (UInt256 × Nat)) (ev s' : State)
    (hcle : gasCost ≤ ev.gasAvailable.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) gasCost (some (.CREATE, arg)) ev = .ok s') :
    s'.gasAvailable.toNat ≤ ev.gasAvailable.toNat := by
  -- the debited gas word and its `.toNat` bound
  set gd : UInt256 := ev.gasAvailable - UInt256.ofNat gasCost with hgd
  have hcsz : gasCost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  have hgdle : gd.toNat ≤ ev.gasAvailable.toNat := gas_sub_le ev.gasAvailable gasCost hcle hcsz
  have hgdsz : ev.gasAvailable.toNat < UInt256.size := ev.gasAvailable.val.isLt
  -- expose the CREATE arm; `evmState` after `execLength+1` then `-ofNat gasCost`
  simp only [step, bind, Except.bind, pure, Except.pure] at h
  -- the post-execLength-bump, post-debit state; its `.gasAvailable` is `gd`.
  -- peel the `pop3` match.
  split at h
  · -- pop3 = some
    rename_i stack μ₀ μ₁ μ₂ _hpop
    -- close the goal once we have `g'.toNat ≤ L gd.toNat`; the result gas is then
    -- `.ofNat (gd.toNat - L gd.toNat + g'.toNat)` independent of the branch's evmState'.
    -- The `(a, evmState', g', z, o)` 3-way split:
    split at h
    · -- nonce-overflow branch: g' = .ofNat (L gd.toNat)
      split at h
      · exact absurd h (by simp)   -- OutOfGass guard fired
      · injection h with h; subst h
        simp only [gasAvailable_replaceStackAndIncrPC]
        refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
        -- g' = .ofNat (L gd.toNat); its toNat = L gd.toNat ≤ L gd.toNat
        have hLsz : L gd.toNat < UInt256.size :=
          Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
        show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
        show (Fin.ofNat _ _).val ≤ _
        simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
    · -- the funds/depth/size guard
      split at h
      · -- Lambda sub-branch
        split at h
        · -- Lambda = .ok (a, cA, σ', g', A', z, o): the leftover gas component is `lamg'`
          rename_i lama lamcA lamσ' lamg' lamA' lamz lamo hΛeq
          split at h
          · exact absurd h (by simp)   -- OutOfGass guard fired
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
            -- hΛ bounds `lamg'` by the forwarded gas `.ofNat (L gd.toNat)`.
            have hb := hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lama, lamcA, lamσ', lamg', lamA', lamz, lamo) hΛeq
            have hLsz : L gd.toNat < UInt256.size :=
              Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
            have hfwd : (UInt256.ofNat (L gd.toNat)).toNat = L gd.toNat := by
              show (Fin.ofNat _ _).val = _
              simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
            rw [hfwd] at hb; exact hb
        · -- Lambda not .ok: g' = ⟨0⟩
          split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
            show (⟨0⟩ : UInt256).toNat ≤ L gd.toNat
            exact Nat.zero_le _
      · -- else branch: g' = .ofNat (L gd.toNat)
        split at h
        · exact absurd h (by simp)
        · injection h with h; subst h
          simp only [gasAvailable_replaceStackAndIncrPC]
          refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
          have hLsz : L gd.toNat < UInt256.size :=
            Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
          show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
          show (Fin.ofNat _ _).val ≤ _
          simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
  · exact absurd h (by simp)   -- pop3 = none → StackUnderflow

set_option maxHeartbeats 4000000 in
/-- **CREATE result-gas STRICT bound.** Strict companion of `create_result_gas_le`:
a successful CREATE step with a *positive* base cost (`1 ≤ gasCost`, supplied by
`Gcreate = 32000` at the assembly) lands at gas *strictly* less than the input. The
strict drop comes from the debit `gd.toNat < ev.gas.toNat` (`gas_sub_lt`), since the
result `gd − L gd + g' ≤ gd < ev.gas`. This bottoms out the `X` loop on a CREATE
iteration. -/
theorem create_result_gas_lt (f gasCost : ℕ) (arg : Option (UInt256 × Nat)) (ev s' : State)
    (hcle : gasCost ≤ ev.gasAvailable.toNat) (hpos : 1 ≤ gasCost)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) gasCost (some (.CREATE, arg)) ev = .ok s') :
    s'.gasAvailable.toNat < ev.gasAvailable.toNat := by
  set gd : UInt256 := ev.gasAvailable - UInt256.ofNat gasCost with hgd
  have hcsz : gasCost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  have hgdlt : gd.toNat < ev.gasAvailable.toNat := gas_sub_lt ev.gasAvailable gasCost hcle hpos hcsz
  have hgdsz : ev.gasAvailable.toNat < UInt256.size := ev.gasAvailable.val.isLt
  simp only [step, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i stack μ₀ μ₁ μ₂ _hpop
    split at h
    · -- nonce-overflow branch
      split at h
      · exact absurd h (by simp)
      · injection h with h; subst h
        simp only [gasAvailable_replaceStackAndIncrPC]
        refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
        have hLsz : L gd.toNat < UInt256.size :=
          Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
        show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
        show (Fin.ofNat _ _).val ≤ _
        simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
    · split at h
      · split at h
        · rename_i lama lamcA lamσ' lamg' lamA' lamz lamo hΛeq
          split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
            have hb := hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lama, lamcA, lamσ', lamg', lamA', lamz, lamo) hΛeq
            have hLsz : L gd.toNat < UInt256.size :=
              Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
            have hfwd : (UInt256.ofNat (L gd.toNat)).toNat = L gd.toNat := by
              show (Fin.ofNat _ _).val = _
              simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
            rw [hfwd] at hb; exact hb
        · split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
            show (⟨0⟩ : UInt256).toNat ≤ L gd.toNat
            exact Nat.zero_le _
      · split at h
        · exact absurd h (by simp)
        · injection h with h; subst h
          simp only [gasAvailable_replaceStackAndIncrPC]
          refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
          have hLsz : L gd.toNat < UInt256.size :=
            Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
          show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
          show (Fin.ofNat _ _).val ≤ _
          simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
  · exact absurd h (by simp)

set_option maxHeartbeats 4000000 in
/-- **CREATE2 result-gas bound.** Identical to `create_result_gas_le` — the CREATE2
arm of `step` differs only in popping 4 stack words (the salt `μ₃`) instead of 3 and
computing `ζ` from it; the gas accounting (`gd − L gd + g'`, the same `.ofNat` wrap,
the same three `g'` branches) is byte-for-byte the same. -/
theorem create2_result_gas_le (f gasCost : ℕ) (arg : Option (UInt256 × Nat)) (ev s' : State)
    (hcle : gasCost ≤ ev.gasAvailable.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) gasCost (some (.CREATE2, arg)) ev = .ok s') :
    s'.gasAvailable.toNat ≤ ev.gasAvailable.toNat := by
  set gd : UInt256 := ev.gasAvailable - UInt256.ofNat gasCost with hgd
  have hcsz : gasCost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  have hgdle : gd.toNat ≤ ev.gasAvailable.toNat := gas_sub_le ev.gasAvailable gasCost hcle hcsz
  have hgdsz : ev.gasAvailable.toNat < UInt256.size := ev.gasAvailable.val.isLt
  simp only [step, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i stack μ₀ μ₁ μ₂ μ₃ _hpop
    split at h
    · split at h
      · exact absurd h (by simp)
      · injection h with h; subst h
        simp only [gasAvailable_replaceStackAndIncrPC]
        refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
        have hLsz : L gd.toNat < UInt256.size :=
          Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
        show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
        show (Fin.ofNat _ _).val ≤ _
        simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
    · split at h
      · split at h
        · rename_i lama lamcA lamσ' lamg' lamA' lamz lamo hΛeq
          split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
            have hb := hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lama, lamcA, lamσ', lamg', lamA', lamz, lamo) hΛeq
            have hLsz : L gd.toNat < UInt256.size :=
              Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
            have hfwd : (UInt256.ofNat (L gd.toNat)).toNat = L gd.toNat := by
              show (Fin.ofNat _ _).val = _
              simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
            rw [hfwd] at hb; exact hb
        · split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
            show (⟨0⟩ : UInt256).toNat ≤ L gd.toNat
            exact Nat.zero_le _
      · split at h
        · exact absurd h (by simp)
        · injection h with h; subst h
          simp only [gasAvailable_replaceStackAndIncrPC]
          refine create_gas_arith gd.toNat ev.gasAvailable.toNat _ ?_ hgdle hgdsz
          have hLsz : L gd.toNat < UInt256.size :=
            Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt hgdle hgdsz)
          show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
          show (Fin.ofNat _ _).val ≤ _
          simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
  · exact absurd h (by simp)

set_option maxHeartbeats 4000000 in
/-- **CREATE2 result-gas STRICT bound.** Strict companion; same as
`create_result_gas_lt` over the `pop4` arm. -/
theorem create2_result_gas_lt (f gasCost : ℕ) (arg : Option (UInt256 × Nat)) (ev s' : State)
    (hcle : gasCost ≤ ev.gasAvailable.toNat) (hpos : 1 ≤ gasCost)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA ev.genesisBlockHeader ev.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) gasCost (some (.CREATE2, arg)) ev = .ok s') :
    s'.gasAvailable.toNat < ev.gasAvailable.toNat := by
  set gd : UInt256 := ev.gasAvailable - UInt256.ofNat gasCost with hgd
  have hcsz : gasCost < UInt256.size := Nat.lt_of_le_of_lt hcle ev.gasAvailable.val.isLt
  have hgdlt : gd.toNat < ev.gasAvailable.toNat := gas_sub_lt ev.gasAvailable gasCost hcle hpos hcsz
  have hgdsz : ev.gasAvailable.toNat < UInt256.size := ev.gasAvailable.val.isLt
  simp only [step, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i stack μ₀ μ₁ μ₂ μ₃ _hpop
    split at h
    · split at h
      · exact absurd h (by simp)
      · injection h with h; subst h
        simp only [gasAvailable_replaceStackAndIncrPC]
        refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
        have hLsz : L gd.toNat < UInt256.size :=
          Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
        show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
        show (Fin.ofNat _ _).val ≤ _
        simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
    · split at h
      · split at h
        · rename_i lama lamcA lamσ' lamg' lamA' lamz lamo hΛeq
          split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
            have hb := hΛ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lama, lamcA, lamσ', lamg', lamA', lamz, lamo) hΛeq
            have hLsz : L gd.toNat < UInt256.size :=
              Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
            have hfwd : (UInt256.ofNat (L gd.toNat)).toNat = L gd.toNat := by
              show (Fin.ofNat _ _).val = _
              simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
            rw [hfwd] at hb; exact hb
        · split at h
          · exact absurd h (by simp)
          · injection h with h; subst h
            simp only [gasAvailable_replaceStackAndIncrPC]
            refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
            show (⟨0⟩ : UInt256).toNat ≤ L gd.toNat
            exact Nat.zero_le _
      · split at h
        · exact absurd h (by simp)
        · injection h with h; subst h
          simp only [gasAvailable_replaceStackAndIncrPC]
          refine create_gas_arith_lt gd.toNat ev.gasAvailable.toNat _ ?_ hgdlt hgdsz
          have hLsz : L gd.toNat < UInt256.size :=
            Nat.lt_of_le_of_lt (L_le _) (Nat.lt_of_le_of_lt (le_of_lt hgdlt) hgdsz)
          show (UInt256.ofNat (L gd.toNat)).toNat ≤ L gd.toNat
          show (Fin.ofNat _ _).val ≤ _
          simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hLsz]
  · exact absurd h (by simp)

/-! ## B2h — the gas-monotonicity mutual induction (assembly)

The gas-monotonicity statements for the six mutual layers. Each is "a successful
result lands at gas `≤` the forwarded gas". They reference each other one fuel level
down, so they are proved by a single strong induction on `fuel` (`gas_mono` below),
threading the proved descent bricks (`call_result_gas_le`, `create*_result_gas_le`,
`step_default_gas_le`, `X_loop_gas_le`).

First the per-CALL/CREATE-arm `step` gas-bounds: each reduces `step`'s arm to the
child `call`/`Lambda` and applies the matching descent brick, with the arg-matching
that reconciles the arm's `Ccallgas`/`Lambda`-forwarded gas with the charged `C'`. -/

/-- `liftM (Option) = .ok x ⇒ the option is `some x`. The local `MonadLift Option
(Except …)` sends `some → .ok`, `none → .error .StackUnderflow`. -/
local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

theorem pop_of_liftM {α} (o : Option α) (tup : α)
    (h : (liftM o : Except EVM.ExecutionException α) = Except.ok tup) : o = some tup := by
  cases hp : o with
  | none => rw [hp] at h; exact absurd h (fun h => Except.noConfusion h)
  | some t =>
    rw [hp] at h
    have h2 : (Except.ok t : Except EVM.ExecutionException α) = Except.ok tup := h
    rw [Except.ok.inj h2]

/-- `AccountAddress` roundtrips through `UInt256`: `ofUInt256 (ofNat a.val) = a`
(addresses are 160-bit, so they fit in a `UInt256` without truncation). This
reconciles the `CALLCODE`/`DELEGATECALL`/`STATICCALL` arms (which pass
`.ofNat codeOwner` and round-trip back) with `C'`'s direct `codeOwner`. -/
theorem accountAddr_roundtrip (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  apply Fin.ext
  have h1 : a.val < AccountAddress.size := a.isLt
  have h2 : AccountAddress.size < UInt256.size := by
    unfold AccountAddress.size UInt256.size; norm_num
  unfold AccountAddress.ofUInt256
  have hv : (UInt256.ofNat a.val).val = a.val := by
    show (Fin.ofNat _ a.val).val = a.val
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans h1 h2)
  rw [hv]
  show (a.val % AccountAddress.size) % AccountAddress.size = a.val
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h1]

set_option maxHeartbeats 4000000 in
/-- **CALL-arm `step` gas-monotonicity.** A successful `step (f+1) (C' s .CALL) (.CALL,_) s`
lands at gas `≤ s.gas`, given the child-`Θ` gas-monotonicity at fuel `f-1` (supplied
by the mutual IH). Reduces the arm to `call f` and applies `call_result_gas_le` with
the `pop7` arg-matching (`Ccallgas(call-args) = Ccallgas(C'-args) ≤ Ccall = C' s .CALL`). -/
theorem step_call_gas_le (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .CALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.CALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop
      split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        simp only [call] at hcall
        exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop
      split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop7 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff, g⟩ := tup
        obtain ⟨hi0, hi1, hi2⟩ := pop7_stack_index s.stack tl a b c d e ff g hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_le f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) b b c c d e ff g s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 b) c a ev.accountMap ev.toMachineState ev.substate ≤ _
          have hC : C' s .CALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) (AccountAddress.ofUInt256 s.stack[1]!) s.stack[2]! s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1, ← hi2]
          exact Ccallgas_le_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **CALLCODE-arm `step` gas-monotonicity.** As `step_call_gas_le`; the `call`-arm
passes `recipient = .ofNat codeOwner`, which round-trips back to `codeOwner` (the
recipient `C' .CALLCODE` charges), reconciled by `accountAddr_roundtrip`. -/
theorem step_callcode_gas_le (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .CALLCODE)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.CALLCODE, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop7 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff, g⟩ := tup
        obtain ⟨hi0, hi1, hi2⟩ := pop7_stack_index s.stack tl a b c d e ff g hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_le f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) (UInt256.ofNat s.executionEnv.codeOwner) b c c d e ff g s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)) c a ev.accountMap ev.toMachineState ev.substate ≤ _
          rw [accountAddr_roundtrip]
          have hC : C' s .CALLCODE = Ccall (AccountAddress.ofUInt256 s.stack[1]!) s.executionEnv.codeOwner s.stack[2]! s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1, ← hi2]
          exact Ccallgas_le_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

/-- **CALL-arm stack arg-matching (pop6).** Exposes the top two stack words. The
`DELEGATECALL`/`STATICCALL` analogue of `pop7_stack_index` (those pop 6). -/
theorem pop6_stack_index {α} [Inhabited α] (s tl : Stack α) (a b c d e f : α)
    (h : s.pop6 = some (tl, a, b, c, d, e, f)) :
    s[0]! = a ∧ s[1]! = b := by
  unfold Stack.pop6 at h
  split at h
  · rename_i hd hd₁ hd₂ hd₃ hd₄ hd₅ tl'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl, _⟩ := h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

set_option maxHeartbeats 4000000 in
/-- **DELEGATECALL-arm `step` gas-monotonicity.** `value = 0` (no stipend), and the
`recipient = .ofNat codeOwner` round-trips back to `codeOwner` (`accountAddr_roundtrip`). -/
theorem step_delegatecall_gas_le (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .DELEGATECALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.DELEGATECALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop6 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff⟩ := tup
        obtain ⟨hi0, hi1⟩ := pop6_stack_index s.stack tl a b c d e ff hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_le f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.source) (UInt256.ofNat s.executionEnv.codeOwner) b ⟨0⟩ s.executionEnv.weiValue c d e ff s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)) ⟨0⟩ a ev.accountMap ev.toMachineState ev.substate ≤ _
          rw [accountAddr_roundtrip]
          have hC : C' s .DELEGATECALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) s.executionEnv.codeOwner ⟨0⟩ s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1]
          exact Ccallgas_le_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **STATICCALL-arm `step` gas-monotonicity.** `value = 0`, recipient `= ofUInt256 μ₁`
matches `C' .STATICCALL` directly (no round-trip needed). -/
theorem step_staticcall_gas_le (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .STATICCALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.STATICCALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop6 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff⟩ := tup
        obtain ⟨hi0, hi1⟩ := pop6_stack_index s.stack tl a b c d e ff hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_le f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) b b ⟨0⟩ ⟨0⟩ c d e ff false ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 b) ⟨0⟩ a ev.accountMap ev.toMachineState ev.substate ≤ _
          have hC : C' s .STATICCALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) (AccountAddress.ofUInt256 s.stack[1]!) ⟨0⟩ s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1]
          exact Ccallgas_le_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **CALL-arm `step` gas STRICT descent.** Strict companion of `step_call_gas_le`: a
successful `step (f+1) (C' s .CALL) (.CALL,_) s` lands at *strictly* less gas. Same
reduction as `step_call_gas_le` but routes to `call_result_gas_lt` with the *strict*
`Ccallgas(call-args) < Ccall = C' s .CALL` (`Ccallgas_lt_Ccall`). This bottoms out the
`X` loop on a CALL iteration (the descent companion that `X_iter_gas_lt` is to a leaf). -/
theorem step_call_gas_lt (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .CALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.CALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat < s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop7 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff, g⟩ := tup
        obtain ⟨hi0, hi1, hi2⟩ := pop7_stack_index s.stack tl a b c d e ff g hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_lt f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) b b c c d e ff g s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 b) c a ev.accountMap ev.toMachineState ev.substate < _
          have hC : C' s .CALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) (AccountAddress.ofUInt256 s.stack[1]!) s.stack[2]! s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1, ← hi2]
          exact Ccallgas_lt_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **CALLCODE-arm `step` gas STRICT descent.** Strict companion of `step_callcode_gas_le`. -/
theorem step_callcode_gas_lt (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .CALLCODE)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.CALLCODE, arg)) s = .ok s') :
    s'.gasAvailable.toNat < s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop7 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff, g⟩ := tup
        obtain ⟨hi0, hi1, hi2⟩ := pop7_stack_index s.stack tl a b c d e ff g hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_lt f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) (UInt256.ofNat s.executionEnv.codeOwner) b c c d e ff g s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)) c a ev.accountMap ev.toMachineState ev.substate < _
          rw [accountAddr_roundtrip]
          have hC : C' s .CALLCODE = Ccall (AccountAddress.ofUInt256 s.stack[1]!) s.executionEnv.codeOwner s.stack[2]! s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1, ← hi2]
          exact Ccallgas_lt_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **DELEGATECALL-arm `step` gas STRICT descent.** Strict companion of
`step_delegatecall_gas_le`. `value = 0` ⇒ no stipend; `Ccallgas = Cgascap < Ccall`
strictly via `Caccess ≥ 1` (`Ccallgas_lt_Ccall`, val=0 branch). -/
theorem step_delegatecall_gas_lt (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .DELEGATECALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.DELEGATECALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat < s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop6 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff⟩ := tup
        obtain ⟨hi0, hi1⟩ := pop6_stack_index s.stack tl a b c d e ff hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_lt f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.source) (UInt256.ofNat s.executionEnv.codeOwner) b ⟨0⟩ s.executionEnv.weiValue c d e ff s.executionEnv.perm ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)) ⟨0⟩ a ev.accountMap ev.toMachineState ev.substate < _
          rw [accountAddr_roundtrip]
          have hC : C' s .DELEGATECALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) s.executionEnv.codeOwner ⟨0⟩ s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1]
          exact Ccallgas_lt_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

set_option maxHeartbeats 4000000 in
/-- **STATICCALL-arm `step` gas STRICT descent.** Strict companion of
`step_staticcall_gas_le`. -/
theorem step_staticcall_gas_lt (f cost : ℕ) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s .STATICCALL)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool)
            (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (.STATICCALL, arg)) s = .ok s') :
    s'.gasAvailable.toNat < s.gasAvailable.toNat := by
  cases f with
  | zero =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall; simp only [call] at hcall; exact absurd hcall (by simp)
  | succ f' =>
    dsimp only [step] at h; simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tup hpop; split at h
      · exact absurd h (by simp)
      · rename_i pr hcall
        have hs' : s'.gasAvailable = pr.2.gasAvailable := by
          have := Except.ok.inj h; rw [← this]; rfl
        rw [hs']
        set ev : State := { toSharedState := s.toSharedState, pc := s.pc, stack := s.stack, execLength := s.execLength + 1 } with hev
        have hpop' : s.stack.pop6 = some tup := pop_of_liftM _ _ hpop
        obtain ⟨tl, a, b, c, d, e, ff⟩ := tup
        obtain ⟨hi0, hi1⟩ := pop6_stack_index s.stack tl a b c d e ff hpop'
        obtain ⟨x, result⟩ := pr
        refine call_result_gas_lt f' cost s.executionEnv.blobVersionedHashes
          a (UInt256.ofNat s.executionEnv.codeOwner) b b ⟨0⟩ ⟨0⟩ c d e ff false ev x result
          (by rw [hev]; exact hcle) ?_ ?_ hcall
        · rw [hcost]
          show Ccallgas (AccountAddress.ofUInt256 b) (AccountAddress.ofUInt256 b) ⟨0⟩ a ev.accountMap ev.toMachineState ev.substate < _
          have hC : C' s .STATICCALL = Ccall (AccountAddress.ofUInt256 s.stack[1]!) (AccountAddress.ofUInt256 s.stack[1]!) ⟨0⟩ s.stack[0]! s.accountMap s.toMachineState s.substate := rfl
          rw [hC, ← hi0, ← hi1]
          exact Ccallgas_lt_Ccall _ _ _ _ _ _ _
        · intro cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq
          exact hΘ cA σ σ₀ Asub src o rcpt cc gg p vv vv' dd ee Hd ww res hΘeq

/-- **Unified `step` gas-monotonicity.** For ANY opcode `w`, a successful
`step (f+1) (C' s w) (w,arg) s` lands at gas `≤ s.gas`, dispatching: default arm →
`step_default_gas_le` (unconditional); CREATE/CREATE2 → `create*_result_gas_le` (child
`Lambda f` mono, `hΛ`); CALL family → `step_{call,callcode,delegatecall,staticcall}_gas_le`
(child `Θ (f-1)` mono, `hΘ`). This is the per-instruction bound the `X` loop needs. -/
theorem step_gas_le (f cost : ℕ) (w : Operation) (arg) (s s' : State)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s w)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool) (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA s.genesisBlockHeader s.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (w, arg)) s = .ok s') :
    s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  by_cases hcc : isCallCreate w
  · unfold isCallCreate at hcc
    rcases hcc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact create_result_gas_le f cost arg s s' hcle hΛ h
    · exact create2_result_gas_le f cost arg s s' hcle hΛ h
    · exact step_call_gas_le f cost arg s s' hcle hcost hΘ h
    · exact step_callcode_gas_le f cost arg s s' hcle hcost hΘ h
    · exact step_delegatecall_gas_le f cost arg s s' hcle hcost hΘ h
    · exact step_staticcall_gas_le f cost arg s s' hcle hcost hΘ h
  · exact step_default_gas_le (f+1) cost w arg s s' hcc hcle h

/-- **Unified `step` gas STRICT descent on a CALL/CREATE opcode.** For any `w` in the
CALL/CREATE family, a successful `step (f+1) (C' s w) (w,arg) s` lands at *strictly* less
gas, given BOTH child hypotheses (`hΘ` for the CALL family at fuel `f-1`, `hΛ` for
CREATE/CREATE2 at fuel `f`). Dispatches CREATE/CREATE2 → `create*_result_gas_lt` (with the
`C'_create*_pos` positivity discharging the strict debit `hpos`), CALL family → the four
`step_*_gas_lt`. This is the per-iteration descent that bottoms out the `X` loop on a
CALL/CREATE iteration — the strict companion of `step_gas_le`. -/
theorem step_gas_lt (f cost : ℕ) (w : Operation) (arg) (s s' : State)
    (hcc : isCallCreate w)
    (hcle : cost ≤ s.gasAvailable.toNat)
    (hcost : cost = C' s w)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool) (res),
          Θ (f-1) s.executionEnv.blobVersionedHashes cA s.genesisBlockHeader s.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA s.genesisBlockHeader s.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (h : step (f+1) cost (some (w, arg)) s = .ok s') :
    s'.gasAvailable.toNat < s.gasAvailable.toNat := by
  unfold isCallCreate at hcc
  rcases hcc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact create_result_gas_lt f cost arg s s' hcle (by rw [hcost]; exact C'_create_pos s) hΛ h
  · exact create2_result_gas_lt f cost arg s s' hcle (by rw [hcost]; exact C'_create2_pos s) hΛ h
  · exact step_call_gas_lt f cost arg s s' hcle hcost hΘ h
  · exact step_callcode_gas_lt f cost arg s s' hcle hcost hΘ h
  · exact step_delegatecall_gas_lt f cost arg s s' hcle hcost hΘ h
  · exact step_staticcall_gas_lt f cost arg s s' hcle hcost hΘ h

set_option maxHeartbeats 2000000 in
/-- **`X` measure descent on a CALL/CREATE iteration.** The CALL/CREATE companion of
`X_iter_gas_lt` (drops its `¬ isCallCreate w` gate): a non-halting `X (f+1)` iteration on a
CALL/CREATE opcode `w` — `Z` ok with cost `cost₂`, `step` ok, `H = none` — lands in a state
with *strictly less* gas, GIVEN the child gas-monotonicity hypotheses (`hΘ` for the CALL
family at `f-1`, `hΛ` for CREATE/CREATE2 at `f`; these are CONDITIONAL — the orchestrator's
mutual induction A1 discharges them). `Z_ok_cost_le_gas` supplies `cost₂ ≤ s₁.gas` and
`cost₂ = C' s₁ w`; `step_gas_lt` does the strict descent. (Unlike `X_iter_gas_lt`, no
`H_none_not_halt`/`runnable`/positivity reasoning is needed — `step_gas_lt`'s strictness
comes from the call's `Ccallgas < Ccall` / create's debit, not from `C' ≥ 1`.) -/
theorem X_iter_gas_lt_callcreate (f cost₂ : ℕ) (validJumps : Array UInt256) (w : Operation)
    (a : Option (UInt256 × Nat)) (s s₁ s₂ : State)
    (hw : isCallCreate w)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool) (res),
          Θ (f-1) s₁.executionEnv.blobVersionedHashes cA s₁.genesisBlockHeader s₁.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA s₁.genesisBlockHeader s₁.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (hZ : Z validJumps w s = .ok (s₁, cost₂))
    (hstep : step (f+1) cost₂ (some (w, a)) s₁ = .ok s₂)
    (hH : H s₂.toMachineState w = none) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  obtain ⟨hle, hcost⟩ := Z_ok_cost_le_gas validJumps w s s₁ cost₂ hZ
  exact step_gas_lt f cost₂ w a s₁ s₂ hw hle hcost hΘ hΛ hstep

set_option maxHeartbeats 2000000 in
/-- **Unified `X` measure descent (any non-halting iteration).** Combines `X_iter_gas_lt`
(non-call/create, unconditional) and `X_iter_gas_lt_callcreate` (call/create, conditional on
the child hyps) under one statement: a non-halting `X (f+1)` iteration ALWAYS lands at
strictly less gas. The child hypotheses `hΘ`/`hΛ` are only *used* on the call/create arms;
on a leaf opcode they are vacuous. This is the single per-iteration descent the loop measure
needs — A1 feeds it into the never-`OutOfFuel` induction. -/
theorem X_iter_gas_lt_any (f cost₂ : ℕ) (validJumps : Array UInt256) (w : Operation)
    (a : Option (UInt256 × Nat)) (s s₁ s₂ : State)
    (hΘ : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ σ₀ : AccountMap)
            (Asub : Substate) (src o rcpt : AccountAddress) (c : ToExecute)
            (gg p vv vv' : UInt256) (dd : ByteArray) (e : Nat) (Hd : BlockHeader) (ww : Bool) (res),
          Θ (f-1) s₁.executionEnv.blobVersionedHashes cA s₁.genesisBlockHeader s₁.blocks σ σ₀ Asub src o rcpt c gg p vv vv' dd e Hd ww
            = .ok res → res.2.2.1.toNat ≤ gg.toNat)
    (hΛ : ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
            (σ σ₀ : AccountMap) (Asub : Substate) (sndr orig : AccountAddress)
            (gg pp vv : UInt256) (ii : ByteArray) (ee : UInt256) (zz : Option ByteArray)
            (Hd : BlockHeader) (ww : Bool) (res),
          Lambda f bvh cA s₁.genesisBlockHeader s₁.blocks σ σ₀ Asub sndr orig gg pp vv ii ee zz Hd ww
            = .ok res → res.2.2.2.1.toNat ≤ gg.toNat)
    (hZ : Z validJumps w s = .ok (s₁, cost₂))
    (hstep : step (f+1) cost₂ (some (w, a)) s₁ = .ok s₂)
    (hH : H s₂.toMachineState w = none) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  by_cases hcc : isCallCreate w
  · exact X_iter_gas_lt_callcreate f cost₂ validJumps w a s s₁ s₂ hcc hΘ hΛ hZ hstep hH
  · exact X_iter_gas_lt f cost₂ validJumps w a s s₁ s₂ hcc hZ hstep hH

set_option maxHeartbeats 2000000 in
/-- **`X` loop gas-monotonicity (with the `cost = C' s' w` hypothesis).** Strengthening
of `X_loop_gas_le`: the per-step bound `hstep` may now assume `cost = C' s' w` (which
`Z_ok_cost_le_gas` supplies in the loop). This is what lets the CALL/CREATE arms of
`step_gas_le` apply (they need `cost = C' s' w` for the `Ccallgas ≤ Ccall` arg-matching). -/
theorem X_loop_gas_le' (vj : Array UInt256)
    (hstep : ∀ (f cost : ℕ) (w : Operation) (arg) (s' s'' : State),
       (w, arg) = (decode s'.toState.executionEnv.code s'.pc |>.getD (.STOP, .none)) →
       cost ≤ s'.gasAvailable.toNat →
       cost = C' s' w →
       step f cost (some (w, arg)) s' = .ok s'' →
       s''.gasAvailable.toNat ≤ s'.gasAvailable.toNat) :
    ∀ (fuel : ℕ) (s : State) (r : ExecutionResult State),
      X fuel vj s = .ok r → resultGas r ≤ s.gasAvailable.toNat := by
  intro fuel
  induction fuel with
  | zero => intro s r hX; exact absurd hX (by simp [X])
  | succ f ih =>
    intro s r hX
    unfold X at hX
    simp only [bind, Except.bind] at hX
    set instr := decode s.toState.executionEnv.code s.pc |>.getD (.STOP, .none) with hinstr
    cases hZ : Z vj instr.1 s with
    | error e => rw [hZ] at hX; exact absurd hX (by simp)
    | ok p =>
      obtain ⟨ev, cost₂⟩ := p
      rw [hZ] at hX
      simp only at hX
      have hevle : ev.gasAvailable.toNat ≤ s.gasAvailable.toNat := Z_ok_state vj instr.1 s ev cost₂ hZ
      have hcodepc : ev.toState.executionEnv.code = s.toState.executionEnv.code ∧ ev.pc = s.pc :=
        Z_ok_code_pc vj instr.1 s ev cost₂ hZ
      cases hs : step f cost₂ instr ev with
      | error e => rw [hs] at hX; exact absurd hX (by simp)
      | ok ev' =>
        rw [hs] at hX
        simp only at hX
        obtain ⟨hcle, hcost⟩ := Z_ok_cost_le_gas vj instr.1 s ev cost₂ hZ
        have hdec : (instr.1, instr.2) = (decode ev.toState.executionEnv.code ev.pc |>.getD (.STOP, .none)) := by
          rw [hcodepc.1, hcodepc.2, ← hinstr]
        have hsle : ev'.gasAvailable.toNat ≤ ev.gasAvailable.toNat :=
          hstep f cost₂ instr.1 instr.2 ev ev' hdec hcle hcost hs
        cases hH : H ev'.toMachineState instr.1 with
        | none =>
          rw [hH] at hX; simp only at hX
          exact le_trans (ih ev' r hX) (le_trans hsle hevle)
        | some o =>
          rw [hH] at hX; simp only at hX
          by_cases hrev : (instr.1 == Operation.REVERT) = true
          · rw [if_pos hrev] at hX
            have : r = ExecutionResult.revert ev'.gasAvailable o := Except.ok.inj hX |>.symm
            rw [this]; exact le_trans hsle hevle
          · rw [if_neg (by simpa using hrev)] at hX
            have : r = ExecutionResult.success ev' o := Except.ok.inj hX |>.symm
            rw [this]; exact le_trans hsle hevle

/-- Gas held by a `Ξ` result: the leftover gas on success (3rd component of the inner
tuple) or the explicit `g'` on revert. The `Ξ`/`Θ`-side analogue of `resultGas`. -/
def xiResultGas (r : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) : ℕ :=
  match r with
  | .success s _ => s.2.2.1.toNat
  | .revert g _ => g.toNat

set_option maxHeartbeats 2000000 in
/-- **`Θ` gas-monotonicity, `Code` arm.** A successful `Θ (n+1) … (.Code code) … g …`
returns leftover gas `≤ g.toNat`, given the child `Ξ n` gas-monotonicity (`hΞ`). The
three result sources: the swallowed-error branch (`g' = ⟨0⟩`), the `revert` branch
(`g'` carried through), and the `success` branch (`g'` carried through) — all `≤ g`.
(The `Precompiled` arm is the separate, non-recursive `Θ_gas_le_precompiled` below, built
on the per-contract `Ξ_*`-gas bricks in `NestedEvmYul.PrecompileGas`.) -/
theorem Θ_gas_le_code (n : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (code : ByteArray)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (hΞ : ∀ (σ₁ : AccountMap) (I : ExecutionEnv) res,
      Ξ n cA gh blocks σ₁ σ₀ g A I = .ok res → xiResultGas res ≤ g.toNat)
    (res) (h : Θ (n+1) bvh cA gh blocks σ σ₀ A s o r (.Code code) g p v v' d e Hd w = .ok res) :
    res.2.2.1.toNat ≤ g.toNat := by
  simp only [Θ, bind, Except.bind, pure, Except.pure] at h
  set I : ExecutionEnv := _ with hI
  set σ₁ : AccountMap := _ with hσ₁
  cases hr : Ξ n cA gh blocks σ₁ σ₀ g A I with
  | error ee =>
    rw [hr] at h; dsimp only at h
    by_cases hee : ee = EVM.ExecutionException.OutOfFuel
    · subst hee
      rw [if_pos (show (EVM.ExecutionException.OutOfFuel == EVM.ExecutionException.OutOfFuel) = true from rfl)] at h
      exact absurd h (fun hc => Except.noConfusion hc)
    · have hb : (ee == EVM.ExecutionException.OutOfFuel) = false := by
        cases ee <;> first | rfl | exact absurd rfl hee
      rw [if_neg (by rw [hb]; simp)] at h
      injection h with h; subst h; exact Nat.zero_le _
  | ok xres =>
    rw [hr] at h
    have hgle := hΞ σ₁ I xres hr
    cases xres with
    | success st oo =>
      simp only at h; injection h with h; subst h
      simp only [xiResultGas] at hgle; exact hgle
    | revert g' oo =>
      simp only at h; injection h with h; subst h
      simp only [xiResultGas] at hgle; exact hgle

set_option maxHeartbeats 4000000 in
/-- **`Θ` gas-monotonicity, `Precompiled` arm.** A successful `Θ (n+1) … (.Precompiled pc) …
g …` returns leftover gas `≤ g.toNat`. NON-recursive: each of the 10 precompiles `Ξ_*`
returns leftover gas `≤ g` (the `*_gas_le` bricks in `NestedEvmYul.PrecompileGas`), and the
`_ => default` fallthrough returns gas `⟨0⟩`. No child hypothesis needed. -/
theorem Θ_gas_le_precompiled (n : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (pc : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (res) (h : Θ (n+1) bvh cA gh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e Hd w = .ok res) :
    res.2.2.1.toNat ≤ g.toNat := by
  simp only [Θ, bind, Except.bind, pure, Except.pure] at h
  set I : ExecutionEnv := _ with hI
  set σ₁ : AccountMap := _ with hσ₁
  -- The `Precompiled pc` path binds `(_, _, _, g', _, _)` from the 10-way numeric match on
  -- `pc` (each arm `.ok (∅, Ξ_* σ₁ g A I)`), or `default` on the fallthrough; then `.ok`s the
  -- assembled tuple whose gas slot is exactly that `g'`. Drill the `pc` match, injecting `h`
  -- to read off `res.2.2.1 = (Ξ_* …).2.2.1`, closed per-arm by the `*_gas_le` bricks.
  split at h <;>
    first
    | (injection h with h; subst h; first
        | exact ecrec_gas_le σ₁ g A I
        | exact sha256_gas_le σ₁ g A I
        | exact rip160_gas_le σ₁ g A I
        | exact id_gas_le σ₁ g A I
        | exact expmod_gas_le σ₁ g A I
        | exact bn_add_gas_le σ₁ g A I
        | exact bn_mul_gas_le σ₁ g A I
        | exact snarkv_gas_le σ₁ g A I
        | exact blake2_f_gas_le σ₁ g A I
        | exact point_eval_gas_le σ₁ g A I
        | exact Nat.zero_le _)
    | exact absurd h (fun hc => Except.noConfusion hc)

/-! ## Precompiled-contract gas bounds

The `.Precompiled` arm of `Θ`-gas-monotonicity (`gas_branch_le` + the per-contract
`Ξ_*`-gas bricks `ecrec_gas_le`/…/`point_eval_gas_le`) lives in the sibling module
`NestedEvmYul.PrecompileGas` (imported above). It was split out because the FFI-backed
precompiles have kernel-heavy `String`-pattern bodies; see that module + the lakefile
`-s` (thread-stack) note. -/

/-- `(UInt256.ofNat x).toNat ≤ g.toNat` when `x ≤ g.toNat` (no wrap, `x < size`). The
common closer for the `.ofNat`-wrapped leftover-gas components in the `Lambda`/precompile
result-gas bounds. -/
theorem ofNat_le_of_le (x : ℕ) (g : UInt256) (hb : x ≤ g.toNat) :
    (UInt256.ofNat x).toNat ≤ g.toNat := by
  have hsz : x < UInt256.size := Nat.lt_of_le_of_lt hb g.val.isLt
  show (Fin.ofNat _ _).val ≤ _
  simp only [Fin.ofNat]; rw [Nat.mod_eq_of_lt hsz]; exact hb

set_option maxHeartbeats 2000000 in
/-- **`Ξ` gas-monotonicity.** A successful `Ξ (n+1) … g … = .ok res` returns leftover
gas `≤ g.toNat`, given the inner `X n` gas-monotonicity on the freshly-built child
state (whose `gasAvailable` is exactly `g`). The `success`/`revert` post-processing
carries the `X`-result gas through unchanged. -/
theorem Ξ_gas_le (n : ℕ)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hX : ∀ s : State, s.gasAvailable = g → ∀ res, X n (D_J I.code ⟨0⟩) s = .ok res → resultGas res ≤ g.toNat)
    (res) (h : Ξ (n+1) cA gh blocks σ σ₀ g A I = .ok res) :
    xiResultGas res ≤ g.toNat := by
  unfold Ξ at h
  simp only [bind, Except.bind] at h
  set s0 : EVM.State := { (default : EVM.State) with accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A, createdAccounts := cA, gasAvailable := g, blocks := blocks, genesisBlockHeader := gh } with hs0
  cases hr : X n (D_J I.code ⟨0⟩) s0 with
  | error e => rw [hr] at h; exact absurd h (by simp)
  | ok xr =>
    rw [hr] at h
    have hxle := hX s0 rfl xr hr
    cases xr with
    | success st oo =>
      simp only at h; injection h with h; subst h
      simp only [xiResultGas, resultGas] at *; exact hxle
    | revert g' oo =>
      simp only at h; injection h with h; subst h
      simp only [xiResultGas, resultGas] at *; exact hxle

/-- `(if c then 0 else a - x) ≤ a`: the `Lambda` create-result leftover gas (`g' = if F
then 0 else gStarStar − codeDeposit`) never exceeds the child's leftover `gStarStar`. -/
theorem ite_zero_sub_le {c : Prop} [Decidable c] (a x : ℕ) : (if c then 0 else a - x) ≤ a := by
  split
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

set_option maxHeartbeats 4000000 in
/-- **`Lambda` gas-monotonicity.** A successful `Lambda (n+1) … g … = .ok res` (contract
creation) returns leftover gas `≤ g.toNat`, given the inner `Ξ n` gas-monotonicity
(`hΞ`). The three result branches: the swallowed-`Ξ`-error (`g' = ⟨0⟩`), `revert`
(`g'` carried), and `success` (`g' = .ofNat (if F then 0 else gStarStar − codeDeposit)`,
bounded by `gStarStar ≤ g` via `ite_zero_sub_le` + `ofNat_le_of_le`). The leading `L_A`
address lift only errors as `.StackUnderflow`. -/
theorem Lambda_gas_le (n : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress) (g p v : UInt256)
    (i : ByteArray) (e : UInt256) (ζ : Option ByteArray) (Hd : BlockHeader) (w : Bool)
    (hΞ : ∀ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (As : Substate)
            (I : ExecutionEnv) res,
          Ξ n cA' gh blocks σ' σ₀ g As I = .ok res → xiResultGas res ≤ g.toNat)
    (res) (h : Lambda (n+1) bvh cA gh blocks σ σ₀ A s o g p v i e ζ Hd w = .ok res) :
    res.2.2.2.1.toNat ≤ g.toNat := by
  simp only [Lambda, bind, Except.bind] at h
  cases hla : Lambda.L_A s (Option.option (⟨0⟩ : UInt256) (·.nonce) (σ.find? s) - ⟨1⟩) ζ i with
  | none =>
    rw [hla] at h
    rw [show (liftM (none : Option ByteArray) : Except EVM.ExecutionException ByteArray) = .error .StackUnderflow from rfl] at h
    exact absurd h (fun hc => Except.noConfusion hc)
  | some lₐ =>
    rw [hla] at h
    rw [show (liftM (some lₐ) : Except EVM.ExecutionException ByteArray) = .ok lₐ from rfl] at h
    dsimp only at h
    split at h
    case _ ee heq =>
      by_cases hee : ee = EVM.ExecutionException.OutOfFuel
      · subst hee
        rw [if_pos (show (EVM.ExecutionException.OutOfFuel == EVM.ExecutionException.OutOfFuel) = true from rfl)] at h
        exact absurd h (fun hc => Except.noConfusion hc)
      · have hb : (ee == EVM.ExecutionException.OutOfFuel) = false := by
          cases ee <;> first | rfl | exact absurd rfl hee
        rw [if_neg (by rw [hb]; simp)] at h
        injection h with h; subst h; exact Nat.zero_le _
    case _ g' oo heq =>
      injection h with h; subst h
      have hxle := hΞ _ _ _ _ _ heq
      simp only [xiResultGas] at hxle; exact hxle
    case _ tup ret heq =>
      obtain ⟨cA'', σ'', gSS, ASS⟩ := tup
      have hxle := hΞ _ _ _ _ _ heq
      simp only [xiResultGas] at hxle
      injection h with h; subst h
      exact ofNat_le_of_le _ g (le_trans (ite_zero_sub_le _ _) hxle)

/-! ## Status of the headline `Θ_never_outOfFuel` — what is closed and what remains

### CLOSED (this run)
* **`step` skeleton** (`noOOF_step`): `step (f+1) … ≠ OutOfFuel` given each
  `call f …` is not `OutOfFuel`. CALL/CALLCODE/DELEGATECALL/STATICCALL route to
  `call f` (`noOOF_call_arm_body`); CREATE/CREATE2 are *unconditional* (they swallow
  `Lambda`'s result into a tuple); the default arm goes through `noOOF_EvmYul_step`
  (the shared interpreter never `OutOfFuel`s — full per-arm sweep).
* **`X` inner loop-induction** (`X_loop_noncallcreate`): the gas measure bottoms out
  the loop — once `fuel > gas + 1`, `X` halts before fuel runs out. Closed for a
  frame whose code never decodes to a CREATE/CALL opcode.
* **Precompiled `Θ`-arm** (`Θ_precompiled_never_outOfFuel`): the literal-pattern arm,
  via `dsimp only [Θ]` (avoids the enormous `.Precompiled` eq-lemma deep recursion)
  + keep-`hc` split + `nomatch`.
* **End-to-end leaf frame** (`Θ_leaf_noOOF`, `Ξ_leaf_noOOF`, `X_leaf_noOOF`): a single
  *non-nesting* message call (Code with no CREATE/CALL opcode) is **unconditionally**
  never `OutOfFuel` when `gas + 2 < fuel`. This is a complete, axiom-clean headline
  for the non-nested fragment — the genuine bake-off deliverable for straight-line +
  intra-frame-control-flow execution.

### CLOSED (this run, B2g) — the CREATE/CREATE2/`Lambda` descent bricks
The CREATE-side analog of the B2f CALL descent. The CREATE/CREATE2 result gas is
`.ofNat (gd.toNat − L gd.toNat + g'.toNat)` where `gd = ev.gas − ofNat gasCost` is the
debited gas and `L n = n − n/64` the create cap — a *`Nat`*-shaped expression wrapped
once by `.ofNat`, NOT CALL's wrapping `UInt256` sum. The result gas depends only on
`g'` (the inner branch's `evmState'.gasAvailable` is overwritten). The bricks reduce the
descent to the single child-`Lambda`-result hypothesis `g'.toNat ≤ (forwarded).toNat`:

* **`create_gas_arith` / `create_gas_arith_lt`** — the `Nat` no-wrap core (CREATE analog
  of `gas_add_sub_le/lt`): from `g' ≤ L gd` and `gd ≤ G` (resp. `gd < G`) conclude
  `(.ofNat (gd − L gd + g')).toNat ≤ G` (resp. `< G`). No wrap: `gd − L gd + g' ≤ gd ≤ G`.
* **`create_result_gas_le` / `create_result_gas_lt`** + **`create2_result_gas_le` /
  `create2_result_gas_lt`** — a successful `step (f+1) gasCost (some (.CREATE/.CREATE2,_))
  ev` lands at gas `≤` (resp. `<`) `ev.gas`, given `gasCost ≤ ev.gas`, `1 ≤ gasCost`
  (strict only), and the child-`Lambda` mono hypothesis `hΛ`. The strict drop is from the
  *debit* (`gd < ev.gas`), not from `g' < L`. Every branch + the `OutOfGass` guard handled.
* **`C'_create_pos` / `C'_create2_pos`** — `C' s .CREATE/.CREATE2 ≥ Gcreate = 32000 ≥ 1`
  (discharges the strict `hpos`).
* **`pop3_stack_index` / `pop4_stack_index`** — CREATE/CREATE2 arg-matching (analog of
  `pop7_stack_index`).

**Verdict: CREATE is tractable** — monotone exactly as expected, `hΛ` plugs into the same
mutual induction as B2f's `hΘ`. No structural surprise; the headline can keep CREATE in scope.

### CLOSED (this run, B2f) — the gas-monotonicity / CALL-descent bricks
The CALL-iteration gas descent (prior "sub-obligation 1") is now fully reduced to the
child-`Θ` gas-monotonicity hypothesis, with every supporting brick proved axiom-clean:

* **`Ccallgas_le_Ccall` / `Ccallgas_lt_Ccall`** (pure arithmetic): the gas a frame
  forwards to its child is `≤` (resp. strictly `<`) the call's total cost
  `Ccall = Cgascap + Cextra`. Strictness holds because `Cextra ≥ Caccess ≥ 1` (val=0)
  and `Cextra ≥ Cxfer = Gcallvalue = 9000 > 2300 = Gcallstipend` (val≠0).
* **`gas_add_sub_le` / `gas_add_sub_lt`** (UInt256 no-wrap core): the call-result gas
  `(ev.gas − ofNat cost) + g'` (a *wrapping* UInt256 sum!) has `.toNat ≤` (resp. `<`)
  `ev.gas.toNat`, given `g'.toNat ≤ cost` (resp. `< cost`). This resolves the
  wraparound subtlety in the call-result accounting.
* **`call_result_gas_le` / `call_result_gas_lt`**: a successful `call (f+1) cost … ev`
  lands at gas `≤` (resp. `<`) `ev.gas`, *given* (i) `cost ≤ ev.gas`, (ii) `Ccallgas
  (call-args) ≤ cost` (resp. `<`), and (iii) the child-`Θ` returns `g'.toNat ≤ gg.toNat`
  (the forwarded gas) — the gas-monotonicity hypothesis. Both `g'` sources (the child
  `Θ` cover-branch and the `.ofNat callgas` else-branch) are handled.
* **`Z_ok_code_pc`**: `Z` preserves `pc`/`code`, so the `X`-loop's decoded opcode (from
  the pre-`Z` state) is the opcode at the post-`Z` step-state. Lets the loop's `hstep`
  recover non-call/create from `hnc`.
* **`X_loop_gas_le`**: the `X` loop never *raises* gas — `resultGas r ≤ s.gas` — given
  every per-instruction `step` lands at gas `≤` input (`hstep`, now phrased with the
  decoded-opcode equation so the leaf case can use `hnc`).
* **`step_default_gas_le` + `X_leaf_gas_le`**: the leaf-frame gas-monotonicity is
  **unconditional** (the default arm's `hstep` is `step_default_gas_le`, the strict
  cousin of `gas_EVM_step_default`).

### CLOSED (this run, B2h) — the gas-monotonicity per-layer reductions
Sub-task 1's per-layer reductions are now ALL proved (axiom-clean, green). Each reduces
one layer's gas-monotonicity to its child's, exactly one fuel level down (with `X`'s loop
internalised). The arg-matching that B2f flagged as "tedious but mechanical" is done:

* **`step_call_gas_le` / `step_callcode_gas_le` / `step_delegatecall_gas_le` /
  `step_staticcall_gas_le`** — each CALL-family arm of `step (f+1) (C' s w) (w,_) s`
  lands at gas `≤ s.gas`, given child `Θ (f-1)` mono. The arg-matching reconciles the
  `call`-arm's `Ccallgas(t,r,val,g)` with `C' s w = Ccall(stack-args)`: `pop7_stack_index`
  / `pop6_stack_index` give `μᵢ = s[i]!`, and `accountAddr_roundtrip` handles the
  `CALLCODE`/`DELEGATECALL` recipient round-trip (`ofUInt256 (ofNat codeOwner) = codeOwner`).
  Then `Ccallgas_le_Ccall` closes it. (`pop_of_liftM` inverts the monadic stack-pop lift.)
* **`step_gas_le`** — the UNIFIED per-instruction bound: dispatches CREATE/CREATE2 →
  `create*_result_gas_le` (child `Lambda f`), CALL family → the four lemmas above (child
  `Θ (f-1)`), default → `step_default_gas_le` (unconditional). This is the `hstep` the loop needs.
* **`X_loop_gas_le'`** — strengthening of `X_loop_gas_le` whose `hstep` may assume
  `cost = C' s' w` (`Z_ok_cost_le_gas` supplies it in the loop) — required for the
  CALL/CREATE arms of `step_gas_le`.
* **`Θ_gas_le_code`** — `Θ (n+1) … (.Code code) … g` returns leftover `≤ g`, given child
  `Ξ n` mono (`hΞ`). All three result sources (swallowed-error `g'=⟨0⟩`, revert, success).
* **`Ξ_gas_le`** — `Ξ (n+1) … g` returns leftover `≤ g`, given child `X n` mono on the
  fresh child state (gas exactly `g`).
* **`Lambda_gas_le`** — `Lambda (n+1) … g` returns leftover `≤ g`, given child `Ξ n` mono.
  Success `g' = .ofNat (if F then 0 else gStarStar − codeDeposit)` bounded via
  `ite_zero_sub_le` + `ofNat_le_of_le`.
* **`xiResultGas`** / **`resultGas`** / **`ofNat_le_of_le`** — the result-gas projections
  and the `.ofNat`-no-wrap closer threaded through all the above.

### REMAINING for the *fully nested* headline (precise, NOT faked)

### CLOSED (this run, G1) — the precompiled `Θ`-gas arm
* **`Θ_gas_le_precompiled`** — the `.Precompiled pc` arm of `Θ`-gas-monotonicity
  (non-recursive, NO child hypothesis), assembled from the 10 per-contract `Ξ_*`-gas bricks
  `ecrec_gas_le`/…/`point_eval_gas_le` + the generic `gas_branch_le`, all in the sibling
  module `NestedEvmYul.PrecompileGas` (the FFI-backed precompiles overflow the worker-thread
  stack under `lake build` unless split out + the lakefile `-s` flag is set). This finishes
  the LAST brick of (former) item 1.

### CLOSED (this run, N1) — the strict CALL/CREATE X-iteration descent
* **`step_call_gas_lt` / `step_callcode_gas_lt` / `step_delegatecall_gas_lt` /
  `step_staticcall_gas_lt`** — the STRICT companions of the `step_*_gas_le` CALL-family
  reductions: route to `call_result_gas_lt` with the strict `Ccallgas < Ccall`
  (`Ccallgas_lt_Ccall`). CONDITIONAL on child `Θ (f-1)` gas-mono (`hΘ`), discharged by A1.
* **`step_gas_lt`** — unified strict per-instruction descent for ANY CALL/CREATE opcode:
  CREATE/CREATE2 → `create*_result_gas_lt` (with `C'_create*_pos` discharging the strict
  debit), CALL family → the four lemmas above. CONDITIONAL on `hΘ` + `hΛ`.
* **`X_iter_gas_lt_callcreate`** — the CALL/CREATE companion of `X_iter_gas_lt` (drops the
  `¬ isCallCreate` gate): a non-halting `X (f+1)` CALL/CREATE iteration drops gas strictly,
  via `Z_ok_cost_le_gas` + `step_gas_lt`. CONDITIONAL on `hΘ` + `hΛ`.
* **`X_iter_gas_lt_any`** — the UNIFIED per-iteration descent (leaf via `X_iter_gas_lt`
  unconditional + call/create via `X_iter_gas_lt_callcreate`); the single descent A1 feeds
  the never-`OutOfFuel` loop measure. The child hyps are vacuous on leaf opcodes.

### REMAINING for the *fully nested* headline (precise, NOT faked)

1. **Gas-monotonicity mutual induction — ASSEMBLY only.** ALL per-layer reductions
   (incl. `Θ_gas_le_precompiled`, G1) are proved; what remains is the single strong
   induction on `fuel` tying them into the mutual fixpoint `gas_mono n : Θ_gas_le n ∧
   Ξ_gas_le n ∧ X_gas_le n ∧ Lambda_gas_le n ∧ step_gas_le n`, feeding the IH at `< n` to
   each reduction's child hypothesis (`X_gas_le` via `X_loop_gas_le'` needs `step_gas_le` at
   all `f`, hence strong induction). No bricks missing — pure assembly (A1).

2. **Never-`OutOfFuel` mutual induction with the depth-aware bound `B`.** Strong
   induction on `fuel` over the layers, each `P_·` reading "`fuel ≥ B gas depth →
   layer ≠ OutOfFuel`". The propagation skeletons (`*_outOfFuel_of`) are the `fuel+1`
   steps; `X_iter_gas_lt_any` (N1) supplies the per-iteration gas descent that bottoms out
   the `X` loop on EVERY iteration (call/create AND leaf), generalising
   `X_loop_noncallcreate` to drop `hnc`, using the strict bricks like `X_loop_gas_le'` uses
   the non-strict ones; at each descent the child's `Θ/Ξ/X` are at strictly smaller fuel AND
   larger depth, so the IH discharges them once `B` is threaded. **`B` is the LINEAR-PRODUCT
   bound `B(g,d) = (1025−d)·(g+c)` (B2i correction — see PLAN.md; NOT the super-linear
   shape sketched below).** This induction (A1) is NOT YET STARTED — the headline does not
   close this run.

   **Bound shape.** The per-frame `X`-loop runs up to `gas` iterations, and *each* may
   spawn a child needing its own full budget `B childgas (depth+1)`, so `B` is
   **super-linear in gas across depth** (`≈ (gas+1)^(1025−depth)`) — defined by
   recursion on the depth-countdown `k = 1025 − depth`:

       B 0     gas = gas + 2
       B (k+1) gas = (gas + 1) * (B k gas + c) + 2     -- c = the X→step→call→Θ→Ξ hops

   so the recurrence holds *definitionally* (assembly arithmetic is a few `omega`/unfold
   steps). The top-level headline instantiates at the initial depth. The original
   `seedFuel g = 4*(g+1)` and the linear product `(1025−depth)*4*(gas+1)` are both
   insufficient (no per-iteration child multiplicity); the sound seed is `B`.
-/

end EvmYul.EVM.NeverOutOfFuel
