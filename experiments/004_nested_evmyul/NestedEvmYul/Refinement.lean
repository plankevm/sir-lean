import NestedEvmYul.SharedObservable

/-!
# The NESTED refinement half against the shared spec

This is the **nested** (`«evmyul»` / exp004) half of the cross-engine refinement.
Its flat mirror is `EVM/BytecodeLayer/Equivalence.lean`
(`emptyObs`, `equivGoalEmpty`).

Cross-engine equivalence is realized as **refinement through a shared spec**: each
engine proves that its observable of a do-nothing program equals the SAME shared
`emptyObs` literal. Here we discharge the nested side for the smallest concrete
do-nothing program — a **single-`STOP` top-level call** (`c = ToExecute.Code ⟨#[0x00]⟩`)
on an empty (untouched) account map with a fresh substate and value `0`.

The result is `observe_nested (runΘ w)` agrees with `emptyObs` at the run's own gas:
`tag = "ok"`, `output = []`, `logs = []`, and storage all-zero. Gas is each engine's
own value (the spec's gas is set to the observable's own gas, so that equality is
`rfl`); exact-gas across engines is a deliberate follow-up (see report).

## Proof architecture

`Θ` is a large mutual recursion (`Θ → Ξ → X → step`, ~140-arm opcode match). Brute
`decide`/`simp` of a full run diverges (the `decode`/`Z` gas machinery loops in `whnf`).
We instead reduce *along the STOP path only*, via small `rfl`/`decide`-closed lemmas
for each layer (`decode_stop`, `Z_stop`, `step_stop`, `H_stop`, `X_stop`, `Xi_stop`),
then evaluate the (concrete, empty-`σ`, `v = 0`) top-level `Θ` bookkeeping. All STOP
gas costs are `0` (`Wzero`/`Gzero`, no memory expansion), so every `Z` guard passes
vacuously and no gas hypothesis is needed.
-/

set_option maxHeartbeats 4000000

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## Per-layer STOP-path reduction lemmas -/

/-- STOP has no memory expansion: its `μᵢ'` is the entry `activeWords` (the `_` arm). -/
theorem memexp_stop (s : EVM.State) : memoryExpansionCost s Operation.STOP = 0 := by
  unfold memoryExpansionCost
  show Cₘ s.activeWords - Cₘ s.activeWords = 0
  exact Nat.sub_self _

/-- STOP's instruction gas is `Gzero = 0` (it is in `Wzero`). -/
theorem cprime_stop (s : EVM.State) : C' s Operation.STOP = 0 := rfl

/-- `decode` of the single-`STOP` code at `pc = 0` yields `STOP` with no argument. -/
theorem decode_stop : decode ⟨#[0x00]⟩ ⟨0⟩ = some (Operation.STOP, none) := rfl

/-- `H` halts the execution loop on `STOP` with empty return data. -/
theorem H_stop (μ : MachineState) : H μ Operation.STOP = some .empty := rfl

/-- The gas/validity gate `Z` passes STOP unconditionally (all costs `0`, no stack
demands, STOP is neither a jump/store/create nor static-mode-restricted), returning
the entry state (modulo the `- 0` cost subtraction) and zero `cost₂`. -/
theorem Z_stop (vj : Array UInt256) (s : EVM.State) (hstk : s.stack = []) :
    Z vj Operation.STOP s = .ok ({s with gasAvailable := s.gasAvailable - UInt256.ofNat 0}, 0) := by
  unfold Z
  rw [memexp_stop]
  simp only [cprime_stop, hstk, Nat.not_lt_zero, reduceIte]
  norm_num [δ, α, W, notIn, belongs, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by decide), if_neg (by simp), if_neg (by simp), if_neg (by simp),
      if_neg (by intro hh; exact absurd hh.2 (by decide)), if_neg (by simp), if_neg (by decide)]

/-- The EVM `step` of STOP succeeds, leaving `toState` (accountMap, substate,
executionEnv, createdAccounts) untouched — only the machine state changes. -/
theorem step_stop (f : ℕ) (s : EVM.State) :
    ∃ s', EVM.step (f+1) 0 (some (Operation.STOP, none)) s = .ok s' ∧ s'.toState = s.toState := by
  unfold EVM.step
  simp only [bind, Except.bind, pure, Except.pure]
  unfold EvmYul.step
  simp only [Id.run]
  exact ⟨_, rfl, rfl⟩

/-- One STOP iteration of the execution loop `X`: decode → gate → step → halt.
Succeeds with empty output; the resulting state keeps the entry `toState`
(accountMap/substate/createdAccounts/executionEnv), only touching the machine state. -/
theorem X_stop (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hcode : s.executionEnv.code = ⟨#[0x00]⟩) (hpc : s.pc = ⟨0⟩) (hstk : s.stack = []) :
    ∃ s', X (f+2) vj s = .ok (.success s' .empty) ∧ s'.toState = s.toState := by
  unfold X
  simp only [hcode, hpc, decode_stop, Option.getD]
  rw [Z_stop vj s hstk]
  simp only [bind, Except.bind]
  obtain ⟨s', hstep, hst⟩ := step_stop f {s with gasAvailable := s.gasAvailable - UInt256.ofNat 0}
  rw [hstep]
  simp only [H_stop, beq_iff_eq, reduceCtorEq, reduceIte]
  exact ⟨s', rfl, hst⟩

/-- The code-execution function `Ξ` on the single-`STOP` code: succeeds, returning the
entry `σ`/`A`/`createdAccounts` unchanged (STOP touches only the machine state). -/
theorem Xi_stop (f : ℕ) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩) :
    ∃ g', Ξ (f+3) cA gh bl σ σ₀ g A I = .ok (.success (cA, σ, g', A) .empty) := by
  rw [Ξ]
  simp only [bind, Except.bind]
  -- `freshEvmState = { default with accountMap := σ, substate := A, createdAccounts := cA,
  -- executionEnv := I, … }`, with `pc = default.pc = ⟨0⟩` and `stack = default.stack = []`.
  obtain ⟨s', hX, hst⟩ := X_stop (s := { (default : EVM.State) with accountMap := σ, σ₀ := σ₀, substate := A, executionEnv := I, blocks := bl, genesisBlockHeader := gh, createdAccounts := cA, gasAvailable := g }) f (D_J I.code ⟨0⟩) hcode rfl rfl
  -- Zeta-reduce `hX`'s state literal so it matches the goal's (`default.field` form).
  simp only [] at hX
  rw [hX]
  refine ⟨s'.gasAvailable, ?_⟩
  simp only []
  -- The success projection reads `toState` fields, all preserved by `hst`.
  have hacc : s'.accountMap = σ := by rw [show s'.accountMap = s'.toState.accountMap from rfl, hst]
  have hsub : s'.substate = A := by rw [show s'.substate = s'.toState.substate from rfl, hst]
  have hcr  : s'.createdAccounts = cA := by
    rw [show s'.createdAccounts = s'.toState.createdAccounts from rfl, hst]
  rw [hacc, hsub, hcr]

/-! ## The concrete `Θ`-reduction of the do-nothing run -/

/-- A do-nothing nested world: a single-`STOP` top-level `Code` call on an **empty**
account map, with a fresh substate (empty `logSeries`) and zero transferred value.
The remaining positional arguments are free; `g`/`e` only feed `seedFuel`. -/
structure IsDoNothing (w : NestedWorld) : Prop where
  /-- The called code is a single `STOP` byte. -/
  code  : w.c = ToExecute.Code ⟨#[0x00]⟩
  /-- The account map is empty (untouched): every storage slot reads `0`. -/
  empty : w.σ = ∅
  /-- The substate is the default (empty log series). -/
  subst : w.A = default
  /-- No value is transferred, so the balance bookkeeping is a no-op on the empty map. -/
  value : w.v = ⟨0⟩
  /-- The call depth is within bounds, so the fuel envelope is `≥ 1` (`Θ` does not
  hit its `OutOfFuel` floor) and the run is genuinely fuel-free. -/
  depth : w.e ≤ 1024

/-- The seed-fuel envelope is positive when the depth is in bounds — enough succ
peels for `Θ → Ξ → X → step` along the STOP path. -/
theorem fuelBound_pos (g e : ℕ) (he : e ≤ 1024) : 1 ≤ NeverOutOfFuel.fuelBound g e := by
  unfold NeverOutOfFuel.fuelBound
  have h1 : 1 ≤ 1025 - e := by omega
  have h2 : 1 ≤ g + NeverOutOfFuel.fuelHops := by unfold NeverOutOfFuel.fuelHops; omega
  calc 1 = 1 * 1 := by ring
    _ ≤ (1025 - e) * (g + NeverOutOfFuel.fuelHops) := Nat.mul_le_mul h1 h2

/-- The do-nothing run succeeds with empty output, the entry (empty) map and the
entry (default) substate. This is the load-bearing Θ-reduction lemma: the
single-`STOP` code drives `Ξ → X → step` to a clean success, and because the entry
map is empty and `v = 0`, Θ's `σ'`/`A'` post-processing returns the *entry* map and
substate (`σ'' == ∅` branch, eqns 127/129). -/
theorem runΘ_doNothing (w : NestedWorld) (h : IsDoNothing w) :
    ∃ cA g', runΘ w
      = .ok (cA, (∅ : AccountMap), g', (default : Substate), true, ByteArray.empty) := by
  obtain ⟨hc, hσ, hA, hv, he⟩ := h
  -- Peel the seed fuel into `m + 3` (`fuelBound ≥ 1`), exposing 3 succ layers.
  obtain ⟨m, hm⟩ : ∃ m, NeverOutOfFuel.fuelBound w.g.toNat w.e = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (fuelBound_pos _ _ he)).symm⟩
  unfold runΘ seedFuel
  rw [hm, hc, hσ, hA, hv]
  -- Θ matches `fuel + 1` with `fuel = m + 3`; the `Code` arm calls `Ξ (m + 3)` on the
  -- entry-balance map `σ₁`. With `σ = ∅`/`v = 0`, the find?/insert bookkeeping is a
  -- no-op: `σ₁` collapses back to `∅`.
  simp only [Θ,
             show Batteries.RBMap.find? (∅ : AccountMap) w.r = none from rfl,
             show (({ val := 0 } : UInt256) != { val := 0 }) = false from by decide,
             Bool.false_eq_true, if_false,
             show Batteries.RBMap.find? (∅ : AccountMap) w.s = none from rfl]
  -- Discharge `Ξ` along the STOP path: it returns `(cA, ∅, g', default)` unchanged.
  obtain ⟨g', hXi⟩ := Xi_stop m w.createdAccounts w.genesisBlockHeader w.blocks ∅ w.σ₀ w.g default
    { codeOwner := w.r, sender := w.o, source := w.s, weiValue := w.v', calldata := w.d,
      code := ⟨#[0x00]⟩, gasPrice := w.p.toNat, header := w.H, depth := w.e, perm := w.w,
      blobVersionedHashes := w.blobVersionedHashes } rfl
  rw [hXi]
  -- Θ's `Code` success arm packs `(cA, true, ∅, g', default, .empty)`, then post-processes:
  -- `σ' = if ∅ == ∅ then σ else ∅ = ∅` and `A' = if ∅ == ∅ then A else _ = default`.
  exact ⟨w.createdAccounts, g', rfl⟩

/-! ## The refinement -/

/-- The shared observable a do-nothing top-level call must produce on **both**
engines: completed (`"ok"`), empty output, empty logs, gas `g`, all-zero storage.
**Field-identical** to the flat side's `BytecodeLayer.emptyObs`. -/
def emptyObs (g : Option Nat) : SharedObservable :=
  { tag := "ok", output := [], gas := g, logs := [], storageAt := fun _ _ => 0 }

/-- `observe_nested`'s `output` of empty return data is the empty list (`ByteArray`'s
`toList` of `empty` is `[]`, which is not `rfl` — the byte-loop must be peeled). -/
theorem ofBytes_empty : SharedObservable.ofBytes ByteArray.empty = [] := by
  unfold SharedObservable.ofBytes ByteArray.toList
  rw [ByteArray.toList.loop]; simp

/-- **The nested refinement.** Under the do-nothing description, the nested run
observes as the canonical do-nothing spec (`emptyObs` at the run's own gas): same
tag (`"ok"`), output (`[]`), gas (`rfl`), logs (`[]`), and pointwise-zero storage. -/
theorem nested_refines_emptyObs (w : NestedWorld) (h : IsDoNothing w) :
    (observe_nested (runΘ w)).agrees (emptyObs (observe_nested (runΘ w)).gas) := by
  obtain ⟨cA, g', hrun⟩ := runΘ_doNothing w h
  rw [hrun]
  refine ⟨⟨rfl, ?_, rfl, ?_⟩, ?_⟩
  · -- output: empty return data normalizes to `[]`.
    show SharedObservable.ofBytes ByteArray.empty = []
    exact ofBytes_empty
  · -- logs: `default.logSeries` is empty, so the mapped log list is `[]`.
    show List.map SharedObservable.ofNestedLog (default : Substate).logSeries.toList = []
    rfl
  · -- storage: the entry map is empty, so `observe_nested`'s `storageAt` is `0`.
    intro addr key
    show (match List.find? (fun p => decide (↑p.1 = addr)) (Batteries.RBMap.toList (∅ : AccountMap)) with
          | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat | none => 0) = 0
    rfl

/-- A fully-proved sanity lemma (no proof placeholder): the nested `emptyObs` data-agrees with
itself whenever the gas matches, and any two `emptyObs` agree pointwise on storage.
Mirror of the flat `emptyObs_storageAgrees`/`emptyObs_dataAgrees`. -/
theorem emptyObs_storageAgrees (g g' : Option Nat) :
    (emptyObs g).storageAgrees (emptyObs g') := by
  intro _ _; rfl

theorem emptyObs_dataAgrees (g : Option Nat) :
    (emptyObs g).dataAgrees (emptyObs g) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end NestedEvmYul
