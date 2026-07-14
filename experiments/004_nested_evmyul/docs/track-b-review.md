# Track B review — nested-EVM never-`OutOfFuel` over a Yul-stripped EVMYulLean (exp004)

*Specs-first review for the project lead. Read-only on code. Every code reference
links to the current source; the load-bearing definitions and statements are quoted
verbatim. Proof bodies are deliberately omitted — at most a one-line strategy. All
links are relative to this file's directory (`experiments/004_nested_evmyul/docs/`);
the Lean is one level up (`../NestedEvmYul/…`, `../EVMYulLean/…`).*

---

## TL;DR

Track B is the **nested** half of the flat-vs-nested bake-off (exp003 = flat `drive`;
exp004 = NethermindEth's mutual `Θ/Ξ/X/step/call/Lambda` fuel-passing recursion). It
vendors EVMYulLean, **monomorphizes it to EVM-only** (B0: the `OperationType = Yul | EVM`
polymorphism and the whole Yul subsystem are gone), and proves the nested analogue of
exp003's `messageCall_never_outOfFuel`. The headline just CLOSED:
[`Θ_never_outOfFuel`](../NestedEvmYul/NeverOutOfFuel.lean#L4665) — once the fuel meets the
depth-aware **LINEAR-PRODUCT** bound
[`fuelBound g e = (1025 − e)·(g + fuelHops)`](../NestedEvmYul/NeverOutOfFuel.lean#L3919)
(plus a `+3` hop offset) and the depth `e ≤ 1024`, a top-level message call `Θ` never
returns `.error .OutOfFuel`, **for arbitrary CALL/CALLCODE/DELEGATECALL/STATICCALL/
CREATE/CREATE2 nesting to depth 1024**. The single most important design correction:
the bound is **linear in gas with a depth factor**, NOT the super-linear `(g+1)^(1025−d)`
the early sketches (and the still-stale milestone text, §7) feared — fuel is a
pass-by-value structural counter, so the binding constraint is the single worst loop
iteration, giving an *additive* depth recurrence.

The proof rests on **two mutual inductions** —
[`gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4071) (6-layer gas-monotonicity,
standalone) and [`never_oof`](../NestedEvmYul/NeverOutOfFuel.lean#L4543) (5-layer
never-OOF; only 5 because CREATE/CREATE2 swallow their child `Lambda`'s `OutOfFuel`) —
and a ~250-line per-opcode **depth-preservation** sweep
([`step_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1218)/[`Z_ok_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1399))
making `fuelBound`'s depth index a sound loop invariant.

**Status (reported from [PLAN.md#L62](../PLAN.md#L62), not re-run):** `lake build
NestedEvmYul.NeverOutOfFuel` GREEN; `#print axioms` on every result ⊆ `[propext,
Classical.choice, Quot.sound]`; grep-clean. I independently confirmed: the only
`sorry`/`native_decide`/`bv_decide` string in `NestedEvmYul/` is inside a docstring
([NeverOutOfFuel.lean#L33](../NestedEvmYul/NeverOutOfFuel.lean#L33)); zero forbidden
tactics in proof bodies; `OperationType` survives only as one comment in the vendored
lakefile. **Caveat:** the headline is a never-OOF *fuel↔gas* theorem (B2); the
external-call **triple/frame rule (B3)** and the **observables-only IR surface (B4)** are
not yet built (§7). Two operational smells: 50 cranked-`maxHeartbeats` sites in the
4.7-kLOC proof file, and an FFI-precompile worker-stack hack in the lakefile (`-s`).

---

## 1. Goal & context

The real-world property is exactly exp003's, on the *other* semantics: **a top-level
message call, given enough fuel, never spuriously runs out of the interpreter's
structural step counter** — so `OutOfFuel` is never observed as a (fake) execution
outcome, and fuel can later be discharged from a gas bound. exp003 proved this over the
flat `drive` ([`messageCall_never_outOfFuel`](../../../EVM/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158));
Track B proves it over the **genuinely nested** EVMYulLean recursion, where a child call
is a real subterm rather than a flattened pending-stack entry
([PLAN.md Goal](../PLAN.md#L6)). The bake-off question ([currentplan.md] END-GOAL): if
both semantics prove the *same* surface theorems, they are interchangeable for IR
reasoning under a shared `EVMSemantics` interface.

The nested semantics is harder here precisely because of nesting: the never-OOF measure
must descend through `Θ → Ξ → X → step → call → Θ …` recursively, and the fuel budget a
parent hands a child must be carved out of the parent's own gas while the call depth is
capped. The bake-off finding recorded in the orchestration log — *"nested never-OOF
[is] dramatically harder than flat"* — is borne out by the 4.7-kLOC proof
([NeverOutOfFuel.lean](../NestedEvmYul/NeverOutOfFuel.lean)) versus exp003's compact
unconditional theorem.

---

## 2. The B0 monomorphization and the vendoring model

The base semantics is **vendored in-tree** under
[`EVMYulLean/`](../EVMYulLean/EvmYul/EVM/Semantics.lean) as a squashed subtree of
NethermindEth/EVMYulLean, then **monomorphized to EVM-only (B0)**: the upstream
`OperationType = Yul | EVM` polymorphism and the τ-indexed types are specialized to their
EVM instances and the whole `EvmYul/Yul/` subsystem is deleted
([lakefile.lean#L4](../lakefile.lean#L4), [PLAN.md B0](../PLAN.md#L24)). I confirmed the
strip is complete: a tree-wide grep finds `OperationType` only in a single explanatory
comment ([EVMYulLean/lakefile.lean#L74](../EVMYulLean/lakefile.lean#L74)) — no remaining
`τ`-indexing, no `Yul` constructor in the live semantics. The reasoning core then
`import EvmYul.EVM.Semantics` and treats these definitions as the trusted model
([NestedEvmYul.lean#L4](../NestedEvmYul.lean#L4)).

The nested mutual block is six layers ([Semantics.lean#L139](../EVMYulLean/EvmYul/EVM/Semantics.lean#L139)):
[`call`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L141),
[`step`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L221),
[`X`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L494) (the per-instruction loop),
[`Ξ`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L529) (build a fresh child machine, run `X`,
return a result tuple), [`Lambda`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L566) (CREATE),
and [`Θ`](../EVMYulLean/EvmYul/EVM/Semantics.lean#L721) (the top-level message call). Each
matches `fuel` first and emits `.error .OutOfFuel` exactly on `0` — these fuel-`0` base
cases ([`X_zero`](../NestedEvmYul/NeverOutOfFuel.lean#L81),
[`step_zero`](../NestedEvmYul/NeverOutOfFuel.lean#L84),
[`call_zero`](../NestedEvmYul/NeverOutOfFuel.lean#L88),
[`Ξ_zero`](../NestedEvmYul/NeverOutOfFuel.lean#L94),
[`Θ_zero`](../NestedEvmYul/NeverOutOfFuel.lean#L100)) are the *only* syntactic
`OutOfFuel` producers; everything else propagates. So the bound only has to keep every
recursive descent away from `fuel = 0`.

---

## 3. The abstraction stack (bottom → top)

Three reasoning modules sit on the vendored semantics. The proof content is one large
file; the two small modules exist purely to keep FFI-heavy kernel reductions out of it.

| Layer | File | Job |
|---|---|---|
| **L0 — vendored EVM semantics** | [`EVMYulLean/EvmYul/EVM/Semantics.lean`](../EVMYulLean/EvmYul/EVM/Semantics.lean) | The trusted Yul-stripped, EVM-monomorphized mutual `Θ/Ξ/X/step/call/Lambda` fuel-passing recursion. |
| **L1 — gas arithmetic helpers** | [`GasArith.lean`](../NestedEvmYul/GasArith.lean) | `UInt256` gas-subtraction bounds ([`gas_sub_le`](../NestedEvmYul/GasArith.lean#L17), [`gas_branch_le`](../NestedEvmYul/GasArith.lean#L35), [`match_proj_le`](../NestedEvmYul/GasArith.lean#L48)) as *imported opaque constants* so the kernel never unfolds them with an FFI precompile body. |
| **L1 — precompile gas-mono bricks** | [`PrecompileGas.lean`](../NestedEvmYul/PrecompileGas.lean) | The `.Precompiled` arm of `Θ`'s gas-mono: each `Ξ_*` precompile returns leftover gas `≤ g` ([`ecrec_gas_le`](../NestedEvmYul/PrecompileGas.lean#L26) … [`point_eval_gas_le`](../NestedEvmYul/PrecompileGas.lean#L118)). Split out because the FFI-backed ones (`BN_MUL`/`SNARKV`/…) overflow kernel whnf inside the big unit. |
| **L2 — the proof core** | [`NeverOutOfFuel.lean`](../NestedEvmYul/NeverOutOfFuel.lean) (4.7 kLOC) | Positivity cornerstone → gas-descent chain → depth keystones → the two mutual inductions → headline. |

**Dependency spine to the headline.**
[`Θ_never_outOfFuel`](../NestedEvmYul/NeverOutOfFuel.lean#L4665)
→ [`never_oof`](../NestedEvmYul/NeverOutOfFuel.lean#L4543) (its `Θ` conjunct, a one-line
projection)
→ [`X_loop_noOOF_bound`](../NestedEvmYul/NeverOutOfFuel.lean#L4228) (the depth-aware loop)
+ [`gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4071) (Stage-1, supplies post-call gas
descent)
+ the `fuelBound` arithmetic
([`fuelBound_succ`](../NestedEvmYul/NeverOutOfFuel.lean#L3923)/[`_mono_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L3932)/[`_pos`](../NestedEvmYul/NeverOutOfFuel.lean#L3939)/[`_ge`](../NestedEvmYul/NeverOutOfFuel.lean#L3948)).
`X_loop_noOOF_bound` in turn rests on the **cornerstone**
[`C'_pos_of_runnable`](../NestedEvmYul/NeverOutOfFuel.lean#L183) (every runnable opcode
burns ≥ 1 gas), the gas-descent chain
([`X_iter_gas_lt`](../NestedEvmYul/NeverOutOfFuel.lean#L1314)), and the **depth keystones**
[`step_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1218)/[`Z_ok_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1399).

---

## 4. The specs that matter

### 4.1 The fuel bound `fuelBound` (the §N2 design payoff)

The bound is the heart of the design argument. It is **linear in gas, scaled by a depth
factor** — closed-form, not a recurrence:

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L3915
abbrev fuelHops : ℕ := 8

-- NestedEvmYul/NeverOutOfFuel.lean#L3919
/-- The depth-aware fuel bound `B(g,e) = (1025 − e)·(g + c)` (`e` = call depth ≤ 1024).
Linear in gas; the `(1025 − e)` is the depth *factor*. -/
def fuelBound (g e : ℕ) : ℕ := (1025 - e) * (g + fuelHops)
```

Why **linear-product, not super-linear** — this is the corrected story and the key
design argument ([file header](../NestedEvmYul/NeverOutOfFuel.lean#L18),
[§N2](../NestedEvmYul/NeverOutOfFuel.lean#L3899)). Fuel is a **pass-by-value structural
counter**: in the loop body, `X (f+1)` runs `step f` then continues `X f validJumps
evmState'` at the *literal* `f` ([Semantics.lean#L506](../EVMYulLean/EvmYul/EVM/Semantics.lean#L506),
[#L513](../EVMYulLean/EvmYul/EVM/Semantics.lean#L513)) — so after a child call returns,
the parent loop resumes at exactly `f`, **independent of how much fuel the child subtree
burned**. Hence the `g` children a frame can spawn do *not* accumulate budgets; the
binding constraint is the single worst (last) loop iteration. The recurrence is therefore
**additive** in depth, `B g e = (g + c) + B g (e+1)`, captured by:

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L3923
theorem fuelBound_succ (g e : ℕ) (he : e ≤ 1024) :
    fuelBound g e = (g + fuelHops) + fuelBound g (e + 1)
```

This is exactly the arithmetic the CALL/CREATE descent uses to hand the child its budget:
one descent level peels off exactly `(g + fuelHops)`. The earlier (B2e–B2h) sketches
feared `(g+1)^(1025−d)` and a super-linear product; the corrected closed form is
quadratic-worst-case (`(1025−e)·g`) but *additive per descent*. `fuelHops = 8 ≥ 5`
generously covers the per-level `Θ→Ξ→X→step→call` hop chain.

### 4.2 The headline `Θ_never_outOfFuel`

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L4665
theorem Θ_never_outOfFuel (fuel : ℕ) (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (he : e ≤ 1024) (hfuel : fuelBound g.toNat e + 3 ≤ fuel) :
    Θ fuel bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w ≠ .error .OutOfFuel :=
  (never_oof fuel).2.2.1 bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w he hfuel
```

**What it claims:** for *any* top-level message call — arbitrary world (`σ`/`σ₀`), gas
`g`, value `v` (no value=0 restriction), callee `c : ToExecute` (Code or Precompiled),
permission `w`, at any depth `e ≤ 1024` — once the fuel clears `fuelBound g.toNat e + 3`,
`Θ` never yields `OutOfFuel`. Only two premises: the budget `hfuel` and the structural
depth cap `he`. No per-arm side conditions, no no-call/create gate. The proof is literally
the `Θ` conjunct of `never_oof`.

### 4.3 The 5-layer never-OOF mutual induction `never_oof`

The headline's engine. Five per-layer predicates, each `fuelBound gas depth + k_L ≤ n →
layer … ≠ OutOfFuel`, bundled into one strong induction on `fuel`:

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L4514  (the Θ predicate; the others mirror it)
def Θ_noOOF_at (n : ℕ) : Prop :=
  ∀ (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Nat) (Hd : BlockHeader) (w : Bool),
    e ≤ 1024 → fuelBound g.toNat e + 3 ≤ n →
    Θ n bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w ≠ .error .OutOfFuel

-- NestedEvmYul/NeverOutOfFuel.lean#L4543
theorem never_oof : ∀ n,
    step_noOOF_at n ∧ call_noOOF_at n ∧ Θ_noOOF_at n ∧ Ξ_noOOF_at n ∧ X_noOOF_at n
```

The per-layer fuel offsets are `k_Θ = 3, k_Ξ = 2, k_X = 1` (the loop's `+1`), `k_step =
0`, and `k_call : fuelBound ≤ n+1` ([predicates at](../NestedEvmYul/NeverOutOfFuel.lean#L4494)).
*Strategy (one sentence): strong induction on `fuel`; each same-depth hop
`Θ→Ξ→X→step→call` drops fuel by 1 and raises `k` by 1 so the bound is preserved by
`omega`; the single depth bump `call → Θ` (`Θ.e := Iₑ+1`) spends the `(g + fuelHops)`
[`fuelBound_succ`](../NestedEvmYul/NeverOutOfFuel.lean#L3923) peel, with the forwarded-gas
bound `Ccallgas ≤ ev.gas` shrinking the child budget via
[`fuelBound_mono_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L3932).*

**Why only 5 layers (no `Lambda`).** This is a real structural point, not an omission.
CREATE/CREATE2 `step` arms are *unconditionally* never-OOF — they **swallow** the child
`Lambda`'s `OutOfFuel` into a result tuple
([`noOOF_step_create`](../NestedEvmYul/NeverOutOfFuel.lean#L2216), file note
[#L4480](../NestedEvmYul/NeverOutOfFuel.lean#L4480)) — so the never-OOF recursion never
descends through `Lambda`, and `never_oof` needs no `Lambda` conjunct. (Gas-monotonicity
still needs `Lambda`, see §4.5, because it must read the leftover gas out of the swallowed
result.) The `call → Θ` arm is the only genuine depth-increasing recursion, gated by
[`call_outOfFuel_of_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L1846) +
[`call_noOOF_of_depth_cap`](../NestedEvmYul/NeverOutOfFuel.lean#L1873) (the `Iₑ = 1024`
edge, where the call is gated off by `Iₑ < 1024` —
[Semantics.lean#L165](../EVMYulLean/EvmYul/EVM/Semantics.lean#L165)).

### 4.4 The depth-aware `X` loop `X_loop_noOOF_bound`

The loop is where the bound bites. `fuelBound s.gas D` is threaded as a **loop invariant**
at the frame's fixed depth `D`:

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L4228
theorem X_loop_noOOF_bound (vj : Array UInt256) (D : ℕ) (hD : D ≤ 1024) (N : ℕ)
    (hstep : ∀ (f : ℕ), f < N → ∀ (w : Operation) (arg) (cost : ℕ) (s2 : State),
       s2.executionEnv.depth = D →
       fuelBound s2.gasAvailable.toNat D ≤ f →
       cost ≤ s2.gasAvailable.toNat →
       cost = C' s2 w →
       step f cost (some (w, arg)) s2 ≠ .error .OutOfFuel) :
    ∀ (fuel : ℕ), fuel ≤ N → ∀ (s : State), s.executionEnv.depth = D →
      fuelBound s.gasAvailable.toNat D + 1 ≤ fuel → X fuel vj s ≠ .error .OutOfFuel
```

*Strategy: induction on `fuel`; gas strictly drops each iteration (via
[`X_iter_gas_lt`](../NestedEvmYul/NeverOutOfFuel.lean#L1314), built on the cornerstone),
so `fuelBound` drops by `≥ (1025−D) ≥ 1`, keeping the invariant `fuelBound ev.gas D + 1 ≤
fuel` as fuel drops by 1. Depth stays `D` across the iteration by the keystones below.*

### 4.5 The gas-monotonicity mutual induction `gas_mono` (Stage 1)

A separate, *6*-layer induction — and notably the **easy** one, because it is **vacuous on
errors** and so needs no never-OOF facts and proves standalone:

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L4071
theorem gas_mono : ∀ n,
    step_gas_mono_at n ∧ call_gas_mono_at n ∧ Θ_gas_mono_at n ∧
    Ξ_gas_mono_at n ∧ Lambda_gas_mono_at n ∧ X_gas_mono_at n
```

Each conjunct says: a *successful* layer result returns leftover gas `≤` the gas it was
handed ([`X_gas_mono_at`](../NestedEvmYul/NeverOutOfFuel.lean#L4063), read via
[`resultGas`](../NestedEvmYul/NeverOutOfFuel.lean#L2377)). It **includes `Lambda`** (unlike
`never_oof`) precisely because CREATE's leftover gas has to be read out of the swallowed
child result. The per-layer corollaries
([`Θ_gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4147) …
[`call_gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4157)) feed the post-call gas
descent `never_oof`'s loop measure needs. The `.Precompiled` arm of `Θ_gas_mono` is
discharged by the [PrecompileGas](../NestedEvmYul/PrecompileGas.lean#L26) bricks.

**The separation is the design point:** gas-monotonicity and never-OOF are different
properties (one about *the value returned*, one about *not erroring*), with different layer
sets (`Lambda` in/out) and different difficulty (vacuous-on-error vs. genuine descent), so
they are two inductions, with `gas_mono` proved first and consumed by `never_oof`.

### 4.6 The depth-preservation keystone (`step_depth` / `Z_ok_depth`)

`fuelBound`'s depth index `D` is only a sound loop invariant if the frame depth does not
move across a loop iteration. Two theorems pin that — and they cost a **~250-line
per-opcode sweep** (the `executionEnv`-preservation lemmas
[`ee_*`](../NestedEvmYul/NeverOutOfFuel.lean#L809) over every combinator and inline arm,
assembled into [`ee_EvmYul_step`](../NestedEvmYul/NeverOutOfFuel.lean#L1104) and
[`step_ee`](../NestedEvmYul/NeverOutOfFuel.lean#L1155)):

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L1218
theorem step_depth (f : ℕ) (cost : ℕ) (w : Operation) (a : Option (UInt256 × Nat))
    (s s' : State) (h : step (f+1) cost (some (w, a)) s = .ok s') :
    s'.executionEnv.depth = s.executionEnv.depth

-- NestedEvmYul/NeverOutOfFuel.lean#L1399
theorem Z_ok_depth (vj : Array UInt256) (w : Operation) (s s' : State) (c : ℕ)
    (h : Z vj w s = .ok (s', c)) :
    s'.executionEnv.depth = s.executionEnv.depth
```

The sweep is needed because `step` dispatches a 140-arm opcode `match`; depth-invariance is
proved arm-by-arm (each combinator/inline arm only rewrites gas/stack/pc, never `depth`)
and reassembled, rather than re-elaborating the giant match. These two facts let
`X_loop_noOOF_bound` carry `D` unchanged through `Z` then `step`
([usage at #L4258](../NestedEvmYul/NeverOutOfFuel.lean#L4258)).

### 4.7 The cornerstone: per-step gas positivity

```lean
-- NestedEvmYul/NeverOutOfFuel.lean#L183
theorem C'_pos_of_runnable (s : State) (w : Operation) (hw : runnable w) : 1 ≤ C' s w
```

Every [`runnable`](../NestedEvmYul/NeverOutOfFuel.lean#L163) opcode (anything but
`STOP/RETURN/REVERT/SELFDESTRUCT/INVALID`) burns `≥ 1` gas — the only `C' = 0` opcodes
either halt the loop via `H` or self-error in `step` (never `OutOfFuel`). This is what
makes gas a *strictly* decreasing well-founded measure on the loop. *Strategy: case on the
grouped `Operation`, route non-constant arms through the positivity helpers
([`Csstore_pos`](../NestedEvmYul/NeverOutOfFuel.lean#L118) etc.), close the rest by a
`decide`-after-membership-guard closer.*

---

## 5. Hypotheses & modeling

**World model.** State is the vendored EVMYulLean `EVM.State` (accounts `σ`, a `σ₀`
snapshot, `Substate`, an `ExecutionEnv` carrying the call `depth`, `gasAvailable`, blocks,
headers). Execution is the nested mutual recursion; "fuel" is a structural ℕ step counter
threaded pass-by-value, distinct from `gasAvailable` (the real EVM gas). The measure that
bounds fuel is *gas*: out-of-gas is itself a halt, so the gas a frame holds bounds its
loop iterations, and the gas forwarded to a child is carved out of the parent
([`Cgascap_le_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L1433),
[`Ccallgas_le_Ccall`](../NestedEvmYul/NeverOutOfFuel.lean#L2455)).

**Hypotheses of the headline — both honest, neither smuggling the conclusion.**
- `he : e ≤ 1024` — the structural EVM call-depth cap. Genuinely load-bearing: at depth
  `1024` the semantics gates the recursive `Θ` off entirely
  ([Semantics.lean#L165](../EVMYulLean/EvmYul/EVM/Semantics.lean#L165)), so the `call`
  conjunct's depth-cap edge ([`call_noOOF_of_depth_cap`](../NestedEvmYul/NeverOutOfFuel.lean#L1873))
  closes without recursing. Not a smell — it is the real EVM invariant.
- `hfuel : fuelBound g.toNat e + 3 ≤ fuel` — the fuel budget. This is the *conclusion's
  enabling resource*, not a smuggle: it is a numeric lower bound on a supplied counter,
  computed from the (honest) gas `g` and depth `e`, exactly analogous to exp003's flat fuel
  side condition. The `+3` is the `Θ → Ξ → X` hop offset.

**No hidden modeling shortcuts I could find.** The headline quantifies over arbitrary
value `v` (no value=0 assumption), arbitrary callee `c` (Code *and* Precompiled arms both
discharged), and all six CALL/CREATE-family opcodes
([`isCallCreate`](../NestedEvmYul/NeverOutOfFuel.lean#L694), dispatched at
[#L4567](../NestedEvmYul/NeverOutOfFuel.lean#L4567)). The bound is the only thing assumed
about fuel.

---

## 6. Results taxonomy

**Headline / mainline.**
[`Θ_never_outOfFuel`](../NestedEvmYul/NeverOutOfFuel.lean#L4665) — the fully-nested,
axiom-clean never-OOF theorem (B2's deliverable).

**Supporting bricks (load-bearing scaffolding).**
- The two mutual inductions: [`never_oof`](../NestedEvmYul/NeverOutOfFuel.lean#L4543)
  (5-layer) and [`gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4071) (6-layer) + its
  corollaries ([`Θ_gas_mono`](../NestedEvmYul/NeverOutOfFuel.lean#L4147)…).
- The depth-aware loop [`X_loop_noOOF_bound`](../NestedEvmYul/NeverOutOfFuel.lean#L4228)
  and the raw [`X_loop_noOOF`](../NestedEvmYul/NeverOutOfFuel.lean#L4170) /
  [`X_loop_noncallcreate`](../NestedEvmYul/NeverOutOfFuel.lean#L1596).
- Cornerstone + descent: [`C'_pos_of_runnable`](../NestedEvmYul/NeverOutOfFuel.lean#L183),
  [`X_iter_gas_lt`](../NestedEvmYul/NeverOutOfFuel.lean#L1314),
  [`Z_ok_cost_le_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L1238),
  [`gas_EvmYul_step`](../NestedEvmYul/NeverOutOfFuel.lean#L706).
- Depth keystones: [`step_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1218),
  [`Z_ok_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1399) (+ the `ee_*` sweep).
- Descent bricks: [`Cgascap_le_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L1433),
  [`call_outOfFuel_of_gas`](../NestedEvmYul/NeverOutOfFuel.lean#L1846),
  [`Θ_outOfFuel_of_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1767),
  [`Ξ_outOfFuel_of_gas_depth`](../NestedEvmYul/NeverOutOfFuel.lean#L1699),
  [`noOOF_step_call_bound`](../NestedEvmYul/NeverOutOfFuel.lean#L4318) and the CREATE arms.
- Fuel arithmetic: [`fuelBound`](../NestedEvmYul/NeverOutOfFuel.lean#L3919) + its four
  lemmas; the FFI-isolated [GasArith](../NestedEvmYul/GasArith.lean) /
  [PrecompileGas](../NestedEvmYul/PrecompileGas.lean) bricks.

**Examples / demos.** None of the usual concrete-program-witness kind. The closest is the
**leaf fragment** ([`Θ_leaf_noOOF`](../NestedEvmYul/NeverOutOfFuel.lean#L2349),
[`Ξ_leaf_noOOF`](../NestedEvmYul/NeverOutOfFuel.lean#L2331),
[`X_leaf_noOOF`](../NestedEvmYul/NeverOutOfFuel.lean#L2319)) — the *unconditional*
non-nesting never-OOF chain, originally the bake-off's first deliverable. It is now
**subsumed** by the nested headline (which handles call/create iterations too), but is a
genuine standalone result, not a witness. Nothing downstream of the headline consumes the
leaf lemmas; treat them as a now-superseded milestone (§7).

**Smells / weak proofs.**
- **50 cranked-`maxHeartbeats` sites** in [NeverOutOfFuel.lean](../NestedEvmYul/NeverOutOfFuel.lean)
  (ranging `1M`–`8M`, e.g. [#L178](../NestedEvmYul/NeverOutOfFuel.lean#L178) at `8M`,
  [#L4536](../NestedEvmYul/NeverOutOfFuel.lean#L4536) at `4M` on `never_oof`). **Does a
  headline depend on these?** Yes — `never_oof` and `gas_mono` and the cornerstone all sit
  directly under the headline. They are not isolated. The cause is the 140-arm opcode
  `match` and the large gas terms (`C'`, `memoryExpansionCost`) the kernel must reduce; the
  author mitigates by `generalize`-ing heavy discriminants to opaque vars rather than
  `split`. This is the expected cost of an unabstracted vendored model, but it is a real
  fragility under the headline and the single biggest maintainability risk.
- **FFI-precompile worker-stack hack** ([lakefile.lean#L17](../lakefile.lean#L17)):
  `moreLeanArgs := #[…, "-s", "1048576"]` raises the per-thread stack to 1 GB because the
  FFI-backed precompile gas lemmas (`Ξ_BN_MUL`/`SNARKV`/…) overflow the default worker stack
  during `lake build` kernel typechecking (`(kernel) deep recursion detected`), though they
  check fine on the main thread. **Does a headline depend on this?** Indirectly: the
  `.Precompiled` arm of `gas_mono` consumes [PrecompileGas](../NestedEvmYul/PrecompileGas.lean),
  which is the reason for the flag. It is a *build-configuration* smell, not a soundness
  one — the lemmas themselves are axiom-clean — but it signals the vendored FFI precompiles
  are awkward to reduce in-kernel. The [GasArith](../NestedEvmYul/GasArith.lean)/PrecompileGas
  module split (opaque-constant + `generalize` the FFI body) is the deliberate containment.
- No `native_decide`/`bv_decide`/`decide`-on-big-terms under any result; the `decide`s are
  confined to state-free opcode-membership guards inside the `c'_close` closer
  ([#L169](../NestedEvmYul/NeverOutOfFuel.lean#L169)).

---

## 7. Rough edges, open questions, and what B3/B4 still owe

- **The milestone text is stale relative to the closed proof (doc↔source).**
  [PLAN.md milestone B2](../PLAN.md#L31) still describes the bound as a **super-linear**
  `B (k+1) gas = (gas+1)·(B k gas + c) + 2` and asserts "the linear product
  `(1025−depth)·4·(gas+1)` [is] insufficient — corrected in B2e." The **shipped proof
  refutes that**: [`fuelBound`](../NestedEvmYul/NeverOutOfFuel.lean#L3919) *is* the
  linear-product `(1025−e)·(g+8)`, and it closes the induction. The later progress log
  ([PLAN.md#L62](../PLAN.md#L62)) and the file header
  ([#L18](../NestedEvmYul/NeverOutOfFuel.lean#L18)) are correct; the milestone checklist at
  the top is the stale text. **Recommend updating milestone B2's bound description** so a
  reader does not believe a super-linear bound was needed — the linear-product correction
  is the headline design finding.
- **B3 (the external-call triple/frame rule) is not built.** [PLAN.md B3](../PLAN.md#L43)
  owes `{P} Ξ(child) {Q}` + a call-site/frame rule showing ≥2 calls compose naturally — the
  nested analogue of exp003's `Runs.call`/`messageCall_runs_calls`. Track B has proved the
  *fuel↔gas* foundation (B2) the triple would rest on, but the compositional surface
  itself is absent. This is the substantive remaining bake-off deliverable: exp003 has
  multi-call composition (Track A); exp004 does not yet.
- **B4 (observables-only IR surface) is not built.** [PLAN.md B4](../PLAN.md#L45) owes a
  fuel/frame-free observables surface for IR consumers. Per project memory, exp004 (a
  low-level layer) may legitimately surface frame-level rules on its `Spec`, but a fully
  observable surface is the eventual convergence target.
- **The headline is a never-OOF theorem, not a fuel-discharge.** It says "given enough
  fuel, no OOF"; it does **not** yet instantiate `fuel := fuelBound g.toNat e + 3` into a
  fuel-free `Θ` execution the way exp003's bridge discharges fuel entirely. That
  discharge (an unconditional surface) is the natural next step and the precondition for a
  shared `EVMSemantics` interface where flat and nested prove the *same* statement.
- **The leaf fragment is now redundant.** [`Θ_leaf_noOOF`](../NestedEvmYul/NeverOutOfFuel.lean#L2349)
  & co. are unconditionally subsumed by the nested headline. They remain as a standalone
  (and historically-first) result; if nothing consumes them, consider retiring them to
  reduce the 4.7-kLOC file, or keep them as the documented non-nesting special case.
- **Proof-engineering fragility.** The 50 cranked-heartbeat sites and the worker-stack flag
  mean the proof is sensitive to the vendored model's reduction behavior. A future
  abstraction layer over `step`/`C'` (the way exp003 abstracts `drive`) would be the
  principled fix; until then, edits near the big inductions risk heartbeat blow-ups.

### Verdict on the bake-off question

Track B has now matched exp003 on the **never-OutOfFuel** property over the genuinely
nested semantics — and done it *fully nested*, to depth 1024, axiom-clean, with the
important conceptual correction that the fuel bound is linear-product (additive per
descent), not super-linear. That is the hard, model-specific result the flat side got
"for free" from trivial termination. What remains for true interchangeability is the
*compositional* surface (B3) and the observables/fuel-free export (B4) — exactly the parts
where exp003's Track A is currently ahead.
