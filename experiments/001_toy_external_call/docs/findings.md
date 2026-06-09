# Findings: proving a lowering theorem against EVMYulLean's `EVM.X`

This documents what worked, what failed, and why — so the next layer
(richer IR, control flow, transaction boundary) doesn't rediscover it.
The earlier findings about the pre-redesign artifact are superseded; the
historical record of the failed preservation statement lives in
`wrong-attempts.md` and in git history (`Obstruction.lean`, removed).

## About EVMYulLean

* It is an **executable specification**: `EvmYul/EVM/Semantics.lean` proves
  no theorems. Any compositional reasoning needs a bespoke lemma layer.
* `EVM.X` (YP Eq. 159) is the right equivalence target: fuel check →
  `decode` → `Z` (memory-expansion cost `cost₁`, instruction cost `cost₂` =
  `C'`, validity checks) → `step` (trace bump, cost deduction, effect) →
  `H` (halting) → recurse. Fuel decreases by exactly 1 per opcode; `step`
  and `call` only *check* their fuel argument (recursion-depth protection),
  with `call` receiving `fuel - 1` and `Θ` receiving `fuel - 2`.
* Gas subtleties that must be mirrored exactly:
  * `Z` deducts `cost₁` first, then computes `C'` **on the charged state**
    — observable for `CALL`, whose `Ccall` reads the gas counter via
    `Cgascap`.
  * `C'` for `CALL` reads the **stack** (`μₛ[0]`, `μₛ[1]`, `μₛ[2]`).
  * `step` deducts `cost₂` for ordinary ops; `EVM.call` deducts it
    internally *after* computing `Ccallgas` on the undeducted state.
  * `MLOAD`/`MSTORE` update `activeWords` even when reading; evaluation
    order of operands is observable through memory-expansion gas.
  * The very first local access pays the full expansion to `localBase`
    (≈ 2.1 M gas at 1 MiB) — semantically irrelevant for the theorem,
    relevant for choosing test gas budgets.

## Design

* **Locals-as-memory beats locals-as-map.** With a separate locals map the
  preservation statement is false without disjointness hypotheses (a CALL
  may clobber reserved slots). Making local `x` *be* memory word
  `localSlot x` turns the simulation relation into literal record equality
  modulo three frame fields, and `injectFrame` pins those.
* **Mirror the machine's bookkeeping, don't abstract it.** The IR state
  embeds `EVM.State` and tracks `execLength` and fuel faithfully. The
  result equality is then `=`, not a relation — every later proof gets
  cheaper.
* **Oracle signature = the reached `EVM.call` instance.** Fuel and
  `gasCost` are explicit oracle parameters; `CallOracleSound` is stated
  against `injectFrame`-shaped states so the rewrite fires at the exact
  point of use, and bundles frame insensitivity of `EVM.call` (provable
  separately, future work).
* The IR's *gas schedule* is defined to equal the cost of its lowering, so
  gas agreement is partly by construction. The theorem's content is
  everything else: decode/assemble correctness, stack discipline, pc
  threading, the `X` loop, halting, error propagation, and that the
  declared cost formulas are what the EVM actually charges.

## Proof-engineering patterns that worked

1. **List-first byte encoding.** Define `codeBytes : List Op → List UInt8`
   and wrap the `ByteArray` only at the end. All decode lemmas take a
   hypothesis `code.data.toList = l ++ opBytes op ++ r` and use plain list
   lemmas (`getElem?_append_right`, `drop_left'`, `take_left'`). The fork's
   list-based `ByteArray.get?`/`extract'` make this seamless.
2. **`injectFrame` + `@[simp]` `rfl` projections.** One definition pinning
   the frame, with every pass-through projection a `rfl` simp lemma. All
   `Z`/`step`/`X` lemmas are stated on `injectFrame` states.
3. **`step` lemmas by `rfl` over destructured states.** `EVM.step` for a
   concrete opcode is definitional. State the conclusion as a flat record
   update and prove with `unfold EVM.step; rfl`. When the stack shape
   matters, destructure the state (`⟨shared, pc, stk, len⟩`), retype the
   stack hypothesis by defeq (`replace hstk : stk0 = _ := hstk`), `subst`.
   For `CALL`, prove the bind/map conversion with a single `exact` —
   structure eta makes the pattern-lambda and `p.1`/`p.2` forms defeq.
4. **Guard alignment with `if_pos`/`if_neg`, not `simp`.** State `Z_*` and
   `callStep_eval` as if-chains whose conditions are *syntactically* the
   `by_cases` propositions. `simp [h]` on `¬(A ∧ B)` turns ifs into
   implications and strands the proof; `rw [hz, if_neg h₁, if_pos h₂]` is
   deterministic.
5. **Evaluate the IR side once, standalone (`callStep_eval`).** Reducing
   the IR action inside the main proof fights `simp`'s record normal forms
   (nested `Exec` updates vs flat literals). A separate equation lemma,
   proven by `by_cases` + `simp` + a final `rfl` (the residue differs only
   in invisible `Decidable` instances), gives the main proof a clean
   `rw` + `cases oracle …` skeleton.
6. **Position-generalized chunk lemmas (`*_at`).** Chunk lemmas at
   `pc = pre.length` force constant rewriting between `length`-form and
   `+`-form. Variants taking `(n : Nat) (hpre : pre.length = n)` (proved by
   `subst`) let successive chunks compose with `(by simp; try omega)` side
   goals and no pc rewriting.
7. **Componentwise cost hypotheses.** `Z_generic` takes
   `hC : ∀ st, st.toState = … → st.stack = … → st.toMachineState = … →
   C' st w = c₂` and is applied with `rw [hC ⟨explicit literal⟩ rfl rfl rfl]`
   — robust against however `simp` displays the charged intermediate state.
8. **Iota-reduce before `rw`.** After `cases h : action s`, the goal's
   `match Except.ok s₁ with …` needs `dsimp only` before a `rw` can find
   terms inside the branch.

## Dead ends (do not retry)

* **Record-update commutation as `@[simp]` lemmas**
  (`{injectFrame … with gasAvailable := g} = injectFrame {… with …} …`):
  simp's projection-reduction inside record literals changes the term shape
  before the pattern can match. Use defeq bridging (`exact`, `show`,
  componentwise hypotheses) instead.
* **`set` for abbreviating cost/state terms** in the `X_call` proof: `set`
  rewrites hypotheses into the let-variable, breaking the syntactic match
  with goal terms produced by `simp`. Write terms longhand or factor into a
  standalone lemma.
* **Multi-line record literals with lower-indented continuation lines**
  silently fail to parse (`unexpected identifier; expected '}'`); keep
  fields one-per-line, indented past the brace.
* **`subst` on `st.stack = …`** fails (projection, not a variable);
  destructure first.

## Fork changes (forks/EVMYulLean)

* `2727b79` exposes `EVM.W/Z/H/belongs/notIn` (visibility only), adds
  `toBytes!_length`, `UInt256.ofNat_toNat`, `fromBytes'_toBytes!`, and
  makes `UInt256.toByteArray`, `ByteArray.get?`, `ByteArray.extract'` pure
  and list-based. `toByteArray` was verified against the upstream
  implementation by evaluation (0, 1, 255, 256, 2^64, 2^255, 2^256−1, …).
* This session: `ffi.ByteArray.zeroes` opaque-extern → pure `def`
  (`List.replicate`), enabling `#eval` interpretation of the semantics.
  Compiled conformance runs lose the native memset; revisit if the fork's
  test suite is ever timed.

## Validation

* `lowering_correct` has no sorries; axioms: `propext`, `Classical.choice`,
  `Quot.sound`.
* Concrete interpretation agrees exactly (gas, values, errors) on a
  two-instruction program in both the funded and underfunded cases.
