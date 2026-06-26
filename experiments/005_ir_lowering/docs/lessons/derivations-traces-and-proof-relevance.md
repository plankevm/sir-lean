# A lesson: derivations, traces, and proof-relevance

*Prompted by a sharp student question — "`Runs` is practically a derivation tree; is
there a pattern that treats the tree like a constructive proof? every constructor is a
step of the interpreter…" Yes. You've independently rediscovered three of the load-bearing
ideas in mechanized semantics. Let me name them and show how they connect, using your own
`Runs` as the running example.*

---

## 0. The question behind your question

You wrote `realisedGas : Runs fr last → GasOracle` and it didn't typecheck, and your gut
said two things at once:

1. *"`Runs` is a derivation tree — morally it's a trace, I should be able to walk it."*
2. *"every constructor of `Runs` is a step of the interpreter."*

Both are **correct and profound**. The reason the function didn't typecheck is the *one*
thing standing between your intuition and reality: **proof-relevance**. Once you see it,
the whole picture — interpreters vs relations, big-step vs small-step, why CompCert is
built on traces — snaps into place.

---

## 1. Proof-relevance: `Prop` forgets *which* proof, `Type` remembers

In Lean (and Coq), `Prop` is **proof-irrelevant**: any two proofs of the same proposition
are *definitionally equal*. `h₁ h₂ : P` with `P : Prop` ⟹ `h₁ = h₂`, for free. The system
*deliberately forgets* which proof you had.

`Type` is **proof-relevant**: `[1,2,3] : List ℕ` and `[3,2,1] : List ℕ` are different data.
The system *remembers*.

Now: a value of `realisedGas` would be a *list of `Word`s* — **data**, in `Type`. To build
it from a `Runs` derivation you'd have to **case-analyze the derivation** ("was the first
step a `GAS`? then cons its value…"). But case-analysis on a `Prop` to *produce data* is
forbidden, because the data would depend on **which** derivation — and `Prop` just told you
that's not allowed to matter. So:

```lean
def realisedGas : Runs fr last → GasOracle    -- ❌ "motive is not type correct" /
  | .step h rest => ...                        --    can't eliminate Prop into Type
```

This isn't a Lean quirk; it's the price of proof-irrelevance (which is what makes `Prop`
erasable at runtime and lets you ignore proof *content* when reasoning). The rule has a
name: **large elimination is restricted to subsingletons.** You may eliminate a `Prop`
into `Type` only when it has **at most one inhabitant** (one constructor, all arguments
themselves `Prop` or forced by the indices) — `And`, `Eq`, `Acc`. `Runs` has `refl`/`step`/
`call`: *many* distinct derivations. Not a subsingleton. No large elimination.

> **Lesson 1.** "Is there a value of type `P`?" (`P : Prop`) and "*here is* the execution"
> (`T : Type`) are different questions. `∃`/`Prop` proves the former and *throws away the
> witness's structure*; a `Type` keeps it. If you want to **compute with** the witness,
> it must live in `Type`.

---

## 2. Your "derivation tree = constructive proof" is Curry–Howard + natural semantics

You sensed that a derivation tree is "kinda like a constructive proof." That's not an
analogy — it's **literally the Curry–Howard correspondence**: *propositions are types,
proofs are programs.* A proof of `Runs fr last` **is** a program — a tree of constructor
applications. The only thing `Prop` does is *erase* that program after type-checking.

And the relation itself? Each constructor is an **inference rule**:

```
─────────────  refl        Runs fr mid    StepsTo last' last    …
 Runs fr fr                ───────────────────────────────────  step
                                      Runs fr last
```

This style — defining evaluation as an inductively-generated relation whose constructors
are inference rules — is **big-step / natural semantics** (Gilles Kahn, 1987). A derivation
of `e ⇓ v` is a finite proof tree, and **its shape is exactly the call tree an interpreter
for `e` would make.** That's your second intuition, dead on: *every constructor is a step
of the interpreter.* The relation is the interpreter with its control flow turned inside-out
into a tree of evidence.

> **Lesson 2.** A big-step relation and a recursive interpreter are **two presentations of
> the same semantics.** The interpreter is the *constructive content* of the relation. Put
> the relation in `Type` and the derivation *is* a reified interpreter run — walkable data.

---

## 3. Small-step, and why "trace" is the natural word you reached for

You said: *"if instead of `Runs` we had a trace of the frame execution."* You were reaching
for **small-step / structural operational semantics** (Plotkin, 1981): a one-step relation
`state → state`, and a whole run is the **reflexive-transitive closure** — i.e. a
**sequence** of steps. A sequence is a `List`; a `List` is `Type`; you can `map` over it.

`Runs` here is morally that closure (`refl` = zero steps, `step` = one more, `call` = a
nested sub-run) — but stated in `Prop`. So:

| presentation | type | a "run" is | can you `map` it? |
|---|---|---|---|
| `Runs : … → Prop` | proof-irrelevant | a *proof that* it runs | **no** (subsingleton bar) |
| `Trace : … → Type` (small-step list / proof-relevant inductive) | proof-relevant | the *actual* sequence of steps | **yes** |

Your `realisedGas` is a `map`/`filter` over the run. It compiles **iff** the run is the
right-hand row.

> **Lesson 3.** Big-step gives you trees, small-step gives you lists; both can live in
> `Prop` (to *reason*) or `Type` (to *compute*). "I want to walk the execution and collect
> the GAS reads" is a `Type`-level, small-step-flavoured operation.

---

## 4. The duality you'll use constantly: interpreter ⟷ relation, joined by *adequacy*

In practice you keep **both**:

- an **executable interpreter** — a *function* in `Type` (here: `drive : ℕ → … → FrameResult`,
  fuel-driven, total, `#eval`-able). This is where computation and data-extraction live.
- an **inductive relation** in `Prop` (here: `Runs`/`StepsTo`) — clean to reason about,
  no fuel, no `Option` clutter.

and you prove an **adequacy theorem** tying them together:

```lean
theorem drive_sound : drive f s state = .ok r → Runs … r      -- function ⟹ relation
theorem runs_complete : Runs … r → ∃ f, drive f s state = .ok r  -- relation ⟹ function
```

Then: **extract data from the function, reason with the relation.** Your `realisedGas` /
`realisedCall` want to be projections of an *instrumented interpreter*:

```lean
structure RunLog where           -- the "interpreter that records introspection points"
  observable : Observable
  gas        : List Word         -- GAS reads, in order   → realisedGas
  calls      : List CallRecord   -- call results          → realisedCall
def runWithLog : Bytecode → World → ℕ → Option RunLog   -- Type-valued ⇒ projections are functions
```

That `RunLog` is the small-step trace, re-cast as exactly the data your oracles need —
and because it's `Type`, `realisedGas := (·.gas)` is a plain function. No proof-irrelevance
wall.

> **Lesson 4.** Don't fight `Prop`. Compute on the `Type`-valued interpreter; reason on the
> `Prop`-valued relation; bridge them once with adequacy.

---

## 5. Why CompCert is built on *traces* — and why your "supplied-observation" model is the same shape

CompCert (Leroy) defines program behaviour as the **trace of observable events** a small-step
execution emits, and proves compiler correctness as a **simulation**: source and target
produce *related traces*. Crucially, it is **not** lockstep — it uses *star* simulations
(one source step ↔ many target steps) precisely because an optimizing pass has no
one-to-one step correspondence (you derived this yourself).

The events are **proof-relevant data** living in `Type` — that's *why* you can state
"same behaviour" by comparing traces. Proof-irrelevant `Prop` couldn't be the currency of
comparison; you'd have nothing to equate.

Your design is this idea, specialized: the "events" are the GAS reads and call results, the
"trace" is the `RunLog`, and "the lowering preserves the observable interaction sequence" is
your simulation relation. You're standing exactly where compiler verification stands.

> **Lesson 5.** Observable **traces are data** (`Type`) because behaviour-equivalence needs
> something to *compare*. The entire supplied-observation model is "compare the
> proof-relevant observation trace, not the proof-irrelevant fact-that-it-ran."

---

## 6. The decision this hands you

For *your* `realisedGas`/`realisedCall`:

- **Regime (i) — instrumented `Type` interpreter (`runWithLog`).** Realised oracles are
  *functions* (projections). Realisability for calls is already `rfl` (the oracle *is* the
  `resumeAfterCall` projection); gas joins it. **Recommended** — it is literally your
  "interpreter that records introspection," and it makes realisability constructive.
- **Regime (ii) — keep `Runs : Prop`, relate via `GasRealises : Prop`.** No `Type`
  extraction; you only ever *relate* a supplied trace to the run. What you have today.
  Fine, but you never get the `realisedGas` *function* — only a predicate.

The proof-relevance lesson is *why* this is a real fork and not a cosmetic one.

---

## 7. Exercises (to make it stick)

1. Write `inductive Box : Prop` with one constructor wrapping a `ℕ`. Try
   `def unbox : Box → ℕ`. Read the error. Now change `Prop`→`Type`. Watch it compile.
   *(You just felt subsingleton elimination.)*
2. Define a 3-instruction toy machine twice: a `step : S → Option S` function and a
   `Step : S → S → Prop` relation. Prove adequacy both directions. Notice the function's
   `match` arms and the relation's constructors are *the same case split*.
3. Make a `Type`-valued `Trace : S → S → Type` (cons-list of steps). Write
   `gasReads : Trace s s' → List Word`. Now redo it with `Trace : … → Prop` and watch it
   break. *(That's `realisedGas` in miniature.)*
4. Look up CompCert's `Smallstep.simulation_star`. Map its `match_states` onto our
   "lowering preserves the observable interaction sequence."

## 8. Further reading

- Pierce, *Types and Programming Languages* — operational semantics, big/small-step.
- Kahn, *Natural Semantics* (1987) — the derivation-tree view.
- Plotkin, *A Structural Approach to Operational Semantics* (1981) — small-step / SOS.
- Leroy, *Formal verification of a realistic compiler* (CompCert) — traces & simulations.
- Lean docs / TAPL on **proof irrelevance** and **large elimination** (the subsingleton rule).
- nLab: *proof relevance*, *propositions as types*.

---

*Takeaway: your two instincts — "the derivation is a constructive proof" and "every
constructor is an interpreter step" — are Curry–Howard and natural semantics respectively.
The only thing stopping `realisedGas` was that you wrote the derivation in the
forgetful universe (`Prop`) and then asked it to remember (`Type`). Move the witness to
`Type` (an instrumented interpreter), keep the relation in `Prop` for reasoning, and bridge
once. That single move is the backbone of verified compilation.*
