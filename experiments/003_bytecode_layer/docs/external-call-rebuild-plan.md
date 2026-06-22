# External-call rung: diagnosis & rebuild plan

Status anchor for the overnight rebuild of the bytecode-layer external-call
reasoning. Updated as phases land. **Phase 4 (history/doc cleanup) is held for
the lead's final review.**

## The diagnosis (confirmed by three independent reviews: code, audit, literature)

The "general external-call rung 2" (`behaves_call` in `BytecodeLayer/ExternalCallGen.lean`)
is **circular in substance**. Its 4-line proof does nothing but apply the callee's
`Behaves` to a child param `cp`, then apply a *hypothesis* `CallerForwards.hforward`
which is **the theorem's own conclusion restated** ("child `messageCall` completes
leaving `v` at `(a,k)` ⟹ top-level `messageCall` completes leaving `v` at `(a,k)`").
The hard part — that a caller faithfully forwards its child's result to the top
level — is *assumed*, then discharged only per-concrete-program.

A second, subtler hole: the only `calleePre` ever supplied (`calleeChildPre`) pins
the callee to **one concrete child world**, so the "black box" callee has exactly
one inhabitant. Both axes (caller and callee) are general in *signature*, concrete
in *substance*. The whole rung has one inhabitant carrying 100% of the content.

### Root cause (verified against the interpreter)

`drive` (`forks/leanevm/Evm/Semantics/Interpreter.lean:36-75`) is the *only*
recursion in the semantics: one `fuel : ℕ` counter, a flat `List Pending` stack,
no depth/frame markers. A CALL conses the parent onto the shared stack and keeps
looping on the child with `fuel-1` — parent and child interleave under one fuel
counter. So there is **no definitional "this sub-tree is a child `messageCall`"**
decomposition to lean on, which is *why* `hforward` had to be assumed. The hole is
a symptom of the interpreter shape not supporting compositional reasoning, papered
over rather than confronted.

### What is already sound (keep it)

`BytecodeLayer/Hoare.lean` is a genuine, sound compositional core: `Runs.trans`
(`Runs m a b → Runs n b c → Runs (m+n) a c`, real prefix▸suffix composition),
`messageCall_runs` (honest boundary bridge with a numeric fuel bound), the
per-opcode `Runs 1` rules, and the SSTORE effect+frame lemmas. **This is the
exemplar the external-call rule should mirror and currently doesn't.** Also keep
`Behaves`, the `Outcome`/`completedWith` vocabulary, and `call_counterexample`
(proves the `∃G₀` gas floor is forced).

## The fix — one brick, no interpreter reshape

Prove a **generic, program-agnostic CALL-boundary decomposition lemma over the
existing flat `drive`** (`drive_descend_eq`): a parent's in-line descent into a
terminating child equals *parent-prefix ▸ independent child `messageCall cp` ▸
parent resume on the child result*. The external-call analogue of `Runs.trans`.

Tractable because every `drive` arm touches only the **head** of the pending
stack, so a bottom segment is provably inert while a child runs. Proof = a
stack-append/framing lemma by fuel induction (mirroring `drive_fuel_succ`'s
skeleton), reusing already-proven bricks: `driveG_*` (stack-general match eqns),
`drive_fuel_succ`/`drive_fuel_mono` (fuel reconciliation), and the currently-dead
`messageCall_never_outOfFuel` (sufficiency — this finally wires it in). Concrete
witness to generalize: `child_run` (`ExternalCall.lean:246-273`).

We deliberately do **not** reshape `drive` into a nested child-evaluation (the
"textbook"/Verifereum design): that would break the conformance suite and every
existing fuel proof. We instead *prove* the flat `drive` behaves like a nested
evaluation at the boundary. (A dedicated report compares our flat model vs
Verifereum's nested HOL model and validates this choice — see
`verifereum-nested-call.md` once it lands.)

## Phases

1. **Core brick** — `drive_descend_eq` (+ `drive_append_framing` helper). **DONE,
   verified green** (`BytecodeLayer/Semantics/Interpreter/DescentEq.lean`, `lake
   build BytecodeLayer` green at 1103/1125 jobs; `#print axioms` = standard only;
   no `sorry`/`axiom`/`native_decide`). Final signatures (namespace
   `BytecodeLayer.Interpreter`):
   - `drive_append_framing : ∀ f top st res, drive f top st = .ok res → ∀ bot, ∃ j, drive f (top ++ bot) st = drive (j+1) bot (.inr res)`
   - `drive_descend_eq (f child res pd ps) (h : drive f [] (.inl child) = .ok res) : ∃ j, drive f (.call pd :: ps) (.inl child) = drive j ps (.inl (resumeAfterCall res.toCallResult pd))`
2. **Rebuild the call rule, delete `CallerForwards`.**
   - **2a DONE, verified green** (`BytecodeLayer/Hoare/CallSequence.lean`, `lake
     build BytecodeLayer` green; axioms standard-only). The sound general rule,
     external-call analogue of `messageCall_runs`:
     - `messageCall_call_runs {n₁ n₂} (p cp fr₀ callFr child last childRes pending halt) (hbegin : beginCall p = .inl fr₀) (hpre : Runs n₁ fr₀ callFr) (hcall : stepFrame callFr = .needsCall cp pending) (hcbegin : beginCall cp = .inl child) (hchild : drive (seedFuel cp.gas) [] (.inl child) = .ok childRes) (hpost : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last) (hhalt : stepFrame last = .halted halt) (hfuel : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas) : messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))`
     - `drive_eq_of_both_ne_oof` — the fuel-reconciliation helper (any two
       non-`OutOfFuel` fuels agree). The child's unknown step count is never
       tracked: `messageCall_never_outOfFuel` + monotonicity discharge it.
     The callee is consumed as a **black-box terminating run** (`hchild`); the
     caller is described by its **honest `Runs` traces** (`hpre`/`hpost`), not by
     any assumed forwarding.
   - **2b DONE, verified green** — `ExternalCallGen.lean` **deleted entirely**;
     `lake build BytecodeLayer` green; grep confirms zero `behaves_call`/
     `CallerForwards`/`hforward` symbols remain in source; axioms standard-only.
     `Spec.lean` surface re-pointed: concrete `messageCall_call_storageAt` now
     delegates directly to `ExternalCall.messageCall_call_storageAt` (no
     `behaves_call`), and a new honest "general external-call rule" section
     re-exports `messageCall_call_runs` + `messageCall_call_completedWith`. The
     `hforward` hole is gone from the codebase.
   - DESIGN DECISION (flag for review): `CallerForwards` and
     the circular `behaves_call` are **deleted outright**, with *no* honest-witness
     re-wrapper (that would just be `CallerForwards` again). The spec surface
     exposes `messageCall_call_runs` + a thin named-`Outcome` corollary
     `messageCall_call_completedWith`. The concrete `messageCall_call_storageAt`
     stays via its existing **direct** proof (`ExternalCall.messageCall_call_storageAt`,
     no `behaves_call`). `messageCall_call_runs` is intentionally left unexercised
     on a concrete program until Phase 3 (instantiating it needs more PUSH opcode
     rules — that is example work).
3. **Reorg + usability + monolith retirement — DONE, verified green & axiom-clean.**
   Decision (from the lead): specs = the formalization's *general* theorems; the
   per-program results are examples. And exp 003's low-level layer may surface
   frame-level rules (the observables-only standard is an exp 001/002 concern). So:
   - **`Spec.lean` is now the general audit surface** — re-exports the
     program-agnostic program-logic rules (`Runs.trans` sequencing, `messageCall_runs`,
     `runs_push1`, `runs_push`, `runs_sstore`, SSTORE framing, `messageCall_call_runs`,
     `messageCall_call_completedWith`). The six concrete per-program theorems moved
     to **`Examples/ConcreteSpecs.lean`**.
   - **`runs_push`** (general PUSH width, via `stepFrame_push`) added to `Hoare.lean`.
   - **`messageCall_call_runs` exercised end-to-end** on the real `callerProg`/
     `calleeProg` in **`Examples/CallerProgExample.lean`** (full 7-arg caller,
     compositional via `Runs.trans`): `messageCall_callerProg_runs` +
     observable `messageCall_callerProg_storageAt` (cell `(addrCallee,7)=5`,
     `g ≥ 30000`). The keystone is no longer a dead island.
   - **All five `maxHeartbeats` bumps in `ExternalCall.lean` removed** — the proofs
     compile at the **default 200k** (the 4e8/8e8 bumps were 2000–4000× over).
   - **`Hoare/Straightline.lean` → `Hoare/OutcomeBridge.lean`** (was misnamed).
   - Remaining (smaller) `maxHeartbeats` in `Examples/{HoareDemo,ProgramExamples}`,
     `Semantics/{Dispatch,Gas,System}` (1e6–16e6) — likely also over-provisioned;
     optional follow-up sweep.
   - Deferred: nominal gas/unit types (lead's call — automation tension).
4. **Burn the intermediate state** — squash the experiment branch into a clean
   narrative and rewrite the grounded docs that document the hole, so the
   `hforward`-slop state leaves no trace. **HELD for the lead's final review.**

## Reference designs (from the literature review)

- eth-isabelle + Amani et al. (CPP 2018) — bytecode-level Hoare logic, basic
  blocks + CFG; the program-logic *shape* to imitate.
- Verifereum (HOL4) — CALL as nested child-machine evaluation with revert
  rollback; the call/state *architecture* reference (we emulate it as a derived
  lemma, not a definitional rewrite).
- Schwinghammer et al. (LMCS 2011), nested Hoare triples / higher-order frame —
  for "callee = code at an address with its own interface."
