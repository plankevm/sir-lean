# Experiment 003 — review of the **rebuilt external-call reasoning layer** (branch `exp003-fuel-layer-cleanup`)

*Navigation surface for the project lead. Every code reference links to the current source; headline statements are quoted verbatim. Links are paths relative to `experiments/003_bytecode_layer/`. This report covers the NOW-SOUND state after the external-call rebuild; the pre-rebuild report (describing the deleted circular rung) is preserved at [`docs/review-report-prerebuild.md`](./review-report-prerebuild.md).*

---

## 1. TL;DR

The old external-call "rung 2" was **circular**: `behaves_call` assumed its own conclusion through a `CallerForwards.hforward` field (child completes ⟹ top-level completes). That entire file (`ExternalCallGen.lean`, `CallerForwards`, `behaves_call`, `hforward`) **no longer exists** — grep-confirmed: zero occurrences of `CallerForwards`/`behaves_call`/`hforward` anywhere in `BytecodeLayer/`. It has been replaced by a genuinely **proved** external-CALL sequencing rule [`messageCall_call_runs`](../BytecodeLayer/Hoare/CallSequence.lean#L50), built on two new program-agnostic `drive` framing bricks ([`drive_append_framing`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L59) / [`drive_descend_eq`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L155)) and the now-**live** unconditional [`messageCall_never_outOfFuel`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L153). The rule consumes the callee as a black-box terminating `drive` run and the caller through honest `Runs` traces — **no hypothesis is conclusion-shaped** (verified below, §5). It is exercised end-to-end on the real `callerProg`/`calleeProg` ([`messageCall_callerProg_storageAt`](../BytecodeLayer/Examples/CallerProgExample.lean#L252)).

The single most important result, [`Spec.lean#L151`](../BytecodeLayer/Spec.lean#L151):

```lean
theorem messageCall_call_runs {n₁ n₂ : ℕ}
    (p cp : CallParams) (fr₀ callFr child last : Frame)
    (childRes : FrameResult) (pending : PendingCall) (halt : FrameHalt)
    (hbegin   : beginCall p = .inl fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcall    : stepFrame callFr = .needsCall cp pending)
    (hcbegin  : beginCall cp = .inl child)
    (hchild   : drive (seedFuel cp.gas) [] (.inl child) = .ok childRes)
    (hpost    : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last)
    (hhalt    : stepFrame last = .halted halt)
    (hfuel    : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))
```

**Verification status (one line, reported not re-run):** zero `sorry`/`admit`/`native_decide`/`bv_decide` in `BytecodeLayer/` (grep-confirmed; the one hit is a comment at [`Maps.lean:11`](../BytecodeLayer/Semantics/Maps.lean#L11)); **all `set_option maxHeartbeats` removed experiment-wide** (grep-confirmed, zero matches); task reports green build + axioms `[propext, Classical.choice, Quot.sound]` — but the recorded `#print axioms` block in [`docs/results.md`](./results.md#L269) is **stale/pre-rebuild** (old symbol names, omits `messageCall_call_runs`/`messageCall_call_completedWith`/`messageCall_never_outOfFuel`) — flagged in §7.

---

## 2. Goal & context

The layer is the external-call rung of the bytecode-first plan: prove that a top-level `messageCall` into a contract that issues a real `CALL` to another contract delivers the expected observable, **with the sub-call run reflexively** (leanevm's own `beginCall`/`drive` on the callee's genuine bytecode — no oracle) and **gas first-class** (the 63/64 `callGasCap` makes the result hold only above a floor). The semantics being reasoned over is leanevm at [`../../forks/leanevm/Evm/Semantics/Interpreter.lean`](../../forks/leanevm/Evm/Semantics/Interpreter.lean), whose entry is `messageCall p = FrameResult.toCallResult <$> drive (seedFuel p.gas) [] (.inl frame)` with `seedFuel g = 2 * g.toNat + 4096` ([`Interpreter.lean#L82`](../../forks/leanevm/Evm/Semantics/Interpreter.lean#L82)).

**The hole that was closed.** `drive` is a *single flat* recursion: one fuel counter, one `List Pending` stack, every CALL pushes a `.call` frame onto the same stack. There is no definitional "this sub-segment is a child `messageCall`" decomposition. The old rung could not derive forwarding generically, so it *assumed* it (`hforward`). The rebuild supplies the missing decomposition **as a proved theorem over the flat `drive`** ([`drive_descend_eq`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L155), the Lean analogue of Verifereum's depth-sliced `run_call` per [`docs/verifereum-nested-call.md`](./verifereum-nested-call.md)), and reconciles fuel via the never-out-of-fuel theorem. The rebuild plan is [`docs/external-call-rebuild-plan.md`](./external-call-rebuild-plan.md); the proof discipline is [`docs/proof-structure.md`](./proof-structure.md).

Note: exp 003 is the **low-level semantics layer**, so the frame-level vocabulary (`Runs`/`Frame`/`stepFrame`) on the `Spec` surface is intentional and correct here — the observables-only export standard belongs to exp 001/002. The `Spec` docstring flags this itself ([`Spec.lean#L22`](../BytecodeLayer/Spec.lean#L22)).

---

## 3. The abstraction stack (bottom-up) & module map

### 3.1 The new/changed files (the rebuild proper)

| Layer | File | Role |
|---|---|---|
| **Drive framing** | [`Semantics/Interpreter/DescentEq.lean`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean) | `drive_append_framing` (a bottom stack segment is inert) + `drive_descend_eq` (the generic CALL-boundary decomposition). Program-agnostic, proved OVER the flat `drive`. **NEW.** |
| **Fuel sufficiency** | [`Semantics/Interpreter/DescentDrops.lean`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean) → [`NeverOutOfFuel.lean`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean) | the unconditional `messageCall_never_outOfFuel`. **Now LIVE** (imported by `CallSequence`), no longer a dead island. |
| **The SOUND CALL rule** | [`Hoare/CallSequence.lean`](../BytecodeLayer/Hoare/CallSequence.lean) | `drive_eq_of_both_ne_oof`, `messageCall_call_runs` (the keystone), `messageCall_call_completedWith` (observable corollary). **NEW — replaces `hforward`.** |
| **Outcome bridge** | [`Hoare/OutcomeBridge.lean`](../BytecodeLayer/Hoare/OutcomeBridge.lean) | `ofCall_completed_of_success` (`.ok r` success → `Outcome.completed`). **Renamed from `Hoare/Straightline.lean`.** |
| **Worked instantiation** | [`Examples/CallerProgExample.lean`](../BytecodeLayer/Examples/CallerProgExample.lean) | `messageCall_call_runs` exercised compositionally on `callerProg`/`calleeProg` → `messageCall_callerProg_storageAt`. **NEW.** |
| **Audit surface** | [`Spec.lean`](../BytecodeLayer/Spec.lean) | now the **general** program-logic rules only; per-program results moved out. |
| **Concrete examples** | [`Examples/ConcreteSpecs.lean`](../BytecodeLayer/Examples/ConcreteSpecs.lean) | the per-program `messageCall_*` results (M1 spine + M2 `∃G₀`/counterexample) moved off `Spec`. **NEW home.** |

### 3.2 Supporting files (unchanged in role, load-bearing)

| File | Role |
|---|---|
| [`Hoare.lean`](../BytecodeLayer/Hoare.lean) | `StepsTo`/`Runs`/`Runs.trans`/`Runs.drive_advance`, `messageCall_runs`, the `runs_push1`/`runs_push`/`runs_sstore` opcode rules. The composition core. |
| [`Hoare/Behaves.lean`](../BytecodeLayer/Hoare/Behaves.lean) | `World := CallParams` + the `Behaves pre code post` for-all-programs predicate. |
| [`Semantics/Interpreter/Drive.lean`](../BytecodeLayer/Semantics/Interpreter/Drive.lean) | `drive_step`/`drive_halt`/`messageCall_eq_drive`/`driveG_needsCall_code`, `drive_fuel_mono`. The bridge that reduces `messageCall` without unfolding it. |
| [`Semantics/System.lean`](../BytecodeLayer/Semantics/System.lean) | the reflexive CALL rule `stepFrame_call`, `callChildParams`, `callPending`, `resumeAfterCall`, plus the gas-inversions feeding `NeverOutOfFuel`. |
| [`Semantics/{Gas,Dispatch,Precompiles,Maps,UInt256}.lean`](../BytecodeLayer/Semantics/) | the per-opcode semantic-inversion + gas-threading + `TransCmp` library. |
| [`ExternalCall.lean`](../BytecodeLayer/ExternalCall.lean) | the **direct** M2 proof: the fuel-explicit child run `child_run`, `messageCall_call_eq`, `messageCall_call_storageAt`, `call_counterexample`. Still present (see §6/§7). |
| [`Examples/ProgramExamples.lean`](../BytecodeLayer/Examples/ProgramExamples.lean) | the 4 M1 `*'` lemmas `ConcreteSpecs` delegates to. |
| [`Examples/{HoareDemo,ProgramDecode,ProgramExamples}.lean`](../BytecodeLayer/Examples/), [`Programs.lean`](../BytecodeLayer/Programs.lean), [`Observables.lean`](../BytecodeLayer/Observables.lean), [`Hoare/Sequence.lean`](../BytecodeLayer/Hoare/Sequence.lean) | data / demos / decode facts / observable lens / `subCharges` gas threading. |

### 3.3 The dependency picture (what feeds the headline)

```
Spec ─► Hoare.CallSequence ─► { DescentEq ─► Drive,
                                DescentDrops ─► NeverOutOfFuel ─► {Gas, System, Drive},
                                Hoare, OutcomeBridge }
     ├► Examples.ConcreteSpecs ─► {ExternalCall, ProgramExamples}
     └► {Programs, Observables, Hoare.Behaves, Hoare.Sequence}

Examples.CallerProgExample ─► {Hoare, Hoare.CallSequence, ExternalCall, UInt256}   (built via lakefile glob; NOT under Spec — see §6.3)
```

**The structural headline of the rebuild:** the never-out-of-fuel subtree, which the pre-rebuild report flagged as a *dead island* imported by zero files, is now **load-bearing** — [`CallSequence.lean#L3`](../BytecodeLayer/Hoare/CallSequence.lean#L3) imports `DescentDrops`, and `messageCall_call_runs` uses `messageCall_never_outOfFuel` directly ([`CallSequence.lean#L96`](../BytecodeLayer/Hoare/CallSequence.lean#L96)). The `Gas`/`System`/`Dispatch` gas-inversion lemmas that fed only the dead island are now transitively on the audit surface. The big SMELL #1 of the prior report is **resolved**.

---

## 4. The specs that matter (verbatim, bottom-up)

### 4.1 Brick layer — the two generic `drive` framing lemmas

These are the rebuild's foundation: the program-agnostic decomposition of a CALL boundary over the flat `drive`.

[`DescentEq.lean#L59`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L59) — **stack-append framing**:

```lean
theorem drive_append_framing :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∀ (bot : List Pending), ∃ j, drive f (top ++ bot) st = drive (j + 1) bot (.inr res)
```

Gloss: a run that drains `top` to `[]` and returns `.ok res` takes the **identical** steps when an inert bottom segment `bot` is appended, until it reaches `(.inr res, bot)` instead of `(.inr res, [])`. The residual fuel is existential (`∃ j`) so no exact bookkeeping is needed. *Proof strategy (one line):* induction on `f` generalizing `top`/`st`, following `drive`'s own `match`; every non-terminal arm reduces to the IH, the `.error` arms are killed by the `.ok res` hypothesis, and the terminal `top = []` arm is the splice point.

[`DescentEq.lean#L155`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L155) — **the generic CALL-boundary descent equation**:

```lean
theorem drive_descend_eq (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCall) (ps : List Pending)
    (h : drive f [] (.inl child) = .ok res) :
    ∃ j, drive f (.call pd :: ps) (.inl child)
      = drive j ps (.inl (resumeAfterCall res.toCallResult pd))
```

Gloss: if a child frame run over the empty stack terminates with `.ok res`, then the **in-line descent** into that child (child suspended on a `.call` ancestor `pd` over arbitrary inert `ps`) equals, for some residual fuel `j`, the **parent resumed** on the child's `CallResult`. This is the program-agnostic generalization of the fuel-explicit `child_run` — the concrete `+5`/concrete child replaced by an arbitrary terminating child. *Strategy:* `drive_append_framing` with `top := []`, `bot := .call pd :: ps`, then peel one `.call` resume step.

### 4.2 Fuel sufficiency — now live

[`DescentDrops.lean#L153`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L153):

```lean
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_descentDrops descentDrops_holds p
```

Gloss: unconditional, quantified over **all** `CallParams` and all programs (including CALL/CREATE descents). It rests on the measure `μ` + `mu_bound` ([`NeverOutOfFuel.lean`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean)) and the five descent/fallback gas conjuncts assembled in [`descentDrops_holds`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L146). It is the fact that lets `messageCall_call_runs` reconcile the black-box child run's fuel against the caller's suffix.

### 4.3 The keystone — the SOUND general external-CALL rule

[`CallSequence.lean#L50`](../BytecodeLayer/Hoare/CallSequence.lean#L50) (re-exported at [`Spec.lean#L151`](../BytecodeLayer/Spec.lean#L151)) — statement quoted in §1. The supporting agreement lemma, [`CallSequence.lean#L30`](../BytecodeLayer/Hoare/CallSequence.lean#L30):

```lean
theorem drive_eq_of_both_ne_oof {a b : ℕ} (stack : List Pending)
    (state : Frame ⊕ FrameResult)
    (ha : drive a stack state ≠ .error .OutOfFuel)
    (hb : drive b stack state ≠ .error .OutOfFuel) :
    drive a stack state = drive b stack state
```

*Proof strategy of the keystone (one line):* reduce `messageCall p` to `drive (seedFuel p.gas) [] (.inl fr₀)`; advance the prefix `Runs` via `Runs.drive_advance`; take the CALL step via `driveG_needsCall_code`; apply `drive_descend_eq` to the (mono-lifted) black-box child run to land at the resumed parent at some fuel `j`; build the suffix run; then reconcile `j` against the suffix fuel with `drive_eq_of_both_ne_oof`, whose hypotheses come from `messageCall_never_outOfFuel` + `drive_fuel_mono`. No proof body is reproduced here.

The observable-level corollary, [`CallSequence.lean#L138`](../BytecodeLayer/Hoare/CallSequence.lean#L138) (re-exported [`Spec.lean#L172`](../BytecodeLayer/Spec.lean#L172)), wraps the raw `messageCall = .ok …` into the named `Outcome.completedWith` via `completedWith_of_ok`/`ofCall_completed_of_success`.

### 4.4 The worked instantiation (the rule is live and exercised)

[`CallerProgExample.lean#L207`](../BytecodeLayer/Examples/CallerProgExample.lean#L207) and [`#L252`](../BytecodeLayer/Examples/CallerProgExample.lean#L252):

```lean
theorem messageCall_callerProg_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    messageCall (callerParams g)
      = .ok (FrameResult.toCallResult
          (endFrame (callerResumed g) (.success (callerResumed g).exec .empty)))

theorem messageCall_callerProg_storageAt (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5
```

Gloss: `messageCall_call_runs` instantiated on the real 7-arg caller. The prefix is the seven CALL-arg pushes glued by `Runs.trans` (five `runs_push1`, two `runs_push` for PUSH3/PUSH4, [`#L74`](../BytecodeLayer/Examples/CallerProgExample.lean#L74)); the CALL step is `caller_call_step` ([`#L107`](../BytecodeLayer/Examples/CallerProgExample.lean#L107)); the black-box child is `child_drive` ([`#L144`](../BytecodeLayer/Examples/CallerProgExample.lean#L144), the reflexive `PUSH;PUSH;SSTORE;STOP`); the suffix is a zero-step `Runs.refl` to `STOP`; the fuel side-condition discharges by `omega` off `childGas_le_caller`. This is the **intended user workflow** — each piece an independent lemma, composed by the general rule, never naming the full trace — contrasted with the `ExternalCall.messageCall_call_eq` monolith (§6.2).

### 4.5 The audit surface & the concrete examples it no longer carries

`Spec.lean` now exposes only the **general** rules: `Runs.trans`, `messageCall_runs`, `runs_push1`/`runs_push`/`runs_sstore` + the SSTORE effect/frame lemmas, and the two external-CALL rules. The per-program results moved to [`Examples/ConcreteSpecs.lean`](../BytecodeLayer/Examples/ConcreteSpecs.lean): the 4 M1 observables (`messageCall_stop_observe` … `messageCall_seq_storageAt`) and the M2 pair below ([`ConcreteSpecs.lean#L88`](../BytecodeLayer/Examples/ConcreteSpecs.lean#L88), [`#L99`](../BytecodeLayer/Examples/ConcreteSpecs.lean#L99)):

```lean
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5

theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0
```

These delegate to [`ExternalCall.messageCall_call_storageAt`](../BytecodeLayer/ExternalCall.lean#L408) and [`call_counterexample`](../BytecodeLayer/ExternalCall.lean), the direct monolithic proofs. `call_counterexample` is the load-bearing gas-honesty witness: at `g = 24000`, `childGas 24000 = 21045 < 22106`, the callee's SSTORE OOGs and rolls back, yet the top-level call completes (`.ok 0`, not an exception) — proving the `∃G₀` cannot be dropped.

---

## 5. Hypotheses & modeling — the soundness verdict

**The central question: does `messageCall_call_runs` assume anything conclusion-shaped? No.** Each hypothesis is structural, contrast with the deleted `hforward`:

| Hypothesis | What it is | Conclusion-shaped? |
|---|---|---|
| `hbegin : beginCall p = .inl fr₀` | caller enters as code | structural |
| `hpre : Runs n₁ fr₀ callFr` | honest prefix trace to the CALL site | structural (a `Runs` derivation, not an assertion about `messageCall p`) |
| `hcall : stepFrame callFr = .needsCall cp pending` | the CALL signal at that frame | structural |
| `hcbegin : beginCall cp = .inl child` | child enters as code | structural |
| `hchild : drive (seedFuel cp.gas) [] (.inl child) = .ok childRes` | **the callee as a black box** — *any* terminating child run, no claim about what it computes | NOT conclusion-shaped |
| `hpost : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last` | honest suffix trace from the resumed frame | structural |
| `hhalt : stepFrame last = .halted halt` | caller halts | structural |
| `hfuel : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas` | numeric fuel bound | arithmetic |

**Contrast with the deleted `hforward`:** the old `CallerForwards.hforward` field literally read `completedWith (ofCall (messageCall cp)) … → completedWith (ofCall (messageCall p)) …` — i.e. "if the child completes, the top-level completes," which **is** the forwarding the engine could not derive. The rebuild derives that implication as the *body* of `messageCall_call_runs` (via `drive_descend_eq` + never-out-of-fuel), so the corresponding fact is now a **theorem, not a hypothesis**. The conclusion `messageCall p = .ok …` is genuinely produced, not assumed. This is the soundness repair.

**Other modeling notes:**
- **World model.** `World := CallParams` ([`Behaves.lean#L40`](../BytecodeLayer/Hoare/Behaves.lean#L40)): entry params carry the account map (all storage), gas, caller/recipient, calldata; preconditions are `World → Prop`. No execution-trace shape.
- **Reflexive child (no oracle).** `hchild` is discharged on the instance by the genuine `drive` of the callee's actual bytecode ([`child_drive`](../BytecodeLayer/Examples/CallerProgExample.lean#L144)) — leanevm's own driver, no oracle.
- **Gas first-class.** The 63/64 cap survives into the side condition `hfuel` and (on the example) into the `g ≥ 30000` floor; the `∃G₀` of the concrete M2 result is non-vacuous, witnessed by `call_counterexample`.
- **No awkward/smuggling hypothesis remains.** The one structural witness that used to smuggle the conclusion (`CallerForwards`) is gone.

---

## 6. Results taxonomy

### 6.1 Headline / mainline
- [`messageCall_call_runs`](../BytecodeLayer/Hoare/CallSequence.lean#L50) and [`messageCall_call_completedWith`](../BytecodeLayer/Hoare/CallSequence.lean#L138) — the sound general external-CALL rule (raw + observable). **The rebuild's reason to exist.**
- [`messageCall_never_outOfFuel`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L153) — now **load-bearing** under the headline (not just on-surface): the keystone uses it. Strongest unconditional statement in the package, finally consumed.

### 6.2 Supporting bricks (load-bearing)
- [`drive_append_framing`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L59) → [`drive_descend_eq`](../BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L155) — the generic decomposition feeding the keystone. Clean, induction-only, no `decide`/`maxHeartbeats`. Good.
- [`drive_eq_of_both_ne_oof`](../BytecodeLayer/Hoare/CallSequence.lean#L30), `drive_fuel_mono`, `Runs.drive_advance`, `driveG_needsCall_code` — the fuel-reconciliation plumbing. Good.
- The Hoare core (`Runs`/`Runs.trans`/`messageCall_runs`/`runs_push1`/`runs_push`/`runs_sstore`) — unchanged, clean. Good.
- `ExternalCall.child_run`, `childGas_lb`/`childGas_ub` — the fuel-explicit child run feeding both the monolith and (via `child_drive`) the example.

### 6.3 Examples / demos
- [`messageCall_callerProg_runs`/`messageCall_callerProg_storageAt`](../BytecodeLayer/Examples/CallerProgExample.lean#L207) — the compositional instantiation. **Caveat (worth the lead's attention): `CallerProgExample.lean` is imported by no file, including the `BytecodeLayer.lean` root** (which imports only `Spec`). It is nonetheless **compiled and checked** because the lakefile uses `globs := #[.andSubmodules \`BytecodeLayer]` ([`lakefile.lean`](../lakefile.lean)) — every submodule builds. So the example is verified, but it is *not* reachable from the documented audit surface `Spec.lean`; a reader of `Spec` alone would not see that the rule has been exercised. Recommend importing it (or its result) somewhere under `Spec`, or noting it in the `Spec` docstring.
- `ConcreteSpecs.lean` M1 spine + M2 `∃G₀`/counterexample — per-program worked examples, reachable from `Spec`. `messageCall_sstore_storageAt`, `messageCall_seq_storageAt` depend on `ProgramExamples` `*'` lemmas.
- [`Examples/HoareDemo.lean`](../BytecodeLayer/Examples/HoareDemo.lean) — still a standalone demo, imported by nothing; harmless leaf.

### 6.4 Smells

| Item | Location | Class | Headline dependency? |
|---|---|---|---|
| `maxHeartbeats` | (none) | — | **RESOLVED — zero in tree** |
| dead never-out-of-fuel island | (none) | — | **RESOLVED — now live under the keystone** |
| `messageCall_call_eq` monolith | [`ExternalCall.lean#L337`](../BytecodeLayer/ExternalCall.lean#L337) | direct M2 proof | feeds `messageCall_call_storageAt` (a `ConcreteSpecs` example), NOT the keystone |
| `decide` on concrete `callExtraCost = 2600` | [`ExternalCall.lean#L385`](../BytecodeLayer/ExternalCall.lean#L385), [`CallerProgExample.lean#L119`](../BytecodeLayer/Examples/CallerProgExample.lean#L119) | brick | local, small concrete terms |
| `set_option maxRecDepth 4000` | [`CallerProgExample.lean#L41`](../BytecodeLayer/Examples/CallerProgExample.lean#L41), `ProgramExamples`/`HoareDemo` | brick | deep concrete reductions; isolated |
| hardcoded magic constants (`0xCA11EE`, `0xFFFFFFFF`, `2600`, `21045`, `22106`, `24000`, `30000`) | M2 files | example-intrinsic | soundness-neutral |

**The one remaining real smell — the `messageCall_call_eq` monolith ([`ExternalCall.lean#L337`](../BytecodeLayer/ExternalCall.lean#L337)).** This is the *old* direct proof: a single ~70-line `rw`-chain driving the whole caller program (7 pushes + CALL + nested child + resume + STOP) through `drive` in one tactic block. It still exists and still backs the `ConcreteSpecs.messageCall_call_storageAt` example. The rebuild **does not delete it** — instead `CallerProgExample` re-proves the same observable *compositionally* through the general rule. So there are now **two proofs of the same caller storage fact**: the monolith (under the `Spec`-reachable example) and the compositional one (off-surface, §6.3). This is redundancy, not unsoundness; with `maxHeartbeats` removed it apparently no longer needs cranked budgets, but it remains a long brittle reduction. **Does a *headline* depend on the monolith? No** — the keystone `messageCall_call_runs` is monolith-free. The monolith is now demonstrably *replaceable* (the example proves the same fact without it).

---

## 7. Honest rough edges & open questions

1. **`messageCall_call_runs` is exercised on exactly one caller** ([`callerProg`](../BytecodeLayer/Programs.lean)) — a single CALL, value 0, single callee, no nesting, no RETURN data threading (callee `STOP`s). The rule's *statement* is general, but its only witness is one flat caller→callee shape. Multi-level nesting (a callee that itself CALLs) is supported by the generic `drive_descend_eq` in principle but not demonstrated.

2. **The worked instantiation is off the audit surface (§6.3).** `CallerProgExample.lean` builds via the lakefile glob but is not imported under `Spec`; the lead's "is the rule exercised?" question is answerable *yes* only by knowing the glob builds it. Recommend wiring it in or documenting it.

3. **The `messageCall_call_eq` monolith persists** (§6.4) as a redundant second proof of the caller storage fact, under the `Spec`-reachable `ConcreteSpecs` example. Recommend either retiring it in favor of the compositional `messageCall_callerProg_storageAt` (and routing `ConcreteSpecs` through the example), or consciously keeping it as the "direct" cross-check and saying so.

4. **Recorded axiom/build evidence is stale (doc↔source discrepancy).** [`docs/results.md#L269`](./results.md#L269) records a `#print axioms` block listing pre-rebuild symbols (`BytecodeLayer.messageCall_child_reflexive`, `…stepFrame_call`, `…drive_halt` — now namespaced `ExternalCall.`/`System.`/`Interpreter.`) and **omits the rebuild's headlines** `messageCall_call_runs`, `messageCall_call_completedWith`, and `messageCall_never_outOfFuel` entirely. [`docs/handoff.md#L102`](./handoff.md#L102) and `results.md` say "green (1111 jobs)"; the count predates the new files. The axiom-cleanliness claim `[propext, Classical.choice, Quot.sound]` is plausible and stated for the rebuild, but **its recorded evidence predates the rebuild** — regenerate `#print axioms` over the current export set (especially the three new theorems) and the job count. Not re-run here per instructions.

5. **`Spec` altitude caveat is self-flagged** ([`Spec.lean#L22`](../BytecodeLayer/Spec.lean#L22)): the program-logic rules are frame-level, not observables-only. Correct and intentional for this low-level layer (per task), but the only fully observable-level export is `messageCall_call_completedWith`; the `Spec` docstring itself says "to reconcile."

**Recommendations (no code edited):** (a) import `CallerProgExample` (or its result) under `Spec` so the rule's exercise is on the audit surface; (b) decide the monolith's fate (retire vs. keep-as-cross-check) and de-duplicate the caller storage fact; (c) regenerate and reconcile the `#print axioms` block / job count post-rebuild — currently the strongest doc↔source discrepancy; (d) consider a second, *nested* caller witness to demonstrate the generic `drive_descend_eq` under recursion.
