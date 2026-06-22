# Experiment 003 — whole-codebase review (end state, branch `exp003-fuel-layer-cleanup`, HEAD `c08e04f`)

*Navigation surface for the project lead. Every code reference links to the current source; headline statements are quoted verbatim. Links are paths relative to `experiments/003_bytecode_layer/`.*

---

## 1. TL;DR

Experiment 003 builds a reusable bytecode reasoning layer over `philogy/leanevm` and lands **7 exported theorems on the audit surface** ([`BytecodeLayer/Spec.lean`](../BytecodeLayer/Spec.lean)): an M1 call-free spine (4 theorems over handwritten straight-line programs), and an M2 external-call rung (the `∃G₀` storage theorem, an executable counterexample forcing the `∃G₀`, and a general black-box rung-2 `behaves_call`). The package is ~20 files / 5,776 lines, but the line count is dominated by a **reusable per-opcode semantic-inversion library** (`Semantics/Gas.lean`, `Dispatch.lean`, `System.lean` — 2,709 lines together) plus a **separate, self-contained never-out-of-fuel proof** that is the single biggest result by strength yet is **not on the Spec surface and is imported by nothing**.

The reader's headline question — *is `messageCall_never_outOfFuel` wired in?* — has a sharp answer: **no.** [`Semantics/Interpreter/DescentDrops.lean`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean) (carrying the unconditional all-programs `messageCall_never_outOfFuel`) is imported by **zero** files, and its only dependency [`Semantics/Interpreter/NeverOutOfFuel.lean`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean) is imported only by `DescentDrops` itself. The entire `Interpreter/{NeverOutOfFuel,DescentDrops}` subtree — plus a large swath of `Gas`/`System`/`Dispatch` gas-inversion lemmas that exist only to feed it — is a **dead island** relative to consumers. The Spec theorems rule out `OutOfFuel` independently, by concrete reduction (each proof computes the exact result on a fixed program where fuel is concretely sufficient via the numeric `n + 2 ≤ seedFuel` bound), never via the general theorem.

**Verification status (one line):** zero `sorry`/`admit`/`native_decide`/`bv_decide` in `BytecodeLayer/` (grep-confirmed; the one `grep` hit is a comment in `Maps.lean:11`); green build + axiom-cleanliness are **claimed in docs but the recorded `#print axioms`/job-count output is stale and pre-reorg** (lists old un-namespaced symbol names, omits `behaves_call` and `messageCall_never_outOfFuel`, and README says 1120 jobs while results.md/handoff say 1111) — flagged in §7; not re-run here per instructions.

---

## 2. Goal & context

The experiment is the first reasoning layer of the bytecode-first plan: prove reusable bricks against handwritten bytecode and show they compose into the export shape wanted — **observables at the `messageCall` boundary, frame-free, fuel-free** — with external calls as the headline target. The semantics being reasoned over is leanevm at [`../../forks/leanevm/Evm/`](../../forks/leanevm/Evm/) (interpreter [`Evm/Semantics/Interpreter.lean`](../../forks/leanevm/Evm/Semantics/Interpreter.lean), entry `messageCall`/`beginCall`/`drive`/`stepFrame`). The intended discipline is fixed by [`docs/proof-structure.md`](./proof-structure.md): single high-level spec, reflexive calls (no oracle), gas by vacuity-propagation away from CALL with local `∃G₀` arithmetic at CALL, exports in observables.

---

## 3. The abstraction stack & module map (bottom-up, every file accounted for)

### 3.1 Module map — role of each file

| Layer | File | Role | Lines |
|---|---|---|---|
| **Data** | [`Programs.lean`](../BytecodeLayer/Programs.lean) | The handwritten bytecode (`stopProgram`…`callerProg`/`calleeProg`), addresses, and the `CallParams` entry points. No theorems. | 135 |
| **Observable lens** | [`Observables.lean`](../BytecodeLayer/Observables.lean) | `Observables`, `CallResult.observe`, `CallResult.storageAt`, and the named `Outcome` (`completed`/`reverted`/`exception`) with `completedWith`/`completedReturning`. The entire export vocabulary. | 110 |
| **Arith leaf** | [`Semantics/UInt256.lean`](../BytecodeLayer/Semantics/UInt256.lean) | `toNat_sub_ofNat` — the one gas-threading UInt64 fact (charging `c` leaves `g-c`). Mirrors leanevm [`Evm/UInt256.lean`](../../forks/leanevm/Evm/UInt256.lean). | 28 |
| **Map leaf** | [`Semantics/Maps.lean`](../BytecodeLayer/Semantics/Maps.lean) | The missing `Std.TransCmp` instances for `UInt256`/`AccountAddress` comparators + `find?`/`findD` insert/frame equations the SSTORE rule needs. Pure data-structure facts. | 110 |
| **Step gas** | [`Semantics/Gas.lean`](../BytecodeLayer/Semantics/Gas.lean) | Per-opcode "a non-halting step strictly drops gas" library, culminating in `stepFrame_next_lt`, plus the CALL/CREATE cost lower bounds. | 673 |
| **Step shape** | [`Semantics/Dispatch.lean`](../BytecodeLayer/Semantics/Dispatch.lean) | The opcode `stepFrame_*` characterizations (`stepFrame_stop`/`push1`/`push`/`sstore`/`sstore_oog`/`return_empty`), `sstoreChargeOf`/`sstorePost`, plus `onlyNext`/dispatch-signal-shape bridges. | 515 |
| **Precompile gas** | [`Semantics/Precompiles.lean`](../BytecodeLayer/Semantics/Precompiles.lean) | 10 per-precompile "returns gas ≤ forwarded" lemmas + `beginCall_inr_gas`. | 135 |
| **System ops** | [`Semantics/System.lean`](../BytecodeLayer/Semantics/System.lean) | The big one: the reflexive CALL rule (`stepFrame_call`, `callChildParams`, `callPending`), `beginCall_code`/`codeFrame`, gas-conservation/inversion lemmas for call/create arms, resume lemmas. | 1521 |
| **Drive vocab** | [`Semantics/Interpreter/Drive.lean`](../BytecodeLayer/Semantics/Interpreter/Drive.lean) | The `drive` rewrite equations (`drive_step`/`drive_halt`/`messageCall_eq_drive`, `driveG_*`) and fuel monotonicity. The bridge that reduces `messageCall` without unfolding it. | 199 |
| **Fuel measure** | [`Semantics/Interpreter/NeverOutOfFuel.lean`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean) | The measure `μ`, `mu_bound`, and `messageCall_never_outOfFuel_of_descentDrops`. **DEAD island (see §6.1).** | 273 |
| **Fuel arith** | [`Semantics/Interpreter/DescentDrops.lean`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean) | The 5 descent/fallback gas conjuncts, `descentDrops_holds`, and the unconditional `messageCall_never_outOfFuel`. **DEAD island (see §6.1).** | 158 |
| **Hoare core** | [`Hoare.lean`](../BytecodeLayer/Hoare.lean) | `StepsTo`/`Runs` (RT-closure of single steps), `Runs.trans` (the sequencing rule), the `messageCall_runs` boundary bridge, and the `runs_push1`/`runs_sstore` opcode rules with SSTORE effect/frame lemmas. | 261 |
| **Hoare/Behaves** | [`Hoare/Behaves.lean`](../BytecodeLayer/Hoare/Behaves.lean) | `World := CallParams` and the `Behaves pre code post` for-all-programs predicate. | 48 |
| **Hoare/Sequence** | [`Hoare/Sequence.lean`](../BytecodeLayer/Hoare/Sequence.lean) | `seqProgram` decode lemmas + `subCharges`/`toNat_subCharges` (prefix-sum gas threading). | 88 |
| **Hoare/Straightline** | [`Hoare/Straightline.lean`](../BytecodeLayer/Hoare/Straightline.lean) | One bridge lemma `ofCall_completed_of_success` (`.ok r` success → `Outcome.completed`). | 32 |
| **External call** | [`ExternalCall.lean`](../BytecodeLayer/ExternalCall.lean) | M2 proof internals: the reflexive child run, the 63/64 arithmetic, `messageCall_call_eq`, `messageCall_call_storageAt`, `call_counterexample`, `messageCall_child_reflexive`. | 589 |
| **External call gen** | [`ExternalCallGen.lean`](../BytecodeLayer/ExternalCallGen.lean) | `CallerForwards`, the general `behaves_call`, and its concrete instance (`behaves_callee`, `callerForwards_callerProg`, `messageCall_call_storageAt_via_behaves_call`). | 243 |
| **Examples** | [`Examples/ProgramDecode.lean`](../BytecodeLayer/Examples/ProgramDecode.lean) | Per-pc `decode` facts for the example programs. | 45 |
| **Examples** | [`Examples/ProgramExamples.lean`](../BytecodeLayer/Examples/ProgramExamples.lean) | The 4 M1 `*'` proof lemmas Spec delegates to (`messageCall_stop/pushStop/sstore/seq`). | 277 |
| **Examples** | [`Examples/HoareDemo.lean`](../BytecodeLayer/Examples/HoareDemo.lean) | `hoare_demo` — a stand-alone effect+frame demonstration. **Not imported by Spec or anything else (see §6.4).** | 170 |
| **Audit surface** | [`Spec.lean`](../BytecodeLayer/Spec.lean) | The 7 exported theorems (statements + docstrings), each delegating to a same-named lemma below. | 166 |

### 3.2 The two import sub-DAGs (the load-bearing structural fact)

`Spec` transitively imports — and the headlines transitively rest on — exactly this **live** subtree:

```
Spec ─► Examples/ProgramExamples ─► Hoare ─► {Dispatch, Drive, System, Maps, Observables}
     ├► ExternalCall    ─► {Drive, System, Dispatch, Observables, Programs, UInt256, Hoare/Sequence}
     ├► ExternalCallGen ─► {Hoare/Behaves, Drive, ExternalCall, Hoare/Straightline}
     └► Hoare/{Behaves, Sequence, Straightline}
System ─► {UInt256, Gas, Precompiles}
```

The **dead** subtree, reachable from nothing:

```
DescentDrops ─► NeverOutOfFuel ─► {Gas, System, Drive}     ← DescentDrops imported by 0 files
             ─► {Gas, UInt256, Precompiles, Dispatch}
```

(grep-confirmed: `grep -rn 'import BytecodeLayer.Semantics.Interpreter.DescentDrops'` → no matches; `NeverOutOfFuel` is imported only by `DescentDrops`.) `Drive` and `System` sit in **both** subtrees (their CALL-rule / drive-vocabulary halves are live; a large set of gas-inversion lemmas inside them feeds only the dead side — see §6.1).

### 3.3 Why so many files for 7 headlines — confirmed

The reader's assumption (most files are a supporting-lemma layer toward a few headlines) is **correct**, with one major caveat. The bulk is genuine reusable machinery in three buckets:

1. **Per-opcode semantic-inversion library** (`Gas` + `Dispatch` + `Precompiles` + most of `System` ≈ 2,800 lines). This is leanevm-generic — it inverts `stepFrame`/`dispatch`/`callArm`/`createArm` across *all* opcode families, far more than the 4 opcodes (PUSH1/PUSH/SSTORE/STOP/CALL) the 7 headlines actually exercise. It is over-built relative to the headlines because it was mined to be upstreamable and to support the (now-dead) never-out-of-fuel argument.
2. **The Hoare composition layer** (`Hoare*` ≈ 430 lines) — the `Runs`/`Runs.trans` sequencing machinery and the `messageCall_runs` boundary bridge, which is what makes the M1 examples short.
3. **The two M2 proof files** (`ExternalCall` + `ExternalCallGen` ≈ 830 lines) — the genuinely hard part: a reflexive nested call with 63/64-cap arithmetic.

The caveat: a substantial fraction of bucket 1 (the `createArm_*` / `systemOp_*_gas` / `stepFrame_next_lt` lemmas) plus the entire `Interpreter/{NeverOutOfFuel,DescentDrops}` (431 lines) exists **only** to prove `messageCall_never_outOfFuel`, which no consumer imports. So the honest framing is: *most files are a supporting layer, but a strength-maximal ~600–900-line slice of that layer is supporting a result that has been disconnected from the export surface.*

---

## 4. The specs that matter (verbatim, bottom-up)

### 4.0 The shared vocabulary the statements project through

[`Observables.lean#L36`](../BytecodeLayer/Observables.lean#L36), [`#L49`](../BytecodeLayer/Observables.lean#L49), [`#L72`](../BytecodeLayer/Observables.lean#L72), [`#L100`](../BytecodeLayer/Observables.lean#L100):

```lean
def CallResult.observe (r : CallResult) : Observables :=
  { success := r.success, output := r.output }

def CallResult.storageAt (r : CallResult) (addr : AccountAddress) (key : UInt256) : UInt256 :=
  r.accounts.find? addr |>.option 0 (fun a => a.lookupStorage key)

inductive Outcome where
  | completed (out : ByteArray) (σ : AccountAddress → UInt256 → UInt256)
  | reverted (out : ByteArray)
  | exception (e : ExecutionException)

def Outcome.completedWith (o : Outcome) (a : AccountAddress) (k : UInt256) (v : UInt256) : Prop :=
  ∃ out σ, o = .completed out σ ∧ σ a k = v
```

### 4.1 M1 — the call-free spine (4 headlines)

These rest bottom-up on: `toNat_sub_ofNat` → the `stepFrame_*` Dispatch characterizations → the `runs_push1`/`runs_sstore` opcode rules ([`Hoare.lean#L173`](../BytecodeLayer/Hoare.lean#L173), [`#L183`](../BytecodeLayer/Hoare.lean#L183)) → `Runs.trans` ([`Hoare.lean#L96`](../BytecodeLayer/Hoare.lean#L96)) → the boundary bridge `messageCall_runs` ([`Hoare.lean#L135`](../BytecodeLayer/Hoare.lean#L135)) → the `Examples/ProgramExamples` `*'` lemmas → Spec.

The sequencing rule and boundary bridge, [`Hoare.lean#L96`](../BytecodeLayer/Hoare.lean#L96) and [`#L135`](../BytecodeLayer/Hoare.lean#L135):

```lean
theorem Runs.trans {m n : ℕ} {fr mid fr' : Frame}
    (h₁ : Runs m fr mid) (h₂ : Runs n mid fr') : Runs (m + n) fr fr'

theorem messageCall_runs {n : ℕ} (p : CallParams) (fr₀ last : Frame)
    (hbegin : beginCall p = .inl fr₀)
    (h : Runs n fr₀ last)
    (halt : FrameHalt) (hhalt : stepFrame last = Signal.halted halt)
    (hfuel : n + 2 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))
```

Note `hfuel : n + 2 ≤ seedFuel p.gas` — this is **how M1/M2 discharge fuel without the never-out-of-fuel theorem**: the step count `n` is a concrete numeral and `seedFuel g = 2*g + 4096`, so the bound is closed by `omega`.

The four exported headlines, [`Spec.lean#L46`](../BytecodeLayer/Spec.lean#L46), [`#L53`](../BytecodeLayer/Spec.lean#L53), [`#L62`](../BytecodeLayer/Spec.lean#L62), [`#L72`](../BytecodeLayer/Spec.lean#L72):

```lean
theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok Observables.ok

theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok Observables.ok

theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok (Observables.ok, 5)

theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok (Observables.ok, 5, 11)
```

The gas hypotheses are exact program costs (`22106 = 3+3+22100` cold SSTORE; `44212 = 2×22106`), stated as plain `≤`. Proven (in `ProgramExamples`) by composing `runs_push1`/`runs_sstore` via `Runs.trans`, then `messageCall_runs`; the stored values are *derived* as SSTORE operands, not asserted.

### 4.2 M2 — the external-call rung (3 headlines)

Rests on the reflexive CALL rule `stepFrame_call` ([`System.lean#L119`](../BytecodeLayer/Semantics/System.lean#L119)), the reflexive child run `child_run` ([`ExternalCall.lean#L246`](../BytecodeLayer/ExternalCall.lean#L246)), the 63/64 lower bound `childGas_lb` ([`ExternalCall.lean#L181`](../BytecodeLayer/ExternalCall.lean#L181)), and the pinned top-level reduction `messageCall_call_eq` ([`ExternalCall.lean#L339`](../BytecodeLayer/ExternalCall.lean#L339)).

The `∃G₀` storage theorem and its forced counterexample, [`Spec.lean#L105`](../BytecodeLayer/Spec.lean#L105) and [`#L116`](../BytecodeLayer/Spec.lean#L116):

```lean
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 :=
  ExternalCall.messageCall_call_storageAt_via_behaves_call

theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0 :=
  ExternalCall.call_counterexample
```

`messageCall_call_storageAt` is **re-derived as an instance of `behaves_call`** (via `messageCall_call_storageAt_via_behaves_call`, [`ExternalCallGen.lean#L218`](../BytecodeLayer/ExternalCallGen.lean#L218)). `call_counterexample` is the load-bearing gas-honesty witness: at `g = 24000`, `childGas 24000 = 21045 < 22106`, the callee's SSTORE OOGs and rolls back, yet the top-level call completes (`.ok 0`, not an exception). The two together prove the `∃G₀` cannot be dropped.

The general rung-2 black box, [`Spec.lean#L155`](../BytecodeLayer/Spec.lean#L155):

```lean
theorem behaves_call
    (callerCode calleeCode : ByteArray)
    (callerPre calleePre : World → Prop)
    (a : AccountAddress) (k v : UInt256) (G₀ : ℕ)
    (hcallee : Behaves calleePre calleeCode (fun o => Outcome.completedWith o a k v))
    (W : ∀ p : World, p.codeSource = .Code callerCode → callerPre p → G₀ ≤ p.gas.toNat →
        ExternalCall.CallerForwards calleeCode calleePre a k v p) :
    Behaves (fun p => callerPre p ∧ G₀ ≤ p.gas.toNat) callerCode
      (fun o => Outcome.completedWith o a k v)
```

with `Behaves` ([`Hoare/Behaves.lean#L45`](../BytecodeLayer/Hoare/Behaves.lean#L45)) and the `CallerForwards` witness ([`ExternalCallGen.lean#L85`](../BytecodeLayer/ExternalCallGen.lean#L85)):

```lean
def Behaves (pre : World → Prop) (code : ByteArray) (post : Outcome → Prop) : Prop :=
  ∀ p : World, p.codeSource = .Code code → pre p → post (Outcome.ofCall (messageCall p))

structure CallerForwards
    (calleeCode : ByteArray) (calleePre : World → Prop)
    (a : AccountAddress) (k v : UInt256) (p : World) where
  cp : CallParams
  hcode : cp.codeSource = .Code calleeCode
  hpre : calleePre cp
  hforward : Outcome.completedWith (Outcome.ofCall (messageCall cp)) a k v →
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v
```

### 4.3 The off-surface strong result

[`DescentDrops.lean#L153`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L153):

```lean
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_descentDrops descentDrops_holds p
```

This is the **strongest statement in the package** — unconditional, quantified over *all* `CallParams` and all programs (including CALL/CREATE descents). It rests on `mu_bound` ([`NeverOutOfFuel.lean#L133`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L133)) over the measure `μ = 2*totalGas + 2*stack.length + tagBit` ([`#L81`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L81)) and the 5 descent conjuncts `descentDrops_holds` ([`DescentDrops.lean#L146`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L146)). It is **not exported from `Spec.lean` and is imported by no file** — dead to consumers (see §6.1).

---

## 5. Hypotheses & modeling

- **World model.** `World := CallParams` ([`Hoare/Behaves.lean#L36`](../BytecodeLayer/Hoare/Behaves.lean#L36)): the entry params carry the account map (all storage), gas, caller/recipient, calldata. Preconditions are `World → Prop`. Clean, no trace shape.
- **Gas as precondition, first-class.** M1 carries the exact cost as a `≤` hypothesis. M2's `∃G₀` is the genuine 63/64-cap floor, exhibited non-vacuously by `call_counterexample`. In `behaves_call`, gas is a conjunct of `pre` (`G₀ ≤ p.gas.toNat`), never erased.
- **Reflexive child call (sound, no oracle).** The CALL runs the real `beginCall`/`drive` on the genuine child `CallParams` — `beginCall_child` ([`ExternalCall.lean#L121`](../BytecodeLayer/ExternalCall.lean#L121)) and `child_run` ([`ExternalCall.lean#L246`](../BytecodeLayer/ExternalCall.lean#L246)) drive the callee's actual bytecode. This matches the proof-structure mandate; no oracle hypothesis.
- **The honest awkward hypothesis: `CallerForwards`.** `behaves_call` is genuinely general over the *callee* (consumed only through its `Behaves`), but the *caller* side is supplied a per-entry structural witness `CallerForwards`, whose `hforward` field essentially asserts the forwarding conclusion the engine cannot derive generically (because `drive` is a single flat fuel-bounded recursion with no clean "this subtree is a child messageCall" decomposition — stated candidly in the [`ExternalCallGen.lean` module docstring](../BytecodeLayer/ExternalCallGen.lean#L20)). This is **load-bearing, not a smell**, but it is the place where "general over both programs" is weaker than it sounds: the caller generality is delegated to a witness the instance discharges by hand from the concrete reductions. The accompanying `callerPre` world precondition is correctly identified as necessary (an adversarial world breaks forwarding) — a sign of honest modeling.
- **Fuel.** Discharged per-program by the numeric `n + 2 ≤ seedFuel` bound in `messageCall_runs` / by concrete reduction in M2; **the general fuel-sufficiency theorem is not used by any export** (§6.1).

---

## 6. Results taxonomy

### 6.1 SMELL #1 (the big one): the dead never-out-of-fuel island

`messageCall_never_outOfFuel` ([`DescentDrops.lean#L153`](../BytecodeLayer/Semantics/Interpreter/DescentDrops.lean#L153)), `messageCall_never_outOfFuel_of_descentDrops` ([`NeverOutOfFuel.lean#L255`](../BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L255)), `mu_bound`, and the 5 `descentDrops_conj*` are **fully proven and unconditional**, but:

- **`DescentDrops.lean` is imported by zero files** (grep-confirmed).
- **`NeverOutOfFuel.lean` is imported only by `DescentDrops`** (grep-confirmed).
- **No headline depends on them.** The M1/M2 exports rule out `OutOfFuel` independently via concrete reduction.

**Does a headline depend on it?** No. It is an isolated, strong, but dead-to-consumers result. This is the single most important structural finding: the package's strongest theorem (the only one quantified over *all* programs) is not on the audit surface and is unreachable from it.

This island also drags in dead-only support inside the live files:

- In `Gas.lean`: `stepFrame_next_lt` ([`Gas.lean#L591`](../BytecodeLayer/Semantics/Gas.lean#L591)), `callExtraCost_ge_100`/`_ge_9000_of_val`, `charge_drop_ge`, `createCost_ge_2`/`create2Cost_ge_2` ([`Gas.lean#L627`](../BytecodeLayer/Semantics/Gas.lean#L627)–[`#L670`](../BytecodeLayer/Semantics/Gas.lean#L670)) — used only via `systemOp_*_gas` → DescentDrops.
- In `System.lean`: the `systemOp_next_gas`/`systemOp_needsCall_gas`/`systemOp_needsCreate_savedGas`/`systemOp_needsCreate_childGas` inversions ([`System.lean#L1412`](../BytecodeLayer/Semantics/System.lean#L1412), [`#L1462`](../BytecodeLayer/Semantics/System.lean#L1462), [`#L1479`](../BytecodeLayer/Semantics/System.lean#L1479), [`#L1504`](../BytecodeLayer/Semantics/System.lean#L1504)) and the entire `createArm_*` family (`createArm_next_gas` [`#L1055`](../BytecodeLayer/Semantics/System.lean#L1055), `createArm_needsCreate_savedGas`, `createArm_needsCreate_childGas`, `callArm_next_gas` [`#L964`](../BytecodeLayer/Semantics/System.lean#L964)) and `resumeAfterCreate_gas_le_savedGas` — all reachable only from the dead island.
- All of `Semantics/Dispatch.lean`'s signal-shape bridges `stepFrame_needsCall_systemOp`/`stepFrame_needsCreate_systemOp`/`stepFrame_next_systemOp` ([`Dispatch.lean#L491`](../BytecodeLayer/Semantics/Dispatch.lean#L491)–[`#L508`](../BytecodeLayer/Semantics/Dispatch.lean#L508)) are used only by DescentDrops.
- `Semantics/Precompiles.lean` is imported by `System.lean` (live) and `DescentDrops` (dead), but its content (`beginCall_inr_gas`) is consumed only by `descentDrops_conj5a` — i.e. the whole precompile-gas file is dead-to-consumers support.

**Soundness:** these are honest, closed proofs — nothing unsound. The smell is *dead weight + a disconnected headline*, not unsoundness.

**Recommendation (no edits made):** either (a) re-wire the M1/M2 fuel discharge through `messageCall_never_outOfFuel` so the strong theorem becomes load-bearing and the per-program `seedFuel` bounds disappear, or (b) export `messageCall_never_outOfFuel` from `Spec.lean` as an 8th headline so it is at least on the audit surface, or (c) consciously document it as a parked, upstream-bound result. As-is, a reader of `Spec.lean` would never learn the package proves it.

### 6.2 SMELL #2: cranked `maxHeartbeats`

| Location | What it proves | Class | Headline dependency? |
|---|---|---|---|
| [`ExternalCall.lean#L241`](../BytecodeLayer/ExternalCall.lean#L241) `4e8` | `child_run` (reflexive callee success path) | brick | **YES** — `messageCall_call_storageAt` |
| [`ExternalCall.lean#L333`](../BytecodeLayer/ExternalCall.lean#L333) `8e8` | `messageCall_call_eq` (top-level pinned reduction) | brick | **YES** — `messageCall_call_storageAt` |
| [`ExternalCall.lean#L427`](../BytecodeLayer/ExternalCall.lean#L427) `2e8` | `child_run_oog` (starved callee) | brick | **YES** — `call_counterexample` |
| [`ExternalCall.lean#L493`](../BytecodeLayer/ExternalCall.lean#L493) `8e8` | `call_counterexample` | headline | **IS a headline** |
| [`ExternalCall.lean#L551`](../BytecodeLayer/ExternalCall.lean#L551) `4e8` | `messageCall_child_reflexive` | brick (off-surface) | feeds `behaves_callee` → `behaves_call` instance → `messageCall_call_storageAt` |
| [`Examples/ProgramExamples.lean`](../BytecodeLayer/Examples/ProgramExamples.lean#L181) `1e6`–`16e6` (8 sites) | M1 `*'` lemmas (stop/pushStop/sstore/seq) | brick | **YES** — the 4 M1 headlines |
| [`Examples/HoareDemo.lean`](../BytecodeLayer/Examples/HoareDemo.lean#L50) `1e6` (5 sites) | `hoare_demo` | EXAMPLE | **NO** — unused leaf (§6.4) |
| [`Semantics/Dispatch.lean`](../BytecodeLayer/Semantics/Dispatch.lean#L40) `1e6`–`2e6` (5 sites) | dispatch signal-shape lemmas | brick | live ones feed M1/M2; the `systemOp` ones feed only the dead island |
| [`Semantics/System.lean#L107`](../BytecodeLayer/Semantics/System.lean#L107) `4e6` | a System lemma | brick | live (CALL rule region) |
| [`Semantics/Gas.lean#L457`](../BytecodeLayer/Semantics/Gas.lean#L457) `1e6` | a gas-drop lemma | brick | mixed |

**The verdict on the `8e8`/`4e8` hotspots in `ExternalCall.lean`:** these are **load-bearing for the M2 headlines** and are the worst smell. `8e8` is ~4000× the Lean default (2e5). They sit on `messageCall_call_eq`/`call_counterexample` — single monolithic `rw`-chains that drive the entire caller program (7 pushes + CALL + nested child run + resume + STOP) through `drive` in one tactic block (see [`ExternalCall.lean#L339`](../BytecodeLayer/ExternalCall.lean#L339)–[`#L406`](../BytecodeLayer/ExternalCall.lean#L406)). This is a **reduction blow-up, not an unsoundness** — symbolic `drive`/`decode`/account-map reductions over a concrete program are simply expensive, and the `min … 0xFFFFFFFF` / `subCharges` gas threading compounds it. It is **soundness-neutral slowness** but a **brittleness + non-ideal-model smell**: the proof is a long imperative reduction rather than routed through reusable characterization lemmas the way M1 is (M1 uses the `Runs`/`messageCall_runs` composition and stays at `≤16e6`). It *could* be broken down — M2 would benefit from a `Runs`-style descent combinator so the caller program composes per-opcode like M1 does, instead of one 8e8 block. That the M1 path (which does compose) needs only `1e6`–`16e6` is direct evidence the blow-up is the monolithic-reduction style, not inherent.

### 6.3 Bricks (live, supporting the headlines) — good

- The Hoare core (`StepsTo`/`Runs`/`Runs.trans`/`messageCall_runs`, `runs_push1`/`runs_sstore` + SSTORE effect/frame) — clean, trace-free, the reason M1 is short. Good.
- `Drive.lean` (`drive_step`/`drive_halt`/`messageCall_eq_drive`/`driveG_*`, fuel monotonicity) — the single bridge that lets every proof avoid unfolding `messageCall`. Good, exactly the characterization discipline the constitution wants.
- `Maps.lean` — supplies `TransCmp` instances leanevm itself defers; pure, no `decide`/`sorry`. Good and genuinely reusable upstream.
- `System.lean`'s CALL-rule half (`stepFrame_call`, `callChildParams`, `callPending`, `beginCall_code`, `codeFrame`, `beginCall_inl_gas`, `resumeAfterCall`) — live, load-bearing for M2. Good.
- `UInt256.toNat_sub_ofNat`, `Hoare/Sequence.toNat_subCharges` — the gas-threading leaves replacing a shadow ledger. Good (this is the "structural gas" the constitution mandates).

### 6.4 Examples / demos

- `Examples/ProgramExamples.lean` — the 4 M1 `*'` lemmas. **These ARE depended on** (Spec delegates to them); not "just examples" despite living in `Examples/`.
- `Examples/HoareDemo.lean` `hoare_demo` ([`HoareDemo.lean#L161`](../BytecodeLayer/Examples/HoareDemo.lean#L161)) — a genuine **example/demo**: it reproves `sstoreProgram` compositionally with an added framing conclusion (cell 8 untouched). **Imported by nothing, exported by nothing — a pure unused leaf.** Harmless, but it duplicates `sstore_runs`/`sstore_messageCall` already present in `ProgramExamples.lean` (redundancy noted). Its `Proof/StraightlineInstances.lean` docstring reference ([`HoareDemo.lean#L11`](../BytecodeLayer/Examples/HoareDemo.lean#L11)) points at a file that does not exist post-reorg.
- `messageCall_child_reflexive` ([`ExternalCall.lean#L552`](../BytecodeLayer/ExternalCall.lean#L552)) — not "just an example": it feeds `behaves_callee` and hence the `behaves_call` instance that backs `messageCall_call_storageAt`. Live, off the audit surface by design (its statement names internal frames).

### 6.5 Other brittle/hardcoded items

- `set_option maxRecDepth 4000` in `Examples/{ProgramExamples,HoareDemo}.lean` ([`ProgramExamples.lean#L36`](../BytecodeLayer/Examples/ProgramExamples.lean#L36)) — needed for the deep `decide`/reduction; mild brittleness, isolated to the M1 examples.
- Hardcoded magic constants throughout M2: `13242862` (= `0xCA11EE`), `4294967295` (= `0xFFFFFFFF`), `2600`, `21045`, `22106`, `24000`, `30000`, `100000` (the `G₀` floor). These are intrinsic to the worked example, but several appear as bare literals in proof bodies (e.g. `childGas 24000 = 21045` reasoning at [`ExternalCall.lean#L496`](../BytecodeLayer/ExternalCall.lean#L496)). The `G₀ = 100000` in the non-`behaves` corollary ([`ExternalCall.lean#L413`](../BytecodeLayer/ExternalCall.lean#L413)) vs `G₀ = 30000` in the `behaves` instance ([`ExternalCallGen.lean#L226`](../BytecodeLayer/ExternalCallGen.lean#L226)) is a loose (non-tight) floor — soundness-neutral.

---

## 7. Honest rough edges & doc↔source discrepancies

1. **`messageCall_never_outOfFuel` is dead to consumers** (§6.1) — the headline finding. Not exported, not imported, no headline depends on it.
2. **README is pre-reorg.** [`README.md`](../README.md) (lines 34–53) still describes the `Reasoning/` + `Proof/` tree that the 4-phase reorg deleted, and says proofs delegate "to Proof/". The actual tree is `Semantics/` + `Hoare/` + `Examples/`. Stale.
3. **`docs/results.md` records a stale `#print axioms` block.** [`docs/results.md`](./results.md) lines 272–281 list `BytecodeLayer.messageCall_child_reflexive`, `BytecodeLayer.stepFrame_call`, `BytecodeLayer.drive_halt` — these symbols are now `BytecodeLayer.ExternalCall.messageCall_child_reflexive`, `BytecodeLayer.System.stepFrame_call`, `BytecodeLayer.Interpreter.drive_halt`. The recorded axiom list also **omits `behaves_call` and `messageCall_never_outOfFuel`** entirely. The axiom-cleanliness claim is plausible but its recorded evidence predates the reorg and the rung-2/never-out-of-fuel work.
4. **Job-count contradiction.** [`README.md`](../README.md#L26) says "green (1120 jobs)"; [`docs/results.md`](./results.md#L264) and [`docs/handoff.md`](./handoff.md#L102) say "1111 jobs". At most one is current; neither was re-run here (instructed not to run `lake build`).
5. **`HoareDemo.lean` docstring references a non-existent `Proof/StraightlineInstances.lean`** ([`HoareDemo.lean#L11`](../BytecodeLayer/Examples/HoareDemo.lean#L11)); `Hoare/Sequence.lean` docstring references the same dead file ([`Hoare/Sequence.lean#L16`](../BytecodeLayer/Hoare/Sequence.lean#L16)). Both are leftovers; the "instance" file was folded away in the reorg.
6. **`behaves_call`'s caller-generality is delegated to the `CallerForwards.hforward` witness** (§5) — honest and documented, but worth the lead knowing the "general over both programs" claim is strongest on the callee side.
7. **The M2 `8e8` maxHeartbeats** (§6.2) — load-bearing, brittle, and decomposable into a `Runs`-style descent the way M1 already is. The strongest candidate for refactoring.

**Recommendations (no code edited):** decide the fate of the never-out-of-fuel island (export it, wire it in, or document-as-parked, and prune the ~600 lines of `Gas`/`System`/`Dispatch`/`Precompiles` lemmas that exist only to support it); regenerate `#print axioms` and the job count post-reorg and reconcile README↔results.md↔handoff; either delete `HoareDemo` or mark it the canonical demo and drop the duplicate in `ProgramExamples`; refactor the M2 reductions toward per-opcode composition to retire the `8e8` heartbeats.
