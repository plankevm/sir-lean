# Experiment 003 — results

Status: **package green, zero `sorry`, axiom-clean.** Both milestones are proven
in the export shape we wanted:

- **M1 (call-free spine)** — observables-only, frame-free, fuel-free message-call
  theorems on handwritten straight-line bytecode, up to a multi-instruction
  storage-effecting sequence.
- **M2 (external calls — the headline target)** — a **sound, program-agnostic
  external-CALL sequencing rule** (`messageCall_call_runs`), instantiated on a real
  caller/callee bytecode pair to give the `∃G₀` storage-observable theorem, plus the
  **executable `∃G₀` counterexample** (the 63/64 cap starves the callee, its
  `SSTORE` rolls back, the caller still completes). The rule rests on the
  unconditional `messageCall_never_outOfFuel` and the generic descent equation
  `drive_descend_eq`; the old circular forwarding hypothesis is gone.

Every exported theorem's `#print axioms` is **exactly** `[propext,
Classical.choice, Quot.sound]` (re-verified — see §5). The two foundation-level
obstructions reported by an earlier run — the `bv_decide` axiom inherited by
`messageCall`, and the `private callArm`/`createArm` — were both resolved by **one
upstream leanevm commit** (`9cefe5b`, conformance unchanged at 2859/2859), which §3
records as the key cross-cutting finding.

> For the detailed module-by-module navigation surface (the abstraction stack,
> the dependency graph feeding the headline, the soundness verdict, and the full
> axiom table), read [`docs/review-report.md`](review-report.md). This file is the
> *results summary* — what's proven, the green/axiom evidence, the foundation
> finding, and the forced abstractions — and points at the review report rather
> than re-stating every signature verbatim.

---

## 1. What is proven (canonical names + namespaces)

All theorems build green against the real `forks/leanevm` (`import Evm`). Every one
below prints **exactly** `[propext, Classical.choice, Quot.sound]` (§5).

### M1 — call-free spine

The per-program specs live in `Examples/ConcreteSpecs.lean`
(`namespace BytecodeLayer.Examples`); they are observables-only worked examples that
delegate to the composed `*'` lemmas in `Examples/ProgramExamples.lean`.

```lean
-- Examples/ConcreteSpecs.lean         (namespace BytecodeLayer.Examples)
def stopProgram : ByteArray := ⟨#[0x00]⟩                              -- in Programs.lean

theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok Observables.ok

def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩             -- PUSH1 5; STOP

theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok Observables.ok

def sstoreProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x00]⟩  -- PUSH1 5;PUSH1 7;SSTORE;STOP

theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok (Observables.ok, 5)

def seqProgram : ByteArray := ⟨#[0x60,0x05,0x60,0x07,0x55,0x60,0x0B,0x60,0x09,0x55,0x00]⟩

theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok (Observables.ok, 5, 11)
```

All four are **frame-free** (no `Frame`, pc, stack), **fuel-free** (`seedFuel`/
`drive` fuel never appears), and stated **only** through `CallResult.observe` /
`CallResult.storageAt`. Their only quantitative content is the program's exact
intrinsic cost (`3`, `22106`, `44212` gas) as a plain `≤` hypothesis — **no
`∃G₀`**, because no 63/64-style nonlinearity arises off the call path.

### M2 — external calls (the headline)

The headline is the **general** rule `messageCall_call_runs` (`Hoare/CallSequence.lean`,
`namespace BytecodeLayer.Hoare`, re-exported on `Spec.lean`). It is program-agnostic
over *both* caller and callee:

```lean
-- Hoare/CallSequence.lean (re-exported BytecodeLayer.messageCall_call_runs in Spec.lean)

/-- The three call-facts, bundled. -/
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending

theorem messageCall_call_runs (p : CallParams) {n₁ n₂ : ℕ}
    {fr₀ callFr resumeFr last : Frame} {halt : FrameHalt}
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcallret : CallReturns callFr resumeFr)
    (hpost    : Runs n₂ resumeFr last)
    (hhalt    : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))
```

A caller that enters as code (`EntersAsCode`), `Runs` its prefix to the CALL site,
issues a CALL whose child *terminates as a black box* and resumes at `resumeFr`
(`hcallret : CallReturns callFr resumeFr` — bundling the CALL step, the child
entering as code, and any `drive … = .ok childRes`, no oracle), then `Runs` its
suffix to a halt, produces exactly the caller's halt result as the top-level
`messageCall`. The rule is a clean **five-hypothesis sequence** with **no numeric
fuel side condition** — the fuel bound is discharged internally by running the
sequence at a large concrete fuel and reconciling with `seedFuel p.gas` via
`drive_eq_of_both_ne_oof` + `messageCall_never_outOfFuel`. The observable-level
lift `messageCall_call_completedWith` adds success+cell hypotheses to land the
named `Outcome.completedWith`.

The worked instantiation and the `∃G₀` spec (`namespace BytecodeLayer.Examples`):

```lean
-- Examples/CallerProgExample.lean — instantiates messageCall_call_runs on real bytecode
--   caller (callerProg): PUSH1 0 ×5 ; PUSH3 0xCA11EE ; PUSH4 0xFFFFFFFF ; CALL ; STOP
--   callee (calleeProg, at 0xCA11EE): PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP
theorem messageCall_callerProg_storageAt (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5

-- Examples/ConcreteSpecs.lean — the ∃G₀ spec delegates to the compositional proof above
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 :=
  ⟨30000, fun g hg => messageCall_callerProg_storageAt g hg⟩

theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0
```

- **`messageCall_call_runs`** is the headline: the sound, program-agnostic CALL
  sequencing rule. Every hypothesis is a *structural* fact about how the bytecode
  executes — the child is a black box (bundled with the CALL step and child entry
  in `CallReturns`), and the caller's prefix/suffix are honest `Runs` traces. There
  is no numeric fuel premise (the bound is discharged internally). No hypothesis is
  conclusion-shaped; the reconciliation a forwarding hypothesis used to assume is
  now *proved* (`drive_descend_eq` + `messageCall_never_outOfFuel` + fuel
  monotonicity).

- **`messageCall_call_storageAt`** (the `∃G₀` goal, witness **`G₀ = 30000`**)
  instantiates that rule on `callerProg`/`calleeProg` via the **compositional**
  `messageCall_callerProg_storageAt`: with enough gas the child clears the 63/64
  `callGasCap`, its `SSTORE` commits, and the callee's cell `(addrCallee, 7)` holds
  `5`. Observables-only, frame-free, fuel-free at the messageCall boundary. There is
  exactly **one** (compositional) proof of this spec.

- **`call_counterexample`** is the executable witness that the `∃G₀` is *forced*,
  not cosmetic: at the modest `g = 24000` the same observable is `0`
  (`childGas 24000 = 21045 < 22106`, so the callee's `SSTORE` out-of-gases under the
  cap and is rolled back), **while the top-level call still completes** (the caller
  is handed flag `0` and `STOP`s cleanly — no top-level `OutOfGas`). So no
  gas-floor-free statement ("completes ⇒ cell is 5") can hold; the existential is
  necessary. This is 001's executable `∃G₀` counterexample, **reached**.

### The unconditional never-out-of-fuel headline

```lean
-- Semantics/Interpreter/NeverOutOfFuel.lean (namespace BytecodeLayer.Interpreter)
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel
```

No fuel/`Frame` in the statement: for *every* `CallParams`, the interpreter never
spuriously reports `OutOfFuel` (out-of-gas is a real halt; fuel is a Lean
termination device and must not leak). This is load-bearing for the CALL rule (it
keeps the prefix descent from being `OutOfFuel`).

### Audit-surface bricks (re-exported on `Spec.lean`, `namespace BytecodeLayer`)

The reusable program-logic rules a user instantiates — all also
`[propext, Classical.choice, Quot.sound]`: the sequencing rule `Runs.trans`; the
`messageCall` boundary bridge `messageCall_runs`; the opcode rules `runs_push1`,
`runs_push`, `runs_sstore`; the SSTORE effect/framing pair
`sstoreFrame_storage_self` / `sstoreFrame_storage_frame`; and the external-CALL rule
`messageCall_call_runs` / `messageCall_call_completedWith`. See `Spec.lean` (and the
module map in `review-report.md` §3) for their exact signatures and homes.

---

## 2. Abstractions the proofs FORCED (validated-necessary)

The rebuilt architecture forces a *smaller, more honest* set of abstractions than
the retired monolith. Each below was extracted exactly when a proof demanded it.

- **The compositional CALL rule `messageCall_call_runs` (`Hoare/CallSequence.lean`).**
  The keystone. It reconciles a black-box terminating child against the caller's
  actual suffix run *without* assuming the forwarding. Forced once we refused to
  carry a conclusion-shaped hypothesis: the only way to land the caller's halt
  result soundly is to prove the descent reconciliation, not assume it.

- **`drive_descend_eq` / `drive_append_framing` (the generic CALL-boundary descent
  equation, `Semantics/Interpreter/DescentEq.lean`).** The program-agnostic,
  fuel-existential replacement for the old fuel-explicit `child_run` scaffolding.
  `drive_append_framing` says an inert bottom stack segment is untouched while
  execution proceeds above it; peeling one `.call` resume step gives
  `drive_descend_eq`: a parent's in-line descent into a *terminating* child equals
  running that child independently and then resuming the parent (residual fuel `j`
  existential, so no exact bookkeeping). Forced by M2's need to relate the in-parent
  child run to a standalone child run, soundly.

- **The measure `μ` + `mu_bound` + `gasFundsDescent` (the never-out-of-fuel
  subsystem, `Semantics/Interpreter/Measure.lean` → `NeverOutOfFuel.lean`).**
  `μ stack state = 2·totalGas + 2·stack.length + tagBit` strictly drops on every
  `drive` recursion; the CALL/CREATE descent and `System`-`.next` fallback drops are
  taken as the `gasFundsDescent` hypothesis in `Measure.lean` and **discharged** in
  `NeverOutOfFuel.lean` (`gasFundsDescent_holds`, five gas-arithmetic conjuncts),
  yielding the unconditional `messageCall_never_outOfFuel`. Forced by the CALL rule's
  need for an *unconditional* "the prefix descent can't be `OutOfFuel`" fact. (The
  governing `Prop` is `gasFundsDescent` — not the old `DescentDrops`.)

- **The localized 63/64 arithmetic: `childGas` / `childGas_lb` + `Gas.liftFloor` /
  `Gas.allButOneSixtyFourth_ge_of_liftFloor_le`.** The *only* genuine gas
  arithmetic in the experiment, living **only at the call site**. The 63/64
  forwarding floor is now mediated by the **universal** lemma `Gas.liftFloor`
  (`Semantics/Gas.lean`): `allButOneSixtyFourth` (`= ⌈63n/64⌉`) clears a cost `C`
  once `n ≥ liftFloor C`. `childGas_lb` (`ExternalCall.lean`) routes its
  `≥ 22106 for g ≥ 30000` success bound through it (`liftFloor 22106 = 22457`); the
  negation (`childGas 24000 = 21045`) drives the counterexample. Extracting the
  universal `liftFloor` lemma localizes the nonlinearity to one reusable fact
  instead of an ad-hoc inequality.

- **`CallResult.observe` + `CallResult.storageAt` (`Observables.lean`, the export
  surface).** The observable projections. `observe` gives world-map-independent
  `(success, output)`; `storageAt` reads a single cell `(addr, key)` exactly as the
  EVM's `SLOAD` (`findD … 0`) off the returned `accounts` map — at the messageCall
  boundary, no frame/pc/stack/fuel. It is the persistent observable the SSTORE and
  CALL rungs assert, and the cell whose value (`5` vs `0`) the `∃G₀`
  counterexample distinguishes.

- **The `Runs` Hoare core + `Runs.trans` + opcode rules (`Hoare.lean`).** The
  composition relation never names a trace; programs are built by gluing per-opcode
  `Runs` rules (`runs_push1`/`runs_push`/`runs_sstore`) with the sequencing rule
  `Runs.trans`, crossing the boundary with `messageCall_runs`. The
  `subCharges`/`toNat_subCharges` gas-threading (`Hoare/Sequence.lean`) reads the
  running `gasAvailable` after a charge list as a fixed prefix sum, avoiding the
  quadratic blow-up of nested `toNat_sub_ofNat` on multi-charge sequences.

### Abstractions that turned out UNNECESSARY (and ones now RETIRED)

- **The old monolith is gone.** `messageCall_call_eq` and its scaffolding
  (`child_run`, `callerResult`, the reflexive-witness `messageCall_child_reflexive`)
  are **deleted** — the `∃G₀` story no longer rides a single giant opcode chain with
  an assumed reflexive child, but the compositional rule + a worked instantiation.
- **No circular forwarding hypothesis.** The retired `behaves_call`/`CallerForwards`/
  `hforward` hypothesis assumed the very forwarding it was meant to prove; it is
  **entirely gone** (grep-confirmed zero occurrences). Its reconciliation is now
  *proved* by `drive_descend_eq` + `messageCall_never_outOfFuel` + fuel monotonicity.
- **No shadow gas ledger, no metered copy of the semantics, no oracle, no
  record-commutation simp.** Gas is carried by the single `charge`/`callGasCap`
  guards; the child is the real `drive`, consumed as a black box, never assumed.
- **No `injectFrame` analogue, no `set`-abbreviation, no record-commutation lemmas.**
  The messageCall boundary is frame-free; nothing pins a final frame in any exported
  observable statement.

---

## 3. The foundation fix that unblocked everything (KEY FINDING)

An earlier run hit two orthogonal foundation-level walls and reported them as
findings (the correct move — a wall is a finding, not a `sorry`):

1. **`bv_decide` axiom.** `Evm.messageCall`/`drive`/`stepFrame`/`beginCall`/
   `endFrame` all inherited `Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7`
   from `Evm/UInt256.lean`, because `blt_iff_toBitVec_lt` was proved by `bv_decide`
   and powered `UInt256`'s `Decidable (·<·)`/`(·≤·)`. This made literal axiom
   purity *structurally impossible* for any `messageCall` theorem.
2. **`private callArm`/`createArm`** in `Evm/Semantics/System.lean` left the CALL
   reduction inaccessible, blocking M2.

**Both were fixed by a single endorsed upstream leanevm commit** (`9cefe5b`,
"Remove bv_decide axiom from the execution path; expose callArm/createArm"):

- `blt_iff_toBitVec_lt` was **reproved without `bv_decide`** — reducing both sides
  to `Nat` (`BitVec.lt_def` + `toNat_limbs`) and discharging the 8-limb
  lexicographic equivalence with `omega` (limb `< 2^32` bounds in scope; the
  `2^(32·i)` weights are constants, so it stays linear). `blt`, `toBitVec`, and the
  `Decidable` instances are unchanged, so the fast limb-wise runtime path is
  preserved. `#print axioms Evm.messageCall` is now `[propext, Classical.choice,
  Quot.sound]`.
- `callArm`/`createArm` made non-`private`.
- **Fast conformance unchanged: 2859/2859** — no semantic regression.

This validated the central diagnosis exactly: the obstruction was
**definition-level in the foundation, not in the bytecode reasoning layer**, and
fixing it upstream made *all* of experiment 003 axiom-clean at a stroke — every
exported theorem now prints `[propext, Classical.choice, Quot.sound]` (§5). The
remaining `bv_decide` uses in `Evm/UInt256.lean` are spec lemmas unreachable from
`messageCall`/`dispatch`, so the execution path is clean.

---

## 4. The `∃G₀` story, completed

001's headline — that external-call correctness *requires* an `∃G₀` gas floor
because the 63/64 cap can starve a callee whose failure the caller swallows — is
now stated and proved against the **real `messageCall`**, in observables, and — the
rebuild's contribution — **without any assumed forwarding**:

- `messageCall_call_runs`: the sound, program-agnostic CALL sequencing rule (black-
  box child bundled in `CallReturns`, honest caller traces, no numeric fuel side
  condition).
- `messageCall_call_storageAt`: `∃ G₀ (= 30000), ∀ g ≥ G₀, cell (addrCallee,7) = 5`,
  obtained by instantiating the rule on `callerProg`/`calleeProg` via the
  compositional `messageCall_callerProg_storageAt`.
- `call_counterexample`: at `g = 24000 < G₀`, the same cell is `0`, *with the
  top-level call completing* — so the floor is not removable.

The gap between success (`5`) and starvation (`0`) is exactly the 63/64
`callGasCap` (`allButOneSixtyFourth`) binding against the callee's `22106` cold
first-write `SSTORE` cost — the single localized arithmetic of §2 (`childGas`
through `Gas.liftFloor`), at the call site, nowhere else.

---

## 5. Green / zero-sorry / axiom confirmation (re-verified)

- `lake build` inside `experiments/003_bytecode_layer`: **`Build completed
  successfully (1127 jobs).`**, with **zero warnings and zero errors** (re-run for
  this regeneration).
- `grep -rEn "sorry|admit|native_decide|bv_decide|maxHeartbeats" BytecodeLayer/`:
  the **only** match is the word "sorry" inside a `Semantics/Maps.lean` docstring —
  no `sorry`/`admit`/`native_decide`/`bv_decide`/`maxHeartbeats` in any proof.
- `#print axioms` (re-run via `lake env lean`) on every audit-surface and headline
  theorem — **all exactly `[propext, Classical.choice, Quot.sound]`**:

```
'BytecodeLayer.Runs.trans'                                  [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_runs'                            [propext, Classical.choice, Quot.sound]
'BytecodeLayer.runs_push1'                                  [propext, Classical.choice, Quot.sound]
'BytecodeLayer.runs_push'                                   [propext, Classical.choice, Quot.sound]
'BytecodeLayer.runs_sstore'                                 [propext, Classical.choice, Quot.sound]
'BytecodeLayer.sstoreFrame_storage_self'                    [propext, Classical.choice, Quot.sound]
'BytecodeLayer.sstoreFrame_storage_frame'                   [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_call_runs'                       [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_call_completedWith'             [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Interpreter.messageCall_never_outOfFuel'     [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.messageCall_stop_observe'           [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.messageCall_pushStop_observe'       [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.messageCall_sstore_storageAt'       [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.messageCall_seq_storageAt'          [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.messageCall_call_storageAt'         [propext, Classical.choice, Quot.sound]
'BytecodeLayer.Examples.call_counterexample'                [propext, Classical.choice, Quot.sound]
```

The same axiom table, with file/line anchors, is in
[`docs/review-report.md`](review-report.md) §6.
