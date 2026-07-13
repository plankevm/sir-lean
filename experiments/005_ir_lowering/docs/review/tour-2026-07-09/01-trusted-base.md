# 01 — The trusted bytecode base and the engine theory built on it

Part of the [exp005 tour](00-overview.md). Siblings: [02 spec layer](02-spec-layer.md) ·
[03 code geometry](03-code-geometry.md) · [04 value channel](04-value-channel.md) ·
[05 simulation](05-simulation.md) · [06 realisability](06-realisability.md) ·
[07 assembler](07-assembler.md).

## TL;DR

Exp005's proofs stand on a two-story trusted base: the **executable EVM machine** vendored in
exp003 ([`EVMLean/`](../../../../003_bytecode_layer/EVMLean/README.md), whose fidelity warrant is
the conformance suite — 2859/2859 fast, 22,308 − 2 expected failures full, *reported, not re-run*),
and exp003's **proved `Runs` Hoare surface**
([`Hoare.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L140)). The project lead's
working assumption — that `Runs` + [`messageCall_runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L195)
was "everything needed" for an IR lowering — turned out false: exp003's theory is **forward-only**
(program → result), while the conformance flagship starts from an actual run and must reason
*backward* and *per-step*. Exp005 had to build, in-house, the reverse direction
[`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357), a ~1,300-line per-opcode
account-presence walk ([`StepWalk.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1119)), a whole-run
presence induction ([`drive_accounts_find_mono`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L159)), a
clean-halt/gas-envelope extractor
([`CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean#L700)), plus memory,
storage-erase, and charge-fold algebra exp003 never provided. The reusable portion of that engine
theory now lives in exp003's `BytecodeLayer/Hoare/` proof layer; lowering-dependent pieces remain
in exp005. Two documented exp003 surface
drifts verify against source: a stale
[`Hoare.lean` docstring](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L26) promising
"`Runs` never appears in an exported statement" (it now sits inside exp005's flagship hypotheses),
and the [`Spec.lean` audit surface](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L11)
that exp005 bypasses entirely.

**Verification status (one line):** every in-scope exp005 file greps clean of
`sorry`/`admit`/`native_decide`/`bv_decide`; the only `maxHeartbeats` in scope is two
`800000` cranks in [`MemAlgebra.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L492) (§8);
axiom-cleanliness (`[propext, Classical.choice, Quot.sound]`) is asserted by build-enforced
`#print axioms` guard lines at the bottom of each file and by exp003's recorded table in
[`results.md` §5](../../../../003_bytecode_layer/docs/results.md) — reported, not re-run.

---

## 1. Scope and layer map

This report covers the three trusted/engine strata every other report in the tour stands on:

| Stratum | Where | Warrant |
|---|---|---|
| **L0a — executable machine** | exp003 [`EVMLean/Evm/`](../../../../003_bytecode_layer/EVMLean/Evm.lean) (`stepFrame`, `drive`, `messageCall`, `decode`, `beginCall`/`beginCreate`, `resumeAfterCall`/`Create`, `seedFuel`) | Empirical: conformance suite (§2) |
| **L0b — exp003's proved surface** | [`BytecodeLayer/`](../../../../003_bytecode_layer/BytecodeLayer.lean) (`Runs`, `CallReturns`, `CreateReturns`, `messageCall_runs`, fuel monotonicity, gas monotonicity, per-opcode rules) | Proved; axiom table recorded in [results.md](../../../../003_bytecode_layer/docs/results.md) |
| **L0b′ — shared interpreter proof theory** | [`BytecodeLayer/Hoare/`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean), [`Frame/StorageErase.lean`](../../../LirLean/Frame/StorageErase.lean), [`Drive/CallPreservesSelf.lean`](../../../LirLean/Drive/CallPreservesSelf.lean), the IR-free half of [`Materialise/CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean) | Reusable core folded into exp003; lowering-specific consumers remain in exp005 |

Engine/proof-layer inventory at the time of this review:

| File | Lines | One-line job |
|---|---|---|
| [`BytecodeLayer/Hoare/AccountMap.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean) | 145 | RBMap presence bricks: `AccPresent`, insert-mono, `≠ ∅` from a `find?` hit |
| [`BytecodeLayer/Hoare/Charges.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean) | 32 | `subCharges` snoc/append fold algebra |
| [`BytecodeLayer/Hoare/CleanHalt.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean) | 103 | `CleanHalts` / `CleanHaltsNonException` + forward closure along `Runs` |
| [`BytecodeLayer/Hoare/Descent.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean) | 844 | CALL/CREATE site inversions (`stepFrame_needsCall_inv` etc.), begin/resume framing, `DescentKind` |
| [`BytecodeLayer/Hoare/DriveMono.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean) | 294 | Whole-`drive`-run account-presence monotonicity (Brick D) |
| [`BytecodeLayer/Hoare/DriveRuns.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean) | 482 | **The reverse direction**: `drive → Runs` (`runs_of_drive_ok`) |
| [`BytecodeLayer/Hoare/MemAlgebra.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean) | 996 | Byte-level MSTORE/MLOAD read-back, disjointness, zero-window CALL memory preservation |
| [`Decode/Modellable.lean`](../../../LirLean/Decode/Modellable.lean) | 462 | Lowering-specific `ModellableStep` producer: `CreateResolves`/`CallsCode` residuals |
| [`BytecodeLayer/Hoare/StepWalk.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean) | 1,336 | THE per-opcode dispatch walk: env-equality + account-presence mono for every `.next` arm |
| [`Frame/StorageErase.lean`](../../../LirLean/Frame/StorageErase.lean) | 217 | `RBMap.erase` read-back (`findD_erase_self`/`_of_ne`) for the zero-write SSTORE |
| [`Drive/CallPreservesSelf.lean`](../../../LirLean/Drive/CallPreservesSelf.lean) | 350 | Self-presence forward-closed along `Runs`, reduced to the one precompile seam |
| [`Materialise/CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean) | 1,123 (~1,000 IR-free) | Per-opcode OOG/`.next` dichotomies + clean-halt ⟹ gas envelopes (envelope half → [report 04](04-value-channel.md)) |

Total ≈ 6,384 lines; the engine-shaped portion ≈ 6,260 of `LirLean`'s 26,867 — **≈ 23%**,
consistent with the codebase map's "~23% counting IR-free majorities" refinement of the audit's
~20% claim.

---

## 2. L0a — the vendored machine, and what its warrant actually is

The machine is philogy/leanevm vendored at commit `9cefe5b` (Cancun), toolchain `v4.30.0`. Its
core is one recursion:

```lean
-- ../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok result
            | pending :: rest =>
              match pending.resume result with
                | .ok parent => drive fuel rest (.inl parent)
                | .error e =>
                  drive fuel rest (.inr (endFrame pending.frame (.exception e)))
        | .inl current =>
          match stepFrame current with
            | .next exec => drive fuel stack (.inl { current with exec := exec })
            | .halted halt => drive fuel stack (.inr (endFrame current halt))
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => drive fuel (.call pending :: stack) (.inl child)
                | .inr result => drive fuel (.call pending :: stack) (.inr (.call result))
            | .needsCreate params pending =>
              drive fuel (.create pending :: stack) (.inl (beginCreate params))
```

with the fuel seed and boundary ([same file](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L71)):

```lean
def seedFuel (gas : UInt64) : ℕ := 2 * gas.toNat + 4096

def messageCall (params : CallParams) : Except ExecutionException CallResult :=
  match beginCall params with
    | .inr result => .ok result
    | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)
```

The pieces exp005 reasons about by name:
[`stepFrame`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Dispatch.lean#L130) (decode +
dispatch of one opcode),
[`beginCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L18) (code child
`.inl` vs precompile/immediate `.inr`),
[`endCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L93) (success keeps the
child world, revert/exception rolls back to the checkpoint),
[`resumeAfterCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L122),
[`beginCreate`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L64) (**total** —
always descends), and the `Except`-typed
[`resumeAfterCreate`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L189)
(the 63/64 retention guard can `throw .OutOfGas` — the source of exp005's `CreateResolves` seam,
§6.2).

**Fidelity warrant — empirical, not formal.** Nothing proves this machine implements the Yellow
Paper. The warrant is the conformance runner against the Ethereum BlockchainTests fixtures:

- fast phase **2859/2859**, recorded at the endorsed upstream commit in
  [exp003 `results.md` §3](../../../../003_bytecode_layer/docs/results.md) — *reported, not re-run*;
- full phase **22,308 tests with exactly 2 expected failures**, the two entries of
  `ExpectedToFail` in [`Conform/Main.lean`](../../../../003_bytecode_layer/EVMLean/Conform/Main.lean#L178)
  (a 4844 blob-count edge and a gas-refund/suicide edge) — *reported, not re-run*.

Anything the tests do not exercise (and everything about the `Frame`/`Pending`/fuel plumbing,
which is interpreter-internal) is trusted definitionally. exp005's flagship inherits exactly this
warrant.

---

## 3. L0b — exp003's proved surface, at the granularity exp005 consumes it

Exp005 imports exactly six exp003 modules
(aggregated from the `import BytecodeLayer.*` lines across `LirLean/`):
[`Hoare`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean),
[`Hoare.CallSequence`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean),
[`Hoare.Sequence`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean),
[`Hoare.GasMonotone`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/GasMonotone.lean),
[`Semantics.Maps`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Maps.lean), and
[`Semantics.Dispatch`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Dispatch.lean)
(plus `import Evm` directly). The rest of `BytecodeLayer` — the
[`Spec.lean`](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean) audit surface, the worked
[`Examples/`](../../../../003_bytecode_layer/BytecodeLayer/Programs.lean), and the dormant
cross-engine equivalence track
([`SharedObservable.lean`](../../../../003_bytecode_layer/BytecodeLayer/SharedObservable.lean),
[`EVMSpec.lean`](../../../../003_bytecode_layer/BytecodeLayer/EVMSpec.lean),
[`Equivalence.lean`](../../../../003_bytecode_layer/BytecodeLayer/Equivalence.lean),
[`Refinement.lean`](../../../../003_bytecode_layer/BytecodeLayer/Refinement.lean),
[`ExternalCall.lean`](../../../../003_bytecode_layer/BytecodeLayer/ExternalCall.lean),
[`Observables.lean`](../../../../003_bytecode_layer/BytecodeLayer/Observables.lean)) — is **never
imported by exp005** (§8.2).

### 3.1 The `Runs` Hoare logic

The whole theory is one inductive over one atom and two black-box descent bundles
([`Hoare.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L52)):

```lean
-- ../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L52
def StepsTo (fr fr' : Frame) : Prop :=
  stepFrame fr = Signal.next fr'.exec ∧ fr' = { fr with exec := fr'.exec }

-- #L91
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending

-- #L118
def CreateReturns (createFr resumeFr : Frame) : Prop :=
  ∃ cp pending childRes,
       stepFrame createFr = .needsCreate cp pending
     ∧ drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes
     ∧ resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr

-- #L140
inductive Runs : Frame → Frame → Prop where
  | refl (fr : Frame) : Runs fr fr
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') : Runs fr fr'
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
  | create {createFr resumeFr fr' : Frame} (hc : CreateReturns createFr resumeFr)
      (rest : Runs resumeFr fr') : Runs createFr fr'
```

where [`EntersAsCode`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/System.lean#L237)
is `beginCall p = .inl fr` and
[`running`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Drive.lean#L32)
is `.inl`. Note the `create` node was added *for exp005* (marked "SPIKE" in source) — exp003's
original experiment never modelled CREATE.

The results exp005 leans on, by consumption weight:

- **[`messageCall_runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L195)**
  — the forward boundary bridge, no fuel side condition:

  ```lean
  theorem messageCall_runs (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
      (hbegin : EntersAsCode p fr₀)
      (h : Runs fr₀ last)
      (hhalt : stepFrame last = Signal.halted halt) :
      messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))
  ```
  Proved via [`Runs.drive_reconcile`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L115)
  (any two non-`OutOfFuel` runs from the two ends of a `Runs` path deliver the same result) +
  [`messageCall_never_outOfFuel`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144)
  (unconditional: fuel is a termination device, never observable — proved through the measure
  [`μ`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Measure.lean#L77) and
  [`mu_bound`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Measure.lean#L125)).

- **[`drive_fuel_mono`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Drive.lean#L185)**
  — fuel erasure: a non-`OutOfFuel` run gives the same answer at every larger fuel. Exp005's
  reverse construction reconciles child fuels through it constantly.

- **[`drive_descend_eq`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L143)**
  / [`drive_append_framing`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L58)
  — the CALL-boundary descent equation (parent's in-line child run = standalone child run + resume,
  residual fuel existential), and its CREATE twin
  [`drive_descend_create_eq`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L63).

- **[`Runs.gasAvailable_le`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/GasMonotone.lean#L281)**
  — gas never increases along a `Runs`, including through `.call`/`.create` nodes (the 63/64
  net-debit, [`CallReturns.gas_le`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/GasMonotone.lean#L218)):

  ```lean
  theorem Runs.gasAvailable_le {fr last : Frame} (h : Runs fr last) :
      last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat
  ```
  This is what makes exp005's monotone gas-read law (v3 IR design) derivable rather than assumed.

- **[`Runs.linear_to_halt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L323)** —
  `stepFrame` is a function, so a `Runs` ending in a halt is linear: every reachable frame
  continues to the *same* halt. This single determinism fact powers exp005's forward clean-halt
  splitting ([`cleanHalts_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L69)) and the
  halting-terminal uniqueness inside
  [`conforms_of_worldeq`](../../../LirLean/Realisability/RealisabilitySpec.lean#L204).

- **Per-opcode `Runs` rules and post-frame vocabulary** — one rule + one named post-frame per
  lowered opcode, e.g.
  [`runs_push`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L376)/`pushFrameW`,
  [`runs_sstore`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L388)/`sstoreFrame` with
  effect/framing pair
  [`sstoreFrame_storage_self`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L789) /
  [`sstoreFrame_storage_frame`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L809),
  [`runs_sload`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L470) with read companion
  [`sloadFrame_storage_self`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L493),
  [`runs_add`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L447) /
  [`runs_lt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L458) /
  [`runs_gas`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L482) /
  [`runs_pop`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L514) /
  [`runs_mstore`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L587) /
  [`runs_mload`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L605), the CFG trio
  [`runs_jump`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L671) /
  [`runs_jumpi_taken`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L684) /
  [`runs_jumpi_fallthrough`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L700) /
  [`runs_jumpdest`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L717), and the
  cancellation lemmas [`Runs.step_cancel`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L258).
  These are the bricks [report 04](04-value-channel.md)'s `MatRuns` and
  [report 05](05-simulation.md)'s `sim_*` arms instantiate; per-decl coverage belongs there.

- **[`subCharges`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L62)** /
  [`toNat_subCharges`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L69) —
  linear gas threading (running gas after a charge list as one prefix sum), extended by exp005's
  [`Charges.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L19).

Not consumed by exp005 but on exp003's surface: the observable-level lifts
([`messageCall_calls_completedWith`](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L246)),
`Hoare/Behaves.lean`, `Hoare/OutcomeBridge.lean`, and the worked `∃G₀` examples — exp003-internal
deliverables, leaves from exp005's perspective.

---

## 4. THE CENTRAL QUESTION: why "a Hoare logic + `messageCall_runs`" was not enough

The belief was reasonable on its face: exp003 delivered a sound, program-agnostic composition
relation with a fuel-free boundary bridge, per-opcode rules, and even multi-call composition. To
verify *hand-written* bytecode, that IS everything: you build the `Runs` forward, rule by rule, and
cash it in at `messageCall_runs`. The lowering flagship broke the assumption because its statement
runs in the **opposite direction and at a different granularity**. The flagship
([`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251), reviewed in
[report 06](06-realisability.md)) starts from `hrun : runWithLog params (seedFuel params.gas) =
some log` — an *actual completed `drive` execution* — and must produce an IR run consuming streams
recorded *from that execution*. Concretely, five things were missing:

### (a) The theory was forward-only; the flagship needs `drive → Runs`

Every exp003 bridge consumes a `Runs` you already have and produces a `drive`/`messageCall` fact.
Nothing ever *produces* a `Runs` from an execution. But the flagship's only runtime premise is a
successful recorded run, so exp005 needed the reverse construction —
[`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357):

```lean
-- ../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357
theorem runs_of_drive_ok :
    ∀ (f : ℕ) (fr : Frame) (res : FrameResult),
      drive f [] (running fr) = .ok res →
      (∀ fr', Runs fr fr' → ModellableStep fr') →
      ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
        ∧ res = endFrame last halt
```

This is *not* a symmetry-flip of `messageCall_runs`; it needed new machinery exp003 had no reason
to build:

- **bounded descent.** `drive_descend_eq`'s residual fuel is an unordered existential — useless for
  a well-founded reverse recursion. Exp005 re-proved the framing with a *strict* bound
  ([`drive_append_framing_lt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L51),
  [`drive_descend_lt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L115), CREATE twin
  [`drive_descend_create_lt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L135)) so the resumed parent
  recurses at `j < f`.
- **error classification.**
  [`drive_error_oof`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L193) (the only `drive` error is
  `OutOfFuel`; exceptions are folded into results by `endFrame`), so a framed non-OOF run forces
  the standalone child to terminate
  ([`child_terminates`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L234),
  [`framed_oof_of_standalone_oof`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L270)).
- **the `ModellableStep` side condition** ([def](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L182)) —
  `Runs` cannot resume two machine configurations: a precompile CALL (`beginCall = .inr`, no
  `Runs` node) and a CREATE whose resume OOG-faults (the `Except` in `resumeAfterCreate`; the
  fault is an exception delivered *through the drive stack*, a control flow `Runs` does not
  model). The reverse construction is honest about this: it carries the residual per reachable
  frame rather than pretending `Runs` is complete. Discharging that residual down to two
  satisfiable seams is the job of
  [`Decode/Modellable.lean`](../../../LirLean/Decode/Modellable.lean#L450) (§6.2).

**What breaks without it:** the flagship's `Conforms` conjunct — assembled in the closed
[`conforms_of_worldeq`](../../../LirLean/Realisability/RealisabilitySpec.lean#L204) and in
[`cleanHalts_of_runWithLog`](../../../LirLean/Drive/DriveSim.lean#L143) — has no way to get from
the recorded run to the halting `Runs` that everything downstream (terminal uniqueness, observable
extraction, gas monotonicity) is stated over.

### (b) No per-step frame walks: account presence had to be proved for every opcode

Exp003's SSTORE effect lemma
([`sstoreFrame_storage_self`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L789))
carries `hself : fr.exec.accounts.find? self = some acc` — in exp003's worked examples that
hypothesis is discharged once, by construction of the concrete initial state. For an *arbitrary*
lowered program, the cursor frame issuing an SSTORE sits an unbounded number of steps — including
returning CALLs and CREATEs, whose resumes swap in the *child's* returned account map — past the
entry frame. Presence must be **transported**, and exp003 had zero per-opcode state-preservation
theory (its dispatch walk, `StepsTo.gas_le`, tracks only gas). Exp005 built the whole stack:

- [`AccountMap.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L102): the tracked-address vocabulary
  and two closers —

  ```lean
  def AccPresent (a : Evm.AccountAddress) (m : Evm.AccountMap) : Prop :=
    ∃ acc : Evm.Account, m.find? a = some acc
  ```
  [`accounts_find?_insert_mono`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L114) (presence survives
  any insert) and [`accMono_emptySwap`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L140) (the
  `if m == ∅ then …` branch in `endCall .success`/precompile fallbacks is dead when `a` is
  present — via the genuinely fiddly RBMap `BEq`-vs-empty short-circuit
  [`find?_some_ne_empty`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L74)).
- [`StepWalk.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L129): **the ~1,300-line single
  induction** over every `dispatch` arm, capped by

  ```lean
  -- ../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1119
  theorem stepFrame_next_accMono {fr : Frame} {exec' : ExecutionState}
      (h : stepFrame fr = .next exec') (a : AccountAddress)
      (hp : AccPresent a fr.exec.accounts) : AccPresent a exec'.accounts
  ```
  plus [`stepFrame_next_execEnvAddr`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1092) (a `.next` never
  moves the execution environment), the self corollary
  [`stepFrame_next_self`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1148), and the halt-success family
  [`stepFrame_halted_success_accMono`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1297)
  (STOP/RETURN/SELFDESTRUCT never erase). Proof method: per-combinator `NoCallCreate`-style
  case grinding, one arm at a time; large but shallow.
- [`Descent.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L124): the CALL/CREATE **site inversions**
  ([`stepFrame_needsCall_inv`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L124),
  [`stepFrame_needsCreate_inv`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L361) and their `site_inv`
  strengthenings) — a `.needsCall` pins the child params' accounts to the issuing frame's, the
  suspended frame's kind and env to the caller's. Plus begin/resume presence threading
  ([`beginCall_inl_accounts_present`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L505),
  [`resumeAfterCreate_exec_accounts_present`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L614)) and the
  [`DescentKind`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L696) interface packaging CALL
  ([`callDescent`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L753)) and CREATE
  ([`createDescent`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L777)) uniformly.
- [`DriveMono.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L159): Brick D, the whole-child-run
  induction —

  ```lean
  theorem drive_accounts_find_mono (a : Evm.AccountAddress)
      (hmono : …) (hprec : …) (hcall_acc : …) (hcall_kind : …) (hhalt : …) :
      ∀ (f : ℕ) (stack : List Evm.Pending) (state : Evm.Frame ⊕ Evm.FrameResult)
        (res : Evm.FrameResult),
        Evm.drive f stack state = .ok res → DrivePresent a stack state →
        AccPresent a res.toCallResult.accounts
  ```
  threading the invariant [`DrivePresent`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L60) (running map
  + running frame's checkpoint + every pending ancestor's checkpoint — three simultaneous facts
  because two `drive` exits *roll back* to checkpoints). Of the five closers, four are the
  universally-true walk/inversion facts above; only `hprec` (precompile output maps preserve
  presence) is a genuine seam.
- [`Drive/CallPreservesSelf.lean`](../../../LirLean/Drive/CallPreservesSelf.lean#L321)
  assembles it all along `Runs`:

  ```lean
  theorem selfPresent_runs_of_call
      (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
        Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
      {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr'
  ```
  — [`stepPreservesSelf`](../../../LirLean/Drive/CallPreservesSelf.lean#L84) is a **theorem**
  (no supplied edge), and the CALL/CREATE edges
  ([`callPreservesSelf_modGuards`](../../../LirLean/Drive/CallPreservesSelf.lean#L214),
  [`createPreservesSelf_modGuards`](../../../LirLean/Drive/CallPreservesSelf.lean#L300)) reduce
  to the single precompile seam `hprec`, exported as
  [`PrecompilesPreservePresence`](../../../LirLean/Spec/Seams.lean#L11) on the flagship surface.
  ([`SelfPresent`](../../../LirLean/Drive/SelfPresent.lean#L353) itself is recorder-adjacent;
  see [report 04](04-value-channel.md).)

**What breaks without it:** every storage-effecting simulation arm. `sim_sstore` cannot fire at an
arbitrary reachable cursor, so no program with a write — i.e., essentially every interesting
program — gets through the walk.

### (c) No recorder: the oracle streams needed a logging twin of `drive`

Exp003's `drive` returns only the final `FrameResult`. Exp005's IR semantics is deliberately
gas-agnostic and call-agnostic — it consumes **oracle streams** (gas reads, call results, create
results) — so conformance needs those streams *realised from the actual run*: a Type-valued
recording interpreter [`runWithLog`](../../../LirLean/Spec/Recorder.lean#L93) mirroring `drive`'s
recursion, with the adequacy bridge
[`runWithLog_drive`](../../../LirLean/RecorderLemmas.lean#L138) pinning
`runWithLog params f = some log → beginCall params = .inl fr₀ ∧ drive f [] (running fr₀) = .ok
log.observable`. The recorder is [report 02](02-spec-layer.md)'s territory; it is listed here
because it is a *machine-shaped* gap: nothing in a Hoare logic, however complete, produces an event
stream — that requires a second executable semantics plus a proved correspondence, and the recorded
channels themselves become definitionally-trusted surface (codebase map §1.3).

### (d) No clean-halt / gas-envelope extraction: envelopes must be derived, not supplied

The per-opcode `Runs` rules all *take* gas bounds as hypotheses. For a hand-verified program you
compute them; for an arbitrary lowered program under a gas-agnostic IR they cannot be supplied —
that was precisely the 2026-07-02 vacuity finding (the old universally-quantified
`GasRealises`/`SloadRealises` ties were unsatisfiable). The fix inverts the direction: a run known
to halt **cleanly** cannot have OOG-faulted en route, so each cursor's gas guard *held* and can be
extracted. The vocabulary lives in [`BytecodeLayer/Hoare/CleanHalt.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L41):

```lean
def CleanHalts (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt

def CleanHaltsNonException (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt ∧ HaltNonException halt
```

forward-closed along `Runs` by
[`cleanHalts_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L69) /
[`cleanHaltsNonException_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L80) (both riding
exp003's `Runs.linear_to_halt`). The extractor is the IR-free bulk of
[`Materialise/CleanHaltExtract.lean`](../../../LirLean/Materialise/CleanHaltExtract.lean#L70):
for each lowered opcode, an OOG lemma (e.g.
[`stepFrame_gas_oog`](../../../LirLean/Materialise/CleanHaltExtract.lean#L83)), its `.next`
inversion ([`stepFrame_gas_inv`](../../../LirLean/Materialise/CleanHaltExtract.lean#L105)), and a
**step dichotomy** ([`stepFrame_gas_dichotomy`](../../../LirLean/Materialise/CleanHaltExtract.lean#L448),
likewise for PUSH/SLOAD/ADD/LT/MLOAD/MSTORE and the §4–§5 JUMP/JUMPDEST/JUMPI terminator families
at [L897](../../../LirLean/Materialise/CleanHaltExtract.lean#L897)–[L1103](../../../LirLean/Materialise/CleanHaltExtract.lean#L1103)):
a continuing op either steps or halts with `.exception` — so a `CleanHaltsNonException` cursor
*must* step ([`next_of_cleanHalt_continuing`](../../../LirLean/Materialise/CleanHaltExtract.lean#L429),
using [`halted_runs_eq`](../../../LirLean/Materialise/CleanHaltExtract.lean#L409)), witnessing its
own gas guard. The lowering-shaped envelope family §3
([`gas_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L700),
[`sload_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L790)) belongs
to [report 04](04-value-channel.md). Exp003 had forward `stepFrame_*` characterizations only —
no OOG companions, no inversions, no dichotomies.

**What breaks without it:** the reshaped run-derived ties (`StmtTies'`/`TermTies'`) revert to
supplied universals — the exact unsatisfiable-hypothesis vacuity the target architecture was
rebuilt to kill.

### (e) The long tail: memory algebra, erase read-back, charge folds

Three more machine-fact families exp003 never needed:

- **[`MemAlgebra.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L15)** — the value channel spills
  temporaries to fixed 32-byte memory slots, so it needs byte-level facts about
  `ByteArray.copySlice`/`readWithPadding` under `mstore`/`mload`:
  read-back [`mload_after_mstore`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L459), disjointness
  [`mstore_mload_disjoint`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L550) /
  [`slot_windows_disjoint`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L872) /
  [`mstore_preserves_slot`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L890), and CALL-invisibility for
  zero-size windows [`resumeAfterCall_mload`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L85) (the
  lowered CALL uses empty in/out windows, so caller memory reads survive the resume). Includes
  the `ffi.ByteArray.zeroes`/`UInt256.toByteArray` reassembly lemmas that killed the earlier
  "opaque-FFI wall".
- **[`Frame/StorageErase.lean`](../../../LirLean/Frame/StorageErase.lean#L189)** — `SSTORE key 0`
  takes `Account.updateStorage`'s **erase** branch, and Batteries provides no `find?_erase`
  characterisation; exp005 derived
  [`findD_erase_self`](../../../LirLean/Frame/StorageErase.lean#L189) /
  [`findD_erase_of_ne`](../../../LirLean/Frame/StorageErase.lean#L199) from a `toList`
  characterisation of the `zoom`/`del` machinery
  ([`mem_erase`](../../../LirLean/Frame/StorageErase.lean#L71)). Without it, zero writes were a
  named scope exclusion; with it, `sim_sstore` covers them (the flagship docstring records the
  seam's removal).
- **[`BytecodeLayer/Hoare/Charges.lean`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L19)** —
  [`subCharges_snoc`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L19) /
  [`subCharges_append`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L26), the two fold laws that let
  multi-statement gas prefixes compose without quadratic `toNat_sub_ofNat` blow-ups.

**Summary verdict on the central question.** exp003's Hoare logic is exactly what it says: a
*composition* theory for runs you construct yourself. The lowering flagship needed a *analysis*
theory for runs handed to you by an execution — reverse reconstruction, per-step invariant
transport, event recording, and guard extraction. None of that is expressible as a corollary of
the forward theory; all of it is generic machine metatheory that conceptually belongs beside
`Runs` in exp003. That is the origin of the D10 debt.

---

## 5. The `ModellableStep` discharge — from raw universal to two honest seams

[`Decode/Modellable.lean`](../../../LirLean/Decode/Modellable.lean) is the file that keeps
`runs_of_drive_ok`'s side condition honest instead of hypothesis-shaped. The reduction target:

```lean
-- ../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L182
def ModellableStep (fr : Frame) : Prop :=
  (∀ cp pending childRes, stepFrame fr = .needsCreate cp pending →
      drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes →
      ∃ resumeFr, resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr)
  ∧ (∀ cp pending result, stepFrame fr = .needsCall cp pending → beginCall cp ≠ .inr result)
```

The per-frame residuals it reduces to
([`CreateResolves`](../../../LirLean/Decode/Modellable.lean#L421),
[`CallsCode`](../../../LirLean/Decode/Modellable.lean#L410)):

```lean
def CreateResolves (fr : Frame) : Prop :=
  ∀ cp pending childRes, stepFrame fr = .needsCreate cp pending →
    drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes →
    ∃ resumeFr, resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr

def CallsCode (fr : Frame) : Prop :=
  ∀ cp pending, stepFrame fr = .needsCall cp pending → ∀ p, cp.codeSource ≠ .Precompiled p
```

glued by [`modellableStep_of`](../../../LirLean/Decode/Modellable.lean#L430) and the producing
lemma [`lower_modellable`](../../../LirLean/Decode/Modellable.lean#L450). The interesting content
is *why these two are irreducible*:

- `CallsCode` is **genuinely runtime-dependent**: the CALL target is a stack value; a lowered IR
  program that materialises address `1..10` as its callee really would hit a precompile, which
  `Runs` has no node for. The reduction to the code source goes through
  [`beginCall_isCode_of_codeSource_ne_precompiled`](../../../LirLean/Decode/Modellable.lean#L367).
- `CreateResolves` is the honest R4 residual: `resumeAfterCreate`'s 63/64 retention guard can
  `throw .OutOfGas` on `UInt64` overflow, and that is a genuine gas fact, not a structural property
  of the lowering. Both are vacuous for call-free / create-free programs.

The file also contains the *structural* half — the ~330-line `NoCallCreate`/`NoCreate` combinator
algebra ([`NoCallCreate`](../../../LirLean/Decode/Modellable.lean#L74) through
[`stepFrame_needsCreate_isCreate`](../../../LirLean/Decode/Modellable.lean#L332)) proving a
`.needsCreate` can only arise from a CREATE/CREATE2 opcode at the current pc
([`currentOp`](../../../LirLean/Decode/Modellable.lean#L61)) — the surviving consumer of the decode
side is [`AtReachableBoundary`](../../../LirLean/Decode/Modellable.lean#L398), which couples this
file to `Decode/BoundaryReach` ([report 03](03-code-geometry.md)). Both residuals surface on the
flagship exactly once, inside
[`PrecompileAssumptions`](../../../LirLean/Spec/Seams.lean#L31):

```lean
-- ../../../LirLean/Spec/Seams.lean#L28
def ReachableFrom (params : Evm.CallParams) (fr' : Evm.Frame) : Prop :=
  ∃ fr₀, Evm.beginCall params = .inl fr₀ ∧ BytecodeLayer.Hoare.Runs fr₀ fr'

structure PrecompileAssumptions (prog : Program) (params : Evm.CallParams) : Prop where
  noErase : Lir.Spec.PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'
```

---

## 6. The trusted-surface question: which exp003 exports are in the flagship STATEMENT

This is the boundary that determines what a skeptical reader must trust *definitionally* versus
what is proof plumbing they may ignore.

**In the statement (trusted vocabulary).** Reading
[`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251) plus the
definitions its hypotheses/conclusion unfold to:

| exp003 export | How it enters the statement |
|---|---|
| `CallParams`, `Account`, `AccountMap.find?`, `GasConstants` | directly in the hypotheses (`hcode`/`hself`/`hgas`) |
| [`seedFuel`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L71) | `hrun : runWithLog params (seedFuel params.gas) = some log` |
| [`beginCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L18) | inside [`ReachableFrom`](../../../LirLean/Spec/Seams.lean#L28) |
| [`Runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L140) | inside `ReachableFrom` — quantified over by `hseams` |
| [`stepFrame`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Dispatch.lean#L130), [`drive`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36), [`beginCreate`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L64), [`resumeAfterCreate`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L189) | inside `CallsCode` / `CreateResolves` (via `hseams`) |
| [`endFrame`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L8) | inside [`observe`](../../../LirLean/Spec/Recorder.lean#L122) → [`Conforms`](../../../LirLean/Spec/Conformance.lean#L20) |

Adequacy is pinned in both directions — forward
[`messageCall_runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L195),
backward [`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357) — so `Runs` appearing in
the statement is *checked* vocabulary, not free-floating (this is D13 in the
[codebase map](../../codebase-map-2026-07-06.md)).

**Proof-internal only (not trusted surface):** `messageCall_runs` itself, `CallReturns`/
`CreateReturns` (constructors of the reconstruction, not statement text),
[`drive_fuel_mono`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Drive.lean#L185),
[`drive_descend_eq`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/DescentEq.lean#L143),
[`messageCall_never_outOfFuel`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144),
[`Runs.gasAvailable_le`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/GasMonotone.lean#L281),
all of §4's exp005 engine theory, and every per-opcode rule. A reader auditing the flagship's
*meaning* needs the table above plus the recorder; a reader auditing its *soundness* needs
everything.

Note `messageCall` itself appears in **neither** — the flagship is stated against
`runWithLog`/`drive` rather than the `messageCall` boundary; the connection to `messageCall` is
one `beginCall` case split away
([`messageCall_eq_drive`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Drive.lean#L75)),
but as stated the top boundary is the recorder. Worth keeping in mind when comparing against
exp003's headline shape.

---

## 7. Results taxonomy (in-scope declarations)

**Headline-grade engine results** (the flagship's `Conforms` half consumes all of these
transitively):
[`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357),
[`lower_modellable`](../../../LirLean/Decode/Modellable.lean#L450),
[`drive_accounts_find_mono`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L159),
[`stepFrame_next_accMono`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1119),
[`selfPresent_runs_of_call`](../../../LirLean/Drive/CallPreservesSelf.lean#L337),
[`cleanHaltsNonException_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L80); on the exp003 side
[`messageCall_never_outOfFuel`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144),
[`drive_fuel_mono`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Drive.lean#L185),
[`Runs.linear_to_halt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L323).

**Bricks** (load-bearing, single-purpose): the `NoCallCreate`/`NoCreate` algebra
([Modellable §1](../../../LirLean/Decode/Modellable.lean#L74)), the descent inversions
([Descent](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L124)), the presence closers
([AccountMap](../../../../003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L114)), the OOG/dichotomy families
([CleanHaltExtract §1–§2](../../../LirLean/Materialise/CleanHaltExtract.lean#L70)), the memory/erase
algebra ([MemAlgebra](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L459),
[StorageErase](../../../LirLean/Frame/StorageErase.lean#L189)), the charge folds
([Charges](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Charges.lean#L19)).

**Currently-unconsumed generality** (not dead — deliberate interface width):
[`DescentKind`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L696) packages CALL/CREATE uniformly ahead of
consumers; [`AtReachableBoundary`](../../../LirLean/Decode/Modellable.lean#L398) +
`notCreate_of_atReachableBoundary` support a structural no-CREATE discharge that the
`Runs.create`-modelling made optional. Per the deep-read-before-deleting rule these are
incremental lemmas toward open leaves, but they deserve a consumed-by note at next touch.

**Examples:** none in scope (exp003's worked examples are exp003-internal leaves; exp005's
byte-coupled worked examples are archived under `_attic/` per the
[lakefile](../../../lakefile.lean)).

---

## 8. Smells, drift, and redundancy

### 8.1 Stale exp003 docstring — verified against source

[`Hoare.lean` L26–29](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L26) still reads:

> "`Runs` mentions `Frame` and so is an internal brick (like `StepsTo`); it **never appears in an
> exported statement**. The boundary bridge `messageCall_runs_completed` turns a `Runs … halt` into
> a high-level `Outcome`…"

Both claims are false against current source: (i) `Runs` is exported on exp003's own
[`Spec.lean`](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L51) (which at least flags the
tension in its "Altitude caveat", [L23–28](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L23))
*and* sits inside exp005's flagship statement via
[`ReachableFrom`](../../../LirLean/Spec/Seams.lean#L28); (ii) **`messageCall_runs_completed` does
not exist anywhere** in the tree (the actual bridges are `messageCall_runs` /
`messageCall_calls_completedWith`). Doc-vs-source discrepancy; the fix is a two-line docstring
edit in exp003. Note the exp003 frame-level surface is *accepted* for exp005's purposes (the
observables-only export standard was an exp001/002 rule); the smell is the stale text, not the
export.

### 8.2 The bypassed audit surface

exp003's [`Spec.lean`](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L11) declares itself
"**the file to read** … the audit surface", but exp005 imports the `Hoare.*` internals directly
and never `BytecodeLayer.Spec` (verified by grep over all `LirLean` imports; §3). Spec.lean's
re-export set (thin `theorem := Hoare.theorem` wrappers, e.g. its
[`messageCall_runs`](../../../../003_bytecode_layer/BytecodeLayer/Spec.lean#L70)) is also a proper
subset of what exp005 actually uses — no `CreateReturns`, no `Runs.linear_to_halt`, no `drive_*`
lemmas. So the file is a stale wrapper: not wrong, just no longer the audit surface of anything.
Either widen it to the real consumed surface and route exp005's imports through it, or demote its
docstring. Similarly, `SharedObservable`/`EVMSpec`/`Equivalence`/`Refinement` are a dormant
cross-engine conformance track exp005 never touches — fine to keep, but a reader of exp003 should
know exp005's cone excludes them.

### 8.3 `maxHeartbeats` in MemAlgebra — isolated to two byte-window lemmas, but under the headline

The only cranked options in scope:
[`copySlice_extract_disjoint`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L493) and
[`copySlice_at_extract_disjoint`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L829), both
`set_option maxHeartbeats 800000` (4× default). These are index-chasing over
`ByteArray.extract`/`Array.append` windows — proof-shape blow-up, not model awkwardness. **They do
sit under the headline** (disjoint-slot preservation → `MatRuns` value channel → sim → flagship),
so they are worth a follow-up simplification (a shared `getElem`-pointwise extraction lemma would
likely kill both cranks), but they are not a soundness risk and there is no `decide`-on-big-terms
pattern anywhere in scope.

### 8.4 D10 status: reusable engine theory folded into exp003

The D10 package boundary debt described by the dated codebase map is closed. The eight IR-free
modules live in `BytecodeLayer/Hoare/`; `Modellable.lean`, which depends on lowering geometry,
lives in `LirLean/Decode/`. Namespace cleanup remains cosmetic follow-up work and does not require
reintroducing an exp005 engine directory.

### 8.5 Namespace fragmentation (cosmetic but real)

The engine theory spans four namespaces — `Lir` (AccountMap, StepWalk, DriveMono, CleanHalt,
CallPreservesSelf), `BytecodeLayer.Interpreter` (DriveRuns, Modellable), `Evm`
(parts of [StepWalk](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L116) and
[Descent](../../../../003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L26)), and `LirLean.MemAlgebra` / `Lir`
(MemAlgebra, Charges) — reflecting extraction history, not design. The map's D10 already
recommends unifying; worth doing *at* relocation time, not before.

### 8.6 No redundancy/supersession found in scope

The plausible-looking overlaps are genuine layerings, not duplicates:
`drive_descend_lt` does not supersede exp003's `drive_descend_eq` (strict bound vs unordered
existential — both consumed); `drive_append_framing_lt` intentionally shadows
`drive_append_framing` for the same reason; `SelfAt`/`SelfPresent` vs `AccPresent` is a
projection, with the general `a`-indexed form required by the cross-frame child-run tracking
(the caller's address is not the running frame's self inside the child). One consolidation
candidate: [`child_ne_oof_of_framed`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L316) is strictly
subsumed by its generic-`Pending` twin
[`child_ne_oof_of_framed'`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L327) — recommend deleting the
former at next touch.

---

## 9. Recommendations

1. **Fix the exp003 `Hoare.lean` docstring** (§8.1) — two lines; it currently promises an export
   discipline the codebase abandoned and names a theorem that does not exist.
2. **Re-charter or retire exp003 `Spec.lean`** (§8.2) so the "audit surface" claim matches the
   consumed surface; if kept, add `CreateReturns`, `Runs.linear_to_halt`, and the `drive_*`
   erasure lemmas, and route exp005 imports through it.
3. **Enforce D10's shrink-only rule mechanically**: new engine lemmas land in exp003; treat any new
   `import Evm`-only file under `LirLean/` as a review flag.
4. **De-crank the two MemAlgebra lemmas** (§8.3) via a shared pointwise-extract brick.
5. **Delete `child_ne_oof_of_framed`** in favour of its primed generalisation (§8.6).
6. At relocation time, move the IR-free §0–§2/§4–§5 of `CleanHaltExtract` into `Engine/` (or
   exp003) so `Materialise/` is purely lowering-shaped — the file's own header already describes
   this split.
