# 08 — Related work: linear frames vs. the field (Verifereum, vyper-hol, and the nested alternative)

Part of the [exp005 tour](00-overview.md)

**Date:** 2026-07-09 · **Question from the lead:** our vendored EVM (exp003 `EVMLean`) runs an
iterative `drive` loop over a frame stack — *linear frames* — instead of a recursive interpreter
where a CALL is a nested sub-execution. *"It felt easier at first, but now considering how much
shit we are dealing with, I'm not as sure."* Was that choice ideal?

**Verdict up front.** Yes — keep it. The two most load-bearing external EVM formalizations we can
compare against, **Verifereum** (HOL4) and **KEVM** (K framework), both chose an explicit
context/frame stack, i.e. exactly our shape; Verifereum even re-derives the "nested call" view by
depth-gating its linear machine, the same move as our `runs_of_drive_ok` and recorder gating. The
genuinely nested alternative was measured in-house: exp004's never-out-of-fuel theorem over
EVMYulLean's mutual recursion took a [4,746-line proof](../../../../004_nested_evmyul/NestedEvmYul/NeverOutOfFuel.lean)
where the flat machine's took a [764-line chain](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144),
and the recorded bake-off finding is *"nested never-OOF [is] dramatically harder than flat"*
([track-b-review.md](../../../../004_nested_evmyul/docs/track-b-review.md#L67)). Most of the pain
we are feeling today (per-statement simulation, pc/jumpdest geometry, coupling invariants,
CallReturns oracle seams) is **lowering-induced, not frame-model-induced** — no prior art has paid
it because no prior art has *proved* an IR→bytecode simulation at all: vyper-hol (the project the
lead calls "ViperHall") has the scaffolding for one, and its two top-level simulation theorems are
both `cheat`ed, with calls excluded from the assembly layer outright. Details in [§6](#6-the-verdict).

**"ViperHall" identified as [verifereum/vyper-hol](https://github.com/verifereum/vyper-hol)** —
the HOL4 Vyper→Venom→EVM verified-compiler project (sister project of Verifereum, same org). Why:
it is the obvious sound-alike ("vyper-hol" ≈ "Viper-Hall"), it is already cited throughout our own
docs as one of the three prior-art forks ([remediation-plan-2026-07-02.md](../../remediation-plan-2026-07-02.md),
[gas-introspection-prior-art.md](../../gas-introspection-prior-art.md)), and we hold a local clone
(`forks/vyper-hol`, pinned `fbb5a40`, 2026-06-01). Alternatives considered and rejected in one
line: ETH Zurich's [Viper](https://viper.ethz.ch) (Rust/permission-logic verification
infrastructure, not EVM), Nethermind's [Clear](https://github.com/NethermindEth/Clear) (Yul in
Lean, no "hall/hol" sound-alike and not a Vyper project).

All fork citations below are pinned-commit GitHub links (verifereum @ `114e4d3` 2026-05-31,
vyper-hol @ `fbb5a40` 2026-06-01 — our local clones), so line anchors are exact; both projects are
active, so master may have moved.

Sibling reports: [01-trusted-base.md](01-trusted-base.md) (the exp003 machine + Hoare logic),
[03-code-geometry.md](03-code-geometry.md) (pc/jumpdest algebra),
[06-realisability.md](06-realisability.md) (the `lower_conforms` flagships),
[07-assembler.md](07-assembler.md) (the planned Asm layer).

---

## 1. Our machine in one screen

The linear-frames design is two definitions. The machine state is either a running
[`Frame`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Frame.lean#L27) or a delivered
`FrameResult`; suspended ancestors live in a `List Pending`; and each `stepFrame` emits a
four-case [`Signal`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Frame.lean#L87):

```lean
inductive Signal where
  | next (exec : ExecutionState)
  | halted (halt : FrameHalt)
  | needsCall (params : CallParams) (pending : PendingCall)
  | needsCreate (params : CreateParams) (pending : PendingCreate)
```

The only recursion in the whole semantics is the driver
([Interpreter.lean](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36)):

```lean
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

A CALL pushes a `Pending` and descends
([`beginCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L18)); a finished
child's result is *delivered* to the innermost suspended parent
([`resumeAfterCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L122)). The
entry point [`messageCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L73)
seeds fuel from the gas limit
([`seedFuel`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L71)); fuel is
an implementation detail, not a semantic bound — `.OutOfFuel` is unreachable for gas-respecting
executions (proved:
[`messageCall_never_outOfFuel`](../../../../003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L144)).
Crucially, **fuel appears once, in the driver** — no per-opcode definition mentions it. This
machine passes the exp003 conformance suite (22,308 Ethereum BlockchainTests fixtures; see
[01-trusted-base.md](01-trusted-base.md)).

## 2. What the design costs downstream (our side of the ledger)

Three concrete artifacts exist *only because* the machine is linear:

**(a) Nesting is re-derived, not native.** The Hoare layer's
[`Runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L140) inductive re-introduces the
call tree as a *derived* notion — a returning external CALL is a black-box node
([`CallReturns`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L91), and its CREATE twin
[`CreateReturns`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L118)):

```lean
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending

inductive Runs : Frame → Frame → Prop where
  | refl (fr : Frame) : Runs fr fr
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') : Runs fr fr'
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
  | create {createFr resumeFr fr' : Frame} (hc : CreateReturns createFr resumeFr)
      (rest : Runs resumeFr fr') : Runs createFr fr'
```

A nested interpreter would give the `call` node by structural induction; here it costs the
`CallReturns`/`CreateReturns` bundles, determinism lemmas, and the `Runs`→`drive` reconciliation
([CallSequence.lean](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean), 286
lines). See [01-trusted-base.md](01-trusted-base.md).

**(b) The loop must be inverted back into `Runs`.** exp005's
[`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357) (482-line module) reconstructs a
halting `Runs` from a clean-terminating top-level `drive`, by strong induction on fuel with a
bespoke bounded-descent lemma
([`drive_append_framing_lt`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L51)) to make the recursion
well-founded across call boundaries, and a per-frame
[`ModellableStep`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L182) residual for the two configurations
`Runs` cannot resume (precompile CALL, 63/64-OOG create resume):

```lean
theorem runs_of_drive_ok :
    ∀ (f : ℕ) (fr : Frame) (res : FrameResult),
      drive f [] (running fr) = .ok res →
      (∀ fr', Runs fr fr' → ModellableStep fr') →
      ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
        ∧ res = endFrame last halt
```

**(c) The recorder is a hand-maintained twin of the loop.** The conformance-oracle recorder
[`driveLog`](../../../LirLean/Spec/Recorder.lean#L51) duplicates `drive`'s entire match structure
to accumulate gas/sload/call/create streams, and must *depth-gate* recording because the linear
stack flattens all depths into one loop — top-level events are recognized by
`stack.isEmpty` / `rest.isEmpty` tests
([Recorder.lean L67](../../../LirLean/Spec/Recorder.lean#L67),
[L77](../../../LirLean/Spec/Recorder.lean#L77)):

```lean
                | .ok parent =>
                  driveLog fuel rest (.inl parent) gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
```

On top of these, the engine walks that discharge frame-level invariants range over *every* opcode
of the real dispatch (e.g. [StepWalk.lean](../../../../003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L5), 1,336 lines;
[DriveMono.lean](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean), 294 lines) — though, as §6 argues, those
walks are per-opcode dispatch inductions any small-step machine needs, not a linear-frames tax.
Rough one-time bill for the frame model itself: `Runs`+bundles
([Hoare.lean](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean), 839 lines incl. linearity
theory) + inversion (482) + recorder twin (132) + boundary framing lemmas ≈ **1.5–2 kLOC, closed
and reusable**.

**(d) The rejected alternative, measured.** exp004 built the same never-OOF result over the
*genuinely nested* EVMYulLean semantics — the mutual `call`/`Θ`/`X`/`Ξ` block
([Semantics.lean](../../../../004_nested_evmyul/EVMYulLean/EvmYul/EVM/Semantics.lean#L139)) where
every case threads `fuel` explicitly ([PLAN.md](../../../../004_nested_evmyul/PLAN.md)). Outcome:
a six-layer mutual induction, a ~250-line depth-preservation keystone, and a
[4,746-line proof file](../../../../004_nested_evmyul/NestedEvmYul/NeverOutOfFuel.lean) versus the
flat machine's 764-line `Measure`/`DescentEq`/`Drive`/`NeverOutOfFuel` chain — with the bake-off
conclusion recorded in
[track-b-review.md](../../../../004_nested_evmyul/docs/track-b-review.md#L63): the nested
semantics is harder *precisely because of nesting* (the fuel/measure must dominate every
call-descent shape at once, mutually with gas). exp004 stopped after B2; its B3 goal ("call rule +
≥2 calls compose naturally") was never reached, while exp003's `Runs.call` node made multi-call
composition a one-line `Runs.trans`.

---

## 3. Deep dive 1 — Verifereum

**What it is.** [Verifereum](https://verifereum.org) ([repo](https://github.com/verifereum/verifereum),
GPL-3.0) is a **HOL4** formalization of the EVM execution layer, led by Ramana Kumar (of CakeML
provenance), aimed at functional-correctness proofs of deployed contracts. Status per
[verifereum.org](https://verifereum.org): production-quality EVM semantics, approximately complete
[EEST conformance coverage](https://verifereum.org/table.html), frame-style preservation theorems
and gas monotonicity proved, program logic under active development, WETH verification in progress.

**Call model: an explicit context stack — linear frames, like ours.** Their
`execution_state` ([vfmContextScript.sml#L123](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmContextScript.sml#L123)):

```sml
Datatype:
  execution_state =
  <| contexts : (context # rollback_state) list
   ; txParams : transaction_parameters
   ; rollback : rollback_state
   ; msdomain : domain_mode
   |>
End
```

A CALL [`push_context`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L270)es
via [`proceed_call`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L1475);
a return runs
[`pop_and_incorporate_context`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L1676)
(their `resumeAfterCall`: pop the callee, refund its gas-left, merge logs/refunds on success or
restore the rollback snapshot on failure). The driver is a single flat iteration of a monadic
small step — **no fuel at all**; HOL4's partiality combinator `OWHILE` replaces it
([vfmExecutionScript.sml#L1762](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L1762)):

```sml
Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End

Definition run_call_def:
  run_call es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
           (step o SND) (INL (), es)
End
```

`run_call` / `run_within_frame` are the smoking gun for our central question: Verifereum
**re-derives the nested sub-execution view by depth-gating the linear machine** — "run until the
context stack is shorter than it was" — precisely the move our `runs_of_drive_ok` and the
recorder's `stack.isEmpty` gating make. They then build a whole frame theory over it
([vfmRunCallScript.sml](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/prop/vfmRunCallScript.sml#L3208):
`run_call_preserves_storage_outside_accessed_slots`, `run_call_preserves_txParams`, …; plus
`vfmSameFrameScript`, `vfmContextLengthScript`, `vfmRunWithinFrameScript`). The most mature
external project in this space independently converged on our architecture *and* paid our
inversion/gating tax.

**Headline results.** (i) Executable conformance: the semantics runs (via HOL4's `cv_compute`)
against the Ethereum Execution Spec Tests, near-complete coverage — the same
"executable-spec-first" posture as exp003's 22,308-fixture suite. (ii)
[`decreases_gas`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/prop/vfmDecreasesGasScript.sml#L8)
— a compositional monad predicate ("this computation never decreases `gasUsed` past the limit, on
the *head context*") proved per-combinator across every opcode (155 theorems in the file); our
remediation plan explicitly copied its ties-as-outputs discipline
([remediation-plan-2026-07-02.md](../../remediation-plan-2026-07-02.md)). (iii) Contract
verification in progress: WETH, via a **Myreen-style machine-code Hoare logic** — `evm2set` state
decomposition, separation-`STAR`, `CODE_POOL`, `SPEC` triples over
[`EVM_MODEL`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/prog/vfmProgScript.sml#L279)
— with
[`SPEC_deposit`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/examples/wrappedEtherScript.sml#L1452)
proved against the *actual deployed WETH bytecode* (pc- and gas-exact, one auxiliary
[`cheat`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/examples/wrappedEtherScript.sml#L946)
remaining in a memory lemma).

**Gas/fuel.** Real gas only: a `gasUsed` counter per context,
[`consume_gas`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L446)
asserting `gasUsed ≤ gasLimit` else `OutOfGas`. No fuel anywhere — `OWHILE` gives partial
iteration for free in HOL, an option Lean's totality checker does not offer us; our
`seedFuel`+never-OOF pair is the Lean-shaped equivalent of their (implicit) termination-from-gas
argument.

**Bytecode-level pc/jumpdest reasoning: yes.** Contexts carry `pc`, code plus a `parsed : num |-> opname`
map; jumps are validated in
[`inc_pc_or_jump`](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/spec/vfmExecutionScript.sml#L1658)
(`FLOOKUP parsed pc = SOME JumpDest`); the program logic asserts pc and code-pool membership per
instruction. Verifereum verifies **existing bytecode directly against the semantics**
(decompilation-style) — it has no compiler and therefore *no lowering-conformance problem*: no
simulation relation, no coupling invariant, no assembler algebra. Nothing in their pc reasoning is
made harder or easier by the frame model — it is per-opcode, exactly as ours is.

**Call composition in proofs: an open TODO.** The one `cheat` in their program logic sits at the
end of
[vfmProgScript.sml](https://github.com/verifereum/verifereum/blob/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2/prog/vfmProgScript.sml#L3809),
directly under a comment sketching the plan: *"Example progression: 1. subroutine that adds two
given numbers 2. code that calls code of 1. (in a local way) 3. verify an external call to 2.
4. next level: external call as a transaction."* I.e. the linear-frames project furthest along has
**not yet built its cross-call composition rule** — our `Runs.call`/`CallReturns` +
[`runs_of_drive_ok`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L357) is *ahead* of the field on
exactly the pain point that prompted this report.

## 4. Deep dive 2 — "ViperHall" = vyper-hol

**What it is.** [vyper-hol](https://github.com/verifereum/vyper-hol) (HOL4, same org as
Verifereum, EF-grant-funded): formal semantics of the **Vyper** language plus a verified compiler
pipeline **Vyper AST → Venom IR → stack-scheduled Asm → EVM bytecode**, with the EVM end being
Verifereum. It is the only prior-art project with our exact problem shape (IR→bytecode lowering
conformance), which is why our docs mined it for design patterns.

**Call model: nesting avoided at every layer.** The Vyper definitional interpreter is total by a
*syntactic* measure (internal calls cannot recurse, loops have syntactic bounds); external calls
(`extcall`/`staticcall`) are **not interpreted recursively — they defer to Verifereum's EVM**, per
their README: *"External calls … are implemented by deferring to the low-level EVM execution
defined in Verifereum. This makes termination straightforward since the interpreter is not
recursive for external calls."* So the high-level semantics black-boxes calls (our
`CallOracle`/`CallReturns` seam, independently reinvented — cf.
[ir-design.md](../../ir-design.md), which modeled our call treatment on theirs), and the low-level
semantics is Verifereum's linear context stack. **No layer of the vyper-hol stack executes a call
as a nested sub-interpretation.**

**The lowering-conformance headline — and its holes.** Their flagship
[`codegen_fn_correct`](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/codegenCorrectnessScript.sml#L359)
is shaped almost exactly like our gas-free co-flagship (cf.
[06-realisability.md](06-realisability.md)) — Venom run ↦ EVM run, state relation at entry/exit,
one top-level gas existential:

```sml
Theorem codegen_fn_correct:
  ∀fuel ctx fn fn_eom data_seg bytecode spill_hwm vs.
    codegen_ready_fn fn ∧
    codegen … = SOME bytecode ∧ … ⇒
    ∃gas_needed.
      ∀es. initial_state_rel fn vs es ∧ … gasLimit ≥ gas_needed … ⇒
        (case run_blocks fuel ctx fn vs of
           Halt vs' => ∃es'. run es = SOME (INR NONE, es') ∧ final_state_rel vs' es'
         | …)
```

But as of the pinned commit its proof ends in
[`cheat`](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/codegenCorrectnessScript.sml#L427)
(gas witness literally `qexists_tac `0`` with the comment *"cheat for now. Real proof: sum of gas
costs for each EVM step in the trace"*), as does the whole-context
[`codegen_correct`](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/codegenCorrectnessScript.sml#L455).
One layer down, the Asm→bytecode forward simulation
[`asm_bytecode_sim`](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/asmToBytecodePropsScript.sml#L62)
is also `cheat`ed — and annotated **"FALSE AS STATED"**, with counterexamples on file: it is
missing the preconditions `no_asm_calls prog` (*"asm uses single-context model; EVM pushes new
contexts"*) and `LENGTH es.contexts = 1` (*"EVM with 2+ contexts: STOP pops context instead of
halting"*). Read that twice: **their assembly layer excludes CALL/CREATE entirely**, and even so
the call/context boundary is what falsified their top-level simulation statement. The boundary
pain we are paying (recorder gating, `ModellableStep`, boundary-cursor walks) is the same wall,
hit by a project with a *different* frame architecture on the low end and *no* frames at all on
the high end. Cheat census at the pin, for calibration: 19 in the Venom→Asm block simulation
([genBlockSimScript.sml](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/proofs/genBlockSimScript.sml)),
~58 more across the Vyper→Venom `lowering/` correctness scripts.

**What they have genuinely proved** (and we should respect): the geometry substrate. Label/offset
resolution, encode/parse round-trips, and jumpdest placement are real theorems, e.g.
[`assemble_parse_correct`](https://github.com/verifereum/vyper-hol/blob/fbb5a4043229da8d769c8f18a28389bc1fd4fc38/venom/codegen/asmToBytecodePropsScript.sml#L40)
(`parse_code` of `assemble prog` yields the right opcode at each `asm_pc_to_offset`), a large
stack-scheduling plan theory (`stackPlanGen`, `spillSim`, `reorderSim`, …), and many proved
per-pass Venom simulations. This partially **corrects our own docs' blanket claim**
([remediation-plan-2026-07-02.md](../../remediation-plan-2026-07-02.md) — *"all forks target
structured Yul/IR interpreters — no pc/stack/jumpdest reasoning"*;
[fleet-2026-07-02/bytecode-interface.md §3](../../fleet-2026-07-02/bytecode-interface.md#L196)):
that was verified true of **Verity** (checked there against its `Compiler/`), but vyper-hol's
`venom/codegen` tree *does* contain real pc/jumpdest/stack reasoning. The defensible version of
our claim, against today's evidence: **no prior project has a completed, call-inclusive
IR→bytecode simulation** — vyper-hol's is single-context, call-free, and cheated at both top
levels; the structural geometry lemmas below it are the analogue of our
[03-code-geometry.md](03-code-geometry.md) layer, which we have closed and they largely have too.
It also **validates the exp005 assembler plan** ([07-assembler.md](07-assembler.md)): they
independently inserted a symbolic-label Asm IR between the structured IR and bytes, exactly the
shape our fleet doc argues for.

**Gas & introspection.** High level gas-free; all accounting in Verifereum; correctness modulo one
top-level `∃ gas_needed` envelope — the consensus design our
[gas-introspection-prior-art.md](../../gas-introspection-prior-art.md) study documented
(source-grounded, 2026-06-23), including that **gas introspection is excluded** there (`MsgGas`
rejected by the type checker; their
[issue #98](https://github.com/verifereum/vyper-hol/issues/98)) — our `Expr.gas` event/recorder
treatment remains ahead of both projects.

## 5. Adjacent prior art, briefly

| Project | System | Call model | Bytecode-level? | Lowering proof? |
|---|---|---|---|---|
| [Verifereum](https://github.com/verifereum/verifereum) | HOL4 | **explicit context list** (linear frames), `OWHILE`, no fuel | yes (pc/jumpdest/`parsed`, machine-code Hoare logic) | no compiler — verifies deployed bytecode directly |
| [vyper-hol](https://github.com/verifereum/vyper-hol) | HOL4 | none at Vyper level (defers to Verifereum); **single-context, call-free** Asm | yes, scaffolding + proved geometry; top sims `cheat`ed | yes (in progress; the only comparable) |
| [KEVM](https://github.com/runtimeverification/evm-semantics) ([paper](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf.pdf)) | K | **explicit `<callStack>` cell** of saved VM states (`#pushCallStack`/`#popCallStack`) — linear frames | yes (complete opcode semantics, conformance-tested) | no (verifies programs/reachability against the semantics) |
| [DafnyEVM](https://github.com/Consensys/evm-dafny) ([FM'23 paper](https://arxiv.org/abs/2303.00152)) | Dafny | CALL suspends into *"a mechanism akin to continuations"* — the host drives child then resumes; not nested interpreter recursion (Dafny totality) | yes (per-opcode, gas split from semantics) | no |
| [EVMYulLean](https://github.com/NethermindEth/EVMYulLean) (exp004 base) | Lean 4 | **genuinely nested** mutual recursion `Θ/Ξ/X`, fuel threaded through every case | yes | no |
| Verity ([lfglabs-dev](https://github.com/lfglabs-dev/verity)) | Lean 4 | EDSL→Yul, calls via `callOracle` env field | **no** (stops at Yul; gas unmodeled; run-match supplied as hypothesis) | partial (success-path, hypothesis-guarded) |
| [Isabelle/EVM](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.FMBC.2026.3) (FMBC 2026) | Isabelle | new EVM formalization (survey mention) | yes | no |

The pattern across the field: **formal EVM semantics that execute and pass conformance tests use
explicit frame stacks or continuation-style suspension** (Verifereum, KEVM, DafnyEVM, us); the one
nested-recursion formalization (EVMYulLean) is the one that entangles fuel with every definition —
and it is conformance-tested but has essentially no proof superstructure built on it by its
authors, while exp004's attempt to build one measured the cost directly.

## 6. THE VERDICT

**What linear frames bought us.**
- **An executable, conformance-testable machine** — 22,308 BlockchainTests fixtures green
  ([01-trusted-base.md](01-trusted-base.md)). This is the trust anchor of the whole study, and it
  is exactly the property Verifereum treats as its own foundation (EEST). exp004's nested base is
  also executable, but its toolchain (v4.22.0) could not even co-import with our stack — the
  bake-off itself had to run refinement-through-shared-spec.
- **Fuel quarantined in one definition.** `drive` mentions fuel once; `stepFrame` and every opcode
  are fuel-free, so per-opcode reasoning is first-order and `grind`-friendly. In EVMYulLean every
  arm of the six-layer mutual block threads `fuel`, and every lemma about it inherits that
  parameter. The flat/nested never-OOF ratio (764 vs 4,746 lines) is the measured price.
- **A machine other tools can drive**: the recorder, the conformance runner, and the depth-gated
  oracle extraction all reuse the loop; a nested interpreter exposes no comparable seam between
  "one step" and "one run".

**What it cost us.** The abstraction bill of §2: nesting re-derived (`Runs`/`CallReturns`,
~839-line Hoare.lean), the loop inverted (`runs_of_drive_ok`, 482 lines with the bounded-descent
and `ModellableStep` machinery), the recorder twin with depth gating (132 lines), and the
boundary-framing lemma family. Call it ~2 kLOC — **paid once, closed, sorry-free, and reusable**
(exp005 consumed it without reopening exp003). The `CallReturns` seams surfacing in the flagship
hypotheses ([06-realisability.md](06-realisability.md)) *look* like frame-model costs but are not
— see attribution below.

**What nested calls would have bought/cost instead.** Bought: `Runs.call` for free (a call is a
subterm; the induction principle of the interpreter *is* the call rule), no loop inversion, no
recorder depth gating (recurse-and-return naturally scopes the log). Cost: fuel in every
definition and every lemma; a fuel/gas reconciliation that exp004 needed a 4.7-kLOC headline plus
a depth-preservation keystone to close *before any program logic existed*; harder conformance
execution ergonomics; and — the exp004 record shows — the call-composition milestone (B3) never
reached. The nested "free call rule" is only free after you have paid the fuel-threading tax
everywhere else; exp004 is our evidence that the tax is larger than the rebate.

**Attribution: which pains are actually frame-model-induced?** Be precise:
- *Frame-model-induced* (would vanish under nesting): `runs_of_drive_ok`, the recorder's
  `stack.isEmpty` gating, `drive_append_framing_lt`-style boundary fuel algebra, the
  `Runs`-linearity theory. Bounded, done, ~2 kLOC.
- *Lowering-induced* (would exist under **any** machine): per-statement simulation, the coupling
  invariant, pc/jumpdest geometry ([03-code-geometry.md](03-code-geometry.md)), decode anchors,
  the value channel, spill/alloc reasoning, and the gas envelopes. Proof: vyper-hol targets a
  different low-level architecture and hit the identical wall — its Asm→bytecode sim is falsified
  by the call/context boundary and its codegen headline is cheated on the gas witness; Verity
  simply assumed the run-match. pc arithmetic is the semantic content of "bytes implement this
  CFG"; no frame model changes it.
- *Call-oracle seams* (`CallOracle`/`CallReturns`/`SelfPresent` in the flagship): induced by
  **refusing to interpret the callee**, not by frames. vyper-hol black-boxes external calls at the
  source level for the same reason; a nested machine proving the same theorem would carry the same
  child-run black box, just spelled as a hypothesis about the recursive call's result.

The honest answer to *"was it ideal?"*: the abstraction choice was **right, and the field's
convergent evolution says so** — but it was not free, and the specific ~2 kLOC of inversion/twin
machinery is real and was underestimated. What is *not* right is attributing the current grind to
it: the grind is the lowering-conformance problem itself, which nobody else has finished — the
closest attempt (vyper-hol) is cheated precisely at the two places we are proving.

**Recommendation.** No pivot. Concretely:
1. **Keep the linear machine and the paid abstraction.** The `Runs`/`Exec` surface plus
   `runs_of_drive_ok` means downstream layers never see `drive` again; the cost is sunk and the
   asset is ahead of Verifereum's own program logic (their cross-call composition is still a
   `cheat`-marked TODO).
2. **Finish the abstraction payment where it is still partial**: the planned Asm layer
   ([07-assembler.md](07-assembler.md)) is the same move vyper-hol made (symbolic labels between
   IR and bytes) — their proved `assemble_parse_correct` and our decode-anchor algebra are
   convergent designs; ours should become the reusable one.
3. **Fix the docs' overbroad prior-art claim** (blanket "no fork does pc/jumpdest reasoning" →
   "no fork has a completed, call-inclusive IR→bytecode simulation"; vyper-hol has proved geometry
   scaffolding, cheated simulations, and a call-free Asm model).
4. If frame-boundary friction recurs, the cheap upgrade is more *derived* structure on top of the
   linear machine (as Verifereum does with `run_call`/`run_within_frame` and we do with `Runs`) —
   never a change of machine.

---

*External sources:* [verifereum.org](https://verifereum.org) ·
[verifereum/verifereum @ 114e4d3](https://github.com/verifereum/verifereum/tree/114e4d3d6b605c84d9b27bf772fb2a76dc93bff2) ·
[verifereum/vyper-hol @ fbb5a40](https://github.com/verifereum/vyper-hol/tree/fbb5a4043229da8d769c8f18a28389bc1fd4fc38) ·
[EEST progress table](https://verifereum.org/table.html) ·
[KEVM semantics (evm.md)](https://github.com/runtimeverification/evm-semantics/blob/master/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md) ·
[KEVM CSF'18 paper](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf.pdf) ·
[DafnyEVM FM'23](https://arxiv.org/abs/2303.00152) ·
[NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean) ·
[Isabelle/EVM (FMBC 2026)](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.FMBC.2026.3) ·
[Nethermind Clear](https://github.com/NethermindEth/Clear) · [ETH Zurich Viper](https://viper.ethz.ch)
