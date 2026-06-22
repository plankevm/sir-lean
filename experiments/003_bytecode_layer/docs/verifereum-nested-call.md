# CALL boundary: nested child-machine (Verifereum/HOL4) vs. flat fuel-bounded driver (this repo / Lean)

Audience: project lead. All excerpts verified from local source under
`/Users/eduardo/workspace/evm-semantics/forks/`. Verifereum **is** checked out
locally (`forks/verifereum`), so all HOL4 below is read from source, not the web.

---

## (A) Our model: one flat `drive` over a shared `List Pending`

The entire EVM recursion is a single tail-recursive function. CALL does **not**
spawn a sub-evaluation; it pushes the parent onto a flat stack and continues the
*same* loop on the child, sharing one fuel counter.

`forks/leanevm/Evm/Semantics/Interpreter.lean:36-75`:

```lean
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>                        -- delivering a finished child
          match stack with
            | [] => .ok result
            | pending :: rest =>
              match pending.resume result with
                | .ok parent => drive fuel rest (.inl parent)
                ...
        | .inl current =>
          match stepFrame current with
            | .next exec => drive fuel stack (.inl { current with exec := exec })
            | .halted halt => drive fuel stack (.inr (endFrame current halt))
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => drive fuel (.call pending :: stack) (.inl child)   -- DESCEND
                | .inr result => drive fuel (.call pending :: stack) (.inr (.call result))
            ...
```

Key facts verified from this excerpt and its neighbours:

- **One recursion, one fuel.** `fuel : ℕ` decrements once per *iteration* — one
  opcode, one descent, or one result delivery. The CALL arm (`.needsCall`)
  recurses with `fuel` on the **child** frame with the parent `.call pending`
  consed onto the *same* `stack`. Parent and child interleave under one counter.
- **The child gets no fresh `messageCall`/`seedFuel`.** `messageCall`
  (`Interpreter.lean:84-87`) and `seedFuel` (`:82`) are invoked **only at the top
  level**:
  ```lean
  def messageCall (params : CallParams) : Except ExecutionException CallResult :=
    match beginCall params with
      | .inr result => .ok result
      | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)
  ```
  A *nested* CALL reaches `drive` via the `.needsCall` arm, which calls
  `beginCall` directly and reuses the running `fuel`. There is no point in a
  nested execution where a sub-term `messageCall cp` is evaluated. This is the
  load-bearing structural fact.
- **`Pending.resume` / `endFrame` deliver results in-place.** When the child halts
  (`.inr result`), the head `pending` is popped and `pending.resume result`
  reconstructs the parent frame (`Interpreter.lean:13-16`); `resumeAfterCall`
  (`Call.lean:122-149`) writes return data into the parent's memory, restores gas,
  pushes the success flag, and advances pc — the parent is *patched*, it does not
  *receive a returned value*.

The descent signal and charging live in `System.lean`. `systemOp` dispatches
`.CALL/.CALLCODE/.DELEGATECALL/.STATICCALL` to one `callArm`
(`System.lean:124-147`), and `callArm` (`:12-71`) does the 63/64 cap, value
transfer, depth check, then emits `.needsCall childParams pending`:

```lean
let gasCap := callGasCap codeAddress recipient value gas accounts exec.gasAvailable exec.substate
let childGas := if value = 0 then gasCap else gasCap + Gcallstipend
...
if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 then
  .ok <| .needsCall { ... gas := .ofNat childGas; depth := depth + 1; ... } pending
else
  .ok <| .next (resumeAfterCall failed pending).exec        -- depth/funds failure, no descent
```

Rollback is realized **not** by discarding a sub-state but by a `Checkpoint`
captured in the frame `kind := .call ⟨createdAccounts, accounts, substate⟩`
(`Call.lean:80`) and consulted in `endCall` (`Call.lean:93-115`): on
`.revert`/`.exception` `endCall` returns the checkpoint's accounts/substate; on
`.success` it keeps the child's. So our model *does* checkpoint, but the checkpoint
is a field threaded through the flat loop, not the natural "the child run's state
is a discardable subterm."

**Established consequence in this project.** Because there is no definitional "this
sub-tree is exactly a child `messageCall`" decomposition, the general external-call
rung had to take a *per-entry structural witness* `CallerForwards` with an
**assumed** `hforward` field. `BytecodeLayer/ExternalCallGen.lean:21-25` states it
directly:

> "The driver `drive` is a single fuel-bounded recursion over a *flat* pending
> stack, so there is no clean 'this sub-tree is exactly a child `messageCall`'
> decomposition to lean on generically — the parent and child interleave under one
> fuel counter."

and the hole itself, `ExternalCallGen.lean:94-96`:

```lean
  hforward : Outcome.completedWith (Outcome.ofCall (messageCall cp)) a k v →
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v
```

`hforward` asserts that a completed *child* `messageCall cp` forwards its `(a,k)=v`
observable to the top-level `messageCall p`. Generically the engine cannot prove
this, precisely because the child is not a subterm; the concrete `callerProg`
instance discharges it from hand-built reflexive child-run reductions (`:185-214`),
not from a general lemma.

---

## (B) Verifereum's model: CALL evaluates a nested child machine to a result

Verifereum is a state-monad interpreter over an `execution_state` whose `contexts`
field is a **stack of (context # rollback_state) pairs**
(`forks/verifereum/spec/vfmContextScript.sml:123-130`):

```
Datatype:
  execution_state =
  <| contexts : (context # rollback_state) list
   ; txParams : transaction_parameters
   ; rollback : rollback_state
   ; msdomain : domain_mode |>
```

A `context` (`vfmContextScript.sml:86-99`) is one frame's full machine (stack,
memory, pc, returnData, gasUsed, logs, msgParams). Crucially each pushed context
carries a **paired `rollback_state` snapshot** — `<| accounts; tStorage; accesses;
toDelete |>` (`:63-70`) — captured *at descent*, which is the discardable state
delta.

**CALL builds and pushes a fresh child context**
(`vfmExecutionScript.sml:1475-1508`, `proceed_call`):

```
Definition proceed_call_def:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo = do
    rollback <- get_rollback;
    data <- read_memory argsOffset argsSize;
    if op ≠ CallCode ∧ 0 < value then
      update_accounts $ transfer_value sender address value else return ();
    ...
    subContextTx <<- <| ... gasLimit := stipend; data := data; ... |>;
    static <- get_static;
    subStatic <<- (op = StaticCall ∨ static);
    context <<- initial_context callee code subStatic outputTo subContextTx;
    push_context (context, rollback);          -- child + snapshot of caller's rollback
    if fIN address precompile_addresses then dispatch_precompiles address else return ()
  od
```

`push_context` is literally `CONS` onto `contexts` (`:270-272`). The child runs to
a result via `OWHILE`-driven `step`, then **the parent extracts that result by
popping the context** (`vfmExecutionScript.sml:1676-1688`,
`pop_and_incorporate_context`):

```
Definition pop_and_incorporate_context_def:
  pop_and_incorporate_context success = do
    calleeGasLeft <- get_gas_left;
    callee_rb <- pop_context;
    callee <<- FST callee_rb;
    unuse_gas calleeGasLeft;            -- refund the child's leftover gas to the parent
    if success then do
      push_logs callee.logs;            -- commit: lift child logs + refunds
      update_gas_refund (callee.addRefund, callee.subRefund)
    od else
      set_rollback (SND callee_rb)      -- REVERT: restore the snapshot taken at descent
  od
End
```

This is the whole nested story in three lines: **commit = keep current rollback +
lift child logs/refunds; revert = `set_rollback (SND callee_rb)`, discarding
everything the child did by reinstalling the snapshot paired with it at push
time.** The state delta is genuinely a discardable subterm.

`handle_exception` (`:1710-1740`) is the resume glue — pop the child, `inc_pc`,
then push the success flag and `write_memory r.offset (TAKE r.size output)` into the
parent (the `Memory r` `outputTo` destination), mirroring our `resumeAfterCall` but
triggered by *unwinding a finished subterm* rather than a flat `.inr` delivery.

**Where the nesting is made syntactic — the depth-scoped loops**
(`vfmExecutionScript.sml:1762-1776`):

```
Definition run_def:        run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
Definition run_call_def:
  run_call es = OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts) (step o SND) (INL (), es)
Definition run_within_frame_def:
  run_within_frame es = OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts = LENGTH es.contexts) (step o SND) (INL (), es)
```

This is the decomposition our side lacks. `run_within_frame` runs `step` **only
while the context-stack depth stays equal to the start** — it executes exactly one
frame's worth and stops the instant a child is pushed or the frame pops. `run_call`
runs while depth `≥` start — exactly one frame *and all its descendants*, stopping
when this frame returns. These are *named sub-evaluations of the same `step`*,
sliced by `LENGTH s.contexts`, giving Verifereum a black-box "run this child to its
result" operator that our flat single-fuel `drive` cannot name. (Depth limit
enforced separately in `step_call`, `vfmExecutionScript.sml:1547-1549`, `if
sucDepth > 1024 then abort_unuse stipend`.)

EVM-concrete handling, confirmed nested:
- **State rollback on revert** — `set_rollback (SND callee_rb)`: reinstall the
  per-child snapshot (`pop_and_incorporate_context`, `:1686`).
- **63/64 gas forwarding** — child gets `stipend` as its own `msgParams.gasLimit`
  (`call_gas`, `step_call:1537`); leftover returned via `unuse_gas calleeGasLeft`
  on pop (`:1681`).
- **Return data** — child's `returnData` becomes the parent's via
  `set_return_data output` + `write_memory` (`handle_exception:1730-1736`).
- **Depth / 1024** — measured as `LENGTH s.contexts` (`get_num_contexts`,
  `:266-268`); both the bound and the loop slices are depth-driven.
- **DELEGATE/STATIC/CALLCODE variants** — one `step_call op` parameterized by `op`
  (`:1510-1554`), branching on `op` for callee/value/static
  (`proceed_call:1486-1501`), structurally identical to our single `callArm`.

---

## (C) Why nested is the more standard design

**General (program-logic) reasons.** A nested child run is an independent subterm
with its own value, so it admits its own Hoare triple and can be consumed as a
black box. This is exactly the classical procedure-call rule and the frame rule:
prove `{P} child {Q}` once, then at every call site reason `{P * R} call {Q * R}`
without reopening the callee. Verifereum's `run_call`/`run_within_frame` give a term
you can state `{P} run_call es {Q}` about; `pop_and_incorporate_context` is the
single point where the child's `Q` is folded into the parent. Reentrancy is free: a
callee re-entering is just another `push_context` — another nested `run_call` with
the same triple — no special interleaving case. Our flat `drive` has no subterm to
give a triple to; the child's behavior is entangled with the parent across `drive
fuel (pending :: stack) …`, which is precisely why rung 2 needed the assumed
`hforward` instead of a frame-rule application.

**EVM-concrete reasons each detail is cleaner nested than flat-under-one-fuel:**
- *Rollback on revert.* Nested: the child's entire state effect is the delta
  between the pushed snapshot and the current `rollback`; revert = `set_rollback
  snapshot`, one assignment, delta provably discarded. Flat: we thread a
  `Checkpoint` field through `endCall` and must reason that no other `drive`
  iteration touched it — a global invariant rather than a local subterm.
- *63/64 gas.* Nested: the child is *metered by its own `gasLimit := stipend`*;
  "child cannot overspend the cap" is an invariant of the child run alone. Flat:
  child and parent share one `fuel ℕ` that is **not** the gas budget (our
  `seedFuel` comment, `Interpreter.lean:30-34`, calls fuel "an implementation
  detail, not a semantic bound"), so the cap is enforced only inside `callArm`'s
  arithmetic, not by the recursion structure.
- *Return-data buffer / depth / variants.* All three are local reads of the child
  context or `LENGTH contexts` in the nested model; in the flat model they are
  facts about the head of a shared list that must be re-established at each
  `resume`.
- *Reentrancy.* Nested: another push, same triple. Flat: another interleaving of
  the same counter, no compositional handle.

**Relation to the Yellow Paper.** The YP defines message calls via
mutually-recursive `Θ` (call) and `Ξ` (code execution), where `Θ` *invokes* `Ξ` on
a child machine and consumes its returned `(σ', g', A', o)` tuple. Verifereum's
`proceed_call` → `run_call` → `pop_and_incorporate_context` is a near-literal
monadic transcription of `Θ`-calls-`Ξ`-returns-tuple. Our flat `drive` is
**further** from the YP's recursive `Θ/Ξ`: it is a defunctionalized, single-loop
reformulation that is *behaviorally* equivalent but *structurally* a CPS/trampoline,
not a recursion that returns child tuples.

---

## (D) Why the flat design exists here, and its tradeoffs

The flat single-`drive` recursion is the EVMYulLean/leanevm
**executable-conformance** lineage. `forks/leanevm/CLAUDE.md` confirms the repo's
purpose: an "Executable Lean 4 specification of the EVM, tested against the Ethereum
BlockchainTests fixtures (`lake exe conform`)." For an executable spec the flat
shape is attractive:

- **Termination is trivial.** One structurally-decreasing `fuel : ℕ` discharges
  termination for *all* of CALL/CREATE/precompile/reentrancy in one shot. A nested
  formulation needs well-founded recursion on depth×gas (or fuel-passing through the
  child call), which Lean's equation compiler handles far less smoothly and which
  complicates `simp`/`grind` reductions.
- **Execution speed / shape.** A single tail-recursive loop over an explicit `List
  Pending` is a defunctionalized trampoline — no deep native call stack, predictable
  for the conformance runner over 22k fixtures.
- **Uniformity.** One `stepFrame`/`drive` pair covers every opcode and every
  descent; exactly one place consumes fuel and one place delivers results.

**Tradeoff:** termination simplicity + execution uniformity bought at the cost of
proof compositionality. The very property that makes it a clean executable loop —
collapsing parent and child into one counter and one list — is what denies a frame
rule and forced the `hforward` assumption. The standard executable-spec-vs-program-
logic tension.

---

## (E) Recommendation for the plan: keep "prove-over-flat"

The Verifereum comparison **reinforces** the current plan
(`external-call-rebuild-plan.md`). Prove a generic decomposition lemma
`drive_descend_eq` (stack-append/framing + fuel-monotonicity) **over** the existing
flat `drive`, rather than reshape `drive` into nested form. Reasons:

1. **Do prove-over-flat now; do not reshape `drive`.** Reshaping would break the
   conformance suite and every existing fuel proof
   (`drive_fuel_succ`/`drive_fuel_mono`/`driveG_*`), for no behavioral gain.

2. **The lemma to prove is precisely Verifereum's `run_call`/`run_within_frame` as a
   derived fact.** What Verifereum gets *definitionally* from the depth-sliced
   `OWHILE` (run the child sub-tree to its result as a black box), we get as a
   *theorem*: a CALL's in-line descent into a child equals `messageCall cp` on that
   child, with the parent's pending suffix framed off. The right target is "every
   `drive` arm touches only the **head** of the pending stack" — the Lean analogue
   of Verifereum slicing by `LENGTH s.contexts`, and what makes the append-framing
   lemma provable by fuel induction. Proving it retires the assumed `hforward` (it
   becomes a corollary, not a witness field).

3. **Defer any nested reformulation to an optional, separate `drive`-equivalent
   semantics.** If a fully compositional program logic is later wanted, build a
   *second* `driveNested` proved equal to `drive` (the executable spec stays the
   conformance source of truth; the nested one is a proof-only mirror). Strictly
   more work than `drive_descend_eq` and unnecessary for closing the current hole —
   only pursue if multiple downstream proofs start re-deriving framing by hand.

**Bottom line:** Verifereum shows nested is the standard, compositional,
Yellow-Paper-faithful shape, and that its single payoff for us is the black-box
child sub-evaluation — recoverable as a lemma over the flat `drive` without paying
the reshape's conformance/termination costs. Prove `drive_descend_eq`, discharge
`hforward` from it, keep the flat executable spec.

**Source note:** Verifereum was read locally; all HOL4 citations are to
`forks/verifereum/spec/`. Line numbers may differ from upstream `master` if the
local checkout has drifted (see `forks/verifereum/PINS`).
