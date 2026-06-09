# Experiment 001 Handoff

## Status: lowering theorem proved

`Preservation.lowering_correct` is fully proved: for **every** program,
initial EVM state, fuel and gas level, executing the lowered bytecode under
EVMYulLean's `EVM.X` is equal to the IR's gas-exact executable semantics.

```bash
cd experiments/001_toy_external_call
lake build                  # passes, no sorries
rg -n "\bsorry\b|\badmit\b|^axiom" ToyExternalCall   # empty
```

`#print axioms Preservation.lowering_correct` reports only
`propext, Classical.choice, Quot.sound`.

A concrete `#eval` check (interpreting both semantics on
`[inputLoad 0 0, add 1 (local 0) (const 5)]`) confirms byte-for-byte
agreement: identical remaining gas (7 804 252 of 10 000 000) and result on
the success path, identical `OutOfGass` on the underfunded path.

## The theorem

```lean
theorem lowering_correct (oracle : CallOracle) (hsound : CallOracleSound oracle)
    (program : Program) (vj : Array UInt256) (s : Exec)
    (hsize : (Bytecode.lower program).size < UInt256.size) :
    EVM.X s.fuel vj
      (injectFrame s.evm (.ofNat 0) [] (Bytecode.lower program)) =
      (run oracle program s).map (fun s' =>
        .success
          (injectFrame s'.evm (.ofNat ((Bytecode.lower program).size - 1)) []
            (Bytecode.lower program))
          ByteArray.empty)
```

How to read it:

* `injectFrame evm pc stack code` overrides exactly the three frame fields
  (`pc`, machine `stack`, `executionEnv.code`) that distinguish an IR state
  from the state of its lowered code. Everything else — memory, gas,
  accounts, substate, return data, trace length — is **equal on the nose**.
* `run` is the IR's executable semantics (`IR.lean`). It is total
  (structural recursion on the program); the fuel counter only mirrors
  `EVM.X`'s and is consumed one unit per lowered opcode, so the theorem
  covers out-of-fuel outcomes too.
* Errors agree exactly: `OutOfGass`, `OutOfFuel`, `StaticModeViolation`
  occur on the source side iff they occur at the corresponding opcode of
  the lowered code.

### Assumptions (exactly two)

1. `CallOracleSound oracle` — the call oracle returns exactly what
   `EVM.call` returns, *and* `EVM.call` passes the frame fields through
   untouched. It is satisfiable by taking the oracle to be `EVM.call`
   itself; the frame-insensitivity half is then a provable (unproven here)
   fact about `EVM.call`, whose body never reads `pc`/`stack`/code.
2. `hsize` — the lowered code is addressable by a 256-bit program counter.
   A representability bound, not a semantic restriction (real EVM code is
   ≤ 24 576 bytes).

## Design decisions (and why the previous attempt failed)

The previous iteration proved its own preservation statement **false**
(`current_evm_preservation_statement_is_false`): the source semantics
ignored gas, and locals lived in a map separate from EVM memory, requiring
an unprovable frame invariant across `CALL` (calls may legally clobber any
memory, including the reserved local slots). Both problems were fixed by
redesign rather than by adding hypotheses:

* **Locals are memory-backed.** `Exec` wraps an `EVM.State` plus fuel;
  local `x` *is* the memory word at `localSlot x`. If a call clobbers a
  local slot, source and target see the identical clobbering — no frame
  invariant, no disjointness side conditions.
* **The semantics is gas-exact.** Each IR action mirrors one `EVM.X`
  iteration: fuel check (`tick`), `EVM.Z`'s two-stage gas accounting
  (`chargeMem`/`requireGas`, including `Cₘ` memory-expansion costs and the
  full `Ccall` formula), `EVM.step`'s fuel guard (`stepGuard`), then the
  effect. Operands evaluate right-to-left, matching push order, because
  evaluation order is observable through memory-expansion gas.
* **Calls go through an oracle** with the exact signature of the reached
  `EVM.call` instance (fuel and gas-cost threaded explicitly).

An honest caveat: the IR's *gas schedule* is defined to be the cost of its
lowering, so gas agreement is partly by construction. The theorem's real
content is everything else — decode/assemble correctness, stack discipline,
pc threading, the `X` loop, halting, error propagation, and that the
declared gas schedule formulas (`wordTouchCost`, `callTouchCost`, `Ccall`,
`Gverylow`, …) are in fact what the EVM charges at each opcode.

## File map

| File | Contents |
|---|---|
| `ToyExternalCall/IR.lean` | Syntax, `Exec`, gas-exact actions, `CallOracle`, `CallOracleSound`, `execInstr`, `run` |
| `ToyExternalCall/Bytecode.lean` | Opcode-level `Op`, list-first byte encoding (`codeBytes`), compilation, `lower` |
| `ToyExternalCall/EVMLemmas.lean` | The reusable lemma layer over `EVM.X`: decode-at-prefix, `Z_generic`/`Z_call`, per-op `step` lemmas, per-op `X` iteration lemmas (incl. `X_call`), `callStep_eval` |
| `ToyExternalCall/Preservation.lean` | Chunk lemmas (operand, write-local, instruction), `run_simulation` induction, `lowering_correct` |

## Validated assumptions about EVMYulLean

* `EvmYul/EVM/Semantics.lean` proves **zero** theorems: it is an executable
  spec. Building our own lemma layer is necessary; the previous agent's
  judgment was correct.
* `EVM.X` is the right layer: the YP Eq. 159 instruction loop with full gas
  accounting. `Ξ`/`Θ`/`Υ` add account/transaction machinery (a later
  experiment); bare `EVM.step` has no loop or halting.
* Fork changes (branch `2727b79` + this session): exposing `Z`/`H`/`W` from
  `X` (visibility only); list-based `ByteArray.get?`/`extract'`
  (extensionally equal; verified `UInt256.toByteArray` against upstream by
  evaluation on edge cases); `ffi.ByteArray.zeroes` got a pure Lean body so
  the semantics is interpretable with `#eval` (compiled conformance runs
  pay a performance cost).

## Proof-engineering notes

See `docs/findings.md` for the patterns that made this tractable (and the
dead ends). The short version: keep byte encodings list-first; pin frames
with `injectFrame` and prove its projections as `@[simp]` `rfl` lemmas;
state `step` lemmas over destructured states so `rfl` closes them; align
guards with `if_pos`/`if_neg` instead of fighting `simp` normal forms;
evaluate the IR side with a standalone equation (`callStep_eval`) rather
than in-proof `simp`; generalize chunk-lemma positions over a `Nat` with a
side equation (`*_at` variants) so pc arithmetic never changes shape.

## Next steps

1. **Discharge half of `CallOracleSound`**: prove `EVM.call` frame
   insensitivity (unfold `call` once, case on the `Θ` result; `Θ` never
   receives the caller's frame fields). The assumption then reduces to pure
   oracle/`EVM.call` agreement, and instantiating `oracle := EVM.call`
   yields an assumption-free corollary for call-free programs.
2. **Returndata**: expose `RETURNDATASIZE`/`RETURNDATACOPY` in the IR; the
   returnData field already agrees on the nose.
3. **Control flow**: `JUMP`/`JUMPI` need `D_J` (valid-jump-destination)
   reasoning; the lemma layer's `validJumps` parameter is already threaded
   everywhere.
4. **Abstract locals**: re-introduce a locals map as a *view* of the
   reserved region with a separation discipline, recovering the
   CompCert-style abstraction on top of `lowering_correct` instead of
   inside it.
5. **Scale the IR toward Plank SIR** (more operators, storage, function
   calls) and wrap the theorem at the `Ξ`/`Θ` message-call boundary.
6. Cosmetic: a number of `unusedSimpArgs` lint warnings remain in
   `EVMLemmas.lean`; harmless.

## Useful commands

```bash
cd /Users/eduardo/workspace/evm-semantics/experiments/001_toy_external_call
lake build
rg -n "\bsorry\b|\badmit\b|\baxiom\b" ToyExternalCall
```
