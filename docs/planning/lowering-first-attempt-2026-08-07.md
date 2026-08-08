# Certified lowering: first proof attempt

## Goal

Land the smallest non-vacuous SIR-to-CFGwAS lowering theorem on top of
`edu/sir-guarded-stores`. The first slice has one function, one block, a halt
terminator, and only `constant`, `copy`, `add`, and `lt` operations. It must
include a certificate that can actually be checked for a concrete program and
must prove execution preservation in both directions.

This is a vertical proof slice, not a second experiment-005 architecture. New
canonical work belongs under `sir/`; experiment 005 is evidence and a source of
counterexamples only.

## Semantic contract

The simulation relates a SIR local environment to the CFG stack and spill-slot
environment through an explicit layout. Related states have equal `Globals`.
Each source primitive and its scheduled target segment use the same operation
oracle and produce the same trace fragment and resulting globals. Stack-only
administrative instructions stutter on the SIR side.

The proof target for this slice is equivalence of finite function evaluations:

```lean
source evaluation -> scheduled target evaluation
scheduled target evaluation -> source evaluation
```

Both directions preserve the exact trace, final globals, and terminal outcome.
An observable entry-behaviour wrapper is desirable only after the evaluation
pair is green.

## Certificate boundary

The certificate is finite program-text data checked in Lean. Its validity says
that replaying the target instructions from the declared entry layout consumes
the source statements in order, performs only layout-correct stack operations,
and reaches the declared exit layout and matching halt terminator.

The theorem must not accept an arbitrary simulation premise or a per-run tie.
The repository must contain at least one concrete source/target/certificate for
which the checker computes successfully. This is the satisfiability guard
against an empty lowering relation.

Definitions that appear in an exported theorem statement belong in `Sir/Spec/`.
Proof machinery and characterization lemmas belong in `Sir/Proofs/`. If
`CfgProgram` must become part of the audit surface, relocate its canonical
definition rather than adding a duplicate facade.

## Memory compatibility

The first slice excludes memory operations but must not specialize the generic
machine in a way that loses them later.

- `mload32` keeps its 32-byte oracle. A later SIR/CFG simulation pairs the same
  oracle on both sides, so bytes outside allocations remain nondeterministic.
- `mstore32` steps only when one provisioned allocation contains all 32 bytes.
  Equal related globals and equal operands make the bounds decision identical
  on both sides.
- CFG spill slots remain outside `Globals.memory` in the first hop. Their later
  EVM-memory representation is a second-hop invariant, not a change to SIR
  memory.

## First-attempt deliverables

1. Inventory the current `Sir.Generic.Cfg` definitions and the audit boundary.
2. Choose the smallest relocation or Spec surface needed for a real theorem.
3. Define a straight-line replay/certificate relation and executable checker.
4. Prove checker soundness.
5. Prove both evaluation directions for the supported slice.
6. Add a concrete checked example.
7. Run `cd sir && lake build`, including `Sir.Audit`.

Each green increment should be committed separately. No `sorry`, `admit`, new
axiom, `native_decide`, supplied semantic simulation premise, or modification of
the memory semantics is permitted.

## Stop conditions

After three materially different failed approaches to one obligation, stop and
report the exact goal, the missing invariant or induction principle, and the
smallest owner lemma that would unblock it. A useful investigation may finish
with no code commit, but it must identify why the proposed statement is too
strong, ill-owned, or missing source well-formedness.
