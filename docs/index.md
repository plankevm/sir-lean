# EVM Semantics Study Notes

This documentation maps the local formalization repos under `forks/` and explains how their EVM models, source/IR semantics, and compiler-correctness hooks fit together.

## Reading Path

1. [Review follow-up plan](./review-followup-plan.md)
2. [Jargon and semantic styles](./jargon.md)
3. [EVM state model and Yellow Paper notation](./evm-state-model.md)
4. [Repository map](./repo-map.md)
5. [Lean-based models: EVMYulLean and Verity](./lean-models.md)
6. [Verity to EVMYulLean bridge](./verity-bridge.md)
7. [HOL-based models: Verifereum and Vyper-HOL](./hol-models.md)
8. [Horizontal concept comparison](./concept-comparison.md)
9. [Plank IR modeling notes](./plank-ir-modeling.md)
10. [SIR to bytecode correctness](./sir-to-bytecode.md)
11. [Pilot SIR formalization plan](./pilot-sir-formalization-plan.md)
12. [Experiment 001: Toy external call](../experiments/001_toy_external_call/docs/plan.md)
13. [Recommended formalization plan](./formalization-plan.md)
14. [Semantics choice for Plank](./semantics-choice.md)

## Short Takeaway

The closest reusable EVM semantics are:

- `forks/EVMYulLean`: Lean executable EVM and Yul semantics, organized around Yellow Paper-style state components and fuel-bounded interpreters.
- `forks/verifereum`: HOL executable EVM semantics, with a monadic small-step interpreter plus a Hoare/spec layer.

The closest examples of "source/IR hooks into EVM" are:

- `forks/verity`: a Lean EDSL and compiler model that lowers to Yul and has bridge code toward EVMYulLean.
- `forks/vyper-hol`: a HOL source-level Vyper interpreter, a Venom IR semantics, lowering relations, pass simulations, and codegen-to-Verifereum statements.

For Plank, the strongest first target is likely SIR/EthIR rather than parser AST or HIR. SIR is already CFG-shaped, close to EVM, and explicit about storage, memory, calldata, calls, logs, return data, and bytecode emission. The most promising architecture is not "prove Plank directly inside EVMYulLean"; it is "give SIR an executable semantics, then prove the bytecode backend refines that semantics using EVMYulLean as the target model."
