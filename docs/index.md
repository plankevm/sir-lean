# EVM Semantics Study Notes

This documentation maps the local formalization repos under `forks/` and explains how their EVM models, source/IR semantics, and compiler-correctness hooks fit together.

## Reading Path

1. [Jargon and semantic styles](./jargon.md)
2. [Repository map](./repo-map.md)
3. [Lean-based models: EVMYulLean and Verity](./lean-models.md)
4. [HOL-based models: Verifereum and Vyper-HOL](./hol-models.md)
5. [Horizontal concept comparison](./concept-comparison.md)
6. [Plank IR modeling notes](./plank-ir-modeling.md)
7. [Recommended formalization plan](./formalization-plan.md)

## Short Takeaway

The closest reusable EVM semantics are:

- `forks/EVMYulLean`: Lean executable EVM and Yul semantics, organized around Yellow Paper-style state components and fuel-bounded interpreters.
- `forks/verifereum`: HOL executable EVM semantics, with a monadic small-step interpreter plus a Hoare/spec layer.

The closest examples of "source/IR hooks into EVM" are:

- `forks/verity`: a Lean EDSL and compiler model that lowers to Yul and has bridge code toward EVMYulLean.
- `forks/vyper-hol`: a HOL source-level Vyper interpreter, a Venom IR semantics, lowering relations, pass simulations, and codegen-to-Verifereum statements.

For Plank, the strongest first target is likely SIR/EthIR rather than parser AST or HIR. SIR is already CFG-shaped, close to EVM, and explicit about storage, memory, calldata, calls, logs, return data, and bytecode emission.

