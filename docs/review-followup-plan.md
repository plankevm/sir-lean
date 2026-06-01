# Review Follow-up Plan

This page records the review concerns being addressed so the docs do not drift back into vague glossary text.

## Main Corrections

1. Replace generic semantic signatures with signatures that distinguish [small-step, big-step, block-step, interpreter, and relational styles](./jargon.md).
2. Explain technical terms when they first matter, especially [Yellow Paper state notation](./evm-state-model.md), machine state, checkpoint state, and execution environment.
3. Expand design consequences: what is gained or lost by using executable interpreters, relational proof layers, abstract source states, or full EVM state.
4. Explain [Verity's bridge to EVMYulLean](./verity-bridge.md): dependency pin, state projection, native lowering, observable result matching, and trust boundary.
5. Make [SIR to bytecode correctness](./sir-to-bytecode.md) a first-class topic rather than treating MIR-to-SIR as the central goal.
6. Record the recommended [semantics choice for Plank](./semantics-choice.md): define SIR semantics and bridge it to EVMYulLean, rather than owning a fresh full EVM semantics immediately.
7. Add a script to download the ignored `forks/` repos so source links resolve for readers: [`scripts/fetch-forks.sh`](../scripts/fetch-forks.sh).

## Documentation Rule Going Forward

When a page invokes a technical concept that affects proof architecture, it should either explain it locally or link to a page that does. Short labels like "small-step", "Yellow Paper state", "state relation", "fuel", "rollback", or "observable projection" should not be left as unexplained decoration.

