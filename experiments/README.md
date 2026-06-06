# Experiments

This directory contains small Lean packages used to explore Plank SIR formalization choices.

Each experiment should be self-contained and include:

- a local `lakefile.lean`;
- Lean source files;
- a `docs/` directory recording the plan, design decisions, what worked, what failed, and what should be reused.

The point is not to keep every experiment polished. The point is to preserve what we learn while we converge on a real SIR formalization.

## Current Experiments

- [`001_toy_external_call`](./001_toy_external_call): tiny instruction-like IR with calldata load, add constant, and external call.

