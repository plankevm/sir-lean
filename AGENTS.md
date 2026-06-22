# AGENTS.md — repo orientation

This repository studies how to **formalize Plank's EVM IRs in Lean**, using
existing EVM/compiler formalizations as references. It is a research notebook
plus a set of self-contained Lean experiments — not a single shipping artifact.

If you are an agent starting work here, read this file, then
[`docs/index.md`](docs/index.md).

## Where to start

1. [`docs/index.md`](docs/index.md) — the documentation hub. It is tiered:
   `docs/reference/` (durable ecosystem/concept knowledge), `docs/planning/`
   (live strategy), `docs/archive/` (superseded, kept with banners).
2. [`docs/planning/bytecode-first-plan.md`](docs/planning/bytecode-first-plan.md)
   — **the head of the stack.** The agreed direction. New formalization work
   starts from here.

## Current state (2026-06)

- **Direction:** *bytecode-first.* Retire the toy-IR ladder; invest once in a
  reusable reasoning layer over a vendored, EVM-only EVMYulLean; move theorem
  boundaries to the `Θ`/`Ξ` message call and state everything in observables;
  make Plank SIR the first IR with a real abstraction gap. Full rationale in the
  bytecode-first plan.
- **Experiment 001 (`experiments/001_toy_external_call/`):** **closed.** A
  straight-line toy IR proved equivalent to EVMYulLean's `EVM.X`, with a gasless
  spec, reflexive calls, and observables export. Permanent findings: `CALL`
  consults gas (so gas-free specs need `∃G₀` statements) and `EVM.call` is
  frame-insensitive (proved cheaply). See its
  [`docs/README.md`](experiments/001_toy_external_call/docs/README.md).
- **Experiment 002 (`experiments/002_ssa_cfg/`):** active. A higher-level SIR —
  CFG of basic blocks, SSA-style variables, small-step + executable semantics,
  and an SCCP optimization pass with a proved `PreservesSemantics`. This is the
  "real IR with abstraction" exploration (no bytecode lowering yet; it studies
  SIR semantics and pass correctness in isolation).

## Repo layout

```
docs/            reference/ + planning/ + archive/ (start at index.md)
experiments/     self-contained Lean packages (001 closed, 002 active)
forks/           vendored reference repos — GIT-IGNORED, fetch separately
scripts/         fetch-forks.sh and tooling
```

The four reference formalizations under `forks/` are EVMYulLean (Lean EVM/Yul),
verifereum (HOL EVM + relational layer), verity (Lean EDSL→Yul bridge), and
vyper-hol (HOL source→Venom IR→codegen). They are **not** tracked in git; run
[`scripts/fetch-forks.sh`](scripts/fetch-forks.sh) to clone the pinned revisions
so source links in the docs resolve.

## Conventions

- **Per-experiment coding rules.** Each experiment may carry its own `AGENTS.md`
  (and `CLAUDE.md`) with Lean style rules — e.g. `002_ssa_cfg` mandates a strict
  `Spec.lean` / `Proof.lean` split (spec readability is the audit surface; proof
  internals never appear in spec statements; proofs go through characterization
  lemmas, never unfolding spec defs). Follow the experiment-local file when
  working inside that package.
- **Spec over proof convenience.** Across experiments, the human audit surface is
  the specification and everything its statements reach; optimize those for
  review, keep proof machinery quarantined.
- **Doc archival.** When a doc is superseded, move it to the relevant `archive/`
  and add a top banner pointing to its replacement. Do not delete (the reasoning
  is usually still worth reading) and do not leave stale docs unmarked in place.
- **Reviewer standard (Philip):** exported theorem statements must be high-level
  — observables, not bytecode-mirroring. A spec that re-notates the EVM
  opcode-for-opcode is the thing this project is trying to move past.
- **Review reports.** A *review report* of a body of Lean work (for a human
  reviewer) must be produced via the `lean-review-report` sub-agent
  ([`.claude/agents/lean-review-report.md`](.claude/agents/lean-review-report.md)),
  not hand-written ad hoc. It is grounded, specs-first, and reviewer-friendly:
  **clickable markdown links / `file:line` to every file it cites, and fenced
  (syntax-highlighted) code blocks — never inline-code-only prose.** Internal
  *plans* (for the agent's own use) are exempt; this rule is for review
  deliverables a human will read.
