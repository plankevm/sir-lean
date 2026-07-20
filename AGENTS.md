# AGENTS.md — repo orientation

This repository **formalizes Plank's EVM IR (SIR) and compilation in Lean**.

## Repo layout

```
EVM/             consolidated bytecode reasoning layer (Evm + BytecodeLayer + Conform)
sir/             canonical SIR package (CFG IR + semantics) — in progress
scripts/         fetch-forks.sh and tooling
```

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
- **No stale cruft — delete superseded code, keep comments local.** This is a
  load-bearing rule, not a nicety. The standing risk in this repo is *scattered
  outward references that silently rot*: links to files/symbols that were renamed
  or deleted, ceremonial backward-compat with a version that was wrong, and
  comments asserting things about *other* code that may no longer be true. Every
  such reference is a thing someone must remember to update, and they won't.
  Therefore:
  - **Delete superseded code outright.** When a better version lands, the old one
    goes — no "kept as a cross-check", no dead second proof, no commented-out
    alternative. One consolidated version is the source of truth. (Standalone
    *docs* are the sole exception — those are archived per the next bullet.)
  - **Keep comments about *local* reasoning; restrict outward allegations.** A
    docstring should explain what *this* definition/proof does and why, not make
    claims about how some other file relates to it ("the generic version of
    `child_run` in `ExternalCall.lean`", "an instance of the rung in `Foo.lean`").
    Those cross-file allegations are exactly what goes stale when the other side
    moves. Prefer describing the thing in itself; name another module only when
    that pointer is genuinely necessary, and then it is your job to keep it true.
  - **When you delete or rename, sweep for references.** `grep` the tree for the
    old file/symbol name and fix or remove every hit (docstrings, module-map
    comments, links) in the same change — never leave a dangling pointer. Do this
    without being asked.
- **Doc archival.** When a standalone *doc* is superseded, move it to the relevant
  `archive/` and add a top banner pointing to its replacement. Do not delete (the
  reasoning is usually still worth reading) and do not leave stale docs unmarked in
  place. (This is about prose documents; superseded *code* and in-source comments
  are deleted/rewritten per the rule above, not archived.)
- **Reviewer standard (Philip):** exported theorem statements must be high-level
  — observables, not bytecode-mirroring. A spec that re-notates the EVM
  opcode-for-opcode is the thing this project is trying to move past.
  **Low-level-layer carve-out (ruled by Eduardo):** the bytecode proof layer
  (`EVM/BytecodeLayer/`) *is* the low-level layer, and its `Spec.lean` audit
  surface may expose frame-level program-logic rules (statements mentioning
  `Runs`/`Frame`/`stepFrame`) — those rules are the reusable theorems a user
  instantiates there. The observables-only standard binds the higher,
  experiment-style exported surfaces, not this layer's audit surface.
- **Review reports.** A *review report* of a body of Lean work (for a human
  reviewer) must be produced via the `lean-review-report` sub-agent
  ([`.claude/agents/lean-review-report.md`](.claude/agents/lean-review-report.md)),
  not hand-written ad hoc. It is grounded, specs-first, and reviewer-friendly:
  **clickable markdown links / `file:line` to every file it cites, and fenced
  (syntax-highlighted) code blocks — never inline-code-only prose.** Internal
  *plans* (for the agent's own use) are exempt; this rule is for review
  deliverables a human will read.
