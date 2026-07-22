# AGENTS.md — repo orientation

This repository **formalizes Plank's EVM IR (SIR) and its compilation to EVM
bytecode in Lean**.

## Repo layout

```
EVM/          bytecode layer (semantics, Hoare, assembler, conformance)
sir/          canonical SIR package: CFG IR + mixed-step semantics
              (small-step opcodes, big-step internal calls, oracle external calls)
experiments/  exploratory lines, mostly frozen — read for context; some are
              still occasionally worked on. Each carries its own local
              AGENTS.md/CLAUDE.md rules; the spec-architecture rules below do
              not apply retroactively there.
forks/        vendored reference repos (read-only)
docs/         planning / review / reference / archive
scripts/      tooling
```

## Spec architecture (applies to `EVM/` and `sir/`)

- **The audit surface is `Spec/` plus the statements in `Theorems.lean`** (and
  any exported `Examples/` results). The rule: every constant reachable from an
  exported theorem *statement* must live in `Spec/`. This is enforced by the
  Audit metaprogram in CI, not by convention alone.
- `Spec/` contains definitions and at most one-line proofs (instances,
  `rfl`-lemmas needed by statements). All other proofs, proof-internal
  definitions, and characterization lemmas live in `Proofs/`. Proofs never
  unfold spec definitions directly — go through a characterization lemma, so
  the spec can be reshaped without breaking the proof corpus.
- `Theorems.lean` holds the exported results; statements must elaborate against
  `Spec/` alone, and proofs there are one-line delegations into `Proofs/`.
- **New definitions land in `Proofs/` by default.** Promoting a definition into
  `Spec/` is a human decision, and the price of admission is: a full-word name
  (no coined abbreviations — a reviewer must be able to read the statement
  aloud) and a docstring stating what it means *and why it exists*.
- Every `WellFormed`-style hypothesis field states its consumer in its
  docstring, or is explicitly marked as an invariant mirrored from the Rust
  compiler / reserved for the lowering proof. Unconsumed and unmarked
  hypotheses are not allowed.
- In spec-leaf definitions prefer named combinators (`map`, `guard`, `foldlM`)
  over `do`/inline closures; the sugar elaborates to anonymous matchers that
  lemmas cannot target.

## Comments

Near-zero comments outside `Spec/`. In `Spec/`: one short paragraph of
rationale per concept — *why it exists* — not a restatement of the code. No
dev-narration, no history, no claims about other files' relationship to this
one (see the cruft rule below).

## No stale cruft — delete superseded code, keep comments local

This is a load-bearing rule, not a nicety. The standing risk in this repo is
*scattered outward references that silently rot*: links to files/symbols that
were renamed or deleted, ceremonial backward-compat with a version that was
wrong, and comments asserting things about *other* code that may no longer be
true. Every such reference is a thing someone must remember to update, and
they won't. Therefore:

- **Delete superseded code outright.** When a better version lands, the old one
  goes — no "kept as a cross-check", no dead second proof, no commented-out
  alternative. One consolidated version is the source of truth. (Standalone
  *docs* are the sole exception — those are archived per the next rule.)
- **Keep comments about *local* reasoning; restrict outward allegations.** A
  docstring explains what *this* definition/proof does and why, not how some
  other file relates to it. Cross-file allegations are exactly what goes stale
  when the other side moves. Name another module only when the pointer is
  genuinely necessary, and then it is your job to keep it true.
- **When you delete or rename, sweep for references.** `grep` the tree for the
  old file/symbol name and fix or remove every hit (docstrings, module-map
  comments, links) in the same change — never leave a dangling pointer. Do this
  without being asked.

## Doc archival

When a standalone *doc* is superseded, move it to the relevant `archive/` and
add a top banner pointing to its replacement. Do not delete (the reasoning is
usually still worth reading) and do not leave stale docs unmarked in place.
(This is about prose documents; superseded *code* and in-source comments are
deleted/rewritten per the rule above, not archived.)

## Reporting

- **Ship-facing text describes what ships.** A work session decides a scope,
  ships it, and what was considered-and-dropped along the way is not part of
  the artifact. PR descriptions, code comments, READMEs, and review reports
  must never mention work that was attempted, removed, or deliberately left
  out during the session — no "not included", no "we also tried", no history
  of the session's decisions. If a dropped direction genuinely matters later,
  record it in a planning doc (those are agent-facing; humans don't read
  them). Human-facing text is a different art from structured writing:
  optimize signal-to-noise, assume the reader's context (Phil knows this
  project — don't re-explain it to him), prefer direct sentences over
  parallel-structured prose, and don't use two different verbs for the two
  sides of one comparison.
- **Axiom/sorry status: silence is the baseline.** Sorry-free and axiom-clean
  (nothing beyond `propext` / `Classical.choice` / `Quot.sound`) is the
  standing bar for everything that lands. Therefore PR descriptions, commit
  messages, and reports must **not** announce it — never write "no new axioms,
  no sorry" and never paste the standard axiom triple as a closing flourish.
  Mention this dimension only on *deviation* — a `sorry`, a new `axiom`,
  `native_decide`, or any dependency beyond the standard three — and then call
  it out loudly.
- **Reviewer standard (Philip):** exported theorem statements must be
  high-level — observables, not bytecode-mirroring. A spec that re-notates the
  EVM opcode-for-opcode is the thing this project is trying to move past.
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
