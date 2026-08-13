# AGENTS.md — repo orientation

This repository **formalizes Plank's EVM IR (SIR) and its compilation to EVM
bytecode in Lean**.

## Repo layout

```
EVM/          bytecode layer (semantics, Hoare, assembler, conformance)
sir/          canonical SIR package: CFG IR + mixed-step semantics
              (small-step opcodes, big-step internal calls, oracle external calls)
experiments/  exploratory lines, mostly frozen — read for context, edit only
              when the task is about that experiment. Each carries its own
              local AGENTS.md/CLAUDE.md rules; the spec-architecture rules
              below do not apply retroactively there.
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
  `Spec/` is a human decision. Name it so a reviewer can read the statement
  aloud, which rules out invented abbreviations — but the words the Rust
  compiler and the IR already use (`alloc`, `ptr`, `mem`, `icall`) are the
  vocabulary, not abbreviations waiting to be expanded.
- **What is already in `Spec/` is not a cleanup target.** Do not rename it, do
  not add docstrings to it, do not audit the directory against the rule above.
  That rule is a gate a human applies when admitting something new; running it
  backwards over code that already landed produces renames and comments nobody
  asked for.
- Every `WellFormed`-style hypothesis field must have a consumer, or be an
  invariant deliberately mirrored from the Rust compiler / reserved for the
  lowering proof. Unconsumed, unjustified hypotheses are not allowed —
  **but do not record the consumer in a docstring.** A "consumed by `foo`"
  comment is a cross-file allegation that goes stale the moment `foo` moves,
  and a reviewer can `grep`. Justify the field in the commit or the PR, not in
  the source.
- In spec-leaf definitions prefer named combinators (`map`, `guard`, `foldlM`)
  over `do`/inline closures; the sugar elaborates to anonymous matchers that
  lemmas cannot target.

## Comments

**Write none.** That is the default everywhere, `Spec/` included. A
specification is read through its names, its signatures and the way it is
split into definitions; a docstring is what you reach for when those failed,
and the fix is the definition, not the paragraph. `sir/` says no comments at
all ([`sir/AGENTS.md`](sir/AGENTS.md)) and that rule wins inside the package.

The exception, outside `sir/`, is a concept a theorem statement forces the
reader to understand and whose *reason to exist* is not visible in the code —
one short paragraph, written in the same commit as the definition. Plumbing
(accessors, operand helpers, structure fields) never qualifies. A file where
every declaration carries a docstring is the failure mode this rule exists to
prevent: they become noise and none of them is read.

Never write dev-narration, history, a hypothesis's consumer, or a claim about
how another file relates to this one (see the cruft rule below). Never add a
docstring to a definition that has been readable without one — a commit that
only adds docstrings is a commit that should not exist.

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
- **When you delete or rename, sweep for references in live code.** `grep` the
  packages you touched for the old file/symbol name and fix or remove every hit
  (docstrings, module-map comments, links) in the same change. Do this without
  being asked. The sweep stops at live code: `experiments/`, `docs/review/`,
  `docs/planning/` and every `archive/` describe the tree as it was on the day
  they were written. A dated document that no longer matches `main` is doing
  its job; editing it destroys the record.

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
- **Don't write like a model.** Everything Eduardo sends to another human —
  PR bodies, commit messages, issue comments, replies — must not carry the
  usual LLM tells. Banned outright: the contrast frame ("X rather than Y",
  "not X but Y", "this isn't A, it's B"); significance-grading ("load-bearing",
  "the operative reason", "worth noting", "importantly", "crucially",
  "genuinely", "precisely", "what matters here"); concessive openers ("that's
  correct, but", "while X, Y"); stacked em-dash asides; rhetorical three-part
  lists; meta-commentary ("nits, not blockers", "to be clear"); reassurance
  that something is fine, clean, or safe; and the filler words "actually",
  "simply", "just", "quite". State the fact and stop. Delete any sentence
  whose only job is to tell the reader how to feel about another sentence.
  Length follows from this: PR bodies say what the code does and, where there
  was a real choice, why — a small PR gets a lead sentence and three or four
  bullets, not a report. This applies to messages to Eduardo too.
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
