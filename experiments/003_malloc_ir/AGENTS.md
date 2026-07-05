- Do not add comments that restate what the code already says. Comment only non-obvious rationale or invariants.
- Spec readability is the top priority. The audit surface is `Spec.lean` plus every definition its statements reach; optimize those for human review, not proof convenience.
- Keep the proof layer separate: proof-internal definitions, invariants, and equivalence/characterization lemmas live in `Proof.lean` and must never appear in spec statements.
- In proofs, do not unfold spec definitions directly; go through a characterization lemma so the spec can be reshaped without breaking the proof corpus.
- In spec-leaf definitions prefer named combinators (`map`, `guard`, `foldlM`) over `do`/inline closures; the sugar elaborates to anonymous matchers that lemmas cannot target.

## `grind`

The `grind` tactic is your hammer, it automatically closes a bunch of goals, try
it all the time, it makes proofs more concise.
