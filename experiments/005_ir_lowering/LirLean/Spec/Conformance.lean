/-!
# LirLean spec surface — conformance (VACUOUS SURFACE DELETED 2026-07-03)

This module used to re-export the exp005 cyclic conformance headline
(`Lir.V2.lower_conforms_cyclic_assembled` / `lower_conforms_cyclic_tiefree`) under `Lir.Spec`
and bundle its supplied hypotheses as `RealisabilityObligations`.

That entire surface was **DELETED** on 2026-07-03. The supplied `StmtTies`/`TermTies`
antecedents were shown UNSATISFIABLE for essentially every nonempty program (the repeated
free-`∀` shape — the gas conjunct's free `ob`, the sload conjunct's free `w`, the assign
conjunct's free `st0'`/`MemRealises` demand plus the spilled-gas-assign static contradiction,
and `TermTies`' un-pinned `Corr`-frame demands), so the conditional headline was **VACUOUS as
stated** — a register of debt, not a claim of truth. See `docs/final-audit-2026-07-03.md`,
`docs/target-architecture-2026-07-02.md` §1, and `docs/fleet-2026-07-02/skeptic-f1-verdict.md`.

**The sole conformance surface is now `LirLean/V2/Realisability/RealisabilitySpec.lean`** — the reshaped
R0–R12 obligation skeleton (the `WIP` sorry-carrying lib), whose ties are DERIVED from the
run (R10a/R10b) rather than supplied. Scope note: `Lir.V2.callStreamOf` maps the WHOLE recorded
`CallRecord` list to the consumed `CallStream` (`realisedCall`), so calls are a positional
multi-CALL stream — no single-CALL scope.

This file is retained as a stub so the canonical conformance path resolves to this honest
notice rather than a missing module.
-/
