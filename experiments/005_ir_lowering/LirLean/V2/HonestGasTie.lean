import LirLean.V2.TieDischarge

/-!
# LirLean v2 — the honest (non-vacuous) gas realisability, contrasted with the spine's

This module makes the **vacuity defect** of the spine's `Corr`-carried gas tie precise, and
exhibits the **honest positional form** that replaces it, both *proved* — the vacuity abstractly
(for any genuine ≥2-distinct-read run), and the non-vacuity concretely against a real
descending-gas run (the two-read milestone `g1Read g`/`g2Read g` of `V2/Mono.lean`, exposed through
`gReads_realisable`).

## The defect (`MaterialiseRuns.lean`, `Lir.GasRealises`)

The spine carries a **single fixed** gas word `obs : Word` through `Corr`, with the realisability
predicate stated as a **universal over every same-address frame**:

```
Lir.GasRealises obs fr  :=  ∀ g, g.addr = fr.addr → obs = ofUInt64 (g.gasAvailable − Gbase)
```

A real EVM run's gas **strictly descends**, so two distinct GAS reads at the *same* address report
two *distinct* words. The universal then forces one word to equal both — it is
**unsatisfiable**. Carried at the entry frame (`entry_corr`/`lower_conforms*`'s `hgasr`
hypothesis), it makes the conformance headline **vacuous on the gas axis**: the hypothesis it
quantifies over cannot hold for any run that reads gas more than once.

`gasRealises_universal_unsatisfiable` proves this abstractly: a *single* later same-address frame
whose GAS-output word differs already refutes the universal, for every `obs`.

## The honest form (`V2/Oracle.lean`, `Oracle.GasRealises`)

The honest tie is **positional / streamed** (the CompCert external-call discipline): the supplied
gas stream `T` equals, *in order*, the words the bytecode's GAS opcodes actually pushed, and the
witness frames are `Runs`-threaded:

```
Oracle.GasRealises T frs  :=  T = frs.map gasReadOf  ∧  FramesRun frs
```

Nothing about the *values* is assumed — not constancy, not monotonicity (monotonicity is a
*derived* consequence, `GasRealises.monotoneGas ⟵ Runs.gasAvailable_le`). The only content is the
positional tie "the i-th supplied read = the i-th bytecode read." This is **satisfiable by a
genuine descending-gas run**: `new_gasRealises_two_read_satisfiable` exhibits the witness for a
real two-read run whose two reads are *distinct*.

`gas_tie_vacuity_resolved` states the contrast in one place against the same milestone run.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Hoare
open Lir

/-! ## The two milestone reads are genuinely distinct (gas descended)

`g1Read g`/`g2Read g` are the words the milestone's two GAS opcodes pushed; the second read
happened after one more `Gbase` charge, so they differ whenever the balance is large enough that
the two subtractions stay in range. Distinctness of the *words* is what makes the universal
unsatisfiable and is the hallmark of a genuine descending-gas run. -/

/-- The two milestone GAS reads are **distinct** for a sufficiently-funded run: their `.toNat`s are
`g.toNat − 22108` and `g.toNat − 22110` (one extra `Gbase`), which differ in range. The `≥ 30000`
funding keeps both subtractions from wrapping, so the words differ. Proved through the *public*
`g1Read`/`g2Read` definitions and `toNat_ofUInt64` only. -/
theorem g1Read_ne_g2Read (g : UInt64) (hg : 30000 ≤ g.toNat) :
    g1Read g ≠ g2Read g := by
  intro heq
  have htoNat : (g1Read g).toNat = (g2Read g).toNat := by rw [heq]
  -- `g1Read g = ofUInt64 (subCharges g [3,3,22100,2])`, sum 22108; `g2Read` adds one `2`.
  have h1 : (g1Read g).toNat = g.toNat - 22108 := by
    show (UInt256.ofUInt64 (subCharges g [3, 3, 22100, 2])).toNat = _
    rw [toNat_ofUInt64, toNat_subCharges g [3, 3, 22100, 2] (by
      show ([3, 3, 22100, 2] : List ℕ).sum ≤ g.toNat
      show (22108:ℕ) ≤ g.toNat; omega)]
    show g.toNat - ([3, 3, 22100, 2] : List ℕ).sum = _
    show g.toNat - 22108 = _; rfl
  have h2 : (g2Read g).toNat = g.toNat - 22110 := by
    show (UInt256.ofUInt64 (subCharges g [3, 3, 22100, 2, 2])).toNat = _
    rw [toNat_ofUInt64, toNat_subCharges g [3, 3, 22100, 2, 2] (by
      show ([3, 3, 22100, 2, 2] : List ℕ).sum ≤ g.toNat
      show (22110:ℕ) ≤ g.toNat; omega)]
    show g.toNat - ([3, 3, 22100, 2, 2] : List ℕ).sum = _
    show g.toNat - 22110 = _; rfl
  rw [h1, h2] at htoNat
  omega

/-! ## The OLD universal is vacuous — abstractly, and against the real run

The spine's `Lir.GasRealises obs fr` is `∀ g, g.addr = fr.addr → obs = ofUInt64 (g.gas − Gbase)`.
A *single* second frame `fr'` with `fr'.addr = fr.addr` whose GAS-output word differs from `fr`'s
already refutes it: the universal at `fr` forces `obs = ofUInt64 (fr.gas − Gbase)`, the universal at
`fr'` forces `obs = ofUInt64 (fr'.gas − Gbase)`, and these differ. A genuine run with two GAS reads
at the same self-address (gas strictly descending) supplies exactly such an `fr'`. -/

/-- **The OLD universal `Lir.GasRealises` is unsatisfiable abstractly.** Given any second
same-address frame `fr'` whose GAS-output word `ofUInt64 (fr'.gas − Gbase)` differs from `fr`'s, the
universal-over-same-address predicate at `fr` is false for *every* `obs`. (A real run with two
distinct same-address GAS reads is precisely this situation — the universal demands one constant gas
word.) This is the constant-gas falsehood the §0 principle forbids; the entry hypothesis `hgasr` of
the conformance headline cannot hold for any such run. -/
theorem gasRealises_universal_unsatisfiable {fr fr' : Frame} {obs : Word}
    (haddr : fr'.exec.executionEnv.address = fr.exec.executionEnv.address)
    (hne : UInt256.ofUInt64 (fr'.exec.gasAvailable - UInt64.ofNat Gbase)
         ≠ UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) :
    ¬ Lir.GasRealises obs fr := by
  intro huniv
  apply hne
  rw [← huniv fr' haddr, ← huniv fr rfl]

/-! ## The NEW positional form is satisfiable — by a *real* two-read run

`Oracle.GasRealises` ties the supplied stream to the *list* of GAS-output words in order, with the
witness frames `Runs`-threaded. The milestone's two **distinct** reads `[g1Read g, g2Read g]` are
exactly the reported words of two `Runs`-threaded GAS-frames (`gReads_realisable`), so the
positional tie **holds** — for a genuine descending-gas run. This is `Oracle.guard_gasRealises`
re-exposed as the "non-vacuity" half of the contrast. -/

/-- **The NEW positional `Oracle.GasRealises` is satisfiable by a real two-read run.** The
distinct, descending two-read stream `[g1Read g, g2Read g]` (`g1Read_ne_g2Read`) is realised by two
`Runs`-threaded GAS-frames whose `gasReadOf` words are exactly those reads. The honest tie encodes
only "supplied = actually-read, in order"; monotonicity is then a *consequence*
(`GasRealises.monotoneGas`), never an assumption. -/
theorem new_gasRealises_two_read_satisfiable (g : UInt64) (hg : 30000 ≤ g.toNat) :
    ∃ frs : List Frame, _root_.Lir.V2.GasRealises [g1Read g, g2Read g] frs :=
  guard_gasRealises g hg

/-! ## The contrast, in one statement

The honest positional `Oracle.GasRealises` is *satisfiable* by a real two-read run, while the
spine's single-`obs` universal is *unsatisfiable* the moment a run has two distinct same-address GAS
reads (which every genuine descending-gas multi-read run does). The vacuity is gone exactly because
the tie became positional. -/

/-- **`gas_tie_vacuity_resolved`.** Both halves of the fix in one place: (1) the honest positional
`Oracle.GasRealises` of two genuinely-distinct, descending reads `[g1Read g, g2Read g]` **holds**
for a real run (`g ≥ 30000`); and (2) the spine's single-`obs` universal `Lir.GasRealises` is
**unsatisfiable** as soon as two same-address frames report distinct GAS-output words — which a real
multi-read run always provides (the `g1Read g ≠ g2Read g` distinctness is the concrete instance).
Same kind of run; new form satisfied, old form refuted. -/
theorem gas_tie_vacuity_resolved (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (∃ frs : List Frame, _root_.Lir.V2.GasRealises [g1Read g, g2Read g] frs)
    ∧ g1Read g ≠ g2Read g
    ∧ (∀ {fr fr' : Frame} {obs : Word},
          fr'.exec.executionEnv.address = fr.exec.executionEnv.address →
          UInt256.ofUInt64 (fr'.exec.gasAvailable - UInt64.ofNat Gbase)
            ≠ UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) →
          ¬ Lir.GasRealises obs fr) :=
  ⟨new_gasRealises_two_read_satisfiable g hg,
   g1Read_ne_g2Read g hg,
   fun haddr hne => gasRealises_universal_unsatisfiable haddr hne⟩

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the vacuity / non-vacuity deliverables.
#print axioms Lir.V2.g1Read_ne_g2Read
#print axioms Lir.V2.gasRealises_universal_unsatisfiable
#print axioms Lir.V2.new_gasRealises_two_read_satisfiable
#print axioms Lir.V2.gas_tie_vacuity_resolved
