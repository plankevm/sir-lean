import LirLean.V2.TieDischarge

/-!
# LirLean v2 — gas realisability regression witnesses (the retired universal vs. the honest form)

**Phase B resolved the gas vacuity at the source** (`docs/uniform-spill-alloc-plan.md` §6): gas is
now spilled to memory, so the conformance spine carries **no** gas universal — the gas value lives
in its slot and is tied by `MemRealises`, with the per-gas-cursor positional value (the consumed
read) supplied at the `assign` def-site (`sim_assign_gas`). The headline hypotheses
(`entry_corr`/`lower_conforms*`) no longer carry any `hgasr`.

This module is now the **regression record**: it keeps the two *proved* facts that motivated the
fix — (1) the OLD `Lir.GasRealises` universal (still defined in `MaterialiseRuns.lean`, but used
only here and in `V2/TieDischarge.lean`'s positional discharge, never in the spine) is
**unsatisfiable** for any genuine ≥2-distinct-read run; and (2) the honest **positional**
`Oracle.GasRealises` IS satisfiable by a real descending-gas run — checked against the two-read
milestone `g1Read g`/`g2Read g` of `V2/Mono.lean` (exposed through `gReads_realisable`). These stand
as the non-vacuity evidence for the design and guard against any regression to a constant-gas tie.

## The retired universal (`MaterialiseRuns.lean`, `Lir.GasRealises`)

The former spine tie carried a **single fixed** gas word `obs : Word`, stated as a **universal over
every same-address frame**:

```
Lir.GasRealises obs fr  :=  ∀ g, g.addr = fr.addr → obs = ofUInt64 (g.gasAvailable − Gbase)
```

A real EVM run's gas **strictly descends**, so two distinct GAS reads at the *same* address report
two *distinct* words. The universal then forces one word to equal both — it is **unsatisfiable**,
so carrying it at the entry frame made the headline vacuous on the gas axis. (Phase B removed it
from the spine entirely; the def survives only as this regression witness's subject.)

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

## The SLOAD twin (Phase C, `docs/uniform-spill-alloc-plan.md`)

The `SLOAD` warmth-cost universal `Lir.SloadRealises` (`MaterialiseRuns.lean`) carried the
**identical** defect, and is recorded here as the gas twin: it is **machine-checked
unsatisfiable** the moment a key is read cold-then-warm (the cost flips `2100 → 100`, forcing
one resolver to equal both — `sloadRealises_universal_unsatisfiable`); and the honest positional
`SloadLogAligned` form admits exactly that distinct two-charge list `[2100, 100]`
(`new_sloadLogAligned_two_read_satisfiable`). `sload_tie_vacuity_resolved` is the one-statement
contrast. These are the satisfiability re-audit witnesses for the Phase-C spill (the SLOAD value
moves to `MemRealises`, the warmth-cost tie becomes per-cursor positional).

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

/-! ## The Phase-B spilled-gas value tie is satisfiable per def-site by a real run

Phase B's `sim_assign_gas` ties the gas slot's stored value `ob` (the IR-bound consumed read) to
the **single** `GAS` opcode at the def-site frame: a real run produces `ob = ofUInt64 (fr.gas −
Gbase)` = `gasReadOf (gasFrame fr)` (`gasReadOf_gasFrame_eq_obs`). This is the honest **positional
one-read** value tie the slot/`MemRealises` channel carries — *one frame, one read*, trivially
realisable by every genuine descending-gas run (NOT a `∀`-over-frames constancy). Two distinct
gas reads at two def-sites store two distinct slot values — exactly what the deleted universal
forbade. -/

/-- **The Phase-B per-def-site gas value tie is realisable.** For *any* frame `fr` (with enough gas
for the `GAS` charge), the value a real run stores into the gas slot — `ofUInt64 (fr.gas − Gbase)` —
is exactly the def-site `GAS` opcode's output `gasReadOf (gasFrame fr)`. This is `sim_assign_gas`'s
stored value `ob` for a genuine run: a single read at a single frame, satisfiable for every frame
(no constancy). Two def-sites with descending gas store two *distinct* values (`g1Read ≠ g2Read`
specialises this) — the multi-read case the old universal could not satisfy. -/
theorem spilled_gas_value_tie_realisable (fr : Frame) :
    gasReadOf (gasFrame fr)
      = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) :=
  gasReadOf_gasFrame_eq_obs fr

/-! ## SLOAD: the same vacuity, the same honest fix (Phase C subject)

The `SLOAD` warmth-cost tie is the exact twin of the gas value tie, and carried the **same**
defect. The spine's `Lir.SloadRealises sloadChg st fr` (`MaterialiseRuns.lean`) is a
**universal over every same-address frame**:

```
Lir.SloadRealises sloadChg st fr  :=
  ∀ g k key, g.addr = fr.addr → st.locals k = some key →
    sloadChg k = sloadCost (g.substate.accessedStorageKeys.contains (g.addr, key))
```

The SLOAD cost is **warmth-dependent**: `sloadCost false = Gcoldsload = 2100` on the first
(cold) read of a key, `sloadCost true = Gwarmaccess = 100` on every later (warm) read — the
`accessedStorageKeys.contains` flag flips after the first access. So a run that reads the
**same key twice** (cold then warm) supplies two same-address frames forcing the single
resolver `sloadChg k` to equal *both* `2100` and `100`: the universal is
**machine-checked unsatisfiable**. Carried through `Corr`, it poisons every headline at any
cursor that re-reads a key.

The honest fix is the **positional** SLOAD form `SloadLogAligned sloadAcc frs` (`SLOAD`'s twin
of `Oracle.GasRealises`, `V2/TieDischarge.lean`): `sloadAcc = frs.map sloadWarmthOf ∧
FramesRun frs` — the i-th supplied cost = the i-th bytecode SLOAD's *actual* warmth-charge, no
constancy. A cold-then-warm two-read run is then *in scope*: it carries the distinct list
`[2100, 100]`, which the positional form admits and the universal forbade. This mirrors the gas
contrast above (`gas_tie_vacuity_resolved`) exactly. -/

/-- **The OLD universal `Lir.SloadRealises` is unsatisfiable abstractly.** Given any two
same-address frames `g₁` (the key is **cold** — `accessedStorageKeys` does not contain it) and
`g₂` (the key is **warm** — it does), both reading the *same* bound key, the
universal-over-same-address predicate forces `sloadChg k = 2100` (from `g₁`, cold) **and**
`sloadChg k = 100` (from `g₂`, warm) — impossible for *every* `sloadChg`. A real run that reads
the same key twice (cold then warm) supplies exactly such a `g₁`/`g₂`. This is the
warmth-constant falsehood the §0 principle forbids; the `Corr.sloadReal` / entry `hsload`
hypothesis cannot hold for any such run. -/
theorem sloadRealises_universal_unsatisfiable {st : V2.IRState} {sloadChg : Tmp → ℕ}
    {fr g₁ g₂ : Frame} {k : Tmp} {key : Word}
    (haddr₁ : g₁.exec.executionEnv.address = fr.exec.executionEnv.address)
    (haddr₂ : g₂.exec.executionEnv.address = fr.exec.executionEnv.address)
    (hbound : st.locals k = some key)
    -- `g₁` reads the key COLD (not yet accessed); `g₂` reads it WARM (already accessed):
    (hcold : g₁.exec.substate.accessedStorageKeys.contains
                (g₁.exec.executionEnv.address, key) = false)
    (hwarm : g₂.exec.substate.accessedStorageKeys.contains
                (g₂.exec.executionEnv.address, key) = true) :
    ¬ Lir.SloadRealises sloadChg st fr := by
  intro huniv
  -- the universal at the cold frame forces `sloadChg k = sloadCost false = 2100`.
  have h1 : sloadChg k = 2100 := by
    have := huniv g₁ k key haddr₁ hbound
    rw [hcold] at this
    rw [this]; rfl
  -- the universal at the warm frame forces `sloadChg k = sloadCost true = 100`.
  have h2 : sloadChg k = 100 := by
    have := huniv g₂ k key haddr₂ hbound
    rw [hwarm] at this
    rw [this]; rfl
  -- `2100 = 100` is false.
  rw [h1] at h2; exact absurd h2 (by decide)

/-- **The NEW positional `SloadLogAligned` admits a cold-then-warm two-read run.** Given two
`Runs`-threaded frames `g₁` (cold) and `g₂` (warm) reading the *same* key, the positional sload
form carries the genuinely-distinct charge list `[2100, 100]` — exactly the multi-read case the
universal could not satisfy. The honest content is only "supplied = actually-charged, in order"
(`sloadAcc = [g₁, g₂].map sloadWarmthOf`), with the frames `Runs`-threaded (`FramesRun`). No
warmth constancy is assumed; the two charges are *allowed* to differ, which is the whole point. -/
theorem new_sloadLogAligned_two_read_satisfiable {g₁ g₂ : Frame} {key : Word}
    (hrun : Runs g₁ g₂)
    (hk₁ : g₁.exec.stack.head? = some key)
    (hk₂ : g₂.exec.stack.head? = some key)
    (hcold : g₁.exec.substate.accessedStorageKeys.contains
                (g₁.exec.executionEnv.address, key) = false)
    (hwarm : g₂.exec.substate.accessedStorageKeys.contains
                (g₂.exec.executionEnv.address, key) = true) :
    SloadLogAligned [2100, 100] [g₁, g₂]
    ∧ (2100 : ℕ) ≠ 100 := by
  refine ⟨⟨?_, ?_⟩, by decide⟩
  · -- `[2100, 100] = [g₁, g₂].map sloadWarmthOf`: cold frame ↦ 2100, warm frame ↦ 100.
    have hw₁ : sloadWarmthOf g₁ = 2100 := by
      simp only [sloadWarmthOf, hk₁, hcold]; rfl
    have hw₂ : sloadWarmthOf g₂ = 100 := by
      simp only [sloadWarmthOf, hk₂, hwarm]; rfl
    simp [List.map, hw₁, hw₂]
  · -- `FramesRun [g₁, g₂]`: the two frames are `Runs`-threaded.
    exact ⟨hrun, trivial⟩

/-- **`sload_tie_vacuity_resolved`.** The SLOAD twin of `gas_tie_vacuity_resolved`, in one
statement: (1) the honest positional `SloadLogAligned` of a cold-then-warm two-read run carries
the genuinely-distinct charge list `[2100, 100]` (and those charges differ); while (2) the
spine's single-resolver universal `Lir.SloadRealises` is **unsatisfiable** the moment a run
reads the same key cold then warm (which every genuine same-key re-read does). Same kind of run;
new form satisfied, old form refuted — exactly the gas contrast, on the SLOAD axis. -/
theorem sload_tie_vacuity_resolved {g₁ g₂ : Frame} {key : Word}
    (hrun : Runs g₁ g₂)
    (hk₁ : g₁.exec.stack.head? = some key)
    (hk₂ : g₂.exec.stack.head? = some key)
    (hcold : g₁.exec.substate.accessedStorageKeys.contains
                (g₁.exec.executionEnv.address, key) = false)
    (hwarm : g₂.exec.substate.accessedStorageKeys.contains
                (g₂.exec.executionEnv.address, key) = true) :
    (SloadLogAligned [2100, 100] [g₁, g₂] ∧ (2100 : ℕ) ≠ 100)
    ∧ (∀ {st : V2.IRState} {sloadChg : Tmp → ℕ} {fr : Frame} {k : Tmp},
          g₁.exec.executionEnv.address = fr.exec.executionEnv.address →
          g₂.exec.executionEnv.address = fr.exec.executionEnv.address →
          st.locals k = some key →
          ¬ Lir.SloadRealises sloadChg st fr) :=
  ⟨new_sloadLogAligned_two_read_satisfiable hrun hk₁ hk₂ hcold hwarm,
   fun haddr₁ haddr₂ hbound =>
     sloadRealises_universal_unsatisfiable haddr₁ haddr₂ hbound hcold hwarm⟩

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the vacuity / non-vacuity deliverables.
#print axioms Lir.V2.g1Read_ne_g2Read
#print axioms Lir.V2.gasRealises_universal_unsatisfiable
#print axioms Lir.V2.new_gasRealises_two_read_satisfiable
#print axioms Lir.V2.gas_tie_vacuity_resolved
#print axioms Lir.V2.spilled_gas_value_tie_realisable
#print axioms Lir.V2.sloadRealises_universal_unsatisfiable
#print axioms Lir.V2.new_sloadLogAligned_two_read_satisfiable
#print axioms Lir.V2.sload_tie_vacuity_resolved
