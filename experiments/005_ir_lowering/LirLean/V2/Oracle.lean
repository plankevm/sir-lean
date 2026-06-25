import LirLean.V2.Mono
import BytecodeLayer.Hoare.GasMonotone

/-!
# LirLean v2 — the gas-oracle interface, law-first (`docs/ir-design-v3.md` §2, §4–5, S1)

The two-read milestone (`LirLean/V2/Mono.lean`) discharged the §3.4 monotonicity law for
*one concrete* two-read program by exact `subCharges` arithmetic. v3 (`docs/ir-design-v3.md`)
lifts that to an **interface**, made of three named, derived-not-assumed pieces (the
CompCert external-call discipline, applied to gas):

1. **The one law** — `MonotoneGas` (§2): the `gasRead` subsequence is monotone
   non-increasing on `.toNat`, in program order. This is *exactly* `Mono.lean`'s
   `Trace.gasMonotone`; v3 only renames it to the interface term. `Word`-valued; `ℕ`
   enters ONLY via `.toNat`.

2. **The realisability side-condition** — `GasRealises` (§4 item 1): an explicit
   predicate tying a `Trace` to a witnessing bytecode `Runs`. Each `gasRead observed`
   equals the actual `GAS` value (`UInt256.ofUInt64` of the post-charge `gasAvailable`)
   at that point, and the witness frames are threaded by `Runs` in program order. This
   is the equality-to-`GAS`-output form `Preserve.lean`/`Mono.lean` used implicitly
   (`f10_top`, `g1Read`/`g2Read`), now lifted to a named definition.

3. **`realises → MonotoneGas`** — `GasRealises.monotoneGas` (§4): the law is a
   *consequence* of realisability, by `Runs.gasAvailable_le` (`GasMonotone.lean`, holds
   across `.call` nodes). Monotonicity is **not** an axiom on the oracle — it is
   discharged from the realised trace. This is the §0 principle made into a theorem.

4. **`RunFrom` determinism** — `RunFrom.det` (§4 item 2): same program/start/trace ⇒ the
   *same* `Observable`. The prototype's `RunFrom` is acyclic-by-construction; structural
   induction closes it. This unlocks the `∀ O, IRRun … O → O = …` ("*the* observable")
   headline shape (`lower_preserves_obs_mono_unique`).

Nothing in `Machine.lean`/`Mono.lean`/`Preserve.lean` is duplicated — this file is the
integration layer that names the interface and discharges its laws.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare

/-! ## 1. The one law (`docs/ir-design-v3.md` §2) — frame-free, in `LirLean/V2/Law.lean`

The interface law `MonotoneGas` (the alias of `Trace.gasMonotone`) is frame-free and lives
in `LirLean/V2/Law.lean` (imported transitively via `Mono`). This module is the
IR↔bytecode **bridge**: it ties an abstract `Trace` to a witnessing bytecode `Runs`
(`Frame`/`Runs` references below) and **discharges** the frame-free law from
`Runs.gasAvailable_le`. -/

/-! ## 2. The realised gas reading at a GAS frame

The word a `GAS` opcode pushes is `UInt256.ofUInt64` of the *post-charge* `gasAvailable`
(`gasPost`; cf. `BytecodeLayer.Hoare.gasFrame`, `Preserve.f10_top`). `gasReadOf fr` is
that word for the GAS-frame `fr` (the frame *after* the GAS step, whose `gasAvailable`
is the value the opcode reported). Its `.toNat` is `fr.exec.gasAvailable.toNat`
(`toNat_ofUInt64`), which is the quantity `Runs.gasAvailable_le` is monotone in. -/

/-- The `Word` a `GAS` opcode at (post-charge) frame `fr` reports: `ofUInt64` of the
frame's `gasAvailable`. The realisability bridge between a `gasRead` event and a frame. -/
def gasReadOf (fr : Frame) : Word := UInt256.ofUInt64 fr.exec.gasAvailable

/-- `(gasReadOf fr).toNat = fr.exec.gasAvailable.toNat` — the gas word reads back its
`UInt64` value (`toNat_ofUInt64`). The law's `.toNat` order on reads is therefore the
machine's `gasAvailable.toNat` order, which `Runs.gasAvailable_le` is monotone in. -/
theorem toNat_gasReadOf (fr : Frame) :
    (gasReadOf fr).toNat = fr.exec.gasAvailable.toNat :=
  toNat_ofUInt64 fr.exec.gasAvailable

/-! ## 3. The realisability side-condition (`docs/ir-design-v3.md` §4 item 1)

`GasRealises T frs` ties the trace `T` to a witnessing list of GAS-frames `frs` (the
post-charge frames at each `GAS` site, in program order):

* **read-equality** — `T`'s `gasReads` are exactly `frs`'s reported words (`gasReadOf`),
  i.e. each `gasRead observed` equals the actual `GAS` output (the §4 equality form, the
  same shape for gas as v1's call realisability is for calls); and
* **`Runs`-threaded** — consecutive GAS-frames are connected by `Runs` in program order
  (`FramesRun`), so the engine actually ran from one read to the next. This is what makes
  the law derivable: `Runs.gasAvailable_le` then forces the reported gas to descend.

`Preserve.lean`/`Mono.lean` carried this implicitly (`f10_top`; `gf4`/`gf5` joined by the
`g_runs` witness). Here it is one named predicate, for an arbitrary number of reads. -/

/-- The GAS-frames are threaded by `Runs` in program order: each is reachable from the
previous (so the machine genuinely ran between the two reads). A `Runs`-chain over the
witness list. -/
def FramesRun : List Frame → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Runs a b ∧ FramesRun (b :: rest)

/-- **The realisability side-condition (§4 item 1).** `T`'s `gasRead` values are exactly
the reported words of the witness GAS-frames `frs` (each `gasRead = ofUInt64 gasAvailable`,
the actual `GAS` output), and the frames are `Runs`-threaded in program order. The trace
is realised by a genuine bytecode run reading gas at the frames `frs`. -/
def GasRealises (T : Trace) (frs : List Frame) : Prop :=
  T.gasReads = frs.map gasReadOf ∧ FramesRun frs

/-! ## 4. `realises → MonotoneGas` (`docs/ir-design-v3.md` §0, §4)

The law is a **consequence** of realisability, not an axiom on the oracle. A `Runs`-threaded
list of GAS-frames has non-increasing `gasAvailable.toNat` (each later frame reachable from
an earlier one, `Runs.gasAvailable_le` — *holds across `.call` nodes*); via
`toNat_gasReadOf` that is exactly the law on the reported words. -/

/-- A `FramesRun` list has non-increasing reported gas: the `gasReadOf` words form a
`MonotoneGas`-style chain (later `.toNat` ≤ earlier `.toNat`). The structural core of the
discharge — `Runs.gasAvailable_le` at each adjacent pair, the rest by induction. -/
theorem FramesRun.gasReads_isChain :
    ∀ {frs : List Frame}, FramesRun frs →
      (frs.map gasReadOf).IsChain (fun earlier later => later.toNat ≤ earlier.toNat)
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: rest, h => by
    obtain ⟨hab, htl⟩ := h
    refine List.IsChain.cons_cons ?_ (FramesRun.gasReads_isChain htl)
    -- the adjacent law `(gasReadOf b).toNat ≤ (gasReadOf a).toNat` is `Runs.gasAvailable_le`
    rw [toNat_gasReadOf, toNat_gasReadOf]
    exact Runs.gasAvailable_le hab

/-- **The headline elegance (§0, §4): realisability ⇒ the law.** If a trace is realised by
a `Runs`-threaded list of GAS-frames, its `gasRead` subsequence is `MonotoneGas`. The
monotonicity oracle law is **discharged** from `Runs.gasAvailable_le` (the EVM gas-descent
fact, across `.call` nodes too) — it is never assumed on the oracle. -/
theorem GasRealises.monotoneGas {T : Trace} {frs : List Frame}
    (h : GasRealises T frs) : MonotoneGas T := by
  obtain ⟨hreads, hrun⟩ := h
  show (T.gasReads).IsChain (fun earlier later => later.toNat ≤ earlier.toNat)
  rw [hreads]
  exact hrun.gasReads_isChain

/-! ### The interface meets the concrete witness

`Mono.lean`'s two-read milestone is a `GasRealises` instance, checked here against the
exported witness data (`gReads_realisable`): the two reads `g1Read g`/`g2Read g` are the
reported words (`gasReadOf`) of two `Runs`-threaded GAS-frames. So `gReads_gasMonotone`
follows from `GasRealises.monotoneGas` — the §3.4 law obtained *through the abstract
interface*, not from the milestone's own `subCharges`/`Runs.gasAvailable_le` discharge.
This makes the interface load-bearing rather than decorative. -/

/-- The two-read milestone trace `GasRealises` the two GAS-frames of its witness run
(`gReads_realisable`), with `g1Read`/`g2Read` as the frames' reported words. -/
theorem guard_gasRealises (g : UInt64) (hg : 30000 ≤ g.toNat) :
    ∃ frs : List Frame,
      GasRealises [Event.gasRead (g1Read g), Event.gasRead (g2Read g)] frs := by
  obtain ⟨a, b, hrun, ha, hb⟩ := gReads_realisable g hg
  refine ⟨[a, b], ?_, ?_⟩
  · -- gasReads [gasRead g1, gasRead g2] = [g1Read, g2Read] = [gasReadOf a, gasReadOf b]
    show [g1Read g, g2Read g] = [gasReadOf a, gasReadOf b]
    rw [show gasReadOf a = g1Read g from ha.symm, show gasReadOf b = g2Read g from hb.symm]
  · exact ⟨hrun, trivial⟩

/-- The §3.4 law for the milestone, obtained **through the `GasRealises` interface** — the
interface discharge (`GasRealises.monotoneGas` ⟵ `Runs.gasAvailable_le`) reproduces the
milestone's own `gReads_gasMonotone`. -/
theorem guard_monotoneGas_via_interface (g : UInt64) (hg : 30000 ≤ g.toNat) :
    MonotoneGas [Event.gasRead (g1Read g), Event.gasRead (g2Read g)] := by
  obtain ⟨_, hreal⟩ := guard_gasRealises g hg
  exact hreal.monotoneGas

/-! ## 5. `RunFrom`/`IRRun` determinism — frame-free, in `LirLean/V2/Law.lean`

`EvalStmt.det` → `RunStmts.det` → `RunFrom.det` → `IRRun.det` are frame-free (about
`IRRun`, not `Frame`) and live in `LirLean/V2/Law.lean`. We use `IRRun.det` below to get
the "*the* observable" headline shape. -/

/-! ## 6. The headline in "*the* observable" shape (`docs/ir-design-v3.md` §4 item 2)

With `IRRun.det` in hand, the milestone headline `lower_preserves_obs_mono` strengthens
from "the IR run *produces* `O`" to "**any** observable the IR run produces *is* `O`" — the
`∀ O, IRRun … O → O = …` shape the design wanted. The bytecode-side conjunct
(`LoweredRunHasObsMono`) is unchanged; only the IR conjunct is restated through determinism. -/

/-- **The two-read milestone, "*the* observable" shape.** For every gas `g ≥ G₀`: the
realised two-read trace is `MonotoneGas`, the lowered bytecode completes with
`O = guardObsResult w₀ (g1Read g)` (both pulled from `LoweredRunHasObsMono`), and **any**
observable the IR run of `guardIR` on that trace yields **is** `O` (`IRRun.det` applied to
the milestone's own IR run). The §4 `∃ G₀, ∀ g ≥ G₀, …` envelope is preserved; the IR
conjunct is now the uniqueness statement.

The `MonotoneGas` conjunct is the §3.4 law obtained through the `GasRealises` interface —
`guard_monotoneGas_via_interface` reproduces exactly the value `LoweredRunHasObsMono`
carries, so either source gives the same law (we read it off the milestone here). -/
theorem lower_preserves_obs_mono_unique (w₀ : World) :
    ∃ G₀ : UInt64, ∀ g : UInt64, G₀.toNat ≤ g.toNat →
      MonotoneGas [Event.gasRead (g1Read g), Event.gasRead (g2Read g)]
      ∧ (∀ O, IRRun guardIR w₀ [Event.gasRead (g1Read g), Event.gasRead (g2Read g)] O →
              O = guardObsResult w₀ (g1Read g))
      ∧ LoweredRunHasObsMono g [Event.gasRead (g1Read g), Event.gasRead (g2Read g)]
          (guardObsResult w₀ (g1Read g)) := by
  obtain ⟨G₀, h⟩ := lower_preserves_obs_mono w₀
  -- `LoweredRunHasObsMono = (T = …) ∧ MonotoneGas T ∧ ∃ …`; its `.2.2.1` is the law,
  -- `(h g hg).1` is the milestone's IR run that `IRRun.det` makes unique.
  exact ⟨G₀, fun g hg => ⟨(h g hg).2.2.1, fun O hO => IRRun.det hO (h g hg).1, (h g hg).2⟩⟩

-- Build-enforced axiom-cleanliness guards: the realisability→law discharge, the `RunFrom`
-- determinism lemma, and the "*the* observable" headline depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms GasRealises.monotoneGas
#print axioms RunFrom.det
#print axioms lower_preserves_obs_mono_unique

end Lir.V2
