import LirLean.V2.Drive.CallPreservesSelf
import LirLean.V2.Modellable
import LirLean.Engine.CleanHalt

/-!
# LirLean spec surface — the tracked-debt register of seams (`Lir.Spec`)

The four **irreducible seams** of the exp005 conformance headline, re-exported under one
reviewer-facing namespace (`docs/headline-transitive-chain.md` §3; Wave 3 of
`docs/fleet-2026-07-02/reorg-legibility.md` §5 Step 3, Pattern C — this file sits
*downstream* of the proof modules by design and only `:=`-forwards their declarations;
nothing new is asserted).

Each seam below is a **supplied** hypothesis of the conditional headline
(`Spec/Conformance.lean`), not a discharged fact. The register exists so the debt is
named, typed, and drift-proof — each re-export is a definitional forwarder that
typechecks only while the underlying declaration keeps its shape.

The call-stream kernel (`Lir.V2.CallStream` / `BytecodeLayer.Hoare.CallReturns`) is
NOT re-registered here: it is already first-class spec surface via `Spec/Semantics.lean`
(the IR-side `CallStream`) and exp003's `Hoare.lean` (the bytecode-side `CallReturns`).
-/

namespace Lir.Spec

/-! ## Seam 1 — `SelfPresent` (the world-half residue of `SstoreRealises`)

The gas half of `SstoreRealises` is already discharged from a real run
(`Lir.materialise_runs_of_cleanHalt`); presence is the residue — do not overclaim more. -/

/-- **Seam 1: the self-account-presence world fact.** SSTORE reads storage through an
`.option 0` lens, so a successful SSTORE step never *witnesses* that the executing account
is present in the account map — presence is not a dispatch gate, hence irreducible from
the run itself. It is a genuine supplied world fact: seeded at the entry `codeFrame`
(`Lir.V2.selfPresent_codeFrame`, from the entry account lookup) and propagated forward by
`Lir.V2.selfPresent_runs_of_call`. Definitional forwarder of `Lir.V2.SelfPresent`
(`V2/Drive/SelfPresent.lean`). -/
def SelfPresent : Evm.Frame → Prop := Lir.V2.SelfPresent

/-! ## Seam 2 — `CallPreservesSelf` and its one surviving closer, the `hprec` shape -/

/-- **Seam 2: per-call self-presence preservation.** A returning external CALL keeps the
caller's self account present. 6 of its 7 framing closers are already discharged
engine-level (`Lir.V2.callPreservesSelf_modGuards`); only the precompile-immediate arm
(`PrecompilesPreservePresence` below) survives as a supplied input. Definitional
forwarder of `Lir.V2.CallPreservesSelf` (`V2/Drive/CallPreservesSelf.lean`). -/
def CallPreservesSelf : Prop := Lir.V2.CallPreservesSelf

/-- **The `hprec` seam shape, named.** A precompile-immediate CALL (`beginCall = .inr imm`)
preserves account presence: every account present in the call's input map is present in the
immediate result's map.

NOT unconditionally true: a live precompile's `.inr` arm really can return an account map
that erases entries (per the in-file docstrings of `V2/Drive/CallPreservesSelf.lean`), so
this must be instantiated per precompile set (addresses 1..10). It is vacuous for call-free
or non-precompile-targeting programs. The presence-side twin of `CallsCode` (Seam 3): that
seam gates the *dispatch* (no precompile is ever targeted), this one bounds the *world
effect* if one is. -/
def PrecompilesPreservePresence : Prop :=
  ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
    Evm.beginCall cp = .inr imm →
    ∀ a, Lir.V2.AccPresent a cp.accounts → Lir.V2.AccPresent a imm.accounts

/-- **The drift-proof binding of Seam 2 to its closer.** `PrecompilesPreservePresence` is
exactly the `hprec` binder of `Lir.V2.callPreservesSelf_modGuards` — this forwarder
typechecks only while the restated shape above stays definitionally equal to the real
hypothesis, so the register cannot silently drift from the proof. -/
theorem callPreservesSelf_of_precompiles :
    PrecompilesPreservePresence → CallPreservesSelf :=
  fun h => Lir.V2.callPreservesSelf_modGuards h

/-! ## Seam 3 — `CallsCode` (the dispatch-side precompile restriction) -/

/-- **Seam 3: every issued CALL targets a *code* account, never a precompile.** A genuine
runtime domain restriction: the CALL target is taken off the stack at run time, so an IR
callee whose materialised value is a precompile address `1..10` would violate it — it is
NOT structurally guaranteed by the lowering (contrast `NotCreate`, which IS discharged
structurally from the emitted bytes). The dispatch-gate twin of `hprec` (Seam 2); vacuous
for call-free programs. Definitional forwarder of `BytecodeLayer.Interpreter.CallsCode`
(`V2/Modellable.lean`). -/
def CallsCode : Evm.Frame → Prop := BytecodeLayer.Interpreter.CallsCode

/-! ## Seam 4 — `CleanHaltsNonException` (the scope premise, not an oracle) -/

/-- **Seam 4: the honest scope premise.** The frame's remaining run reaches, by a `Runs`
path, a `.halted` outcome that is NOT one of the 8 `ExecutionException` variants (OOG
etc.); REVERT is in scope. This is a *scope boundary*, not an oracle: a genuine
OOG/exception run is un-modellable by the gas-agnostic IR and falls outside conformance by
declaration. Supplied ONCE at the entry (grounded by `Lir.V2.cleanHalts_of_runWithLog`
from a successful recorded run) and propagated per-edge by
`Lir.V2.cleanHaltsNonException_forward` — not a per-edge assumption. Definitional
forwarder of `Lir.V2.CleanHaltsNonException` (`Engine/CleanHalt.lean`). -/
def CleanHaltsNonException : Evm.Frame → Prop := Lir.V2.CleanHaltsNonException

end Lir.Spec
