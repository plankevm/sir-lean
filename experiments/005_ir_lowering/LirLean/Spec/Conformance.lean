import LirLean.Spec.Recorder

/-!
# LirLean spec surface — conformance statement vocabulary

The **trusted statement vocabulary** of the exp005 conformance headline: the IR entry state, the
log-side clean-scope predicate, the observable-agreement conclusion, and the gas-introspection-free
scope. Hoisted out of the non-default WIP lib (`LirLean/V2/Realisability/Surface.lean`) so the
trusted surface can *state* what the project claims without depending on the sorry-carrying
skeleton. Every definition here is sorry-free.

The flagship theorem itself (`lower_conforms` and its `_exact`/`_gasfree` variants) and its
run-producer skeleton (R0–R12) remain in `LirLean/V2/Realisability/RealisabilitySpec.lean` (the
`WIP` lib) — this file holds only the vocabulary those statements are phrased in. The exact
whole-stream mirror (`RunFromLeft`/`RunFromAll`) lives next to `RunFrom` in `Spec/Semantics.lean`;
the realised oracle-stream entries (`evmV2CallEntry`/`evmV2CreateEntry`) in `Spec/CallEntry.lean`.

Scope note: `Lir.V2.callStreamOf` maps the WHOLE recorded `CallRecord` list to the consumed
`CallStream` (`realisedCall`), so calls are a positional multi-CALL stream — no single-CALL scope.

Still stranded in the WIP lib (blocked on later refactor stages — the seam bundle needs the
`CallsCode`/`AccPresent` proof modules relocated, plan §1D/§1E): `PrecompileAssumptions`,
`ReachableFrom`, and `WellFormedLowered`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter

/-- The IR entry state of a top-level call: empty locals, world = the recipient's storage
lens of the pre-call accounts (the `find?/lookupStorage` lens `resultStorageAt`/`observe`
read, applied to `params.accounts`). Replaces the supplied entry `StorageAgree` hypothesis
of the since-deleted `lower_conforms_wf` BY DEFINITION — the entry world *is* the params' lens (the pin is
then `rfl`-flavoured at the entry `codeFrame`, whose `accounts` are `params.accounts`).
DERIVED status: definitional (nothing to discharge). -/
def entryState (params : CallParams) : IRState :=
  { locals := fun _ => none
    world  := fun k => (params.accounts.find? params.recipient).option 0 (·.lookupStorage k) }

/-- **The log-side clean-scope predicate** (the flagship's `hclean`). The recorded run
halted cleanly: a top-level `.call` result that either succeeded or reverted with gas left.

Ground truth (`endCall`, exp003 `Evm/Semantics/Call.lean`): `.success → success := true`;
`.revert g o → success := false, gasRemaining := g`; `.exception → success := false,
gasRemaining := 0, output := .empty`. So an exception is distinguishable from a revert ON
THE LOG only via `gasRemaining ≠ 0` — **a genuine zero-gas revert is conservatively
excluded** (scope cut; sound: the hypothesis is then false and the flagship silent). The
fleet sketch's `ResultNonException` does not exist in the tree; this is its honest
decidable-on-the-log replacement. A `.create` observable is out of scope (top-level frames
here are calls). SUPPLIED status: a decidable premise read off the log (both branches are
`Bool`/`DecidableEq` facts). R2 turns it into the `∀ last halt`-universal
`cleanHalts_of_runWithLog` consumes. -/
def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

/-- **Full observable agreement** (the flagship's conclusion edge). The IR observable
agrees with the `observe` of the recorded bytecode result on **both** channels: the
world (self-account storage lens) AND the halt result — `observe`'s result is now live
(empty output ⇒ `.stopped`, else the RETURN window decoded back to `.returned w`; the
faithful inverse of the `ret` lowering, `Spec/Recorder.lean` `observe`). So `Conforms`
says the contract *behaves* the same, not merely that storage matches. DERIVED status:
the conclusion, not a premise. -/
def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world
  ∧ O.result = (observe self log.observable).result

/-- **Gas-introspection-free scope** (the co-flagship's `hng`): no statement reads `.gas`.
Static, decidable. Under it the realised gas stream plays no role (companion sorry:
`realisedGas_nil_of_noGasReads`), so the co-flagship needs no R1 — the de-risking
checkpoint (target-architecture decision 2). -/
def NoGasReads (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ (pc : Nat) (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) → e ≠ .gas

end Lir.V2
