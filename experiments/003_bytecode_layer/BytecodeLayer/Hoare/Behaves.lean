import Evm
import BytecodeLayer.Observables

/-!
# `Behaves` — the for-all-programs behavior predicate at the messageCall boundary

The current specs are about fixed `CallParams`. The generalization plan
(`docs/generalization-plan.md`) needs statements quantified **over programs**,
with gas and structure as **preconditions** and a **named** `Outcome` (never a
raw `.ok`). `Behaves` is that predicate.

## The "world"

A run's world is its entry point: a `CallParams` carries the account map (hence
all storage), the gas budget, caller/recipient, calldata — everything a
precondition could constrain. So `World := CallParams`, and a precondition is a
`World → Prop`. The plan writes the predicate `pre` first: `Behaves pre code post`.

## Gas is a precondition, kept first-class

`Behaves pre code post` says: for **every** entry `p` running `code`
(`p.codeSource = .Code code`) whose world satisfies `pre p`, the named outcome of
`messageCall p` satisfies `post`. The **gas-respecting** hypothesis is *part of*
`pre`: e.g. the call rule `behaves_call` supplies a `∃G₀`-style gas floor. Gas is
never erased — it appears, visibly, in the `pre` the caller must discharge. Because
the conclusion ranges over `Outcome`, a `post` may legitimately *require* `completed`
(no top-level exception).
-/

namespace BytecodeLayer.Hoare
open Evm

/-- The world a `messageCall` runs against: its entry parameters (account map and
hence all storage, gas budget, caller, calldata, …). Preconditions are predicates
on it. -/
abbrev World : Type := CallParams

/-- `Behaves pre code post` (precondition first): for **every** entry `p` whose
code is `code` and whose world satisfies `pre`, the **named** outcome of
`messageCall p` satisfies `post`.

The gas-respecting requirement is carried inside `pre` (e.g. `cost code ≤ p.gas`),
so gas stays first-class and program-agnostic; `post` ranges over the named
`Outcome`, so no statement reads as `= .ok …`. -/
def Behaves (pre : World → Prop) (code : ByteArray) (post : Outcome → Prop) : Prop :=
  ∀ p : World, p.codeSource = .Code code → pre p → post (Outcome.ofCall (messageCall p))

end BytecodeLayer.Hoare
