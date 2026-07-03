import LirLean.Spec.Seams
import LirLean.V2.Drive.Headline
import Batteries.Tactic.Alias

/-!
# LirLean spec surface — the conditional conformance headline (`Lir.Spec`)

The transitional (Pattern C) audit surface over the exp005 headline
(`V2/Drive/Headline.lean`): the two conditional headline theorems re-exported under
`Lir.Spec`, and their supplied-hypothesis list bundled as one named `Prop`
(`RealisabilityObligations`) so the debt is a single reviewable object.

## HONESTY — read before citing anything in this file

* **Every field of `RealisabilityObligations` is currently SUPPLIED, not discharged.**
  Nothing in the default build produces a `RealisabilityObligations` term for
  `lower prog` from a real run; the headline theorems below are *conditionals* whose
  antecedents no in-tree producer satisfies.
* **The supplied `StmtTies`/`TermTies` were shown UNSATISFIABLE for essentially every
  nonempty program** (2026-07-02 audit fleet, adversarially verified): the repeated
  free-`∀` shape — the gas conjunct's free `ob`, the sload conjunct's free `w`, the
  assign conjunct's free `st0'`/`MemRealises` demand plus the spilled-gas-assign static
  contradiction, and `TermTies`' un-pinned `Corr`-frame demands — forces contradictory
  instances. See `docs/target-architecture-2026-07-02.md` §1 and
  `docs/fleet-2026-07-02/skeptic-f1-verdict.md`. **The conditional headline is therefore
  VACUOUS as stated**: this structure is a register of the debt, not a claim of truth.
* **The plan of record** is the reshaped R0–R12 obligation surface in
  `LirLean/V2/RealisabilitySpec.lean` (the `Nightly` sorry-carrying lib), which
  supersedes these shapes.
* Scope note: `Lir.V2.callOracleOf` reads only the *first* `CallRecord` of the log —
  the realised call oracle is single-CALL scope.
-/

namespace Lir.Spec

open Evm
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-- **The supplied-obligation bundle of the assembled headline** — a register of debt,
NOT a claim of truth (see the module docstring: nothing in the default build produces a
term of this structure for `lower prog` from a real run, and the `stmtTies`/`termTies`
fields were shown UNSATISFIABLE for essentially every nonempty program, making the
conditional headline vacuous as stated; the reshaped R0–R12 surface in
`LirLean/V2/RealisabilitySpec.lean` supersedes these shapes).

Field types are copied verbatim from `Lir.V2.lower_conforms_cyclic_assembled`'s
hypothesis list (frozen in `Audit.lean`'s `#check` guard); the bundled forwarder
`lower_conforms_cyclic_of_obligations` typechecks only while they stay aligned. The
Type-valued `RunDefinable prog` and the entry facts (`DriveCorr`, the recipient lookup)
stay curried — this bundle is `Prop`-valued. -/
structure RealisabilityObligations (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (o : V2.CallOracle) (self : Evm.AccountAddress) : Prop where
  /-- The purely-structural fuel/pc/offset/slot side-conditions (satisfiable; the
  acyclic-program producer is `Lir.wellFormedLowered_of_acyclic`). -/
  wellFormed : WellFormedLowered prog
  /-- The §7 per-block statement ties — SUPPLIED and (as shaped) unsatisfiable for
  essentially every nonempty program (free-`∀` `ob`/`w`/`st0'` + the spilled-gas-assign
  static contradiction). -/
  stmtTies : ∀ (L : Label) (b : Block), V2.blockAt prog L = some b →
    StmtTies prog sloadChg obs o L b
  /-- The §7 per-block terminator ties — SUPPLIED and (as shaped) unsatisfiable for
  essentially every nonempty program (un-pinned `Corr`-frame demands). -/
  termTies : ∀ (L : Label) (b : Block), V2.blockAt prog L = some b →
    TermTies prog sloadChg obs o self L b
  /-- Seam 2: per-call self-presence preservation (obtainable from
  `Lir.Spec.callPreservesSelf_of_precompiles` given the per-precompile-set `hprec`). -/
  callSelf : V2.CallPreservesSelf
  /-- Cursor-label presence at every `DriveCorrPlus` boundary (static CFG
  well-formedness). -/
  blockPresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label)
      (gasAcc : List Word) (gasFrs : List Frame)
      (sloadAcc : List ℕ) (sloadFrs : List Frame),
    V2.DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
    ∃ b, V2.blockAt prog L = some b
  /-- `jump` destination presence (static CFG well-formedness). -/
  jumpPresent : ∀ (L : Label) (b : Block), V2.blockAt prog L = some b →
    ∀ (dst : Label), b.term = .jump dst →
      ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst
  /-- `branch` successor presence, both targets (static CFG well-formedness). -/
  branchPresent : ∀ (L : Label) (b : Block), V2.blockAt prog L = some b →
    ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
      (∃ bthen : Block, prog.blocks.toList[thenL.idx]? = some bthen)
      ∧ (∃ belse : Block, prog.blocks.toList[elseL.idx]? = some belse)
  /-- The `branch` cond-materialise stack-room fold (a static charge-length bound, not
  gas-derivable). -/
  stkBranch : ∀ (L : Label) (b : Block), V2.blockAt prog L = some b →
    ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
      (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024

/-- **Re-export of the tie-free conditional headline** (`Lir.V2.lower_conforms_cyclic_tiefree`,
`V2/Drive/Headline.lean`). CONDITIONAL: its per-block `SimStmtStep`/`SimTermStep`
universals are supplied opaquely; see the module docstring — no in-tree producer
discharges them for `lower prog`. -/
alias lower_conforms_cyclic_tiefree := Lir.V2.lower_conforms_cyclic_tiefree

/-- **Re-export of the assembled conditional headline**
(`Lir.V2.lower_conforms_cyclic_assembled`, `V2/Drive/Headline.lean`). CONDITIONAL and —
because its supplied `StmtTies`/`TermTies` antecedents are unsatisfiable for essentially
every nonempty program — VACUOUS as stated (module docstring;
`docs/target-architecture-2026-07-02.md` §1). -/
alias lower_conforms_cyclic_assembled := Lir.V2.lower_conforms_cyclic_assembled

/-- **The bundled form of the assembled headline.** Pure application of
`Lir.V2.lower_conforms_cyclic_assembled` to the fields of a `RealisabilityObligations`
bundle — no new supplied hypothesis, no weakened conclusion, and the same honesty caveat:
the bundle's tie fields are unsatisfiable as shaped, so no in-tree producer can invoke
this with a real run. The entry facts (`hbase`, `hwf`) and the Type-valued `hdef` stay
curried. -/
theorem lower_conforms_cyclic_of_obligations {prog : Program} {sloadChg : Tmp → ℕ}
    {obs : Word} {o : V2.CallOracle} {self : Evm.AccountAddress}
    {st₀ : V2.IRState} {T : V2.Trace} {params : Evm.CallParams} {code : ByteArray}
    {acc : Evm.Account}
    (hbase : V2.DriveCorr prog sloadChg obs st₀ (codeFrame params code) prog.entry)
    (hwf : params.accounts.find? params.recipient = some acc)
    (hdef : V2.RunDefinable prog)
    (h : RealisabilityObligations prog sloadChg obs o self) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs (codeFrame params code) last
        ∧ Evm.stepFrame last = .halted haltSig
        ∧ (V2.observe self (Evm.endFrame last haltSig)).world = O.world)
      ∧ V2.RunFrom prog o st₀ T prog.entry O :=
  -- (Destructuring match rather than `h.field` dot-notation: the structure parameter
  -- named `self` shadows the projections' record binder of the same name.)
  match h with
  | ⟨hwfl, hstmtties, htermties, hcallSelf, hpresent, hjumpPresent, hbranchPresent,
     hstkBranch⟩ =>
    Lir.V2.lower_conforms_cyclic_assembled hbase hwf hdef hcallSelf hpresent
      hwfl hstmtties htermties hjumpPresent hbranchPresent hstkBranch

end Lir.Spec
