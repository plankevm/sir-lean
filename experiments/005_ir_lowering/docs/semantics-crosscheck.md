# Three-Way EVM Semantics Consistency Audit

**References:** Yellow Paper (YP, Cancun/Shanghai) vs. EVMYulLean (NethermindEth `EvmYul`, exp004 base) vs. our EVMLean (exp003 bytecode base, exp005 conformance target).
**Method:** behavioral-contract comparison by reading code (input-state → output: world/account-map, stack, gas, substate, halting outcome). Read-only; no build, no edits. Adversarially verified each candidate divergence against YP text / EIPs where contested.
**Date:** 2026-06-29. **Scope:** 6 dimensions — BASELINE, CREATE, CALL, STATE, HALT, GAS, COREOPS.

> **HONESTY BANNER.** This is a best-effort *behavioral* audit by reading two Lean models, **not** a formal equivalence proof. Confidence is per-dimension below. The YP PDF did not reliably text-extract via web tooling on several attempts; for the contested CREATE/STATE failure-state equations we relied on the YP `Paper.tex` source plus EVMYulLean's own inline YP-equation annotations (treated as a faithful YP proxy per the audit method), supplemented by EIP text where parseable.

---

## 1. Executive Summary

**Overall verdict: our patched EVMLean is behaviorally consistent with EVMYulLean and the Yellow Paper on every opcode and state transition exp005 depends on.** Across all six dimensions, the two Lean models share an identical Cancun fee schedule (`GasConstants.lean` is byte-identical), the same opcode/instruction set and arities, and the same observable input→output contracts for CREATE, the CALL family, precompiles, SELFDESTRUCT/halts, gas metering, and the core lowered opcodes.

**Headline: no divergence threatens exp005 soundness.** Every candidate divergence that survived adversarial verification is either (a) a non-observable internal exception-tag / evaluation-order difference that the YP itself does not constrain, or (b) confined to a near-unreachable model-artifact arm (RLP address-derivation failure, fuel exhaustion). In the two places where a *real* world-state divergence stands up, **EVMLean is the YP-faithful side**, and the difference lives on arms that exp005's lowering never exercises.

**Two genuine (standing) divergences**, both with EVMLean more faithful, both non-threatening:
- **CREATE-2 / CREATE-BEGINFAIL-1** — EVMYulLean's CREATE dispatch wipes the *caller* `accountMap := ∅` on a `Lambda`-`.error` (reachable only via L_A/RLP address-derivation failure or OutOfFuel); EVMLean preserves the caller checkpoint. YP §7 mandates `σ' ≡ σ` (caller world unchanged) on creation failure — **EVMLean is faithful, EVMYulLean's ∅ is not** on that arm.
- This is exactly the arm our **CREATE patch** targets — see §2.

**Our CREATE patch is CONFIRMED faithful and load-bearing** (§2): changing the `beginCreate=.error` driver arm from `accounts := ∅` to `accounts := caller checkpoint` converges EVMLean toward both EVMYulLean's *real* begin-failure arms and the YP soft-failure contract, AND is what makes exp005's `drive_accounts_find_mono` provable (`AccPresent a ∅` is false; the old ∅ would break SSTORE/SelfPresent presence soundness).

No upstream fix is *required* for exp005. One **upstream-candidate** observation for EVMYulLean (its `accountMap := ∅` failure arm is YP-unfaithful where reachable) is noted in §5 for the Nethermind maintainers, not for us.

---

## 2. Our CREATE Patch Adjudication

**The patch.** EVMLean's drive loop `.needsCreate` / `beginCreate = .error` arm (`BytecodeLayer/.../Interpreter.lean:63-82`) was changed from `accounts := ∅` (empty map) to `accounts := pending.frame.exec.accounts` (the caller's pre-CREATE checkpoint). `resumeAfterCreate` (`EVMLean/.../Create.lean:166-168`) then writes `result.accounts` straight back into the resumed caller, leaving the caller world **unchanged**, pushing 0.

**Claim:** this converges toward EVMYulLean (whose CREATE begin-failure arms return caller `evmState` unchanged) and toward the YP soft-failure (push 0, caller world unchanged).

**Verdict: CONFIRMED — faithful AND load-bearing.**

1. **Faithful vs YP.** YP §7 (Contract Creation), eq. (115): on creation failure `F ∨ σ**=∅`, `σ' ≡ σ` — the caller world reverts to its pre-creation state; the prose states a failed/aborted creation leaves the state "as it was immediately prior to attempting the creation." The YP never wipes the whole caller world to ∅ (the only ∅ is the *intermediate* sentinel `σ**` and `σ'[a]=∅` removing the single new account in the DEAD case). The patched arm (caller map unchanged) matches this; the pre-patch ∅ did not. (Source: YP `Paper.tex`, ethereum/yellowpaper; PDF unparseable, relied on TeX + EVMYulLean inline (113)-(118) annotations.)

2. **Faithful vs EVMYulLean's real arms.** EVMYulLean's actual begin-failure arms — nonce overflow (`Semantics.lean:253`) and precondition-not-met (`:287-288`) — return `evmState` with `accountMap` **UNCHANGED**, push 0. The patched EVMLean arm now matches.

3. **EVMLean's normal begin-failures were ALREADY faithful.** `createArm` (`System.lean:99-122`) soft-fails *in place* via the `failed` path (`failed.accounts := accounts`, un-bumped caller map, `gasRemaining := L(gas)`, push 0) — emitting `.next`, never `.needsCreate`. This is the YP "otherwise" branch exactly, and the patch does not touch it. The patched driver arm is a *separate, near-unreachable* path.

4. **The patched arm is near-dead.** `beginCreate`'s only `.error` is `Create.lean:36` (`contractAddressBytes = none` → RLP/address-preimage derivation failure). RLP-encoding `[creator, nonce]` never fails for well-formed inputs; CREATE2's salt path is unconditionally `.some`. So this arm fires on no real EVM state.

5. **Load-bearing for exp005.** `drive_accounts_find_mono`'s CREATE-fault arm (`TieDischarge.lean:3578-3590`) establishes `AccPresent a result.accounts` from `result.accounts = pending.frame.exec.accounts`. With the old `∅`, `AccPresent a ∅` is **false** (`AccPresent := ∃ acc, find? a = some acc`, `TieDischarge.lean:1803`), so the lemma — and thus `SelfPresent` / SSTORE-presence soundness — would be **unprovable**. The patch makes it provable while *removing* a latent unfaithfulness.

**Residual (non-fatal).** The patched arm sets `gasRemaining := 0` (`Interpreter.lean:78`) whereas the YP / EVMYulLean / `createArm`'s own path return `L(gas)`. This deviates from YP `g' = L(µg)` — but only on the unreachable RLP-failure branch, so it is observationally moot. *Optional* cleanup, not a soundness issue.

---

## 3. Ranked Divergence Table (STOOD UP under verification)

Only two candidates survived adversarial verification as **real divergences**. Both: EVMLean is the YP-faithful side; neither threatens exp005.

| # | Severity | Topic | EVMLean does | EVMYulLean does | YP-faithful | YP/EIP citation | Affects exp005? |
|---|----------|-------|--------------|-----------------|-------------|-----------------|-----------------|
| 1 | **moderate** (cosmetic in practice) | **CREATE caller-world on `Lambda`-`.error` begin/derivation failure** (CREATE-2 / CREATE-BEGINFAIL-1 / STATE) | Preserves caller checkpoint: `beginCreate=.error` (post-patch) → `accounts := pending.frame.exec.accounts`; `endCreate` rolls all init-code failures to `checkpoint.accounts`. Never ∅. | Dispatch catch-all (`Semantics.lean:286`/`:344`) sets caller `accountMap := ∅` whenever `Lambda` returns `.error`. Reachable only via `L_A`=none (RLP/address-derivation) or OutOfFuel. | **EVMLean** | YP §7 eq.(115): `σ' ≡ σ` on creation failure; only ∅ is the intermediate `σ**` / single-account `σ'[a]=∅`, never the whole caller world. EIP-3860/7610 govern checks, not the failure-state. | **No.** exp005 never exercises RLP-derivation failure or fuel exhaustion; EVMLean (the conformance base) has no ∅-world path. The patch makes EVMLean's side both faithful and provable. |
| 2 | low | (same divergence, init-code-failure facet) | `endCreate .revert/.exception` → `checkpoint.accounts`, `.revert` keeps revert gas, `.exception` zeroes gas | `Lambda` `.ok(z=false)` on real init-code OOG/exception/revert returns *original σ* (`Semantics.lean:659-663`) — faithful and **agrees with EVMLean** here | both (agree) | YP §7 / EIP-140 (REVERT) | No |

**Notes on #1.** The candidate's EVMYulLean description initially missed that the `:286`/`:344` ∅ arm is reachable on `L_A`=none (not only OutOfFuel) — corrected during verification. On that *reachable* input the two models give a genuinely different observable `accountMap` (∅ vs caller checkpoint), so it stands as a real divergence — but it is the YP-unfaithful side that diverges (EVMYulLean), it is near-unreachable, and EVMLean's `seedFuel`/no-fuel regime plus exp004's `Θ_never_outOfFuel` proof exclude the OutOfFuel facet entirely from the conformance regime.

**Brutal-honesty caveat.** Divergence #1's "real" status rests on whether `L_A`/RLP-derivation failure is *ever* reachable in practice. I believe it is not (a 20-byte address + ≤8-byte nonce always RLP-encodes; a client whose address derivation failed would itself abort). If truly unreachable it downgrades to vacuous. It is marked standing because the code paths demonstrably differ *where defined*.

---

## Appendix A — False Positives / Encoding-Only (did NOT stand up)

All of the following were investigated and refuted as behavioral divergences — same observable contract, different code shape / evaluation strategy / non-observable exception tag. None affect exp005.

| ID | Topic | Why it's not a divergence |
|----|-------|---------------------------|
| FORK-1 | Monolithic `C'` (EVMYulLean) vs distributed inline `charge` (EVMLean) | Same per-opcode gas values; spot-checked SSTORE/SLOAD/EXP/SELFDESTRUCT/CREATE/CALL/base groups all equal. YP Appendix H defines C as one piecewise fn; both faithful. |
| FORK-2 | `parseInstr : UInt8 → Operation` vs `→ Option Operation` | EVMYulLean's `parseInstr` returns `some _` for *every* byte (no `none` arm in the byte table); the genuine `Option` is at the outer `decode` (PC-past-end → STOP) in both. YP §9.4.1, EIP-141. |
| CREATE-1 | `beginCreate=.error` patched arm (begin-failure world) | Real begin-failure goes through `createArm` (`.next`, faithful), not this arm. Patched arm is the near-dead RLP-failure path; patch is a cosmetic convergence on a dead branch. YP §9.4.2 CREATE 0xf0 "otherwise" branch. |
| CREATE-3 | Init-code REVERT gas/returndata accounting | Field-by-field identical: raw revert gas (no deposit charge), output as returndata, push 0, caller world rolled back, 63/64 reservation. EIP-140. |
| CREATE-LAMBDA-EMPTY-2 | EVMYulLean `accountMap := ∅` as *OutOfFuel-only* artifact | Distinct from #1: on the OutOfFuel facet the arm is provably dead in exp005's regime (exp004 `Θ_never_outOfFuel`); fuel is not a YP concept. (The *reachable* L_A facet is what stands up as divergence #1.) |
| CALL-STATIC-ORDER | StaticModeViolation-first (EVMLean) vs OutOfGas-first (EVMYulLean) for gas-starved static value-CALL | YP §9.4.2 `Z` is a precedence-free disjunction with no exception tags; both produce the YP all-gas-consumed/revert outcome. Tag not observable. |
| CALL-SELFDESTRUCT-WHALT | SELFDESTRUCT as halting opcode (empty output) | Both: frame ends success, returndata empty, world effects committed. YP `H` predicate. Code shape only. |
| CALL-FAIL-GAS-3 / SD-1 / SD-2 | CALL begin-failure substate; static-vs-OOG order for SELFDESTRUCT; dead INVALID/`No 'self'` arms | Warmed substate retained + caller map untouched (identical); unordered-`Z` tag difference (unobservable); dead/defensive arms produce no state change. EIP-2929, YP `Z`, EIP-141. |
| GAS-CREATE-BEGINFAIL-1 / GAS-CREATE-INITFAIL-1 | Gas envelope on CREATE begin/init failure | Gas identical (`gas − L(gas) + g'`); `L = allButOneSixtyFourth = n − n/64` shared. EIP-150. (Map representation is the STATE concern → divergence #1.) |
| OVERFLOW-OOG-ORDER-1 / UNDERFLOW-OOG-ORDER-2 / MEMEXP-OVERFLOW-3 | Stack-overflow-vs-OOG / underflow-vs-OOG tag order; bounded-UInt64 guard vs unbounded-ℕ blow-up for memory-expansion | Exception tag erased at every boundary; all paths → exceptional halt, gas burned, caller world unchanged. Both reject oversized offset with OOG. Unreachable for well-formed lowered code. YP `Z`, Appendix H. |

---

## 4. Per-Dimension Consistency Summary

| Dimension | Verdict | Confidence | Deeply checked | Sampled | Not reached |
|-----------|---------|------------|----------------|---------|-------------|
| **BASELINE** (fork/opcodes/constants) | Consistent | high | opcode inductive sets (full enum, both files end-to-end); opcode→byte tables (all fork-sensitive + System block); δ-arity tables (line-by-line); `GasConstants.lean` (byte-identical); cost fns sstore/exp/selfdestruct/sload/callGas*/create/intrinsic; 63/64 rule; initcode cap | base-cost group assignments (grepped key fork ops, not every charge site) | α push-count tables beyond grep; EIP-6780 state effect (HALT dim); `memoryExpansionCost` M-equality (structure only) |
| **CREATE/CREATE2** | Consistent (1 standing divergence, EVMLean faithful) | high | `createArm`, `beginCreate`/`endCreate`/`resumeAfterCreate` (full), driver CREATE arm incl. patch; EVMYulLean CREATE/CREATE2 dispatch + `Lambda` + L_A + result types | exact create-cost constants (assumed equal; GAS dim owns) | literal YP (113)-(118) PDF text (relied on `Paper.tex` + EVMYulLean annotations) |
| **CALL family + precompiles** | Consistent | high | operand wiring (all 4 ops); 63/64 cap byte-for-byte; depth/balance precond + not-taken world; value transfer; success-flag x; returndata write; static write-set + perm propagation; precompile set 1..10, `toExecute`, all 10 bodies, hprec output-map seam | crypto FFI internals (wrappers + gas/branch matched, underlying Rust not diffed); numeric gas-constant magnitudes (formula refs matched) | full YP/geth cross-check for static-vs-gas precedence |
| **STATE** (checkpoint/revert/substate) | Consistent (1 standing divergence = #1, EVMLean faithful) | high | CALL + CREATE state-threading (full); drive loop + patched arm; exp005 consumer `drive_accounts_find_mono` + `AccPresent` + CREATE-fault arm; `==∅` sentinel; checkpoint snapshot point; EIP-7610 line-by-line | precompile substate; createdAccounts/EIP-6780 threading (structural) | blockchain-test vectors; `Υ` tx finalization; **SELFDESTRUCT account-deletion world effect not compared this pass — flagged for separate audit**; REVERT-in-staticcall returndata edge on EVMLean side |
| **HALT** (SELFDESTRUCT/halts) | Consistent | high | `Halt.lean` (selfdestruct/return-revert/halt), dispatcher, INVALID/overflow interception, endCall/endCreate halt arms, drive halt routing, finalization erase, selfdestructCost; EVMYulLean H/X/Z/Θ/Λ + finalization + createdAccounts | precompile CALL arms; `lookupAccount`/`dead` defs (same-named, assumed identical) | literal YP text for static-vs-gas order (EVMYulLean inline cites as proxy) |
| **GAS** | Consistent | high | full fee schedule (byte-identical); `Cₘ` + M; EIP-2929 warm/cold; SSTORE cost + EIP-2200/3529 refund-delta; tx-level /5 refund cap + post-processing; CALL gas (63/64+stipend+Cextra); CREATE gas (EIP-3860 word cost, 49152 guard, reconciliation); EXP/KECCAK/copy/LOG/intrinsic; SELFDESTRUCT; TSTORE/TLOAD; JUMPDEST | per-opcode base buckets (dispatch route confirmed, not every constant re-derived) | precompile internal gas formulas (route confirmed only; low relevance — exp005 gas-agnostic via oracle) |
| **COREOPS** (exp005's lowered ops) | Consistent | high | ADD, LT, PUSH32/PUSH0, MLOAD, MSTORE, GAS, STOP, RETURN, SLOAD, SSTORE (cost+refund+warmth+guards), JUMP, JUMPI, JUMPDEST, jump-validity set; gas-charge ORDERING; confirmed exp005's *actually-emitted* opcode set = exactly this list (grep over `LirLean/`); GAS-push = `gasAvailable − Gbase` matches | `UInt256.add/lt` limb impl (relied on stated BitVec256-equiv); `writeBytes`/`readWithPadding` byte-exactness (shared fn shapes) | CALL/CREATE world effects (other dims); precompiles; tx-level `Υ` |

**Cross-cutting limits of this audit (honest).** (1) Read-only — no build, no test execution, no proof replay; lemma locations in `TieDischarge.lean` were taken on the comparator's description and are *consistent with* the confirmed data-flow but not independently re-checked by running Lean. (2) The YP PDF was not reliably text-extractable; contested failure-state equations lean on `Paper.tex` + EVMYulLean's inline annotations as a YP proxy. (3) Crypto-precompile FFI internals were matched at the Lean-wrapper/gas/branch level, not at the underlying Rust level (assumed identical by shared upstream lineage). (4) SELFDESTRUCT's *account-deletion* world transition (vs. the gas/refund/halting facets, which were checked) was **not** compared this pass.

---

## 5. Recommended Actions

**exp005 (us) — no blocking action.**
- ✅ Keep the CREATE patch — confirmed faithful (YP §7 `σ'≡σ`) and load-bearing for `drive_accounts_find_mono`. No change needed.
- ⚠️ *Optional cleanup:* the patched arm's `gasRemaining := 0` (`Interpreter.lean:78`) deviates from YP `g' = L(gas)` on the unreachable RLP-failure branch. Harmless (arm is dead) but inconsistent with `createArm`'s own `failed` path; align to `L(gas)` if/when touching that code.
- 🔎 *Follow-up audit (separate pass):* compare **SELFDESTRUCT's account-deletion / selfDestructSet erase world transition** between the two models end-to-end. The HALT dimension confirmed the *opcode-body* contract (no in-opcode `RBMap.erase`, erase deferred to tx finalization — matching exp005's hhalt claim) and the gas/refund facets, but did **not** trace the finalization-time account-deletion world effect, and the STATE dimension explicitly deferred it. Low risk (exp005 doesn't lower SELFDESTRUCT-driven deletion), but it touches the account map.

**EVMYulLean (upstream-candidate, for Nethermind — NOT required for exp005).**
- The CREATE/CREATE2 dispatch catch-all (`Semantics.lean:286`/`:344`) sets the **caller** `accountMap := ∅` on any `Lambda` `.error`. On the *reachable* `L_A`/RLP address-derivation-failure path this contradicts YP §7 (`σ'≡σ`) AND EVMYulLean's own `Lambda` arms (which return original σ on every real init-code failure). EVMLean's checkpoint rollback is the faithful behavior. A maintainer fix would replace `accountMap := ∅` with the caller's pre-create σ. Flag for a Nethermind semantics maintainer.

**Needs a human semantics expert (low priority).**
- Confirm whether `L_A`/RLP address-derivation failure is *ever* truly reachable on a well-formed transaction. If provably unreachable, divergence #1 downgrades from "real" to "vacuous" and both models are effectively equivalent on CREATE failure.
- Settle the static-mode-vs-OOG exception-*tag* precedence (CALL-STATIC-ORDER, SD-1, OVERFLOW/UNDERFLOW-OOG) against a reference client (geth/EELS) if any future conformance statement ever asserts exception-*kind* equality. Currently unobservable and YP-unconstrained, so no action while exp005 observes only world/gas/halting outcomes.

---

### Project-lead summary (≤15 lines)

1. Verdict: our patched EVMLean is behaviorally consistent with EVMYulLean and the Yellow Paper across all six audited dimensions.
2. `GasConstants.lean` is byte-identical between the two models; opcode set, arities, and Cancun EIPs (2929/2200/3529/3860/1153/6780/7610/4844/150) all match.
3. No divergence threatens exp005 soundness. Every survivor is either a non-observable exception-tag/eval-order difference (YP-unconstrained) or a near-unreachable model-artifact arm.
4. Exactly TWO real divergences stood up — both on CREATE/STATE failure arms, and on BOTH our EVMLean is the YP-faithful side.
5. The standing divergence: EVMYulLean wipes the caller world to ∅ on a CREATE Lambda-error (reachable via RLP address-derivation failure); EVMLean keeps the caller checkpoint — YP §7 requires σ'≡σ. Upstream-candidate fix for Nethermind, NOT for us.
6. Our CREATE patch (beginCreate=.error: ∅ → caller checkpoint) is CONFIRMED faithful (YP §7) AND load-bearing: the old ∅ made `AccPresent a ∅` false and would break SSTORE/SelfPresent presence soundness in `drive_accounts_find_mono`.
7. All 13 opcodes exp005 actually lowers (ADD, LT, SLOAD, SSTORE w/ EIP-2200/2929 warmth, GAS, MLOAD, MSTORE, PUSH32, JUMP, JUMPI, JUMPDEST, RETURN, STOP) match contract-for-contract, incl. GAS-push = `gasAvailable − Gbase`.
8. Confidence: high on all six dimensions; this is a read-only behavioral audit, not a formal proof.
9. Honesty limits: YP PDF didn't text-extract — contested CREATE failure-state equations lean on YP Paper.tex + EVMYulLean's inline YP annotations as proxy.
10. Action items for us: keep the patch (no change); optional gas cleanup on the dead RLP-failure arm; one follow-up pass on SELFDESTRUCT account-deletion world effect (not compared this round).
11. No human-semantics-expert escalation required for soundness; one optional question (is RLP-derivation failure ever reachable?) would downgrade the lone divergence to vacuous.
12. Full report: `experiments/005_ir_lowering/docs/semantics-crosscheck.md`.
