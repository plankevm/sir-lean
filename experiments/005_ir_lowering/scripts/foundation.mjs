export const meta = {
  name: 'exp005-foundation',
  description: 'Strengthen the conformance theorem at the FOUNDATION with no tech debt: (1) remove the nonzero-SSTORE restriction, (2) replace the single-call function-oracle with a consumed call STREAM, (3) model the FULL observable (return value + halt kind, not just storage) — re-proving ALL breakage. Sequential, easiest-first, hard no-new-sorry/no-new-hypothesis gate; stops if a fix cannot land clean.',
  phases: [
    { title: 'nonzero-sstore' },
    { title: 'call-stream' },
    { title: 'full-observable' },
  ],
}

const WT = '/Users/eduardo/workspace/evm-semantics/.worktrees/foundation/experiments/005_ir_lowering'

const OPEN_LEAVES = `callRealises_of_recorded, the R6 boundary bricks (in runs_atReachableBoundary's edge lemmas), stmtTies'_of_runWithLog, lower_conforms / lower_conforms_exact / lower_conforms_gasfree, realisedGas_nil_of_noGasReads, exProg_satisfies_hypotheses, exProg_nonvacuity`

const RULES = `GLOBAL RULES (honesty-critical — this branch exists BECAUSE a vacuous theorem was caught and deleted):
- Work ONLY in ${WT} (git branch 'foundation'). Warm APFS CoW .lake: \`cd ${WT} && lake build\` (default LirLean, sorry-free spine) and \`lake build Nightly\` (the WIP conformance lib = LirLean/RealisabilitySpec.lean) are INCREMENTAL (minutes; run in background if >8min). Never \`lake update\`, never delete .lake, never push.
- The change must STRENGTHEN the theorem: REMOVE the target restriction/hypothesis. You may NEVER add a new hypothesis, restriction, or scope cut to make a proof go through, and NEVER weaken a conclusion.
- NO NEW TECH DEBT. The default LirLean library MUST stay green AND sorry-free — you must RE-PROVE every proof your change breaks. The ONLY sorries permitted anywhere are the pre-existing tracked OPEN LEAVES in RealisabilitySpec.lean (${OPEN_LEAVES}); those must be RESTATED faithfully for the new foundation (updated types), NOT deleted, NOT given new hypotheses. Introducing ANY new sorry / admit / native_decide / axiom is FORBIDDEN.
- If you genuinely cannot finish without a shortcut (new sorry / new hypothesis / weakened statement / definitional hack), STOP and put a precise honest blocker in 'blocker'. An honest STOP beats shipping debt.
- Commit to 'foundation' ONLY when default \`lake build\` is green + sorry-free AND \`lake build Nightly\` is green (the open leaves may emit 'declaration uses sorry' warnings — that is expected; NO OTHER declaration may). Commit message: 'exp005 foundation <id>: ...'. Never push.`

const FIXES = [
  {
    id: 'nonzero-sstore',
    title: 'nonzero-sstore',
    goal: `Remove the "SSTORE writes a nonzero value" restriction so the theorem covers zero writes (clearing a slot).`,
    detail: `WHERE IT LIVES: the lowered-SSTORE simulation carries \`hnz : vw ≠ 0\` — LirLean/SimStmt.lean:372 and LirLean/LowerDecode.lean:155 (SstoreRealises + hnz), surfaced up through LowerConforms.lean:479 (\`∧ vw ≠ 0\`) and threaded into the conformance spec as the \`NonzeroSstores\` predicate (RealisabilitySpec.lean:576), the \`DriveCorrLog.nonzeroSstores\` field (:665), and the flagships' \`hnzw\` hypothesis. NOTE the IR semantics EvalStmt.sstore (Spec/Semantics.lean:179) is ALREADY unconditional (handles vw=0) — so this is purely a gap in the bytecode SIMULATION proof, almost certainly the EVM SSTORE zero-write (SSTORE_CLEAR / refund) gas edge that the nonzero case dodged.
TASK: extend the SSTORE simulation lemma(s) to the vw=0 case (prove the lowered SSTORE matches EvalStmt.sstore when vw=0 too — handle whatever gas/decode fact the nonzero proof used \`hnz\` for). Then DELETE \`NonzeroSstores\`, \`DriveCorrLog.nonzeroSstores\`, the \`∧ vw ≠ 0\` conjunct, the \`hnz\` hypotheses, and every flagship's \`hnzw\` hypothesis + the \`hnzw\` conjunct in exProg_satisfies_hypotheses. Sweep all now-dangling references.
DONE = default build green+sorry-free, Nightly green, and \`grep -rn "NonzeroSstores\\|vw ≠ 0\\|hnzw" LirLean/\` returns nothing (except maybe historical prose you should also clean).`,
  },
  {
    id: 'call-stream',
    title: 'call-stream',
    goal: `Remove the single-external-call restriction (SingleCall / hsingle / hone) by replacing the function-shaped call oracle with a CONSUMED STREAM, exactly mirroring how gas already works.`,
    detail: `ROOT CAUSE: \`abbrev CallOracle := Word → Word → World → (World × Word)\` (Spec/Semantics.lean:96) is a FUNCTION — it returns the same result for the same (callee, gasFwd, world), so two dynamic calls to the same address with the same visible inputs but different EVM outcomes are indistinguishable, and \`realisedCall\` reads only the FIRST recorded CallRecord. That FORCES ≤1 call.
THE TEMPLATE ALREADY EXISTS: gas is a consumed stream — \`GasOracle := List Word\` (Trace), threaded head-first through EvalStmt/RunStmts/RunFrom as the \`T → T'\` argument (Spec/Semantics.lean). Do the SAME for calls.
TASK: redesign \`CallOracle\` as a consumed stream of recorded call-results (e.g. \`List (World × Word)\` consumed head-first, threaded alongside the gas Trace — pick the cleanest representation consistent with the existing gas threading). Update: EvalStmt.call (consume the head call-result instead of applying a function), RunStmts / RunFrom / IRRun (thread the call-stream like T), the determinism proofs (Law.lean), and \`realisedCall\` / \`callOracleOf\` (produce the FULL stream from log.calls, not just the head). Re-prove ALL breakage across Call.lean, CallRealises.lean, DriveSim.lean, the sim lemmas, and RealisabilitySpec.lean.
Then DELETE \`SingleCall\`, \`hsingle\`, and \`hone\` from every flagship + exProg_satisfies_hypotheses. RESTATE the open leaf \`callRealises_of_recorded\` (R3) for the stream model (it stays a sorry — an OPEN LEAF — but its statement must now reflect multi-call with NO single-call assumption).
This is the deep one: budget for wide breakage. If a sub-part genuinely blocks, land what builds green + sorry-free and STOP with a precise blocker — do NOT re-introduce a single-call assumption anywhere.`,
  },
  {
    id: 'full-observable',
    title: 'full-observable',
    goal: `Compare the FULL observable — the returned value and halt kind, not just storage — so the theorem says the contract BEHAVES the same, not merely that storage matches.`,
    detail: `ROOT CAUSE: \`observe\` (Spec/Recorder.lean:339) hardcodes \`result := .stopped\`, discarding the bytecode's real result; and the lowering emits an EMPTY RETURN (the IR \`ret t\` word is never written to the return buffer). So \`Conforms\` (RealisabilitySpec) only equates storage-worlds. The \`Observable\` type ALREADY has a \`result : IRHalt\` field (stopped | returned w) — it's just stubbed.
TASK: (1) LOWERING — make \`emitTerm\` for \`Term.ret t\` write t's word to memory and RETURN that 32-byte window (find the RETURN emission in Spec/Lowering.lean; today it is the empty-window cut). (2) OBSERVE — un-stub \`observe\` to read the real return data (the returned word) + halt kind from the FrameResult. (3) CONFORMS — extend it (RealisabilitySpec) to ALSO assert \`O.result = (observe self log.observable).result\`, not only the world. (4) SIM — carry the result/value channel through SimTerm.lean (the \`ret\` arm must now prove the returned word matches) and up through sim_cfg / DriveSim / LowerConforms, and through conforms_of_worldeq's analogue for the result channel.
Re-prove all breakage; default stays green+sorry-free. Open leaves stay sorry (restated to carry the result channel). If the RETURN value channel genuinely needs a big new machine-run lemma you cannot close, land the observe+Conforms+lowering parts that DO build green and STOP with a precise blocker on the remaining sim obligation — restated as a NEW open leaf is acceptable ONLY here (a full-observable sim obligation) and ONLY if you cannot close it, clearly reported; never a hidden shortcut.`,
  },
]

const preamble = (f) => `exp005 FOUNDATION strengthening — fix "${f.id}". ${RULES}\n\nGOAL: ${f.goal}\n\nDETAIL:\n${f.detail}`

const IMPL_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    fix: { type: 'string' },
    restrictionRemoved: { type: 'boolean', description: 'is the target restriction/hypothesis fully gone from the flagship + spec?' },
    defaultGreenSorryFree: { type: 'boolean' },
    nightlyGreen: { type: 'boolean' },
    newSorriesIntroduced: { type: 'array', items: { type: 'string' }, description: 'MUST be empty except an explicitly-reported full-observable sim obligation; list any' },
    openLeavesRestated: { type: 'array', items: { type: 'string' } },
    filesReproven: { type: 'array', items: { type: 'string' } },
    commit: { type: 'string' },
    blocker: { type: 'string', description: 'precise honest blocker if not fully done, else "none"' },
    notes: { type: 'string' },
  },
  required: ['fix', 'restrictionRemoved', 'defaultGreenSorryFree', 'nightlyGreen', 'newSorriesIntroduced', 'openLeavesRestated', 'filesReproven', 'commit', 'blocker', 'notes'],
}
const REVIEW_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    fix: { type: 'string' },
    verdict: { type: 'string', description: 'CLEAN | DEBT | PARTIAL — CLEAN only if restriction gone, default green+sorry-free, NO new sorry/hypothesis, no weakened conclusion' },
    restrictionGone: { type: 'boolean' },
    noNewDebt: { type: 'boolean', description: 'no new sorry/admit/native_decide/axiom/hypothesis/weakening beyond the allowed open leaves' },
    findings: { type: 'array', items: { type: 'string' } },
  },
  required: ['fix', 'verdict', 'restrictionGone', 'noNewDebt', 'findings'],
}

const results = []
for (const fix of FIXES) {
  phase(fix.title)
  const plan = await agent(`${preamble(fix)}\n\nPLANNER (read-only; do NOT edit). Read the cited anchors and the surrounding proofs in ${WT}. Produce a concrete plan: the exact defs to change, the proofs that will break and how to re-prove them, the open leaves to restate, and the risk. Be specific with file:line. Return prose the implementer follows.`,
    { phase: fix.title, label: `plan:${fix.id}` })

  const impl = await agent(`${preamble(fix)}\n\nIMPLEMENTER. Plan:\n${plan}\n\nDo the WHOLE fix in ${WT}: change the def(s), re-prove ALL breakage (iterate: edit → \`lake build\` → fix, background builds >8min), restate the open leaves, keep default green+sorry-free and Nightly green. Commit to 'foundation' only when green. If you must shortcut, STOP and report the blocker instead. Never fake, never weaken, never re-add the removed restriction.`,
    { phase: fix.title, label: `impl:${fix.id}`, schema: IMPL_SCHEMA })

  const review = await agent(`${preamble(fix)}\n\nREVIEWER (adversarial). Implementer reported:\n${JSON.stringify(impl)}\n\nVerify against ${WT} + git diff HEAD~1: (1) the target restriction is GONE from the flagship signatures + spec (grep to confirm); (2) default \`lake build\` is green AND sorry-free — run it, grep the output for 'declaration uses sorry' and confirm ZERO in the default LirLean cone; (3) \`lake build Nightly\` green with sorries ONLY on the allowed open leaves (${OPEN_LEAVES}) — no NEW sorry/admit/native_decide/axiom anywhere; (4) NO new hypothesis was added and NO conclusion weakened (diff the changed statements); (5) the change genuinely STRENGTHENS (the theorem now covers the previously-excluded case). Verdict CLEAN only if all hold. Return findings.`,
    { phase: fix.title, label: `review:${fix.id}`, schema: REVIEW_SCHEMA })

  results.push({ fix: fix.id, impl, review })
  if (!review || review.verdict !== 'CLEAN') {
    log(`Fix '${fix.id}' did NOT land CLEAN (verdict: ${review?.verdict ?? 'null'}). Stopping — refusing to build later fixes on an unclean foundation. Blocker: ${impl?.blocker ?? 'n/a'}`)
    break
  }
  log(`Fix '${fix.id}' landed CLEAN — proceeding.`)
}
return { foundation: results }
