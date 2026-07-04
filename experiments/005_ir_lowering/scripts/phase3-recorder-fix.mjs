export const meta = {
  name: 'exp005-phase3-recorder-fix',
  description: 'Option B — gate recordCall on rest.isEmpty (default-target recorder), re-prove adequacy + Nightly helpers, close R7e unconditionally; then parallel docs update for the course-correction',
  phases: [{ title: 'Plan' }, { title: 'Implement' }, { title: 'Review' }, { title: 'Docs' }],
}

const WT = '/Users/eduardo/workspace/evm-semantics/.worktrees/p3-recorder/experiments/005_ir_lowering'
const BRANCH = 'p3/recorder'
const REC = 'LirLean/Spec/Recorder.lean'
const SPEC = 'LirLean/V2/RealisabilitySpec.lean'

const base = `Phase 3 course-correction (Option B), exp005 IR->EVM conformance. Worktree: ${WT} (branch ${BRANCH}); warm APFS CoW .lake clone — \`cd ${WT} && lake build\` / \`lake build Nightly\` are incremental (minutes), background any build >8min.

THE FIX (settled, from the R7e decision brief): the recorder's returning-CALL record is UNGATED — \`recordCall\` fires at every call delivery at any depth, while gas/sload gate on \`stack.isEmpty\`. This makes R7e's "consumes exactly one CallRecord" false in general (true only under the flagship's single-call \`hone\`). Gate it so only the TOP-LEVEL program's own returning calls are recorded, matching gas/sload and the recorder's own docstrings.

KEY FACTS (verify in-tree):
- \`driveLog\` is white-box (steps callee code inline via a pending stack); the delivery branch is around ${REC}:183-188 (\`pending.resume result\` -> \`.ok parent\` / \`.error e\`, each calling \`recordCall pending result callAcc\`).
- The correct top-level test at the DELIVERY branch is \`rest.isEmpty\` (the resumed pending stack): the top-level program's own CALL returns with \`rest = []\`; a callee's inner CALL returns with \`rest\` non-empty.
- gas/sload gate on \`stack.isEmpty\` at ${REC}:~202/205.
- Consumers to re-verify: \`driveLog_drive\` (RecorderLemmas.lean:~60, adequacy — erases the accumulator via .map, so structurally preserved, expect a trivial split), \`realisedCall\`/\`callOracleOf\`/\`realisedCall_eq_evmV2\` (read log.calls directly — statements unchanged, meaning improves), and the Nightly helpers \`recordCall_append\` + \`driveLog_acc_hom\` (RealisabilitySpec — mechanical \`by_cases rest.isEmpty\`; append-homomorphism still holds since a gated no-op appends []).

GLOBAL RULES: never push; only touch this worktree; no \`lake update\`; never delete \`.lake\`. Real proofs only (no new sorry/admit/native_decide); do not weaken any statement. This touches the TRUST-CRITICAL default-target recorder, so correctness + axiom-cleanliness are paramount.`

const IMPL_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    recorderGated: { type: 'boolean', description: 'recordCall now gated on rest.isEmpty in Spec/Recorder.lean' },
    adequacyReproven: { type: 'boolean', description: 'driveLog_drive re-proven green' },
    helpersReproven: { type: 'array', items: { type: 'string' }, description: 'Nightly helpers re-proven (recordCall_append, driveLog_acc_hom, ...)' },
    r7eClosed: { type: 'boolean', description: 'recorderCoupled_call closed WITHOUT the hone hypothesis' },
    r7eSignature: { type: 'string', description: 'the final R7e signature (to confirm no hone was added)' },
    defaultBuildGreen: { type: 'boolean' },
    nightlyBuildGreen: { type: 'boolean' },
    commit: { type: 'string' },
    blockers: { type: 'string' },
    notes: { type: 'string' },
  }, required: ['recorderGated', 'adequacyReproven', 'helpersReproven', 'r7eClosed', 'r7eSignature', 'defaultBuildGreen', 'nightlyBuildGreen', 'commit', 'blockers', 'notes'],
}
const REVIEW_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    verdict: { type: 'string', description: 'CLEAN | DEFECTS | PARTIAL' },
    gateCorrect: { type: 'string', description: 'is the rest.isEmpty gate at the right site + semantically right (only top-level calls recorded)?' },
    adequacyPreserved: { type: 'string', description: 'driveLog_drive still holds + axiom-clean?' },
    r7eUnconditional: { type: 'boolean', description: 'R7e closed with NO hone/single-call hypothesis added' },
    realisedCallMeaning: { type: 'string', description: 'did realisedCall meaning stay correct/improve (not silently narrow)?' },
    findings: { type: 'array', items: { type: 'string' } },
  }, required: ['verdict', 'gateCorrect', 'adequacyPreserved', 'r7eUnconditional', 'realisedCallMeaning', 'findings'],
}

phase('Plan')
const plan = await agent(`${base}\n\nPLANNER (read-only; do NOT edit). Read ${WT}/${REC} (driveLog delivery branch + recordCall + the gas/sload gates), ${WT}/LirLean/RecorderLemmas.lean (driveLog_drive + realisedCall_eq_evmV2), and ${WT}/${SPEC} (recorderCoupled_call = R7e, recordCall_append, driveLog_acc_hom). Produce the concrete edit + re-proof plan: exact gate edit at the delivery branch; how driveLog_drive's proof accommodates the split; the by_cases pattern for recordCall_append/driveLog_acc_hom; how R7e closes once the child records nothing (confirm hone can be dropped from its signature); and any other consumer that could break. Return prose the implementer follows.`,
  { phase: 'Plan', label: 'plan:recorder' })

phase('Implement')
const impl = await agent(`${base}\n\nIMPLEMENTER. Plan:\n${plan}\n\nExecute the fix end to end in ${WT}: (1) gate both recordCall calls in ${REC}'s delivery branch on \`rest.isEmpty\`; (2) re-prove driveLog_drive (RecorderLemmas.lean) + re-run/confirm the recorder axiom guards; (3) re-prove recordCall_append + driveLog_acc_hom in ${SPEC}; (4) close recorderCoupled_call (R7e) and REMOVE the hone hypothesis from its signature (it must be unconditional now) — also drop its escalation docstring note. Build BOTH \`lake build\` (default) and \`lake build Nightly\` green (background >8min). Commit to ${BRANCH} ('exp005 phase3 recorder-fix: gate recordCall on rest.isEmpty + close R7e unconditionally'); never push. If anything doesn't close, land partial + precise blocker — do NOT fake it, do NOT weaken a statement, do NOT leave the default target broken.`,
  { phase: 'Implement', label: 'impl:recorder', schema: IMPL_SCHEMA })

phase('Review')
const review = await agent(`${base}\n\nREVIEWER (adversarial). Implementer reported:\n${JSON.stringify(impl)}\n\nVerify against ${WT} + git diff: (1) the gate is at the delivery branch and on \`rest.isEmpty\` (NOT stack.isEmpty — the resumed stack) — is it semantically "only top-level calls recorded"? attack it with a nested-call scenario; (2) driveLog_drive still holds and is axiom-clean ([propext, Classical.choice, Quot.sound]); (3) recorderCoupled_call (R7e) is closed with NO hone / single-call hypothesis in its signature — diff the signature to confirm; run \`#print axioms\` on it; (4) realisedCall/callOracleOf meaning: confirm it now keys on the top-level call and did NOT silently narrow conformance for in-scope (single-call) programs (byte-identical log.calls there); (5) both default + Nightly build green; no OTHER default-target decl broke. Return the verdict + checks.`,
  { phase: 'Review', label: 'review:recorder', schema: REVIEW_SCHEMA })

// Docs phase — only if the fix is sound
let docs = null
if (review && review.verdict === 'CLEAN') {
  phase('Docs')
  const docBase = `Course-correction DOCS update for the exp005 recorder gating fix (Option B), just landed on branch ${BRANCH} in ${WT}. What changed: the recorder's returning-CALL record (recordCall in Spec/Recorder.lean) was UNGATED (recorded nested callee calls too), contradicting its own docstrings and the gas/sload gating; it is now gated on \`rest.isEmpty\` so only the top-level program's own returning calls are recorded. Consequence: R7e (recorderCoupled_call) now holds UNCONDITIONALLY (the single-call hone hypothesis was dropped), realisedCall is faithful even when the top-level call's callee itself calls, and this unblocks the R3' multi-call generalization. Edit ONLY the files you're told; add dated notes, don't delete history; commit to ${BRANCH}, never push.`
  docs = await parallel([
    () => agent(`${docBase}\n\nCODE-DOCSTRING task. Update in-code docstrings in ${WT} to reflect the gate: (a) ${REC} — the recordCall / driveLog delivery-branch docstring (it should now describe the rest.isEmpty gate + that only top-level calls record, matching gas/sload); (b) ${SPEC} — recorderCoupled_call (R7e): replace the old escalation/asymmetry note with a note that it's now closed unconditionally post-gate, and update the module header if it references the recorder asymmetry. Comment/docstring text only — do not touch any proof or signature. Report per-file edits.`,
      { phase: 'Docs', label: 'docs:code' }),
    () => agent(`${docBase}\n\nLIVING-DOCS task. Update the exp005 living docs under ${WT}/experiments/005_ir_lowering/docs (and repo-root status surfaces if relevant): append to docs/final-audit-2026-07-03.md's post-audit-actions the recorder course-correction; add a dated note to docs/target-architecture-2026-07-02.md (the recorder-model fix + that R3' now builds on the corrected recorder); update docs/gas-decision.md or add a short docs/recorder-model-note.md capturing the ungated-recordCall finding, the rest.isEmpty gate, and the decision rationale (Option B chosen over the Nightly-only stopgap). Markdown only. Report per-file edits.`,
      { phase: 'Docs', label: 'docs:living' }),
  ])
}

return { fix: { impl, review }, docs: docs ? docs.filter(Boolean) : 'skipped (fix not CLEAN)' }
