export const meta = {
  name: 'exp005-phase3-round4',
  description: 'Phase 3 Round 4 (home stretch) — assembly (R10a/b, R11, R11-all, gasfree, R12a/b, RunFromLeft) + the two hard leaves (R3 calls, R6 boundary walk); plan -> implement -> review per track in parallel worktrees',
  phases: [{ title: 'Plan' }, { title: 'Implement' }, { title: 'Review' }],
}

// PREREQ (the launching agent must do this BEFORE running the workflow):
//   for t in asm-ties asm-flagship asm-adequacy asm-witness leaf-r3 leaf-r6; do
//     git worktree add .worktrees/p3-$t -b p3/$t exp005-honesty-cleanup
//     cp -Rc .worktrees/ir-lowering/experiments/005_ir_lowering/.lake .worktrees/p3-$t/experiments/005_ir_lowering/.lake
//   done
const WT_ROOT = '/Users/eduardo/workspace/evm-semantics/.worktrees'
const EXP = 'experiments/005_ir_lowering'
const SPEC = 'LirLean/RealisabilitySpec.lean'

const preamble = (t) => `Phase 3 Round 4 (home stretch), exp005 IR->EVM lowering conformance. Track "${t.id}" (${t.title}).
Worktree: ${t.wt} (branch ${t.branch}); spec ${t.wt}/${SPEC}. Warm APFS CoW .lake clone — \`cd ${t.wt} && lake build Nightly\` is incremental (minutes), background >8min.
ALREADY CLOSED (real, axiom-clean [propext, Classical.choice, Quot.sound], citable): R0b, R7a/b/c/d/e (the recorder-coupling spine; R7e is unconditional after the recorder was gated on rest.isEmpty), R1 (gas_suffix_head_realised), R2 (haltNonException_of_cleanLog), R4 (sstoreRealises_at_frame), R5 (termTies'_of_walk — all four terminator arms), R8 (present_of_closed), R9 (wellLowered_check_exists), the exProg witness (revalidatesPerBlock_exProg / singleCall_exProg / not_defsSound_stale), and helpers (driveLog_acc_hom, driveLog_frame_nonempty, recordCall_append, recorderCoupled_call_extract, recorderCoupled_stepsTo_other, runs_kind, atReachableBoundary_entry, atReachableBoundary_of_runs, not_runs_atReachableBoundary).
KEY: because this is a sorry-skeleton, you MAY cite still-open obligations (R3, R6) by their STATEMENT — the Nightly build stays green (their sorries are warnings) and your proof goes axiom-clean once they close. So the assembly can be fully wired now.
GLOBAL RULES: never push; only your worktree; no \`lake update\`; never delete \`.lake\`; do NOT touch any default-target (LirLean) file unless your task explicitly permits — if you think you need one, STOP and report a brief. Real proofs only (no new sorry/admit/native_decide); no weakened conclusions; no added hypothesis unless your task says so (and then argue it's legitimate well-formedness, not vacuity). Honest partial + precise blocker beats a fake close; the review diffs statements + re-checks axioms.

YOUR OBLIGATION(S):
${t.obligations}
SALVAGE / inputs: ${t.salvage}`

const TRACKS = [
  {
    id: 'asm-ties', branch: 'p3/asm-ties', wt: `${WT_ROOT}/p3-asm-ties/${EXP}`,
    title: 'R10a + R10b — the ties BUILT from the run',
    obligations: `R10a (stmtTies'_of_runWithLog) and R10b (termTies'_of_runWithLog): assemble the reshaped ties from a real runWithLog, dispatching each statement/terminator arm to the closed per-arm obligations. Cite R1 (gas), R4 (sstore, via sstoreRealises_at_frame), R7b/c (suffix-head consumption), R5 (termTies'_of_walk) and R3/R6 statements as needed. Watch the hretEmit seam R5 introduced (a static pc-bound) — supply/thread it here as tracked static well-formedness if R10b needs it.`,
    salvage: `R1, R4, R5, R7a-e, R8, R9 (all closed); StmtTies'/TermTies' defs (§3); RecorderCoupled + recorderCoupled_step_* ; the recorder (Spec/Recorder.lean).`,
  },
  {
    id: 'asm-flagship', branch: 'p3/asm-flagship', wt: `${WT_ROOT}/p3-asm-flagship/${EXP}`,
    title: 'R11 + R11-all + gasfree co-flagship',
    obligations: `R11 (lowering_conforms — THE flagship), R11-all (lowering_conforms_all, the exact-consumption RunFromAll strengthening), and the gasfree co-flagship (lowering_conforms_gasfree, NoGasReads prog). Assemble from R10a/R10b (ties from the run), R6 (boundary walk), R9 (checker), R2 (clean scope), the RunFrom/RunFromAll drivers, and RunFromLeft adequacy. Cite open leaves (R3/R6/R10/RunFromLeft) by statement — the flagship goes axiom-clean once they close. Do NOT add hypotheses; the flagship's premise list is settled (target-architecture §2).`,
    salvage: `R10a/R10b (asm-ties track, may still be sorry — cite the statement), R6 (leaf-r6), R2/R9 (closed), RunFromLeft (asm-adequacy track), realisedGas/realisedCall (recorder). Reference target-architecture-2026-07-02.md §2 for the exact flagship shape.`,
  },
  {
    id: 'asm-adequacy', branch: 'p3/asm-adequacy', wt: `${WT_ROOT}/p3-asm-adequacy/${EXP}`,
    title: 'RunFromLeft adequacy + realisedGas_nil',
    obligations: `Close runFrom_of_runFromLeft (~:986) and runFromLeft_exists (~:994) — the two RunFromLeft adequacy lemmas R11-all needs (RunFromLeft is the exact-leftover-trace variant of RunFrom; adequacy = the two directions relating them). Also close realisedGas_nil_of_noGasReads (the NoGasReads => realisedGas = [] fact the gasfree co-flagship consumes).`,
    salvage: `RunFrom / RunFromLeft defs (§4/§5), realisedGas + the recorder, NoGasReads def. These are structural — expect them to close.`,
  },
  {
    id: 'asm-witness', branch: 'p3/asm-witness', wt: `${WT_ROOT}/p3-asm-witness/${EXP}`,
    title: 'R12a + R12b — the concrete non-vacuity witness',
    obligations: `R12a (the flagship's antecedent is TRUE somewhere — machine-check that exProg satisfies lowering_conforms's premises incl. log.calls.length <= 1) and R12b (end-to-end: lowering_conforms instantiated at exProg). This is THE non-vacuity milestone. Cite R11 (asm-flagship track) by statement; discharge exProg's premises by decide/evaluation using the closed exProg witness lemmas.`,
    salvage: `R11 (asm-flagship, cite statement), exProg + singleCall_exProg + revalidatesPerBlock_exProg + wellLowered_check_exists (R9, closed), the concrete-program evaluators. Everything about exProg is decidable/evaluable.`,
  },
  {
    id: 'leaf-r3', branch: 'p3/leaf-r3', wt: `${WT_ROOT}/p3-leaf-r3/${EXP}`,
    title: 'R3 — call realisation from the log (the arg-push producer)',
    obligations: `Close R3 (callRealises_of_recorded, ~:1291). Round 3 landed Piece-A (recorderCoupled_call_extract: the recorded CallRecord yields a CallReturns witness + record identity). The BLOCKER is Piece-B: an arg-push machine-run producer — that the materialise of the call args runs (Runs) from the cursor to the CALL-site frame with the right pins, so CallRealisesS's arg-push conjunct is discharged. Build that producer, wire Piece-A + Piece-B into R3. SECONDARY RISK: the resumeAfterCall frame-pins may need a lemma that lives in the DEFAULT target — if so, STOP and write a short decision brief (like the recorder Option A/B one) rather than touching the default target; report it as the blocker.`,
    salvage: `recorderCoupled_call_extract + recorderCoupled_stepsTo_other (Round 3, closed), R7e, evmV2CallOracle/postStorage/resumeAfterCall (CallRealises.lean), materialise + its Runs lemmas (MaterialiseRuns.lean, LowerDecode.lean), CallRealisesS (§3), realisedCall.`,
  },
  {
    id: 'leaf-r6', branch: 'p3/leaf-r6', wt: `${WT_ROOT}/p3-leaf-r6/${EXP}`,
    title: 'R6 — the boundary walk (STEP/CALL edge lemmas)',
    obligations: `Close R6 (runs_atReachableBoundary, ~:2130 — statement ALREADY FIXED with hne + hsize; do NOT change it). Round 3 produced no committed progress here; the blocker is the STEP and CALL edge lemmas feeding atReachableBoundary_of_runs — that one stepFrame, and a returning CALL, from a reachable instruction boundary lands at another reachable boundary of lower prog. Build those edge lemmas (real proofs; case on the opcode/decode at the boundary using the landing salvage), then close R6 via atReachableBoundary_of_runs seeded by atReachableBoundary_entry. This is genuinely hard pc-reachability geometry — budget for it; land partial + precise blocker if it doesn't fully close.`,
    salvage: `atReachableBoundary_entry / atReachableBoundary_of_runs / not_runs_atReachableBoundary (closed), AtReachableBoundary def (Decode/Modellable.lean:407), jump_landing_of_cleanHalt / branch_landing_of_cleanHalt (MaterialiseCleanHalt/LowerDecode), BoundaryReach bricks, decode/jumpdest algebra (BytecodeLayer/Hoare/*, DecodeAnchors, DecodeLower).`,
  },
]

const IMPL_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    track: { type: 'string' },
    sorriesClosed: { type: 'array', items: { type: 'string' } },
    sorriesRemaining: { type: 'array', items: { type: 'string' } },
    statementChanges: { type: 'string', description: 'any statement change + legitimacy argument, or "none"' },
    defaultTargetBrief: { type: 'string', description: 'if a default-target change was needed (STOP-and-report): the decision brief; else "none"' },
    buildGreen: { type: 'boolean' },
    commit: { type: 'string' },
    blockers: { type: 'string' },
    notes: { type: 'string' },
  }, required: ['track', 'sorriesClosed', 'sorriesRemaining', 'statementChanges', 'defaultTargetBrief', 'buildGreen', 'commit', 'blockers', 'notes'],
}
const REVIEW_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    track: { type: 'string' },
    verdict: { type: 'string', description: 'CLEAN | DEFECTS | PARTIAL' },
    confirmedClosed: { type: 'array', items: { type: 'string' } },
    findings: { type: 'array', items: { type: 'string' } },
    vacuityCheck: { type: 'string', description: 'axiom-cleanliness (modulo open transitive sorries), no false-hypothesis reliance, any statement change legitimate; for R12 confirm the witness genuinely inhabits the flagship antecedent' },
  }, required: ['track', 'verdict', 'confirmedClosed', 'findings', 'vacuityCheck'],
}

const results = await pipeline(TRACKS,
  (t) => agent(`${preamble(t)}\n\nPLANNER (read-only; do NOT edit). Locate your exact sorry line(s)/statements in ${t.wt}/${SPEC}, read the salvage, and produce a concrete proof plan: skeleton, salvage consumed (file:line), which open leaves you cite by statement, feasibility, helper lemmas to add. For leaf-r3, assess whether the resumeAfterCall pins need a default-target lemma and say so. Return prose the implementer follows.`,
    { phase: 'Plan', label: `plan:${t.id}` }),
  (plan, t) => agent(`${preamble(t)}\n\nIMPLEMENTER. Plan:\n${plan}\n\nFill your owned sorry(s) in ${t.wt}/${SPEC} with real proofs (cite open leaves by statement where needed). Build incrementally (\`cd ${t.wt} && lake build Nightly\`, background >8min) until closed + green. If leaf-r3 needs a default-target lemma, STOP and put the brief in defaultTargetBrief (do NOT touch the default target). Honest partial + precise blocker if at-risk; never fake, never weaken. Commit to ${t.branch} ('exp005 phase3 ${t.id}: ...'); never push.`,
    { phase: 'Implement', label: `impl:${t.id}`, schema: IMPL_SCHEMA }),
  (impl, t) => agent(`${preamble(t)}\n\nREVIEWER (adversarial). Implementer reported:\n${JSON.stringify(impl)}\n\nVerify against ${t.wt}/${SPEC} + git diff: (1) each claimed close is a real proof — no residual sorry/admit/native_decide; (2) statements byte-unchanged except declared changes; (3) targeted \`#print axioms\` on closed obligations — [propext, Classical.choice, Quot.sound] modulo open transitive sorries (a citation of an open leaf shows sorryAx — that's expected and fine, note which leaf); (4) no false-hypothesis reliance; for R12 confirm exProg genuinely satisfies the flagship antecedent (real non-vacuity); (5) no default-target file touched. Return verdict + confirmed-closed + vacuity check.`,
    { phase: 'Review', label: `review:${t.id}`, schema: REVIEW_SCHEMA }),
)

return { round: 4, tracks: results.filter(Boolean) }
