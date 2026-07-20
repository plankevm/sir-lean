# Bytecode-layer audit — decision queue for Eduardo (2026-07-20)

Ledger recorded by the audit-fix track (branch `codex/bytecode-audit-fixes`,
tracks T1–T4). None of these block the landed fixes; they are open calls the
fixes deliberately did NOT make.

## 1. EVMSpec: adopt vs. archive (V7 endgame)

`EVM/BytecodeLayer/EVMSpec.lean` is a parked draft (banner made truthful in T1):
un-imported by the root aggregator on purpose, additive over the canonical
`EVMSemantics`/`flatSem` interface (`SharedObservable.lean`). Decision needed:
**adopt** the reshape (retire `flatSem` in favour of `flatSpec`, mirror on the
nested side) or **archive** the draft. Until decided, the module builds only via
the lakefile glob and must not be re-imported.

## 2. EVMSpec draft: Option-B ratification (pending)

The draft's State/Result modeling choice (§"The modeling choice" in
`EVMSpec.lean`) records the draft author's Option-B pick, **not yet Eduardo's**.
Ratification is a precondition of the adopt arm of decision 1; the banner
explicitly awaits it.

## 3. Behaves: surface vs. annotate — resolved MINIMALLY

The audit's Behaves finding was closed on the minimal arm (annotate + drop the
dead import). Full surfacing of the `Behaves` interface remains open if wanted.

## 4. HoareDemo: KEEP arm taken — flag for confirmation

Resolved on the report's recommended KEEP arm (it hosts a unique framing
theorem). Flagged here for Eduardo's confirmation; the delete arm is still
available if the framing theorem is rehomed first.
