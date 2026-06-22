# Track C — local plan (High-level IR → EVM bytecode, lowering preserved)

Worktree: `../evm-semantics-wt/ir-lowering` · Branch: `exp005-ir` · Base: `exp003-fuel-layer-cleanup`
Master index: repo-root `currentplan.md`.

## Goal
Define an *interesting* high-level IR, lower it to EVM bytecode, and prove the
lowering preserves semantics — reusing exp003's reasoning layer (`Runs` + boundary
bridges). The IR's job is to exercise the three primitives we actually need:
**storage arithmetic, external calls, and branching**. Branching is what makes
**gas introspection** reasoning meaningful (a `GAS`-dependent branch).

## Starting material
- exp002 `experiments/002_ssa_cfg/SirLean/` — an existing SSA/CFG IR
  (`IR.lean`, `SmallStep.lean`, `Eval.lean`, `Spec.lean`, `Proof.lean`, `SCCP.lean`,
  `State.lean`). Reuse/extend it, but ENSURE branches and external calls are
  first-class (the previous IR may lack one or both).
- exp003 `experiments/003_bytecode_layer/` — the bytecode reasoning layer and its
  `Runs`/`messageCall_runs` API. Track C is its first real consumer.

## Milestones
- [x] **C1** Define the IR: storage arithmetic + external calls + branching.
  Decide build-on-exp002 vs fresh. Write a design doc (`docs/ir-design.md`).
  → DONE: fresh `LirLean` IR + design doc + compiling skeleton (no `sorry`).
- [x] **C2** Lowering IR → EVM bytecode (decode-compatible with exp003).
  → DONE: `lower` now materialises operands (recompute-on-use) and emits a real,
  runnable EVM byte stream for the full single-call surface; decode-compatibility
  is build-enforced by `LirLean/Decode.lean` (`example … := by rfl` at every pc of
  a worked single-call program). See the C2 log entry below.
- [ ] **C3** Prove lowering preserves semantics via exp003's `Runs` machinery.
- [ ] **C4** Acceptance check: does exp003 sequencing suffice for **multi-call** IR
  programs? If NOT, write the precise requirement here and flag Track A
  (`exp003-runs-call`) — this is the A↔C feedback edge.

## Agent brief (durable — re-spawn from this verbatim)
> Work ONLY in `/Users/eduardo/workspace/evm-semantics-wt/ir-lowering`, branch
> `exp005-ir`, dir `experiments/005_ir_lowering`. Do **Milestone C1 only** this run
> (design + skeleton, no heavy proofs yet), then stop and report. First STUDY
> exp002's `SirLean/` and exp003's `Runs`/boundary-bridge API; decide extend-vs-fresh
> with reasons. Produce `docs/ir-design.md` (IR grammar: storage read/write +
> arithmetic, CALL, conditional branch; small-step or denotational semantics choice;
> how it lowers to exp003-decodable bytecode; how gas introspection appears) and a
> compiling Lean skeleton (`lakefile.lean` requiring what it needs; IR datatype +
> stubbed lowering signature — types only, no `sorry`-backed theorems). Append dated
> progress to this PLAN.md; commit on this branch; do not touch other tracks.
> Report the design decision + skeleton build status.

## Progress log
- 2026-06-22: Track seeded. Awaiting C1 agent.
- 2026-06-22 (C1): Studied exp002 `SirLean/` and exp003's `Runs`/boundary-bridge
  API. **Decision: fresh IR (`LirLean/`), not an extension of `SirLean`.** Reasons
  (full version in `docs/ir-design.md` §1): `SirLean.Word = UInt32` vs EVM
  `UInt256`; `SirLean.World = Word → Word` is disconnected from the EVM
  account/storage model the preservation proof must target; `SirLean` has **no
  external CALL** and **no gas/gas-introspection**; its SSA/dominance/`refs_valid`
  + `SCCP` scaffolding (>80 KB) is dead weight for lowering. We keep only exp002's
  *structural idea* (a CFG of basic blocks with branch terminators).
- 2026-06-22 (C1): Wrote `docs/ir-design.md` — IR grammar (Tmp/Label/Expr/Stmt/
  Term/Block/Program with first-class `sload`/`sstore`/`add`/`lt`, `Stmt.call`,
  `Term.branch`, and `Expr.gas` introspection); small-step + gas-aware semantics
  choice (rationale: mirror exp003's `Runs` for a simulation proof); two-pass
  lowering to `Evm.decode`-compatible bytecode (per-block `JUMPDEST`, fixed-width
  `PUSH4` destinations → prefix-sum offset table); call→`Runs`/`CallReturns`
  mapping; preservation statement *shape* (per-step `Match` simulation +
  top-level `messageCall_runs`/`_call_runs` discharge).
- 2026-06-22 (C1): **⚠ C4 surfaced early (flag for Track A).** Reading
  `Hoare/CallSequence.lean`: `messageCall_call_runs` is hard-wired to exactly ONE
  `CallReturns` between a prefix and suffix `Runs`. A `Runs` link is one
  *non-halting* `stepFrame` (`Signal.next`); a CALL is `Signal.needsCall`, so it is
  NOT a `StepsTo` link and cannot be glued in by `Runs.trans`. Therefore a
  ≥2-call IR program (`prefix → call → middle → call → suffix → halt`) is
  inexpressible with the current bridge. Track C's multi-call lowering (C3/C4) is
  blocked on Track A's planned `Runs.call` constructor (A1–A3). Single-call
  lowering can proceed against the current API now. (Detail in `ir-design.md` §5.)
- 2026-06-22 (C1): Wrote the compiling Lean skeleton — `lakefile.lean` (requires
  exp003's `bytecode_layer`, transitively `evm`/Mathlib), `lean-toolchain`
  (v4.30.0, matching exp003), `LirLean/IR.lean` (the IR datatypes),
  `LirLean/Lowering.lean` (`lower : Program → ByteArray` with a concrete,
  `sorry`-free two-pass body — correctness deferred to C2). No theorems stated, so
  nothing is `sorry`/`axiom`-backed. `lake build` status recorded on commit.

- 2026-06-22 (C2): **Decode-compatible single-call lowering — DONE, green,
  axiom-clean.** `lake build` succeeds (1106 jobs); the decode checks are
  kernel-`rfl` (`#print axioms` on a representative check: only `propext`,
  `Quot.sound` — no `sorryAx`, no `native_decide` axiom).

  **What `lower` now emits per IR construct** (`LirLean/Lowering.lean`). The
  big change from C1: operands are *materialised* onto the stack by
  recompute-on-use (an `assign` emits **no** bytes; its RHS is re-emitted at each
  consuming opcode, exactly like exp003's hand-written programs push a literal
  immediately before consuming it). `materialiseExpr` walks a program-global
  `defs : Tmp → Option Expr` map; binary ops push the **second** operand first so
  the first ends up on top.
  - `Expr.imm w`     → `PUSH32 w` (uniform 32-byte literal; BE, round-trips via
                       `uInt256OfByteArray`).
  - `Expr.tmp t`     → re-materialise `t`'s defining expression (no bytes of its own).
  - `Expr.add a b`   → materialise `b`; materialise `a`; `ADD`.
  - `Expr.lt  a b`   → materialise `b`; materialise `a`; `LT`.
  - `Expr.sload k`   → materialise `k`; `SLOAD`.
  - `Expr.gas`       → `GAS`.
  - `Stmt.assign`    → **nothing** (recompute-on-use).
  - `Stmt.sstore k v`→ materialise `v`; materialise `k`; `SSTORE` (leaves
                       `key :: value :: rest` — the shape `runs_sstore` wants).
  - `Stmt.call cs`   → push 7 CALL args (value-free, zero-memory: five `PUSH32 0`,
                       then `callee`, then `gasFwd` on top — the `callerProg`
                       order); `CALL`. The 0/1 success flag is left on the stack
                       for a following use of `resultTmp`.
  - `Term.ret t`     → materialise `t`; `RETURN`.
  - `Term.stop`      → `STOP`.
  - `Term.jump L`    → `PUSH4 off(L)`; `JUMP`.
  - `Term.branch c t e` → materialise `c`; `PUSH4 off(t)`; `JUMPI`;
                          `PUSH4 off(e)`; `JUMP`.
  Block layout unchanged from C1: each block is `JUMPDEST :: body`; the
  `Label → byte offset` table is a prefix sum of `blockLen` (destination pushes
  are fixed-width `PUSH4`, so layout is push-width-independent and the two passes
  agree).

  **Decode round-trip checks** (`LirLean/Decode.lean`, build-enforced). A worked
  3-block single-call program `workedCall` exercises the whole surface
  (`sstore`/`sload`/`add`/`lt`, one external `CALL` to `0xCA11EE` forwarding
  `0xFFFFFFFF` gas, a `branch` on the `lt` result, plus `ret` and `stop`). It
  lowers to a 520-byte array; block JUMPDESTs at offsets 0 / 414 / 518.
  `example … := by rfl` pins `Evm.decode code pc = expected` at **every** emitted
  instruction pc (≈40 checks), covering: `JUMPDEST`, every `PUSH32` literal (incl.
  the recompute order — `lt`/`add`/`sload` operands at pcs 300/333/366 and again
  415/448/481), `SSTORE`, the seven CALL-arg pushes + `CALL`, `ADD`, `LT`, `SLOAD`,
  the two `PUSH4` branch destinations (immediates 414, 518), `JUMPI`, `JUMP`,
  `RETURN`, `STOP`. Confirms the exp003 decode form: `ADD/LT = .ArithLogic …`,
  `SLOAD/SSTORE/GAS/JUMP/JUMPI/JUMPDEST = .Smsf …`, `STOP/RETURN/CALL = .System …`,
  pushes carry `(immediate, width)`. (`maxRecDepth` is bumped — `lower` is a deep
  computation — but the checks are pure kernel `rfl`, no `native_decide`.) The two
  branch destinations are shown to land on real `JUMPDEST`s via the four relevant
  `rfl` decode checks rather than `validJumpDests` (which is `partial def` and would
  force `native_decide`, breaking the axiom-clean bar).

- 2026-06-22 (C2): **⚠ Missing exp003 `Runs` rules — C3/Track-A dependency.**
  The opcodes `lower` emits line up with exp003's existing `Runs` API only
  partially. exp003 currently provides opcode `Runs` rules for **PUSH1 / PUSH
  (any width) / SSTORE** (`runs_push1`, `runs_push`, `runs_sstore` in `Spec.lean`),
  and the CALL boundary (`CallReturns` + `messageCall_call_runs`), plus step-level
  halt characterizations `stepFrame_stop` / `stepFrame_return_empty` (consumed at
  the `messageCall_runs` boundary). It has **NO `runs_*` rule** for the following
  opcodes that single-call lowering emits — each is a C3 prerequisite (and a
  candidate Track-A deliverable, since they are generic opcode bricks):
  - **`SLOAD` (0x54)** — needed by `Expr.sload`.
  - **`ADD` (0x01)** — needed by `Expr.add`.
  - **`LT` (0x10)** — needed by `Expr.lt`.
  - **`GAS` (0x5a)** — needed by `Expr.gas` (gas introspection).
  - **`JUMP` (0x56)** — needed by `Term.jump` and the `else` edge of `Term.branch`.
  - **`JUMPI` (0x57)** — needed by `Term.branch`.
  For `STOP` and `RETURN` the step-level `stepFrame_stop` / `stepFrame_return_empty`
  exist but are not yet packaged as `runs_*` halt lemmas; C3 will need a thin
  `Runs … → halt` wrapper for the terminator. So C3's per-step simulation can chain
  `runs_push`/`runs_sstore`/the CALL facts today, but is **blocked** on new
  `runs_sload`/`runs_add`/`runs_lt`/`runs_gas`/`runs_jump`/`runs_jumpi` opcode
  rules. (The multi-call composition block — `messageCall_call_runs` admitting only
  ONE `CallReturns` — remains the separate C4/Track-A `Runs.call` dependency
  recorded in the C1 log and `docs/ir-design.md` §5; single-call lowering, this
  milestone, is unaffected by it.)
