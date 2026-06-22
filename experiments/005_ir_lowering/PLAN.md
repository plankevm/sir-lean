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
- [~] **C3** Prove lowering preserves semantics via exp003's `Runs` machinery.
  → IN PROGRESS: small-step IR semantics (`LirLean/SmallStep.lean`) + the `Match`
  invariant, all **per-construct atomic simulation lemmas**, and the top-level
  boundary discharge (`LirLean/Match.lean`) are proved, green, axiom-clean. The
  remaining piece is the program-global assembly of the `Runs fr₀ last` under the
  offset-table pc clause `M1`. See the C3 log entry below.
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

## C→A opcode-rule request (for Track A `exp003-runs-call`)

The C3 preservation proof (`docs/ir-design.md` §6.4 obligation table) consumes
Track A's new index-free `Runs` API (`Runs.step`/`Runs.call`/`Runs.trans`,
`messageCall_runs` / `messageCall_runs_calls`). On top of the rules A already ships
(`runs_push1`, `runs_push`, `runs_sstore` + framing), C3 needs the following
**six new opcode `Runs` rules**. Each is a generic, program-independent brick of
the same form A already wrote for SSTORE: under purely semantic preconditions
(decode + gas bound + stack shape) it advances **one** frame to a named post-frame
transformer, derived from the matching `stepFrame_*` characterization. **No halt
wrapper and no CALL `runs_*` is requested** — A's `messageCall_runs` takes the
`STOP`/`RETURN` halt directly via its `hhalt` argument (using the existing
`stepFrame_stop` / `stepFrame_return_empty`), and `CALL` is a `Runs.call` node
built from `CallReturns` (A's `stepFrame_call`), not a `runs_*` rule. JUMP/JUMPI
are noted as already in A's CFG-combinator work; if not yet exposed as `runs_*`,
the shapes below are the request.

Gas/stack facts are confirmed against A's worktree (`EVMLean/Evm/Semantics/
{Smsf,PrimOps,GasConstants}.lean`): `binOp`/`unOp` charge `Gverylow = 3`; `pushOp`
charges `Gbase = 2`; `sloadCost warm = if warm then Gwarmaccess(100) else
Gcoldsload(2100)`; JUMP charges `Gmid = 8`, JUMPI charges `Ghigh = 10`; jump targets
are resolved by `Frame.get_dest dest = fr.validJumps.find? (· == dest.toUInt32)`.

1. **`runs_add`** (ADD `0x01`) — `Expr.add`.
   ```
   def addFrame (fr) (a b : UInt256) (rest : Stack UInt256) : Frame :=    -- pops a,b; pushes a+b; pc+1; −Gverylow
   theorem runs_add (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
       (hdec : decode fr.exec.code fr.exec.pc = some (.ArithLogic .ADD, none))
       (hstk : fr.exec.stack = a :: b :: rest)
       (hgas : 3 ≤ fr.exec.gasAvailable.toNat) (hsz : fr.exec.stack.size ≤ 1024) :
       Runs fr (addFrame fr a b rest)
   ```
   (post: top = `a + b`, then `rest`; the IR `IRStep` for `add` must subtract the
   same `Gverylow`.)

2. **`runs_lt`** (LT `0x10`) — `Expr.lt`. Identical shape to `runs_add` with
   `.ArithLogic .LT` and `ltFrame` pushing `if a < b then 1 else 0` (EVM `LT`
   compares `top < second`, i.e. `a < b` for stack `a :: b :: rest`; charge
   `Gverylow`).

3. **`runs_sload`** (SLOAD `0x54`) — `Expr.sload`. Pops `key`, pushes the self
   account's stored value, charges `sloadCost warm`:
   ```
   def sloadFrame (fr) (key : UInt256) (rest : Stack UInt256) : Frame :=     -- pops key; pushes value@key; pc+1; −sloadCost
   theorem runs_sload (fr : Frame) (key : UInt256) (rest : Stack UInt256)
       (hdec : decode fr.exec.code fr.exec.pc = some (.Smsf .SLOAD, none))
       (hstk : fr.exec.stack = key :: rest) (hsz : fr.exec.stack.size ≤ 1024)
       (hgas : sloadCost (fr.exec.substate.accessedStorageKeys.contains
                  (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
       Runs fr (sloadFrame fr key rest)
   ```
   Desired **read companion** (mirrors `sstoreFrame_storage_self`): the pushed value
   equals the storage lens C3's `Match` (M3) uses —
   `(sloadFrame fr key rest).exec.stack.head = (fr.exec.accounts.find?
   fr.exec.executionEnv.address |>.option 0 (·.lookupStorage key))`.

4. **`runs_gas`** (GAS `0x5a`) — `Expr.gas` (gas introspection). Pushes
   `UInt256.ofUInt64 fr.exec.gasAvailable`, charges `Gbase = 2`, pops nothing:
   ```
   def gasFrame (fr) : Frame :=     -- pushes ofUInt64 gasAvailable; pc+1; −Gbase
   theorem runs_gas (fr : Frame)
       (hdec : decode fr.exec.code fr.exec.pc = some (.Smsf .GAS, none))
       (hgas : 2 ≤ fr.exec.gasAvailable.toNat) (hstk : fr.exec.stack.size + 1 ≤ 1024) :
       Runs fr (gasFrame fr)
   ```
   (Note: the pushed value is gas **after** the `Gbase` charge in the EVM model;
   the exact post-charge value must be pinned in the post-frame so C3's `M4`
   threading stays honest — this is the gas-introspection coupling.)

5. **`runs_jump`** (JUMP `0x56`) — `Term.jump` and the not-taken edge of
   `Term.branch`. Pops `dest`, sets pc to the resolved target, charges `Gmid = 8`:
   ```
   def jumpFrame (fr) (newPc : UInt32) (rest : Stack UInt256) : Frame :=    -- pops dest; pc:=newPc; −Gmid
   theorem runs_jump (fr : Frame) (dest : UInt256) (newPc : UInt32) (rest : Stack UInt256)
       (hdec : decode fr.exec.code fr.exec.pc = some (.Smsf .JUMP, none))
       (hstk : fr.exec.stack = dest :: rest)
       (hdst : fr.get_dest dest = some newPc)              -- dest ∈ validJumps
       (hgas : 8 ≤ fr.exec.gasAvailable.toNat) :
       Runs fr (jumpFrame fr newPc rest)
   ```
   C3 supplies `hdst` from the lowering's offset table landing on a `JUMPDEST`
   (the `Decode.lean` checks already witness `decode code off = JUMPDEST`).

6. **`runs_jumpi`** (JUMPI `0x57`) — `Term.branch`. Pops `dest, cond`, charges
   `Ghigh = 10`; **two** post-frames by the condition. Cleanest as one rule per
   edge (so C3 picks the edge its `Match` is on):
   ```
   theorem runs_jumpi_taken (fr) (dest cond : UInt256) (newPc : UInt32) (rest)
       (hdec : decode … = some (.Smsf .JUMPI, none))
       (hstk : fr.exec.stack = dest :: cond :: rest) (hc : cond ≠ 0)
       (hdst : fr.get_dest dest = some newPc) (hgas : 10 ≤ …) :
       Runs fr (jumpiTakenFrame fr newPc rest)              -- pc := newPc; −Ghigh
   theorem runs_jumpi_fallthrough (fr) (dest cond : UInt256) (rest)
       (hdec : …) (hstk : fr.exec.stack = dest :: cond :: rest) (hc : cond = 0)
       (hgas : 10 ≤ …) :
       Runs fr (jumpiFallFrame fr rest)                      -- pc := pc+1; −Ghigh
   ```

**Priority for C3's first worked program** (`workedCall`, `Decode.lean`):
`runs_sload`, `runs_add`, `runs_lt`, `runs_gas` are needed for the storage-arith +
introspection surface; `runs_jump` + `runs_jumpi_*` for the branch. All six are
required for the full single-/multi-call preservation theorem.

- 2026-06-22 (C-review/C3-design): **Rebase-safe review + C3 design milestone.**
  Studied Track A's NEW `exp003-runs-call` API (read-only, from
  `../runs-call/.../BytecodeLayer/{Hoare.lean, Hoare/Sequence.lean,
  Hoare/CallSequence.lean, Examples/TwoCallExample.lean}`). Three API facts that
  change C3's target vs. the C1/C2 assumptions: (i) `Runs` is now **index-free**
  (`Runs fr fr'`, no `Nat`); (ii) `call` is a **constructor of `Runs`**
  (`Runs.call hcall rest`, payload `CallReturns`) — so the C1/C2 multi-call blocker
  is **RESOLVED** (worked in A's `TwoCallExample`); (iii) the boundary bridge is the
  single `messageCall_runs` (alias `messageCall_runs_calls`) and it **takes the halt
  itself** via `hhalt : stepFrame last = .halted halt` — so C3 needs **no** halt
  `runs_*` wrapper (the C2-log "thin Runs→halt wrapper" note is superseded).
  - **Simplified C1+C2** (build still green, 1106 jobs; axiom-clean — `#print axioms`
    on a decode check = `[propext, Quot.sound]`, no `sorryAx`/native axiom). Removed
    two genuinely dead defs from `LirLean/Lowering.lean`: `Byte.push1` (only
    PUSH4/PUSH32 are ever emitted) and `destPushBytes` (referenced only in a doc
    comment, never load-bearing — `emitDest` fixes the PUSH4 width itself); fixed the
    one comment that named it. Reviewed recompute-on-use: it is correct and is in
    fact the simplification that lets C3's `Match` drop the register↔slot map
    entirely (see §6.1). No behavioural change — the 40 decode round-trip `rfl`
    checks still pass, confirming the byte layout is identical.
  - **Wrote the concrete C3 plan** in `docs/ir-design.md` §6: the `Match` invariant
    (M1 pc-via-offset-table, M2 code, M3 storage-via-observable-lens, M4 honest gas,
    M5 empty-stack-at-statement-boundary — no slot map, thanks to recompute-on-use);
    the `lower_simulates_step` engine and `lower_preserves` top-level shapes against
    A's new API; and the **per-construct proof-obligation table** mapping every IR
    construct to the exact `runs_*` / `Runs.call` / bridge-halt step it consumes.
    Updated §5 to A's new API and marked the multi-call blocker RESOLVED.
  - **Wrote the C→A opcode-rule request** above (six rules: `runs_add`, `runs_lt`,
    `runs_sload` (+read companion), `runs_gas`, `runs_jump`, `runs_jumpi_*`), each
    with a precise signature shape (semantic preconditions + named post-frame),
    gas/stack/pc facts confirmed against A's `EVMLean/Evm/Semantics/*`.
  - Did **not** attempt the preservation proof (gated on A's merge into this base).
    No `sorry`, no `axiom` introduced.

- 2026-06-22 (C3): **Single-call lowering preservation — small-step semantics +
  `Match` + per-construct simulation engine + boundary discharge, all green and
  axiom-clean.** Track A's new API is now merged into this base, so C3 builds
  directly on the index-free `Runs` (`refl`/`step`/`call`, `Runs.trans`), the
  single bridge `messageCall_runs` (= `messageCall_runs_calls`, halt via `hhalt`),
  and the opcode rules `runs_push`/`runs_sstore`/`runs_add`/`runs_lt`/`runs_sload`
  (+`sloadFrame_storage_self`)/`runs_gas`/`runs_jump`/`runs_jumpi_*`/
  `runs_jumpdest`/`runs_branch`. `lake build` is green (1126 jobs, up from 1106);
  `#print axioms` on every new lemma = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no native axiom).

  **`LirLean/SmallStep.lean` — the small-step, gas-aware IR semantics** (§3).
  - `IRState { locals : Tmp → Option Word, storage : Word → Word, gas : UInt64 }`
    — `gas` is a **`UInt64`** (not `ℕ`) so it equals `fr.exec.gasAvailable`
    *exactly*: the `Match` gas clause `M4` is a plain `UInt64` equality and each IR
    charge is the same `UInt64.ofNat <const>` subtraction the EVM post-frame does.
    `storage` mirrors the self account through the observable lens (`M3`).
  - `IRHalt` (`stopped` / `returned w`), `IRConf` (`running L pc st` / `halted h`).
  - `evalExpr st : Expr → Option Word` — total via `Option`; **arithmetic is
    exp003's own** (`add → UInt256.add`, `lt → UInt256.lt`, `sload → storage lens`,
    `gas → UInt256.ofUInt64 st.gas`), so the IR value is *definitionally* the word
    the lowered opcode pushes. Helpers `setLocal` / `setStorage` / `charge` mirror
    the EVM post-frame field updates; `blockAt` / `stmtAt` cursor accessors; the gas
    constants `gVerylow`/`gBase`/`gMid`/`gHigh` (= `Gverylow`/`Gbase`/`Gmid`/`Ghigh`)
    and a `matCost` recursion for materialisation cost.

  **`LirLean/Match.lean` — the invariant + the simulation engine** (§6.1, §6.2).
  - `Match prog L pc st fr` is a `structure` with the five clauses of §6.1:
    `pc_eq` (M1, `fr.exec.pc = UInt32.ofNat (pcOf prog L pc)`), `code_eq` (M2),
    `storage_eq` (M3, `∀ k, selfStorage fr k = st.storage k`), `gas_eq` (M4,
    `fr.exec.gasAvailable = st.gas`), `stack_nil` (M5), plus `can_modify`. `pcOf`
    is the offset-table address (prefix sum, computable). `selfStorage` / `storageAt`
    are the observable storage lenses (the latter keyed on an explicit address to
    match exp003's `sstoreFrame_storage_*` form exactly).
  - **Per-construct atomic simulation lemmas** (the bricks `lower_simulates_step`
    threads with `Runs.trans`), each proved by discharging straight to its `runs_*`
    rule and reading back the IR-relevant post-frame fact:
    * `sim_imm` → `runs_push (.PUSH32)`; pushes `w` (the `evalExpr (.imm w)` value).
    * `sim_add` / `sim_lt` → `runs_add` / `runs_lt`; top = `UInt256.add`/`.lt a b`
      (definitionally `evalExpr` of `.add`/`.lt`).
    * `sim_sload` → `runs_sload`; top `= selfStorage fr key` via
      `sloadFrame_storage_self` (the M3 read companion).
    * `sim_gas` → `runs_gas`; gas drops by `gBase`, top = post-charge gas.
    * `sim_sstore` → `runs_sstore`; the written cell reads back `value`
      (`sstoreFrame_storage_self`) and every other cell is unchanged
      (`sstoreFrame_storage_frame`) — i.e. M3 re-established.
    * `sim_jump` → `runs_jump`; pc set to the resolved target.
    * `sim_branch` → `runs_branch` (the CFG combinator, case-split on the runtime
      condition; takes the per-arm `Runs` continuation).
    * `sim_call` → `Runs.call` node from a `CallReturns` witness (built exactly as
      `Examples.CallerProgExample.caller_callReturns`).
    * `halt_stop` / `halt_ret` → `stepFrame_stop` / `stepFrame_return_empty`: the
      halt step the bridge consumes via `hhalt` (terminators are **not** `runs_*`).
  - **Top-level boundary discharge** (`lower_preserves`, §6.3, the bridge half):
    `lower_preserves_discharge` crosses `messageCall_runs` given an assembled
    `Runs fr₀ last` + the terminator halt; `lower_preserves_stop` /
    `lower_preserves_ret` are the two terminator instances (halt from
    `halt_stop`/`halt_ret`). This is the exact half that consumes A's bridge, and it
    already covers **any number** of `Runs.call` nodes in the assembled run (so the
    multi-call discharge is free — C4 is then only the *assembly*, not the bridge).

  **What remains for full C3** (the honest gap — NOT faked with `sorry`): the
  **program-global assembly** of `Runs fr₀ last`. The atomic lemmas are stated
  frame-locally (they take the frame's decode/stack/gas hypotheses), which is what
  lets them compose; the missing engine is `lower_simulates_step` proper —
  induction over the IR statement/terminator stream that, for each construct,
  (i) discharges `M1` by computing `decode (lower prog) (pcOf prog L pc)` = the
  expected opcode from the offset-table prefix sum (the `Decode.lean` `rfl` checks
  do this *per worked program*; the general lemma needs `decode (lower prog)`
  correctness as a theorem, the C2-flagged generic decode lemma), and (ii) threads
  the materialisation pushes (`materialiseExpr` → a `Runs.trans` chain of
  `runs_push`) ahead of each effecting opcode while keeping `M5` (stack returns to
  `[]`). This byte-layout arithmetic over `lower prog` is the bulk of the remaining
  work; the worked single-call program (`Decode.lean`'s `workedCall`) is the
  intended first instantiation once the generic decode lemma lands. C4 (multi-call)
  reuses the same engine — the bridge already composes calls.

- 2026-06-22 (C3b): **Generic `decode_lower` infrastructure — DONE, green,
  axiom-clean.** `lake build` green (1127 jobs, up from 1126); `#print axioms` on
  every new lemma = `[propext, Quot.sound]` (`bget` only `[propext]`) — no `sorryAx`,
  no native axiom. New module `LirLean/DecodeLower.lean`. This closes the
  C2/C3-flagged "generic decode lemma" need: the per-pc `rfl` checks in `Decode.lean`
  reduce the *whole* lowered `ByteArray` by kernel computation per worked program;
  `DecodeLower` factors that into **program-independent** lemmas so a decode fact
  follows from a *list-local* statement about the lowered byte list.

  **The two foundation lemmas** (list-backed `ByteArray` ↔ its list):
  * `bget : ByteArray.get? ⟨l.toArray⟩ n = l[n]?` — the byte `decode` reads at `pc`.
  * `bextract : ((⟨a⟩ : ByteArray).extract b e).data = a.extract b e` — the immediate
    window `decode` slices for a PUSH (then `uInt256OfByteArray`s). Proved by
    unfolding `ByteArray.extract`/`copySlice` to `Array.extract` and discharging the
    empty-slice prefix/suffix + the `b + (e-b) = max b e` window arithmetic.

  **The two generic decode lemmas**, each computing `Evm.decode ⟨l.toArray⟩
  (UInt32.ofNat n)` from a local fact about `l` at `n` (precondition `n < 2^32` so
  `(UInt32.ofNat n).toNat = n`):
  * `decode_nonpush_of_list` — `l[n] = byte`, `pushArgWidth (parseInstr byte) = 0`
    ⇒ decodes to that zero-immediate opcode. Covers every effecting opcode `lower`
    emits (`JUMPDEST/SSTORE/SLOAD/ADD/LT/GAS/JUMP/JUMPI/CALL/STOP/RETURN`).
  * `decode_push_of_list` — `l[n] = byte` a PUSH of width `w > 0` and the immediate
    sublist `l[n+1 .. n+1+w]` `uInt256OfByteArray`s to `imm` ⇒ decodes to that PUSH
    carrying `(imm, w)`. Covers every `PUSH32` literal and `PUSH4` destination.
  Plus `lower`-specialised forms `decode_lower_nonpush` / `decode_lower_push` (via
  `lower_eq_flatBytes : lower prog = ⟨(flatBytes prog).toArray⟩`, `rfl`), phrased
  directly on `lower prog` so a caller supplies `(flatBytes prog)[n]? = some opByte`
  (and the immediate's `uInt256OfByteArray`).

  **Build-exercised end-to-end on the worked program** (`Decode.lean`, two new
  `example`s): a non-push (`JUMPDEST` at pc 0) and a push (`PUSH32 5` at pc 1) are
  re-derived *through* the generic lemmas — the `flatBytes workedCall [n]? = some …`
  byte and the `uInt256OfByteArray …extract… = 5` immediate are each a small
  `rfl`/`decide`, confirming the infrastructure connects. So the generic decode core
  is real and reusable, not just stated.

  **What this leaves for full C3** (still NOT faked): the offset-table **byte-layout
  arithmetic** — proving `(flatBytes prog)[pcOf prog L pc]? = some <expected opByte>`
  (and the immediate sublist) for each construct *as a theorem over arbitrary `prog`*,
  i.e. the prefix-sum decomposition of `flatBytes` at a block's `JUMPDEST + 1 +
  Σ emitted-stmt-lengths`. `DecodeLower` is exactly the brick that turns such a
  list-index fact into a `decode (lower prog) (pcOf …)` fact; the index fact itself is
  the remaining work (provable per-worked-program by `rfl` today via the `lower`
  specialisations, generic over `prog` by induction on the block/statement stream).
  And the **`Runs fr₀ last` assembly** for a worked single-call program: this is the
  large gas-tracked `Runs.trans` chain + a `Runs.call` node carrying a real
  `CallReturns` (a genuine child `drive` run, ≈200 lines in exp003's
  `CallerProgExample.caller_callReturns`); the discharge half across `messageCall_runs`
  is already proved (`lower_preserves_discharge`). `lower_preserves` for `workedCall`
  is therefore **not yet fully closed** — it is gated on (a) the offset-table index
  arithmetic feeding `decode_lower`, and (b) the per-program `CallReturns`/gas
  assembly. Both are mechanical-but-large; neither is stubbed.

- 2026-06-22 (C3c): **Offset-table byte-layout arithmetic + symbolic `M1`
  discharge — DONE, green, axiom-clean.** This closes gap (a) above: the
  offset-table index arithmetic that feeds `decode_lower` is now a **theorem over an
  arbitrary program**, not a per-program `rfl`. `lake build` green (1128 jobs);
  `#print axioms` on the new lemmas = `[propext, Classical.choice, Quot.sound]`
  (`flatMap_split` only `[propext]`) — no `sorryAx`, no native axiom. New module
  `LirLean/Layout.lean`; the `pcOf`-level wrappers live in `LirLean/Match.lean`.

  **`LirLean/Layout.lean`** — the prefix-sum decomposition of `flatBytes prog`:
  * `emitTerm_length_labelOff` / `emitBlockBody_length_labelOff` /
    `blockLen_eq_length` — the lowered byte length is **independent of the resolved
    offset table** (`emitDest` is a fixed-width `PUSH4`), so the measuring pass and
    the emitting pass agree; this is what makes the two-pass offset table the genuine
    byte layout.
  * `flatMap_split` — a `List.flatMap` decomposes around the element at a known
    index into `prefix ++ f a ++ suffix` (generic; reused for both the block stream
    and the statement stream).
  * `blockPrefix_length` — the bytes of the first `i` lowered blocks total exactly
    `offsetTable defs fuel blocks i` (the table *is* the prefix sum of `blockLen`).
  * `flatBytes_block_split` / `flatBytes_block_offset` — `flatBytes prog` decomposes
    around block `L` into `pre ++ (JUMPDEST :: emitBlockBody b_L) ++ suf` with
    `pre.length = offsetTable … L.idx`.
  * `mid_index` — index into the middle of a three-way append.
  * **`stmt_byte_anchor`** (the payoff) — over an arbitrary `prog`, the byte
    `flatBytes prog` holds at `offsetTable … L.idx + 1 + (Σ emitStmt-lengths over the
    first `pc` statements)` is the *head byte* of the statement at `(L, pc)` —
    `(emitStmt … s)[0]`. The full prefix-sum/offset-table arithmetic, discharged once.

  **`LirLean/Match.lean`** — the `pcOf`-level `M1` wrappers:
  * `blockAt_of_toList` — `prog.blockAt L = some b` from the `toList` index witness.
  * `pcOf_eq_anchor` — `pcOf prog L pc` (with its `blockAt`/`getD 0`) **equals** the
    `Layout` anchor index when block `L` is present.
  * **`flatBytes_at_pcOf`** — the generic `M1` byte fact:
    `(flatBytes prog)[pcOf prog L pc]? = (emitStmt … s)[0]?`. Composed with
    `decode_lower_{nonpush,push}` this is `decode (lower prog) (UInt32.ofNat (pcOf …))`
    for the construct — the program-global `M1` discharge the engine consumes per
    statement step.

  **Build-exercised end-to-end** (`LirLean/Decode.lean`, new `example`): decode at the
  **symbolic** `pcOf workedCall ⟨0⟩ 2` (the `sstore` cursor) is derived
  `= PUSH32 5` through `pcOf_eq_anchor → flatBytes_at_pcOf (→ stmt_byte_anchor) →
  decode_lower_push` — no literal pc, no whole-array `rfl`. So `decode_lower` at a
  symbolic offset-table address is real and connected, generically over the program.

  **What this leaves for full C3** (gap (b), unchanged, NOT stubbed): the
  **`Runs fr₀ last` assembly** for a worked single-call program — the gas-tracked
  `Runs.trans` chain of `sim_*`/`runs_push` steps + a `Runs.call` node carrying a
  concrete `CallReturns` (a genuine child `drive` run, the ≈200-line
  `CallerProgExample.caller_callReturns` shape, specific to the callee's bytecode/gas).
  The decode side of every step is now generic (`flatBytes_at_pcOf` + `decode_lower`);
  the discharge across `messageCall_runs` is already proved
  (`lower_preserves_discharge`, any number of calls). What remains is purely the
  per-program frame/gas threading + the child-run `CallReturns` for `workedCall`'s
  single CALL. `lower_preserves` for `workedCall` is therefore **still not fully
  closed end-to-end**, but both halves of `M1` (decode generic; pc arithmetic generic)
  and the bridge half are done; the open piece is the concrete `Runs`/`CallReturns`
  assembly, which is mechanical-but-large and would also bag C4 (the bridge already
  composes multiple `Runs.call` nodes). Nothing is faked with `sorry`.
