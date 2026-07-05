# Compositional vs. lockstep: why the cyclic headline needs one run-producer

Date: 2026-07-05. An important conclusion from exp005 (recorded from the design discussion
with the lead). Companion to `docs/create/STATUS.md` (the R11 producer is the terminal
obligation) and `docs/target-architecture-2026-07-02.md`.

## The conclusion in one line

The dream is fully compositional — *"each fragment of `lower` turns a bit of IR into a bit of
bytecode with matching semantics (modulo oracles), then glue."* We **have** the per-fragment
half; but EVM bytecode does not compose the way the IR does, so the glue is irreducibly **one
well-founded induction over the actual execution** — the "run-producer" `runFrom_of_driveCorrLog`.

## The compositional half already exists

The local semantics-preservation lemmas are done and green: `sim_stmt` / `sim_term` /
`sim_stmts_block` / `sim_cfg` and the `Corr` match relation (in `Sim/` and `Assembly/`). Each is
exactly "this piece of `lower` preserves semantics modulo the value channel + oracles." What is
missing is only the *assembly*, and the assembly cannot be a structural fold. Five reasons:

1. **There is no "piece of bytecode" in isolation.** `lower` emits one *flat* byte array; control
   flow is `JUMP`/`JUMPI` to **absolute** offsets computed from the whole-program layout
   (`offsetTable`/`flatBytes`). A block's bytecode only behaves correctly *inside the global
   layout* — hence the whole `Decode/` cluster (jumpdest validity, `SegAligned`, offset tables).
   A per-block lemma cannot own its own jump targets.

2. **The EVM stepper is a flat small-step over one frame with a pc into the whole code.** There is
   no "run this sub-array" primitive; the machine advances `pc` until the frame ends, and *where*
   it leaves depends on the global layout. `Runs` is a relation over the whole frame execution —
   you cannot chop it into independent sub-runs and concatenate without already knowing the global
   control flow (which is the induction).

3. **Loops.** The IR CFG has back-edges. A structural fold terminates on a *tree*, not when blocks
   revisit. Cycles force a **well-founded induction over the dynamic execution** (the fuel /
   `totalGas` measure driving the "F2 recursion"), not over static structure. "The program
   revisits this block" is a fact about the *trace*, not the syntax.

4. **The value channel is non-local by construction (spill/recompute).** This lowering does *not*
   keep IR temps in stack registers; it recomputes/spills them (the `Materialise/` layer). A temp
   defined in block A and used in block B is reconstructed at the use site, so the IR-temp ↔
   bytecode-value correspondence spans def-site and every use-site. `Corr` is therefore a
   **whole-state invariant**, and invariants only pay off across an induction. (Why spill and not
   move: see below.)

5. **Oracles + gas are a positional alignment across the run.** CALL/CREATE results come from
   streams; gas is threaded; `RecorderCoupled` ties the recorded bytecode drive to the IR streams
   *positionally over the whole run* — a global relation discharged by walking.

## We had the easy route; it was dropped on purpose

The **acyclic** headline (`lower_conforms_acyclic`, since deleted) used exactly the clean
compositional approach: structural induction on a static block-rank, no dynamic walk. It was
genuinely simpler — and only valid for **loop-free** CFGs. The lead's call was that the general
(cyclic) result is the one worth having; for cyclic control flow there is no way around *an*
induction over the trace.

## Why IR temps are *reconstructed*, not *moved* (the spill/alloc design)

The EVM stack is **not random-access** — you can only reach the top ~16 slots (`DUP`/`SWAP`), and
positions shift as the stack grows/shrinks. Keeping many live IR temps in stack slots would
require full **stack scheduling / register allocation on a stack machine** — the classic hard part
of compiling to the EVM, and a moving target for the layout/decode proofs.

exp005 sidesteps that with the **uniform spill/alloc** design (`docs/uniform-spill-alloc-plan.md`):
every temp gets a **static, uniform location** (`slot = f(tmp)`), and its value is *materialised*
at use — pure temps recomputed from their defining `Expr`, oracle-derived values (gas / sload /
call / create results, which cannot be recomputed symbolically) **spilled** to a fixed slot at the
def-site and loaded at the use-site. Two payoffs: (a) locations are static and uniform, which keeps
the layout/decode proofs tractable; (b) it **killed a vacuity** — the earlier gas/sload universal
was unsatisfiable, and the spill-to-slot-with-materialise channel made the correspondence
provable. The cost is precisely reason #4: the value channel is non-local, so `Corr` must be
carried by the run-producer.

## Relocatable blocks — would it be "overall preferable"?

Partly, and it's worth a design study, but it is **not a silver bullet**:

- **It improves modularity.** Parameterising each block's bytecode by a base offset and proving
  per-block correctness *relative to the base*, then a linking lemma that instantiates bases, would
  push reasons #1–#2 into local, position-parameterised lemmas and shrink the `Decode/` cluster.
- **EVM has no relative jumps.** `JUMP`/`JUMPI` take absolute destinations off the stack; there is
  no PC-relative opcode. So "relocatable" is a *proof-engineering* technique (base-parameterised
  lemmas + a link step), not a bytecode feature — you still resolve to absolute offsets at link.
- **It does not remove the producer.** Loops (#3), the whole-state `Corr` invariant from spill
  (#4), and the positional oracle/gas alignment (#5) still require one trace induction. Relocatable
  blocks make the *local* lemmas cleaner; the *global* walk remains.
- **It's a large refactor of a mostly-green proof.** We are one lemma (`runFrom_of_driveCorrLog`)
  from closing the headline.

**Recommendation:** close the headline under the current design first (the producer is needed
regardless), and treat relocatable blocks as a *v2-architecture* study — most valuable if the
producer's offset sub-lemmas turn out intractable under flat layout, in which case
base-parameterised blocks would ease exactly those sub-lemmas.

## The terminal obligation

`runFrom_of_driveCorrLog` is the single run-producer: the induction that walks the drive from entry
to halt, carrying `Corr` + `RecorderCoupled` + the boundary geometry, firing the local sim bricks
only at reached frames, and yielding the IR `RunFrom` + terminal world equation. It gates the CALL
**and** CREATE flagship ties identically — proving it once closes both. Everything below it is
green; everything above it (`conforms_of_worldeq`) is closed assembly.
