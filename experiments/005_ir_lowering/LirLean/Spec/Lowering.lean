import LirLean.Spec.IR
import Evm

/-!
# LirLean — lowering IR → EVM bytecode (fold-based emission)

`lower : Program → ByteArray` emits opcode bytes that exp003's `Evm.decode`
(`EVMLean/Evm/Semantics/Decode.lean`) reads back as the intended opcode stream.
See `docs/ir-design.md` §4 for the layout (per-block `JUMPDEST`, two-pass offset
table, uniform `PUSH4` destination width) and the per-op opcode templates.

## Structure: policy / mechanism / backend

* **Policy** — `defsOf prog : Alloc` decides where each tmp's value lives: spilled
  defs (gas / sload / call-result / create-result) at a private memory slot
  (`Loc.slot (slotOf t)`, stashed once at the def-site and re-read via `MLOAD` on
  use), every other (pure) def rematerialised on use (`Loc.remat e`). `defsOf` is
  the first-find view of the **ordered def-environment** `defEnv prog`.
* **Mechanism** — the per-tmp byte cache `matCache prog`, a structural **left-fold**
  of `matStep` over `defEnv prog` (total — no fuel, structural termination
  throughout), and the emitters `emitStmt`/`emitTerm`/`emitBlockBody`/`emit`, which
  resolve every operand by cache lookup. Program order is a valid topological order
  for `DefEnvOrdered` programs (`docs/phase2a-valuechannel-design.md` §1), which is
  what makes each cache value the fully-expanded operand byte sequence.
* **Backend** — `encode`, the `ByteArray` wrap `Evm.decode` reads.

The full single-call IR surface lowers: storage arithmetic (`sload` / `sstore` /
`add` / `lt`), one external `Stmt.call`, `Stmt.create`/`CREATE2`, and structural
`Term.branch` (`PUSH4 thenOff; JUMPI; PUSH4 elseOff; JUMP`). Decode-compatibility
is established by the decode-anchor theorems in `Decode/DecodeAnchors.lean`:
`Evm.decode (lower prog) pc = expected` at every statement head, intra-statement
cursor, and terminator offset. Nothing in this file is `sorry`- or `axiom`-backed;
it is executable byte emission only.

Opcode bytes (confirmed against `EVMLean/Evm/Instr.lean`):
`STOP 0x00`, `ADD 0x01`, `LT 0x10`, `SLOAD 0x54`, `SSTORE 0x55`, `JUMP 0x56`,
`JUMPI 0x57`, `GAS 0x5a`, `JUMPDEST 0x5b`, `PUSH1 0x60`, `PUSH4 0x63`,
`PUSH32 0x7f`, `CREATE 0xf0`, `CALL 0xf1`, `CREATE2 0xf5`, `RETURN 0xf3`.
-/

namespace Lir

open Evm

/-! ## Opcode bytes (a thin local table, kept in sync with `Evm.Instr`) -/

namespace Byte
def stop     : UInt8 := 0x00
def add      : UInt8 := 0x01
def lt       : UInt8 := 0x10
def pop      : UInt8 := 0x50
def mload    : UInt8 := 0x51
def mstore   : UInt8 := 0x52
def sload    : UInt8 := 0x54
def sstore   : UInt8 := 0x55
def jump     : UInt8 := 0x56
def jumpi    : UInt8 := 0x57
def gas      : UInt8 := 0x5a
def jumpdest : UInt8 := 0x5b
def push4    : UInt8 := 0x63
def push32   : UInt8 := 0x7f
def create   : UInt8 := 0xf0
def call     : UInt8 := 0xf1
def create2  : UInt8 := 0xf5
def ret      : UInt8 := 0xf3
end Byte

/-- Big-endian 4-byte encoding of a `Nat` jump destination (low 32 bits). Read
back by `decode` via `uInt256OfByteArray` (which is big-endian), so the immediate
round-trips to `UInt256.ofNat (n % 2^32)`. -/
def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8),  UInt8.ofNat n ]

/-- 32-byte big-endian encoding of a word (for `PUSH32 imm`). -/
def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

/-! ## Allocation policy — where each tmp lives (`Loc` / `Alloc`)

The lowering's per-value decision is a single *policy* choice — **rematerialise or
spill** (`docs/uniform-spill-alloc-plan.md` §2.1). `Loc` names the two answers; an
`Alloc` is the per-tmp policy: pure defs (`imm`/`tmp`/`add`/`lt`) ⇒ `remat`, the
non-recomputable defs (gas / sload / call-result / create-result) ⇒ `slot`.

`Alloc` is `Tmp → Option Loc` (partial) rather than the total `Tmp → Loc` of the
design sketch: a tmp with **no** definition (used but never assigned — impossible in
a `WellFormed` program) has *no* location, `defsOf`'s `none`. -/

/-- Where a tmp's value lives: rematerialise its defining expression on each use, or
spill it to a fixed memory slot and `MLOAD` on use. -/
inductive Loc where
  /-- Recompute the defining expression `e` at each use (pure, cheap, stable values). -/
  | remat (e : Expr)
  /-- The value lives in EVM memory at `slot n`; load it (`PUSH n; MLOAD`) on use. -/
  | slot  (n : Nat)
deriving DecidableEq, Repr

/-- A per-tmp allocation policy. Partial (`Option`): a tmp with no definition has no
location (the `defsOf … = none` case). -/
abbrev Alloc := Tmp → Option Loc

/-- Legacy fuel-era view (unconsumed by the canonical pipeline; deleted at P9): the
defining-expression a `Loc` flattens to for the old `Tmp → Option Expr` environment,
with `slot n` re-encoded as the generic spill-load `Expr.slot n`. -/
def Loc.toDef : Loc → Expr
  | .remat e => e
  | .slot  n => .slot n

/-- Legacy fuel-era view (unconsumed by the canonical pipeline; deleted at P9): an
`Alloc` flattened to the old `defs : Tmp → Option Expr` environment via `Loc.toDef`. -/
def Alloc.toDefs (a : Alloc) : Tmp → Option Expr := fun t => (a t).map Loc.toDef

/-! ## Shared emission helpers -/

/-- Emit a literal push (`PUSH32 w`). -/
def emitImm (w : Word) : List UInt8 := Byte.push32 :: wordBytesBE w

/-- Private memory slot for a spilled tmp. Unique per tmp id; SSA single-binding
⇒ write-once. Base offset keeps slots clear of the (zero-size) CALL windows. -/
def slotOf (t : Tmp) : Nat := t.id * 32

/-- Emit a destination push (`PUSH4 off`). -/
def emitDest (off : Nat) : List UInt8 := Byte.push4 :: offsetBytesBE off

/-! ## Definition environment (the ordered carrier) + allocation policy

Recompute-on-use needs each tmp's location. `defEnv prog` records the program-order
`(tmp, Loc)` def-sites in `blocks`-then-`stmts` scan order — the **ordered** carrier
the byte-cache fold walks; `defsOf prog` is its first-find view, the program-global
`Alloc`. For `DefEnvOrdered` programs program order is a valid topological order of
the def-graph (`docs/phase2a-valuechannel-design.md` §1.2), so the fold below fully
expands every cache entry. -/

/-- Classify a defining expression into a `Loc`: an `Expr.slot` (the generic
spill-load) is already a `Loc.slot`; everything else rematerialises. -/
def locOfExpr : Expr → Loc
  | .slot n => .slot n
  | e       => .remat e

/-- The ordered def-environment: the program-order `(tmp, Loc)` pairs in
`blocks`-then-`stmts` scan order. Each spilled def — a **gas** assign, an **sload**
assign, a **call result**, a **create result** — carries `Loc.slot (slotOf t)` (the
value is stashed once at the def-site and re-read via `MLOAD` on use, never
re-emitting the fresh/warmth-charged/dynamic opcode); every other (pure) assign
carries the `locOfExpr`-classified `Loc.remat` of its defining expression. This is
the ordered carrier the fold walks; `defsOf` is its `find?`-view
(`defsOf_eq_defEnv_find`). -/
def defEnv (prog : Program) : List (Tmp × Loc) :=
  prog.blocks.toList.flatMap (fun b =>
    b.stmts.filterMap (fun
      | .assign t .gas       => some (t, Loc.slot (slotOf t))
      | .assign t (.sload _) => some (t, Loc.slot (slotOf t))
      | .assign t e          => some (t, locOfExpr e)
      | .call ⟨_, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | .create ⟨_, _, _, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | _                    => none))

/-- **The allocation policy** — the program-global `Alloc`, as the **first-find**
view of the ordered def-environment `defEnv prog`: the FIRST def-site of a tmp id
in program order determines its location (`DefsConsistent` forces every later
def-site to agree). Spilled defs land at `Loc.slot (slotOf t)`; pure defs at
`Loc.remat e` (see `defEnv`). -/
def defsOf (prog : Program) : Alloc :=
  fun t => ((defEnv prog).find? (fun p => p.1 == t)).map (·.2)

/-- **The rematerialisation view of `defsOf`** — the `.remat` projection: the defining
expression of a tmp *when that tmp is rematerialised* (pure `imm`/`tmp`/`add`/`lt`),
and `none` when it is spilled (gas / sload / call / create result, all routed by
`defsOf` to `Loc.slot (slotOf t)`). This decouples the recompute-soundness spine
(`DefsSound`, `DefsSoundS`, `ReadsOf`, `StepScopedS`, the `defsSound_preserved_*`
walk) from `defsOf`'s codomain: the spine feeds these expressions to `evalExpr`, and
a spilled entry never carried a satisfiable recompute claim. -/
def rematOf (prog : Program) (t : Tmp) : Option Expr :=
  match defsOf prog t with
  | some (.remat e) => some e
  | _               => none

/-- Compatibility shim: `allocate = defsOf`, reducible, so the landed statements
spelled over `allocate prog` (the P4/P5 fold twins, `defEnv_entry_eq_allocate`)
unify definitionally with `defsOf prog`. Where syntactic matching fights,
`simp only [allocate]` bridges. Deleted at P9 after the spelling sweep. -/
@[reducible] def allocate (prog : Program) : Alloc := defsOf prog

/-! ## The byte cache: a structural left-fold over `defEnv`

`matCache prog` is the fuel-free materialisation core: walk `defEnv prog` in program
order, and at each def-site bind the tmp to the bytes of its `Loc` — resolving
operand tmps against the cache built *so far*. Define-before-use (`DefEnvOrdered`)
makes each operand's cache value final at its use sites (`matCache_unfold`, the
fold fixpoint), so each cache entry is the fully-expanded push-sequence. Total:
`foldl` over a finite list; an undefined tmp falls back to `emitImm 0`. -/

/-- Materialise an expression's value onto the stack: the push-sequence that leaves
`e`'s value on top, resolving operand tmps against a byte-`cache`. Operands of
binary ops are pushed in reverse so the first operand ends up on top (`a` on top of
`b`). -/
def matExpr (cache : Tmp → List UInt8) : Expr → List UInt8
  | .imm w   => emitImm w
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [Byte.add]
  | .lt  a b => cache b ++ cache a ++ [Byte.lt]
  | .sload k => cache k ++ [Byte.sload]
  | .gas     => [Byte.gas]
  | .slot n  => emitImm (UInt256.ofNat n) ++ [Byte.mload]

/-- The bytes a `Loc` materialises to under a byte-`cache`: `remat e` runs `matExpr`;
`slot n` is the spill-load `PUSH n; MLOAD`. -/
def matLoc (cache : Tmp → List UInt8) : Loc → List UInt8
  | .remat e => matExpr cache e
  | .slot n  => emitImm (UInt256.ofNat n) ++ [Byte.mload]

/-- One fold step: extend the cache by binding `p.1` to the bytes `matLoc` emits for its
`Loc` under the cache built so far. -/
def matStep (c : Tmp → List UInt8) (p : Tmp × Loc) : Tmp → List UInt8 :=
  Function.update c p.1 (matLoc c p.2)

/-- The cache fold over a def-env prefix from an initial cache — the reusable core of
`matCache`, with `init` explicit so fold proofs induct along the def-env. -/
def matFold (init : Tmp → List UInt8) (l : List (Tmp × Loc)) : Tmp → List UInt8 :=
  l.foldl matStep init

/-- The per-tmp byte cache: a structural left-fold of `matStep` over `defEnv prog`,
with the undefined-tmp fallback `emitImm 0`. Fuel-free; structural termination via
`foldl` over a finite list. -/
def matCache (prog : Program) : Tmp → List UInt8 :=
  matFold (fun _ => emitImm 0) (defEnv prog)

/-! ### Reduction lemmas (definitional; keep the fold proofs mechanical) -/

@[simp] theorem matExpr_imm (cache : Tmp → List UInt8) (w : Word) :
    matExpr cache (.imm w) = emitImm w := rfl
@[simp] theorem matExpr_tmp (cache : Tmp → List UInt8) (t : Tmp) :
    matExpr cache (.tmp t) = cache t := rfl
@[simp] theorem matExpr_add (cache : Tmp → List UInt8) (a b : Tmp) :
    matExpr cache (.add a b) = cache b ++ cache a ++ [Byte.add] := rfl
@[simp] theorem matExpr_lt (cache : Tmp → List UInt8) (a b : Tmp) :
    matExpr cache (.lt a b) = cache b ++ cache a ++ [Byte.lt] := rfl
@[simp] theorem matExpr_sload (cache : Tmp → List UInt8) (k : Tmp) :
    matExpr cache (.sload k) = cache k ++ [Byte.sload] := rfl
@[simp] theorem matExpr_gas (cache : Tmp → List UInt8) :
    matExpr cache .gas = [Byte.gas] := rfl
@[simp] theorem matExpr_slot (cache : Tmp → List UInt8) (n : Nat) :
    matExpr cache (.slot n) = emitImm (UInt256.ofNat n) ++ [Byte.mload] := rfl

@[simp] theorem matLoc_remat (cache : Tmp → List UInt8) (e : Expr) :
    matLoc cache (.remat e) = matExpr cache e := rfl
@[simp] theorem matLoc_slot (cache : Tmp → List UInt8) (n : Nat) :
    matLoc cache (.slot n) = emitImm (UInt256.ofNat n) ++ [Byte.mload] := rfl

@[simp] theorem matFold_nil (init : Tmp → List UInt8) :
    matFold init [] = init := rfl
@[simp] theorem matFold_cons (init : Tmp → List UInt8) (p : Tmp × Loc)
    (l : List (Tmp × Loc)) :
    matFold init (p :: l) = matFold (matStep init p) l := rfl

theorem matCache_eq (prog : Program) :
    matCache prog = matFold (fun _ => emitImm 0) (defEnv prog) := rfl

/-! ## Per-construct emission (cache/alloc-driven) -/

/-- Emit the opcode bytes for one statement: operands resolve against the
byte-`cache` (`matCache prog` at the call sites); the `assign` def-site consults
the `Alloc` for its spill slot.

* `assign t e` — a tmp the allocation spills (`alloc t = some (.slot n)`: gas,
  sload, call/create results never reach here — they spill at their own emitters)
  is computed **once** and stashed to its memory slot
  (`matExpr cache e ++ PUSH n ++ MSTORE`); a rematerialised tmp emits **no** bytes —
  its value is recomputed at each use.
* `sstore key value` → cache `value`, cache `key`, `SSTORE` (leaving
  `key :: value :: rest` — the stack shape exp003's `runs_sstore` expects).
* `call cs` → push the seven CALL args (value-free, zero-memory window:
  `out_size, out_off, in_size, in_off, value`, then `callee`, then `gasFwd` on
  top — the `callerProg` order), then `CALL`. The 0/1 success flag CALL pushes is
  stashed to `slotOf t` (`resultTmp = some t`) or `POP`ped.
* `create cs` → push the three create args (empty-init first cut: all 0), then —
  if `cs.salt = some s` — cache the salt and `CREATE2`, else `CREATE`; the pushed
  deployed-address-or-0 word is stashed to `slotOf t` (byte-identical to the CALL
  result stash) or `POP`ped. See `docs/create/BUILD-PLAN.md` §2 Step 4. -/
def emitStmt (cache : Tmp → List UInt8) (alloc : Alloc) : Stmt → List UInt8
  | .assign t e =>
      match alloc t with
      | some (.slot n) => matExpr cache e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
      | _ => []
  | .sstore key value =>
      cache value ++ cache key ++ [Byte.sstore]
  | .call cs =>
      emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ cache cs.callee
      ++ cache cs.gasFwd
      ++ [Byte.call]
      ++ (match cs.resultTmp with
          | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
          | none   => [Byte.pop])
  | .create cs =>
      emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ (match cs.salt with
          | some s => cache s ++ [Byte.create2]
          | none   => [Byte.create])
      ++ (match cs.resultTmp with
          | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
          | none   => [Byte.pop])

/-- Emit the opcode bytes for a terminator: operands resolve against the
byte-`cache`; branch destinations resolve via the offset table `labelOff` (label
index → byte offset of its `JUMPDEST`).

`ret t` pushes the cached bytes of `t` (leaving the returned word `vw` on top),
stashes it to memory at offset `0` (`PUSH32 0; MSTORE` — stack `0 :: vw`, `MSTORE`
pops `addr = 0`, `val = vw`), then returns that 32-byte window
(`PUSH32 32; PUSH32 0; RETURN` — stack `0 :: 32`, `RETURN` pops `offset = 0`,
`size = 32`). So `RETURN(0, 32)` returns exactly `vw`'s big-endian bytes — the
returned value is the observed halt result (`observe` reads it back as
`returned vw`). The tail after `cache t` is
`PUSH32 0 ++ MSTORE ++ PUSH32 32 ++ PUSH32 0 ++ RETURN`, i.e.
`33 + 1 + 33 + 33 + 1 = 101` bytes. -/
def emitTerm (cache : Tmp → List UInt8) (labelOff : Nat → Nat) : Term → List UInt8
  | .ret t              => cache t
                             ++ emitImm 0 ++ [Byte.mstore]
                             ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]
  | .stop               => [Byte.stop]
  | .jump dst           => emitDest (labelOff dst.idx) ++ [Byte.jump]
  | .branch cond thenL elseL =>
      cache cond
      ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
      ++ emitDest (labelOff elseL.idx) ++ [Byte.jump]

/-! ## Block layout (two-pass offset table) -/

/-- Bytes of one block, *excluding* the leading `JUMPDEST`, given the byte-`cache`,
the allocation, and the offset table. Pass 1 measures lengths with a zero offset
table; pass 2 emits with the real table. Both pass through the same function, and
`emitDest` always emits a fixed-width `PUSH4 <off>` (5 bytes) regardless of the
offset value, so the two passes agree on lengths. -/
def emitBlockBody (cache : Tmp → List UInt8) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) : List UInt8 :=
  (b.stmts.flatMap (emitStmt cache alloc)) ++ emitTerm cache labelOff b.term

/-- Length of a lowered block (leading `JUMPDEST` + body). Independent of the
offset table because destination pushes have fixed width. -/
def blockLen (cache : Tmp → List UInt8) (alloc : Alloc) (b : Block) : Nat :=
  1 + (emitBlockBody cache alloc (fun _ => 0) b).length

/-- The offset table: byte offset of block `i`'s `JUMPDEST`, as a prefix sum of
block lengths over `blocks[0..i)`. -/
def offsetTable (cache : Tmp → List UInt8) (alloc : Alloc) (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map (blockLen cache alloc)).sum

/-! ## The composition: `lower = encode ∘ emit (defsOf prog)`

The lowering factors into a **mechanism** (`emit`, cache/alloc-driven byte assembly)
and a **backend** (`encode`, the offset-table-resolved byte concatenation +
`ByteArray` wrap). `emit a prog` reads operand bytes from the total fold cache
`matCache prog` and def-site spill slots from the allocation `a`; with
`a := defsOf prog` the result is the canonical lowering. -/

/-- **Mechanism.** The flat byte list of a program under allocation `a`: each block
lowered as `JUMPDEST :: emitBlockBody`, with branch destinations resolved via
`offsetTable`. Operand bytes come from the fold cache `matCache prog`. -/
def emit (a : Alloc) (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let labelOff := offsetTable cache a prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache a labelOff b)

/-- **Backend.** Wrap an emitted byte list as the `ByteArray` `Evm.decode` reads. -/
def encode (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- **The lowering.** `lower = encode ∘ emit (defsOf prog)`: allocate (policy),
emit (mechanism), encode (backend). The result is a `ByteArray` that `Evm.decode`
reads back as the intended opcode stream (established by the decode-anchor theorems
in `Decode/DecodeAnchors.lean`). -/
def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)

/-! ## Legacy fuel-based materialisation (unconsumed by the canonical pipeline; P9 deletes)

The pre-fold lowering recursed through a `defs : Tmp → Option Expr` environment
under a fuel bound (`recomputeFuel`). The canonical pipeline above no longer
consumes these definitions — operand bytes come from the total fold `matCache`.
They remain compiling solely for the residual generic-`defs` fuel lemmas, and are
deleted at P9 together with `Expr.slot`. NOTE: `matCache` is NOT equal to
`materialiseExpr (defsOf …) (recomputeFuel …)` — `recomputeFuel` undercounts the
recompute depth (~2× per binary level), so no bridge equation exists
(`docs/phase2a-valuechannel-design.md`, 2026-07-07 banner). -/

/-- Legacy (P9-deletes): fuel-bounded expression materialisation. Truncates to `[]`
when fuel runs out — soundness required the deleted `rank_lt_fuel` envelope. -/
def materialiseExpr (defs : Tmp → Option Expr) : Nat → Expr → List UInt8
  | _,      .imm w  => emitImm w
  | _,      .slot slot => emitImm (UInt256.ofNat slot) ++ [Byte.mload]
  | 0,      _       => []                       -- fuel exhausted (ill-formed IR)
  | f + 1,  .tmp t  =>
      match defs t with
      | some e => materialiseExpr defs f e
      | none   => emitImm (0 : Word)            -- undefined tmp → conservative 0
  | f + 1,  .add a b =>
      materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add]
  | f + 1,  .lt a b =>
      materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt]
  | f + 1,  .sload k =>
      materialiseExpr defs f (.tmp k) ++ [Byte.sload]
  | _ + 1,  .gas    => [Byte.gas]

/-- Legacy (P9-deletes): fuel-bounded tmp materialisation. -/
def materialise (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) : List UInt8 :=
  materialiseExpr defs fuel (.tmp t)

/-- Legacy (P9-deletes): the fuel bound the old pipeline threaded (statement count
+ 1). NOT sufficient for deep definition chains — see the module note above. -/
def recomputeFuel (prog : Program) : Nat :=
  (prog.blocks.toList.map (fun b => b.stmts.length)).sum + 1

end Lir
