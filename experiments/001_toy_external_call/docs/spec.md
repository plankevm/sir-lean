# Specification guide

This explains every definition that appears in the statement of
`Preservation.lowering_correct`, why it has the shape it has, and the
inventory of lemmas we had to prove about `EVM.X` because EVMYulLean
provides none. Reading order for the code itself:
`IR.lean` → `Bytecode.lean` → `EVMLemmas.lean` → `Preservation.lean`.

## 1. The theorem, in one picture

```
        run oracle program s              -- IR side: Except Exception Exec
              ‖  (equal after wrapping)
        EVM.X s.fuel vj (injectFrame s.evm 0 [] (lower program))
                                          -- EVM side: Except Exception (ExecutionResult State)
```

Precisely:

```lean
EVM.X s.fuel vj (injectFrame s.evm (.ofNat 0) [] (Bytecode.lower program)) =
  (run oracle program s).map (fun s' =>
    .success
      (injectFrame s'.evm (.ofNat ((Bytecode.lower program).size - 1)) []
        (Bytecode.lower program))
      ByteArray.empty)
```

Read it as three claims at once:

* **Error agreement.** If the IR run fails (`OutOfGass`, `OutOfFuel`,
  `StaticModeViolation`, or an oracle error), `EVM.X` fails with the *same*
  exception, and vice versa. (`Except.map` is the identity on errors.)
* **Success agreement.** If the IR run succeeds with final state `s'`,
  `EVM.X` halts via the terminal `STOP` with output `ByteArray.empty` and a
  machine state that is **equal on the nose** to `s'.evm` — memory, gas,
  `activeWords`, accounts, substate, return data, `execLength` — except for
  the three *frame fields* that `injectFrame` pins (next section).
* **Quantification.** This holds for *every* initial `EVM.State`, every
  fuel value (including too little), every gas level (including too
  little), and every `validJumps` array `vj` (the lowered code never
  jumps, so `Z` never consults it).

The two hypotheses are `CallOracleSound oracle` (§4) and
`(lower program).size < UInt256.size` — the lowered code must be
addressable by a 256-bit program counter. The latter is a representability
bound, not a semantic one (mainnet caps code at 24 576 bytes; our bound
allows ~10⁷⁵).

## 2. `injectFrame` — the simulation relation, as a function

```lean
def injectFrame (evm : EVM.State) (pc : Word) (stack : List Word) (code : ByteArray) :
    EVM.State :=
  { evm with
      pc := pc
      stack := stack
      executionEnv := { evm.executionEnv with code := code } }
```

An IR state (`Exec`) embeds a full `EVM.State`, but three of its fields
are meaningless on the IR side, because the IR has no instruction pointer,
no operand stack, and is not "executing" any bytecode:

| field | meaning on the EVM side | on the IR side |
|---|---|---|
| `pc` | byte offset into the lowered code | — (the IR is structurally recursive) |
| `stack` | operand stack mid-chunk | — (operands are bound by `let`) |
| `executionEnv.code` | the lowered bytecode being executed | — |

The conventional way to relate the two machines would be a simulation
relation `R : Exec → EVM.State → Prop` saying "all fields agree except
pc/stack/code, and pc/stack/code have such-and-such values". `injectFrame`
is that relation *presented as a function*:

```
R s evmState  ⟺  evmState = injectFrame s.evm pc stk code
```

Presenting it functionally is what makes the whole development equational:
every proof step is a `rw`/`congr` on a closed term instead of
constructing and destructing relation witnesses, and the final theorem is
an `=` between two executable expressions (which is also what made the
`#eval` cross-check possible). The cost is that `injectFrame` appears in
the statement, which reads oddly until you know it's the relation.

The invariant maintained by the proof:

* **At instruction boundaries** (before instruction *k* of the program):
  the EVM state is `injectFrame s_k.evm (ofNat offset_k) [] code`, where
  `s_k` is the IR state after the first *k* instructions and `offset_k` is
  the byte offset of instruction *k*'s chunk. Note the empty stack — the
  lowering's stack discipline.
* **Mid-chunk**: same, but the stack holds the operand values pushed so
  far (e.g. `[gas, target, value, inOff, inSize, outOff, outSize]` right
  before the `CALL` opcode).

Everything `injectFrame` does *not* mention is asserted equal by the
theorem. That is the payoff of the locals-as-memory design: there is no
"locals map related to reserved memory slots" clause, because locals *are*
those memory words on both sides.

`EVMLemmas.lean` proves ~15 `@[simp]` projection lemmas
(`injectFrame_gasAvailable`, `injectFrame_accountMap`, …, all `rfl`)
saying every non-frame projection passes through; these do most of the
routine rewriting in the lemma layer.

## 3. The IR semantics (`IR.lean`)

`Exec` is `{ evm : EVM.State, fuel : Nat }`. The fuel field mirrors
`EVM.X`'s fuel argument (EVMYulLean's termination device) one unit per
lowered opcode; carrying it makes the theorem hold for *all* fuel rather
than "sufficient fuel", and it is genuinely semantic for `CALL`, whose
recursion depth in EVMYulLean is fuel-bounded.

Each lowered opcode is executed by `EVM.X` as:

```
fuel check → decode → Z (charge cost₁; check cost₂; validity) → step (fuel guard; trace bump; charge cost₂; effect) → H (halt?)
```

The IR mirrors this with four named micro-actions, composed per opcode:

| IR action | mirrors |
|---|---|
| `tick` | `X`'s fuel check + decrement |
| `chargeMem c₁` / `requireGas c₂` (= `payZ`) | `Z`'s two gas checks (`c₁` deducted, `c₂` only checked) |
| `stepGuard` | `step`'s fuel-≥-1 guard |
| `commit c₂` | `step`'s `execLength` bump + `cost₂` deduction |

and per-opcode steps built from them: `pushStep` (PUSH32, also the
accounting of ADD/CALLDATALOAD), `mloadStep`, `mstoreStep`, `callStep`,
`stopStep`. Instruction semantics (`execInstr`) are `do`-compositions of
these; `run` folds `execInstr` over the program and ends with `stopStep`.

Two details that are easy to miss:

* **Operand order.** `add dst l r` evaluates `r` then `l`, because the
  lowering pushes right-to-left and *evaluation is observable in gas*
  (an `MLOAD` of an uninitialized local expands memory).
* **Cost formulas.** `wordTouchCost`/`callTouchCost` are the
  memory-expansion formulas (`Cₘ`-differences); `CALL`'s `c₂` is
  EVMYulLean's own `EVM.Ccall` evaluated on the `c₁`-charged machine state
  (because `Z` computes `C'` after deducting `cost₁`, and `Ccall` reads the
  gas counter). The IR's gas schedule is thus *defined* to be the lowered
  cost — gas agreement is partly by construction, and the theorem's
  content is that these formulas are what the EVM actually charges, plus
  all the decode/stack/pc/loop/halting correctness.

## 4. The call oracle

```lean
abbrev CallOracle :=
  Nat → Nat → EVM.State →                            -- fuel, gasCost, state at the CALL
  (gas target value inOffset inSize outOffset outSize : Word) →
  Except EVM.ExecutionException (Word × EVM.State)    -- success flag, post state
```

The signature is exactly the `EVM.call` instance the lowered code reaches:
`fuel` is what `EVM.step` passes down (`X`'s fuel − 1), `gasCost` is `Z`'s
`cost₂`, and the state is the caller's state with `cost₁` charged and the
trace bumped (`EVM.call` deducts `cost₂` itself, *after* computing the
63/64 forwarding from the undeducted counter — this is why the oracle
must receive `gasCost` rather than a pre-charged state).

```lean
def CallOracleSound (oracle : CallOracle) : Prop :=
  ∀ fuel gasCost s gas target value inOffset inSize outOffset outSize pc stack code,
    EVM.call fuel gasCost s.executionEnv.blobVersionedHashes
      gas (.ofNat s.executionEnv.codeOwner) target target value value
      inOffset inSize outOffset outSize s.executionEnv.perm
      (injectFrame s pc stack code) =
    (oracle fuel gasCost s gas target value inOffset inSize outOffset outSize).map
      (fun r => (r.1, injectFrame r.2 pc stack code))
```

This single law says two things at once:

1. **Agreement**: the oracle computes what `EVM.call` computes;
2. **Frame insensitivity**: `EVM.call` neither reads nor disturbs
   pc/stack/code — they commute out as the `injectFrame` on both sides.

It is satisfiable: take `oracle f c s args := (EVM.call f c … args s)`,
for which (1) is `rfl` and (2) is a provable fact about `EVM.call`
(its body builds the result from memory/accounts/substate/env fields and
passes the rest of the record through; `Θ` never receives the caller's
frame). Proving (2) and splitting the law in two is the top "next step" —
it would shrink the trusted surface to nothing for call-free programs.

Why quantify over `pc stack code` at all? Because at the point of use the
EVM-side state is `injectFrame s' pc (full argument stack) code` and the
IR-side oracle call sees only `s'`; the law is stated so the rewrite fires
literally at that point.

## 5. The lowering (`Bytecode.lean`) and why `Op` exists

`Bytecode.Op` (7 constructors: `push v`, `calldataload`, `add`, `mload`,
`mstore`, `call`, `stop`) is **not** a redefinition of EVM operations — it
is the compiler's instruction-selection alphabet, and the byte encoding
`opBytes` is defined via EVMYulLean's own `EVM.serializeInstr`. See §7 of
the handoff FAQ below for the full rationale; in short, EVMYulLean's
`Operation .EVM` carries no immediates (a `PUSH32`'s argument lives in the
byte stream, returned separately by `decode`), provides no assembler, and
has ~150 constructors where our case analyses need 7.

`codeBytes : List Op → List UInt8` is deliberately **list-first**; the
`ByteArray` is wrapped only at the end (`lower`). All decode lemmas then
take a hypothesis `code.data.toList = l ++ opBytes op ++ r` and reason
with ordinary list lemmas.

The round-trip back into EVMYulLean is closed by the
`parse_serialize_*` lemmas (`EVM.parseInstr (EVM.serializeInstr w) = some w`)
and the two decode-at-prefix lemmas — i.e. EVMYulLean's *own decoder*
applied to our bytes yields the intended instruction stream.

## 6. The lemma layer (`EVMLemmas.lean`) — what `EVM.X` was missing

EVMYulLean's `EvmYul/EVM/Semantics.lean` proves **zero** theorems; all of
the following had to be built. They are organized bottom-up and all are
reusable for future experiments against `EVM.X`.

### 6.1 Foundations

| lemma | statement gist |
|---|---|
| `toNat_ofNat_of_lt`, `ofNat_add`, `UInt256_ofNat_zero` | the `UInt256` pc arithmetic actually used (`ofNat` round-trips below 2²⁵⁶; `ofNat a + ofNat b = ofNat (a+b)` unconditionally) |
| `injectFrame_*` (≈15, all `rfl`, `@[simp]`) | every non-frame projection of `injectFrame` passes through |
| `parse_serialize_*` (7, all `rfl`) | EVMYulLean's parser inverts its serializer on our opcodes |

### 6.2 Decode at a prefix

| lemma | statement gist |
|---|---|
| `decode_one_byte_at` | `decode code (ofNat l.length) = some (w, none)` when `code.data.toList = l ++ [serializeInstr w] ++ r` |
| `decode_push_at` | `decode code (ofNat l.length) = some (PUSH32, some (v, 32))` when the bytes are `l ++ opBytes (push v) ++ r` — includes the 32-byte immediate extraction and the `toBytes!`/`fromBytes'` round-trip |

### 6.3 One `EVM.X` iteration, dispatched

`EVM.X` is a fueled loop; these four lemmas are "the loop unrolled once",
keyed on how the iteration resolves:

| lemma | resolves as |
|---|---|
| `X_error_Z` | `Z` rejects (out of gas / validity) → `X` returns that error |
| `X_error_step` | `step` fails (e.g. its fuel guard) → `X` returns that error |
| `X_continue` | `step` succeeds, `H` says not halting → `X fuel = X (fuel−1)` on the post state |
| `X_halt_success` | `H` says halting (our `STOP`) → `.ok (.success …)` |

### 6.4 `EVM.Z` evaluated on our states

| lemma | statement gist |
|---|---|
| `Z_generic` | for any opcode passing all validity checks, `Z` is exactly the two-gas-check if-chain; instruction cost supplied as a componentwise hypothesis so it's robust to record display |
| `Z_call` | the `CALL` instance: memory-expansion cost `callTouchCost`, instruction cost `Ccall` on the charged state, plus the static-mode check `¬perm ∧ value ≠ 0` |
| `memExp_*` (6) | `memoryExpansionCost` of each opcode on an `injectFrame` state (0 for stack-only ops; `wordTouchCost`/`callTouchCost` for memory ops) |
| `C'_*` (7) | `C'` of each opcode (`Gverylow`, `Gzero`, `Ccall …`) |

### 6.5 `EVM.step` per opcode (all definitional, `unfold; rfl`)

`step_stop`, `step_push32`, `step_add`, `step_calldataload`, `step_mload`,
`step_mstore` — each: "`step (f+1) c (some (op, arg)) st` = `.ok` of this
explicit record update" — and `step_call`, which exposes the embedded
`EVM.call` application as an `Except.map`.

### 6.6 Per-opcode `X` iteration lemmas (the workhorses)

`X_stop`, `X_push`, `X_add`, `X_calldataload`, `X_mload`, `X_mstore`,
`X_call`, each of the shape

```
EVM.X s.fuel vj (injectFrame s.evm (ofNat l.length) ⟨stack shape⟩ code) =
  match ⟨the corresponding IR action on s⟩ with
  | .error e  => .error e
  | .ok …     => EVM.X s'.fuel vj (injectFrame s'.evm (ofNat (l.length + opSize)) ⟨new stack⟩ code)
```

quantified over all fuel and gas (the match's error branch covers
out-of-fuel/out-of-gas at exactly the right opcode). `X_call` additionally
takes `CallOracleSound` and is where the oracle law is consumed.
`callStep_eval` is a standalone evaluation equation for the IR's `callStep`
(an if-chain), which keeps the `X_call` proof to a deterministic
`rw`-and-`cases` skeleton.

### 6.7 Composition (`Preservation.lean`)

| lemma | composes |
|---|---|
| `operand_chunk` | 1–2 opcodes ⇒ `evalOperand` (const: push; local: push slot + mload) |
| `writeLocal_chunk` | push slot + mstore ⇒ `writeLocal` |
| `*_at` variants | the same with pc as an arbitrary `Nat` plus a side equation — so successive chunks compose without rewriting between `length`-form and `+`-form |
| `instr_chunk` | a whole instruction (`inputLoad`/`add`/`call`) ⇒ `execInstr` |
| `run_simulation` | induction over the program: suffix of chunks ⇒ `run` |
| `lowering_correct` | instantiates at `pre = []`, pc 0 |

## 7. FAQ

**Why not state the theorem with a relation instead of `injectFrame`?**
You can — define `Simulates code src tgt ⟺ tgt = (src.map …)` and restate.
It would read better but prove identically; the equational form is what
the proofs manipulate. A cosmetic wrapper is a reasonable cleanup.

**Why is `vj` (validJumps) a free variable?** `Z` consults it only for
`JUMP`/`JUMPI`, which the lowering never emits, so the theorem holds for
any array — stronger and simpler than computing `D_J`.

**Why `(lower program).size - 1` as the final pc?** `STOP` does not
advance the pc, and `X` halts via `H` right after executing it; the last
byte of the lowered code is the `STOP`.

**Why does the success output say `ByteArray.empty`?** That is `H`'s
output for `STOP` (`RETURN` would carry data; the IR has no `RETURN` yet).

**Where exactly is gas "assumed" vs "proved"?** Nothing about gas is
assumed. The IR's cost formulas are *defined* to match the lowering, and
the lemmas in §6.4 *prove* those formulas equal `Z`'s charges on the
lowered code. What is by-construction is only the choice of the IR's gas
schedule; what is proved is that the schedule is the EVM's.

## 8. Known cleanliness debts

* `CallOracleSound` conflates oracle agreement with `EVM.call` frame
  insensitivity; splitting it (and proving the latter) is the first item
  of future work.
* The theorem statement would read better behind a `Simulates` wrapper
  and with `Exec`'s frame-fields invisibility enforced by construction
  (e.g. a quotient or a dedicated structure without those fields, paying
  an embedding function instead of `injectFrame`).
* `EVMLemmas.lean` carries harmless `unusedSimpArgs` lint warnings.
