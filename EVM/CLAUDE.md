# LeanEVM

Executable Lean 4 specification of the EVM, tested against the Ethereum
BlockchainTests fixtures (`lake exe conform <threads>`).

## Native helpers

The conform runner shells out to `tools/evmrs` (rust; built automatically by
the `evmrs` lakefile target) for: ripemd160, ECDSA sender recovery (fallback —
fixtures usually carry `sender`), alt_bn128 add/mul/pairing, 4844 point
evaluation, and Merkle-Patricia trie roots (fallback — only blocks expecting
exceptions and hash-only postState fixtures need them; `state-root` computes
a whole state root, storage tries included, in one process).

## Python

There is no python in this repo (evmrs + C FFI replaced it). If python is ever
needed for a one-off, **always and only use `uv`** — never `pip install` into
the system or user site-packages, never `--break-system-packages`.

## Conform suite notes

- **Never run a test sample without first proving it runs ≤30s** (estimate
  from a measured tier). Full runs are for phase gates only, with user
  sign-off. The default `lake exe conform 8` runs the **fast phase** — a
  curated sample (`FastSample`, ~2,900 tests, ~8s wall on 8 threads) — the
  iteration default after every change. `--full` runs the whole conformance
  phase (22,308 tests, ~2 min wall on 8 threads; what CI runs). `--perf`
  additionally runs the throughput stress tests (`vmPerformance/` + blake2f
  max rounds — minutes per test, raw 256-bit arithmetic, no extra semantic
  coverage).
- A second CLI arg substring-filters fixture file paths for quick samples:
  `lake exe conform 8 stMemoryTest`.
- `nproc` does not exist on macOS; always pass an explicit thread count.
- Per-test results land in `tests_0.txt` (fast/filtered) or `tests_1.txt`
  (`--full`); expected failures are listed in `Conform/Main.lean`.

## Proof conventions

Prefer `grind`; avoid axiom-introducing tactics (`native_decide`). `bv_decide`
also depends on `ofReduceBool` — fallback only, currently used solely for the
`UInt256` limb/`BitVec 256` equivalence theorems in `Evm/UInt256.lean`.
