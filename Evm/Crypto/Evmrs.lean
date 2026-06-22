/--
Native helper binary for primitives not implemented in Lean — ripemd160,
ECDSA recovery, alt_bn128, 4844 point evaluation, and Merkle-Patricia trie
roots (`tools/evmrs`, built by the `evmrs` lakefile target via cargo).
-/
def evmrsExe : String := "tools/evmrs/target/release/evmrs"
