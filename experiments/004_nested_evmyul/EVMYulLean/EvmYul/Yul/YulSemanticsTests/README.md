# Testing the Yul semantics

To test the Yul semantics with a custom Solidity smart contract, follow these guidelines.

1.

Compile the contracts to test into Yul such as with:

```
SOLC_VERSION=0.8.30 solc --optimize --ir-optimized --yul-optimizations 'ho[esj]x[esVur]' Storage.sol > Storage.yul
```

`solc-select` can be obtained via running `nix-shell` in this directory (to get Nix see https://nixos.org).

2. Follow the example of `Main.lean` and put the dispatcher (which is the Yul code between the braces without a function name, after, e.g. `object "Storage_25_deployed"`) into the body of `dispatcher := ...` inside a definition of type `YulContract`. Enclose the Yul code inside the syntax `<s ... >`. Remove comments and `memoryguard(...)` (keep the argument of `memoryguard`).

3. Follow the example of `Main.lean` and add each named function in the `FinMap` of `functions := ...` where the key of the `FinMap` is a string of the name of the function (with no arguments). Enclose the Yul function (including it's name and arguments) inside the syntax `<f ... >`. Remove comments and `memoryguard(...)` (keep the argument of `memoryguard`).

4. Set up a call, such as in the example of `test₁` in `Main.lean`. Note that the `codeOwner` in the state needs to be set appropriately, such as to the address, `callerAddress` of the smart contract as it has been defined in the state.

5. Due to dependencies on foreign functions, we need to use `lake exe yulSemanticsTests` to run the tests (rather than `#eval`). If necessary modify `lakefile.lean` to run your `.lean` file, see the example of `lean_exe «yulSemanticsTests»`.