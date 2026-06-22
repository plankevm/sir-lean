import Evm.PerformIO
import Evm.Crypto.Evmrs
import Evm.Wheels

/--
Run an `evmrs` subcommand whose input is too big for the command line: the
payload goes to a temp file whose path is passed as the first argument,
followed by `extraArgs`.
-/
def runEvmrsWithInputFile (subcommand : String) (payload : String)
    (extraArgs : Array String := #[]) : String :=
  totallySafePerformIO do
    let entropy ← IO.getRandomBytes 3
    let entropy' ← IO.monoNanosNow
    let inputFile := (← IO.FS.createTempDir) / s!"trieInput_{entropy}{entropy'}.txt"
    IO.FS.writeFile inputFile payload
    let result ← IO.Process.run {
      cmd := evmrsExe,
      args := #[subcommand, inputFile.toString] ++ extraArgs
    }
    IO.FS.removeFile inputFile
    pure result

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  let payload := ws.foldl (init := "") λ acc s ↦ acc ++ s.1 ++ "\n" ++ s.2 ++ "\n"
  runEvmrsWithInputFile "trie-root" payload #[ws.size.repr]

/--
State trie root over whole accounts in one `evmrs` call (see the input format
on the rust side). One process per root, instead of one per contract account.
-/
def blobComputeStateRoot (payload : String) : String :=
  runEvmrsWithInputFile "state-root" payload
