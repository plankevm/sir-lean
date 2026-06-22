import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.30.0"

package «evm» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage __name__) (dirname url : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "Evm" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  if !(←System.FilePath.pathExists "EthereumTests") then
    dbg_trace s!"Cloning EthereumTests into a submodule."
    discard <| IO.Process.run {cmd := "git", args := #["submodule", "update", "--init"]}

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[sha256O, keccak256, ffiO]

/-- Build the rust helper binary (`tools/evmrs`) the conform runner shells out to. -/
target evmrs pkg : FilePath := do
  let exe := pkg.dir / "tools" / "evmrs" / "target" / "release" / "evmrs"
  if !(← exe.pathExists) then
    dbg_trace "Building rust helper: cargo build --release (tools/evmrs)"
    let out ← IO.Process.output {
      cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir / "tools" / "evmrs"
    }
    if out.exitCode != 0 then
      error s!"evmrs cargo build failed: {out.stderr}"
  return pure exe

lean_lib «Conform»

@[default_target]
lean_lib «Evm»

@[test_driver]
lean_exe «conform» where
  root := `Conform.Main
  extraDepTargets := #[`evmrs]
