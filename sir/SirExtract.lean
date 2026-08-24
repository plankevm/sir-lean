import Sir.Text.Extract

private def readFile (path : System.FilePath) : IO (Except IO.Error String) := do
  try
    return .ok (← IO.FS.readFile path)
  catch error =>
    return .error error

private def writeFile (path : System.FilePath) (contents : String) : IO (Except IO.Error Unit) := do
  try
    return .ok (← IO.FS.writeFile path contents)
  catch error =>
    return .error error

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [input, output, declaration] =>
      match ← readFile input with
      | .error error =>
          IO.eprintln s!"{input}: {error}"
          return 1
      | .ok source =>
          match Sir.Vars.Text.extract source declaration with
          | .error message =>
              IO.eprintln s!"{input}: {message}"
              return 1
          | .ok module =>
              match ← writeFile output module with
              | .ok _ => return 0
              | .error error =>
                  IO.eprintln s!"{output}: {error}"
                  return 1
  | _ =>
      IO.eprintln "usage: sir-extract <input.sir> <output.lean> <declaration>"
      return 1
