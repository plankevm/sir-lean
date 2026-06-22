unsafe def unsafePerformIO {α} [Inhabited α] (io : IO α) : α :=
  match unsafeIO io with
    | Except.ok    a => a
    | Except.error e => panic! s!"unsafePerformIO was a not great idea after all: {e}"

@[implemented_by unsafePerformIO]
def totallySafePerformIO {α} [Inhabited α] (io : IO α) : α := Inhabited.default
