import SirLean.Basic

namespace Sir

structure World  where
  data : Word → Word

def World.get (w : World) (key : Word) := w.data key
def World.set (w : World) (key : Word) (value : Word) : World :=
  { data := fun k =>
      if key = k
      then value
      else w.get k }

end Sir
