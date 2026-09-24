# shake/args: the process argv, each word reusable, internal (main.bend
# exports it). `IO.args` answers a `&1` list; the rest of a program reads the
# line more than once, so the walk copies it.
import Base

# a &1 list copied to &2
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      h <> copy(t)

# the process argv
def argv() -> IO(List<&2, String>):
  IO.bind(List<&1, String>, List<&2, String>, IO.args(),
    xs => IO.pure(List<&2, String>, copy(xs)))
