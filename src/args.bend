# shake/args: the process's arguments, each word reusable, internal (main.bend
# exports it). `IO.args` answers a `&1` list that starts with the program as
# invoked (bend 2.0.32 and later); the rest of a program reads the line more
# than once, so `words` drops that head and copies the rest.
import Base

# a &1 list copied to &2
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      h <> copy(t)

# the arguments of an IO.args line: every word after the program name, copied
def words(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_h, t}:
      copy(t)

# the process's arguments, without the program name
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv (SHAKE-TRUST-4)
  IO.bind(List<&1, String>, List<&2, String>, IO.args(),
    xs => IO.pure(List<&2, String>, words(xs)))
