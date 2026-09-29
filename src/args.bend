# shake/args: the process argv, each word reusable, internal (main.bend
# exports it). `IO.args` answers a `&1` list whose first word is the program,
# as C's argv; the rest of a program reads the line more than once, so the
# walk copies the words after that name.
import Base

# a &1 list copied to &2
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      h <> copy(t)

# the words after the program, which `IO.args` gives first; none when it
# gave none
def after(xs: List<&1, String>) -> List<&1, String>:  # noqa: L001 the program name (SHAKE-TRUST-4)
  match xs:
    case Nil{}:
      Nil{}
    case Con{_h, t}:
      t

# the process argv
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv (SHAKE-TRUST-4)
  IO.bind(List<&1, String>, List<&2, String>, IO.args(),
    xs => IO.pure(List<&2, String>, copy(after(xs))))
