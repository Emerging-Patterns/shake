# shake/args: the process's arguments, each word reusable, and the values of a
# spec's env vars, internal (main.bend exports them). `IO.args` answers a `&1`
# list that starts with the program as invoked (bend 2.0.32 and later); the
# rest of a program reads the line more than once, so `words` drops that head
# and copies the rest.
import Base
import ./cli.bend as C

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

# a name and its value in front of the pairs, when `IO.get_env` found one
def kept(
  +name: String,
  got: Result<&1, &1, U32 & String, String>,
  rest: List<&2, C.Var>
) -> List<&2, C.Var>:
  match got:
    case Done{vv}:
      (name, vv) <> rest
    case Fail{_e}:
      rest

# the names that are set, each with its value, in order
def vars(names: List<&2, String>) -> IO(List<&2, C.Var>):  # noqa: L001 IO: reads env vars (SHAKE-TRUST-5)
  match names:
    case Nil{}:
      IO.pure(List<&2, C.Var>, [])
    case Con{+hh, tt}:
      IO.bind(Result<&1, &1, U32 & String, String>, List<&2, C.Var>, IO.get_env(hh),
        got => IO.bind(List<&2, C.Var>, List<&2, C.Var>, vars(tt),
          rest => IO.pure(List<&2, C.Var>, kept(hh, got, rest))))

# the env vars a spec names that are set, each with its value
def env_vars(spec: C.Cli) -> IO(List<&2, C.Var>):  # noqa: L001 IO: reads env vars (SHAKE-TRUST-5)
  vars(C.env.names(spec))
