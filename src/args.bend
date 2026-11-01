# shake/args: the process's arguments, each word reusable, and the values of a
# spec's env vars, internal (main.bend exports them). `IO.args` answers a `&1`
# list that starts with the program as invoked (bend 2.0.32 and later); the
# rest of a program reads the line more than once, so `words` drops that head
# and copies the rest.
#
# Trusted, not proved (IO no law reaches; each is one bind, checked by
# reading):
# - A program compiled by bend 2.0.38 hands `IO.args` the program as invoked
#   (the process's `argv[0]`), then the process's words in order and
#   unchanged, less the runtime's: a `+RTS` opens a bracket of runtime
#   options and a `-RTS` closes it (one left open runs to the end), and
#   neither word nor any word inside reaches `IO.args`; at the first `--RTS`
#   it stops looking, drops it and passes every later word through. Every
#   other word reaches it, `--`, `--help`, `--threads`, `--gpu`,
#   `--gpu-build` and `--bend-help` included. Run as `bend file.bend [args]`,
#   `IO.args` is the file as given, then the arguments, after `bend` took a
#   first `--`. This is the C `main` bend emits and bend2/effs/args.c, read
#   from 2.0.38 and confirmed by compiling a program that prints its
#   `IO.args`; 2.0.29, 2.0.32 and 2.0.38 each changed it, so every bend bump
#   rechecks it.
# - `argv` hands on exactly the list `IO.args` answers, through `words`
#   (laws/ArgvDropsProgram.bend).
# - `env_vars(spec)` answers, for each name it asks for
#   (laws/EnvVarsAskedInOrder.bend) and in that order, the name and the
#   value `IO.get_env` answers, unchanged and empty included, and no pair
#   for a name `IO.get_env` fails for. bend 2.0.38 answers `getenv`'s value
#   for a set variable and fails for an unset one (`io_get_env_run` in
#   bend2/effs/get_env.c); every bend bump rechecks it.
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
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv (trusted above)
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
def vars(names: List<&2, String>) -> IO(List<&2, C.Var>):  # noqa: L001 IO: reads env vars (trusted above)
  match names:
    case Nil{}:
      IO.pure(List<&2, C.Var>, [])
    case Con{+hh, tt}:
      IO.bind(Result<&1, &1, U32 & String, String>, List<&2, C.Var>, IO.get_env(hh),
        got => IO.bind(List<&2, C.Var>, List<&2, C.Var>, vars(tt),
          rest => IO.pure(List<&2, C.Var>, kept(hh, got, rest))))

# the env vars a spec names that are set, each with its value
def env_vars(spec: C.Cli) -> IO(List<&2, C.Var>):  # noqa: L001 IO: reads env vars (trusted above)
  vars(C.env.names(spec))
