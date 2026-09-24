# examples/demo: a small CLI that parses with shake
import Base
import ../../main.bend as Shake

# the program spec
def spec() -> Shake.Cli:
  Shake.app("demo", "A tiny command-line program.", Some{"0.1.0"},
    [Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
    [
      Shake.sub("greet", "Print a greeting",
        [
          Shake.opt("name", Some{"n"}, Some{"name"}, "Who to greet", False{},
            Some{"world"}, []),
          Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output"),
          Shake.pos("who", "Optional who, overrides --name", False{}, None{}, [])
        ], []),
      Shake.sub("add", "Add two numbers",
        [
          Shake.pos("a", "First addend", True{}, None{}, []),
          Shake.pos("b", "Second addend", True{}, None{}, []),
          Shake.opt("times", None{}, Some{"times"}, "How many times", False{},
            Some{"1"}, []),
          Shake.opt("base", None{}, Some{"base"}, "Number base", False{},
            Some{"10"}, ["10", "16"])
        ], [])
    ])

# the verbose line, when asked
def greet.v(vv: Bool) -> IO(Unit):
  match vv:
    case True{}:
      IO.print("verbose")
    case False{}:
      IO.pure(Unit, Unit{})

# a successful greet
def greet(+mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  do IO<Unit>:
    +who : String <- IO.pure(String,
      Bool.pick(String, String.is_empty(Shake.get(mm, "who")),
        Shake.get(mm, "name"), Shake.get(mm, "who")))
    IO.print("hello " ++ who)
    greet.v(Shake.on(mm, "verbose"))

# a successful add
def add(+mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  IO.print(Shake.get(mm, "a") ++ " + " ++ Shake.get(mm, "b") ++ " x" ++
    Shake.get(mm, "times") ++ " base " ++ Shake.get(mm, "base"))

# dispatch on the selected path
def run.path(+path: String, +mm: Shake.Matched) -> IO(Unit):
  Bool.pick(IO(Unit), String.eq(path, "greet"), greet(mm),
    Bool.pick(IO(Unit), String.eq(path, "add"), add(mm),
      IO.write(Shake.help(spec(), []))))

# the selected command
def run(+mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  run.path(String.join(Shake.path_of(mm), "/"), mm)

# a hard error
def fail.err(+app: Shake.Cli, ee: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Shake.err_text(app, ee))
    IO.die(Unit, 1, "")

# help text for a request for help, else the error
def fail.at(+app: Shake.Cli, ask: Maybe<&2, List<&2, String>>, ee: Shake.ParseErr) -> IO(Unit):
  match ask:
    case Some{path}:
      IO.write(Shake.help(app, path))
    case None{}:
      fail.err(app, ee)

# a failed parse: help text, or an error
def fail(+app: Shake.Cli, +ee: Shake.ParseErr) -> IO(Unit):  # noqa: L001 IO
  fail.at(app, Shake.help_path(ee), ee)

# the parse result
def go(  # noqa: L001 IO
  +app: Shake.Cli,
  rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>
) -> IO(Unit):
  match rr:
    case Fail{e}:
      fail(app, e)
    case Done{m}:
      run(m)

def main() -> IO(Unit):  # noqa: L001 IO
  do IO<Unit>:
    +app : Shake.Cli <- IO.pure(Shake.Cli, spec())
    av : List<&2, String> <- Shake.argv()
    go(app, Shake.parse(app, av))
