# examples/demo: a small CLI that parses with shake
import Base
import ../../shake/main.bend as Shake
import ../../shake/args.bend as Args

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
def greet.v(v: Bool) -> IO(Unit):
  match v:
    case True{}:
      IO.print("verbose")
    case False{}:
      IO.pure(Unit, Unit{})

# a successful greet
def greet(+m: Shake.Matched) -> IO(Unit):
  do IO<Unit>:
    +who : String <- IO.pure(String,
      Bool.pick(String, String.is_empty(Shake.get(m, "who")),
        Shake.get(m, "name"), Shake.get(m, "who")))
    IO.print("hello " ++ who)
    greet.v(Shake.on(m, "verbose"))

# a successful add
def add(+m: Shake.Matched) -> IO(Unit):
  IO.print(Shake.get(m, "a") ++ " + " ++ Shake.get(m, "b") ++ " x" ++
    Shake.get(m, "times") ++ " base " ++ Shake.get(m, "base"))

# dispatch on the selected path
def run.path(+path: String, +m: Shake.Matched) -> IO(Unit):
  Bool.pick(IO(Unit), String.eq(path, "greet"), greet(m),
    Bool.pick(IO(Unit), String.eq(path, "add"), add(m),
      IO.write(Shake.help(spec(), []))))

# the selected command
def run(+m: Shake.Matched) -> IO(Unit):
  run.path(String.join(Shake.path_of(m), "/"), m)

# a hard error
def fail.err(+app: Shake.Cli, e: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Shake.err_text(app, e))
    IO.die(Unit, 1, "")

# a failed parse: help text, or an error
def fail(+app: Shake.Cli, e: Shake.ParseErr) -> IO(Unit):
  match e:
    case Shake.NeedHelp{path}:
      IO.write(Shake.help(app, path))
    case other:
      fail.err(app, other)

# the parse result
def go(+app: Shake.Cli, r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) ->
  IO(Unit):
  match r:
    case Fail{e}:
      fail(app, e)
    case Done{m}:
      run(m)

def main() -> IO(Unit):
  do IO<Unit>:
    +app : Shake.Cli <- IO.pure(Shake.Cli, spec())
    av : List<&2, String> <- Args.argv()
    go(app, Shake.parse(app, av))
