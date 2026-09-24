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
          Shake.many("tag", Some{"t"}, Some{"tag"}, "A tag to add, as often as wanted", False{},
            None{}, []),
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

# the tags line, when any were given
def greet.tags(tags: List<&2, String>) -> IO(Unit):
  match tags:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{hh, tt}:
      IO.print("tags: " ++ String.join(hh <> tt, " "))

# the value bound to `name`, or "" when nothing bound it
def text(+mm: Shake.Matched, +name: String) -> String:
  Maybe.default(&2, String, Shake.get(mm, name), "")

# a successful greet: `who` when given, else `--name`, which has a default;
# verbose when the root's `-v` or greet's own is set
def greet(+root: Shake.Matched, +mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  do IO<Unit>:
    +who : String <- IO.pure(String,
      Maybe.default(&2, String, Shake.get(mm, "who"), text(mm, "name")))
    IO.print("hello " ++ who)
    greet.tags(Shake.get_all(mm, "tag"))
    greet.v(Bool.or(Shake.on(root, "verbose"), Shake.on(mm, "verbose")))

# a successful add
def add(+mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  IO.print(text(mm, "a") ++ " + " ++ text(mm, "b") ++ " x" ++ text(mm, "times") ++ " base " ++
    text(mm, "base"))

# the root's help page, when no subcommand was selected
def run.none() -> IO(Unit):
  IO.write(Shake.help(spec(), []))

# greet with its own Matched
def run.greet(+root: Shake.Matched, sel: Maybe<&2, Shake.Matched>) -> IO(Unit):
  match sel:
    case Some{mm}:
      greet(root, mm)
    case None{}:
      run.none()

# add with its own Matched
def run.add(sel: Maybe<&2, Shake.Matched>) -> IO(Unit):
  match sel:
    case Some{mm}:
      add(mm)
    case None{}:
      run.none()

# dispatch on the name of the subcommand selected
def run.sub(+root: Shake.Matched, sel: Maybe<&2, String>) -> IO(Unit):
  match sel:
    case None{}:
      run.none()
    case Some{name}:
      Bool.pick(IO(Unit), String.eq(name, "greet"), run.greet(root, Shake.sub_of(root, "greet")),
        run.add(Shake.sub_of(root, "add")))

# the root's Matched: dispatch on its subcommand
def run(+mm: Shake.Matched) -> IO(Unit):  # noqa: L001 IO
  run.sub(mm, Shake.sub_name(mm))

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
