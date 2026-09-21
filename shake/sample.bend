# shake/sample: a fixture Cli the laws parse
import Base
import ./main.bend as Shake

# flags, options, positionals, one nested command
def spec() -> Shake.Cli:
  Shake.app("demo", "A tiny command-line program.", Some{"0.1.0"},
    [Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
    [
      Shake.sub("greet", "Print a greeting",
        [
          Shake.opt("name", Some{"n"}, Some{"name"}, "Who to greet", False{},
            Some{"world"}, []),
          Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output"),
          Shake.pos("who", "Who to greet", False{}, None{}, [])
        ], []),
      Shake.sub("add", "Add two numbers",
        [
          Shake.pos("a", "First addend", True{}, None{}, []),
          Shake.pos("b", "Second addend", True{}, None{}, []),
          Shake.opt("color", None{}, Some{"color"}, "A color", False{}, None{},
            ["red", "green", "blue"])
        ],
        [Shake.sub("more", "A nested add", [], [])])
    ])
