# shake

CLI argument parser for [Bend 2](https://github.com/bendlang/bend).

## Install

Install Bend, then import the library from a program in this tree:

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import ./shake/main.bend as Shake
```

Or with nix, `nix develop` puts `bend` on PATH.

## Help

shake ships a `help` subcommand. Print usage with `tool help` or
`tool help <command>`. `--help` is consumed by the Bend runtime of a compiled
binary and never reaches the program.

A `--` ends option parsing: every word after it is a positional.

## Build the fixture

```
git clone https://github.com/Emerging-Patterns/shake
cd shake
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin help
bin/demo.bin greet --name Ada -v
bin/demo.bin add 2 3 --times 2
```

`nix build` builds the same fixture to `result/bin/demo`.

## API

A program spec is Bend data, not a macro:

```
Cli { name, about, version?, args, subcommands }
Arg { name, short?, long?, kind: Flag | Opt | Pos, help, required, default?, choices? }
Sub { name, about, args, subcommands }
```

```
parse(app, argv) -> Result<Matched, ParseErr>
help(app, path) -> String
```

`Matched` is the selected subcommand path and the bindings for flags, options,
and positionals. `ParseErr` is `UnknownFlag`, `Missing`, `BadValue`,
`NeedHelp`, or `Unexpected`.

```
import Base
import ./shake/main.bend as Shake

def spec() -> Shake.Cli:
  Shake.app("demo", "A tiny command-line program.", Some{"0.1.0"},
    [Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
    [Shake.sub("greet", "Print a greeting",
      [Shake.opt("name", Some{"n"}, Some{"name"}, "Who to greet", False{},
        Some{"world"}, [])], [])])

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&2, String> <- Shake.argv()
    IO.print(Shake.show(Shake.parse(spec(), av)))
```

`Shake.argv` copies `IO.args` so each word can be read more than once. The
Bend runtime strips `--threads`, `--gpu`, `--gpu-build`, and `--help`;
everything after a `--` is program argv.

## Tests

Each file under `shake/tests/` prints `ok` lines and ends in a `#|` trailer
naming those lines.

```
bend shake/tests/parse.bend
bend shake/tests/err.bend
bend shake/tests/help.bend
```
