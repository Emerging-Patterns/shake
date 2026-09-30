# shake

CLI argument parser for [Bend 2](https://github.com/bendlang/bend). A program
spec is Bend data: `parse` binds flags, options, positionals, and nested
commands; `help` writes usage.

## Install

With [Bend](https://github.com/bendlang/bend) alone there is nothing to
install: import shake by its hub name, at v0.4.0, and `bend` fetches it from
[the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first run.

```bend
import shake@0.4.0.0/main.bend as Shake
```

`shake@0.4.0.0` resolves to `0xcab8a7a189cec2b51e8db0484f69c593`;
`import 0xcab8a7a189cec2b51e8db0484f69c593/main.bend` pins it by content.
shake needs bend 2.0.32 or later (see below), and is built and checked on
bend 2.0.34.

Or with [ez](https://github.com/Emerging-Patterns/ez), which records the
package in `ez.toml` (`ez init` makes one):

```
ez add Emerging-Patterns/shake
```

## Usage

A spec, a parse, and a read. `Shake.argv()` is the command line without
the program name; `parse` answers `Done` with what the words bound, or
`Fail` with why they could not be bound:

```bend
import shake@0.4.0.0/main.bend as Shake

def spec() -> Shake.Cli:
  Shake.app("hi", "Say hello.", None{},
    [Shake.opt("name", Some{"n"}, Some{"name"}, "Who to greet", False{},
      Some{"world"}, [])],
    [])

def greet(got: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> String:
  match got:
    case Done{mm}:
      "hello " ++ Maybe.default(&2, String, Shake.get(mm, "name"), "")
    case Fail{ee}:
      Shake.err_text(spec(), ee)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&2, String> <- Shake.argv()
    IO.print(greet(Shake.parse(spec(), av)))
```

`bend hi.bend -- --name Ada` prints `hello Ada`, and so does a compiled
`hi.bin --name Ada`. The same code works in an ez project, where
`ez add` has put shake in the ledger.

On bend 2.0.32 and later, `IO.args()` starts with the program as invoked
(`hi.bin`, or `hi.bend` when interpreted), so a program that passes
`IO.args()` straight to `parse` must drop that first word; `Shake.argv()`
does it for you. shake needs bend 2.0.32 or later for that reason.

`main.bend` is the whole interface: the types (`Shake.Cli`, `Shake.Sub`,
`Shake.Arg`, `Shake.Matched`, `Shake.ParseErr`, `Shake.SpecErr`), the
builders (`app`, `sub`, `flag`, `opt`, `many`, `pos`, `rest`), `check` and
`spec_err_text`, `parse`, the readers (`get`, `get_all`, `on`, `sub_name`,
`sub_of`, `at`, `path_of`), `help`, `err_text`, `help_path`, `err_path` and
`argv`. Everything under `src/` is
internal and may change in any release; import only `main.bend`.
[SPEC.md](SPEC.md) lists what shake guarantees, and which of it is proved.

`check(spec)` lists every way a spec contradicts itself (a rest positional
that is not the last, a repeated name or spelling, a subcommand named
`help`, a default outside its choices, a required positional after an
optional one). `parse` does not call it; the guarantees hold for a spec it
passes, so check yours once, at start or in your own laws.

`parse` fails with a request for help on `tool help`, `tool help <command>`,
`tool --help` or `tool <command> --help` (a command that declares its own
long `help` gets `--help` as that argument instead): `help_path` gives its
command path, for `help` to print, and is `None` for every other error,
which `err_text` describes.
A successful parse is read one command at a time, as clap's `ArgMatches`
is: `get`, `get_all` and `on` read the bindings a command made, and
`sub_name(m)` and `sub_of(m, name)` give the subcommand selected under it and
its own `Matched` (`at(m, path)` follows a whole path). A root `-v` and a
subcommand's `-v` are different arguments, so `tool -v greet -v` sets both;
a flag or `opt` option given twice to one command is refused. A rest
positional keeps every leftover word under one name; `get_all` reads that
list, and `get` still reads one value. `argv` is the process's
arguments, each word reusable.

A compiled Bend program's runtime reads the command line before shake does
(bend 2.0.34):

- `--bend-help` prints the runtime's own usage and exits, and `--gpu-build`
  builds the GPU image and exits; neither runs `main`. `--help` reaches
  the program, and shake reads it as a request for help.
- `--threads N` and `--gpu X` are taken, with their value, and a bad value
  stops the program.
- The first `--` is taken too, and every word after it is passed on
  unexamined.

So a `--` ends shake's option parsing (every later word is a positional)
only when it is the second one: `tool add -- -- -5 3` binds `-5` and `3`.

```
git clone https://github.com/Emerging-Patterns/shake
cd shake
mkdir -p bin
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin help
bin/demo.bin greet --help
bin/demo.bin greet --name Ada -v
bin/demo.bin add 2 3 --times 2
```

`nix build` builds the same fixture to `result/bin/demo`.

## Layout

- `main.bend`: the interface.
- `src/`: the implementation, with `src/LAWS.bend` stating the parser's laws
  and `src/PROOF.bend` proving them. `nix flake check` runs the proof gate.
- `examples/demo/`: a small program that uses only `main.bend`.
- `ez.toml` and `ez.lock.toml`: the ledger and lock; bolt, the linter, is
  pinned there as `[tools.bolt]`, and `nix flake check` runs it.
- `docs/rfc/`: the specification in progress.
