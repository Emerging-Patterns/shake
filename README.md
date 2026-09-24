# shake

CLI argument parser for [Bend 2](https://github.com/bendlang/bend). A program
spec is Bend data: `parse` binds flags, options, positionals, and nested
commands; `help` writes usage.

## Install

Use with [Bend](https://github.com/bendlang/bend) or install easily with [ez](https://github.com/Emerging-Patterns/ez):

```
ez init
ez add Emerging-Patterns/shake
```

## Usage

```
import 0xdf41d30432187d983a3c5b9db32d376d/main.bend as Shake
```

`main.bend` is the whole interface: the types (`Shake.Cli`, `Shake.Sub`,
`Shake.Arg`, `Shake.Matched`, `Shake.ParseErr`, `Shake.SpecErr`), the
builders (`app`, `sub`, `flag`, `opt`, `pos`, `rest`), `check` and
`spec_err_text`, `parse`, the readers (`get`, `get_all`, `on`, `path_of`),
`help`, `err_text`, `help_path` and `argv`. Everything under `src/` is
internal and may change in any release; import only `main.bend`.
[SPEC.md](SPEC.md) lists what shake guarantees, and which of it is proved.

`check(spec)` lists every way a spec contradicts itself (a rest positional
that is not the last, a repeated name or spelling, a subcommand named
`help`, a default outside its choices, a required positional after an
optional one). `parse` does not call it; the guarantees hold for a spec it
passes, so check yours once, at start or in your own laws.

`parse` fails with a request for help on `tool help` or
`tool help <command>`: `help_path` gives its command path, for `help` to
print, and is `None` for every other error, which `err_text` describes.
A rest positional keeps every leftover word under one name; `get_all` reads
that list, and `get` still reads one value. `argv` is the process's
arguments, each word reusable.

A compiled Bend program's runtime reads the command line before shake does
(bend 2.0.26):

- `--help` prints the runtime's own usage and exits, and `--gpu-build`
  builds the GPU image and exits; neither runs `main`.
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
bin/demo.bin greet --name Ada -v
bin/demo.bin add 2 3 --times 2
```

`nix build` builds the same fixture to `result/bin/demo`.

## Layout

- `main.bend`: the interface.
- `src/`: the implementation, with `src/LAWS.bend` stating the parser's laws
  and `src/PROOF.bend` proving them. `ez prove` is the proof gate.
- `examples/demo/`: a small program that uses only `main.bend`.
- `ez.toml` and `ez.lock.toml`: the ledger and lock; bolt, the linter, is
  pinned there as `[tools.bolt]`, and `nix flake check` runs it.
- `docs/rfc/`: the specification in progress.
