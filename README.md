# shake

CLI argument parser for [Bend 2](https://github.com/bendlang/bend). A program
spec is Bend data: `parse` binds flags, options, positionals, and nested
commands; `help` writes usage. `shake/LAWS.bend` states the parser;
`shake/PROOF.bend` proves those laws.

## Install

Install Bend, then import the library from a program in this tree:

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import ./shake/main.bend as Shake
import ./shake/args.bend as Args
```

Or with nix, `nix develop` puts `bend`, `ez`, and `bolt` on PATH.

## Usage

Print usage with `tool help` or `tool help <command>`. `--help` is consumed
by the Bend runtime of a compiled binary and never reaches the program. A
`--` ends option parsing: every word after it is a positional. `Args.argv`
copies `IO.args` so each word can be read more than once; the runtime also
strips `--threads`, `--gpu`, and `--gpu-build`.

```
git clone https://github.com/Emerging-Patterns/shake
cd shake
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin help
bin/demo.bin greet --name Ada -v
bin/demo.bin add 2 3 --times 2
```

`nix build` builds the same fixture to `result/bin/demo`.
