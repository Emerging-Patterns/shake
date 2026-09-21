# shake

CLI argument parser for [Bend 2](https://github.com/bendlang/bend). A program
spec is Bend data: `parse` binds flags, options, positionals, and nested
commands; `help` writes usage. `shake/LAWS.bend` states the parser;
`shake/PROOF.bend` proves those laws.

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import 0xebdf72b20ad527103f6efc0d2aa8f1ec/main.bend as Shake
```

## Usage

Print usage with `tool help` or `tool help <command>`. `--help` is consumed
by the Bend runtime of a compiled binary and never reaches the program. A
`--` ends option parsing: every word after it is a positional. A rest
positional keeps every leftover word under one name; `get_all` reads that
list, and `get` still reads one value. Copy `IO.args` so each word can be
read more than once; the runtime also strips `--threads`, `--gpu`, and
`--gpu-build`.

```
git clone https://github.com/Emerging-Patterns/shake
cd shake
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin help
bin/demo.bin greet --name Ada -v
bin/demo.bin add 2 3 --times 2
```

`nix build` builds the same fixture to `result/bin/demo`.
