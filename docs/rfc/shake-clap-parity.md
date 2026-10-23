# RFC: clap's built-ins, an Arguments block, argument names in errors, and checked reads

Read at `9b05b9c` on `main`, bend 2.0.38, bolt v1.17.0. Requested by the maintainer after comparing shake with `bend-cli` (`cli@0.1.0.0` on the hub), which matches clap more closely in four places shake can take without giving up a proved row.

## Draft Status

**State:** Accepted; the rows it adds or rewords are pending until their laws land (see [Rollout](#rollout)).

- [x] <!-- REVIEW-C1 (resolved): `--version` and `-V` are answered by shake, as clap's version flag is, with a new `ParseErr` constructor `NeedVersion{}` and a new `version_of(spec, err)`, beside `help_path`. -->
- [x] <!-- REVIEW-C2 (resolved): a program that declares its own spelling owns the feature. `-h` asks for help only when the current command declares neither the short `h` nor the long `help`; `--version` is answered only when the root declares no long `version`, and `-V` only when it declares neither the short `V` nor the long `version`. bolt declares its own `--version` flag, so nothing changes for it. -->
- [x] <!-- REVIEW-C3 (resolved): `-h` is read only as a whole word, as `--help` is; a cluster `-vh` is not a request for help. This keeps every cluster law as it is. -->
- [x] <!-- REVIEW-C4 (resolved): help pages show the built-in rows, as clap does: `-h, --help  Print help` on every page whose command shake answers help for, and `-V, --version  Print version` on the root page when shake answers the version, each with only the spellings shake answers there. They count for the `[OPTIONS]` hint. -->
- [x] <!-- REVIEW-C5 (resolved): an Arguments block lists the positionals, after Commands and before Options, with the same `[env: ...]`, `[default: ...]` and `[possible values: ...]` extras an option line has. Each block has its own label width, as clap's do. -->
- [x] <!-- REVIEW-C6 (resolved): errors name an argument by its display form, as clap's do (`--name <NAME>`, `--verbose`, `<B>`, `[WHO]`, `<FILES>...`), looked up from the error's path upward; a BadValue for an argument with choices adds clap's `  [possible values: ...]` line. `ParseErr` keeps the binding name; the form is derived in `err_text`. -->
- [x] <!-- REVIEW-C7 (resolved): reads are checked statically, by a new pure `check_reads(spec, reads)`, not at run time. A program lists what it reads (`read_flag(path, name)`, `read_value(path, name)`) and states in its own laws that the list checks. There is no third read kind for `get_all`: `get` and `get_all` both work on every valued kind, so a separate kind would never report anything different. -->

## Problem

Four things a clap user expects are missing from shake, and bend-cli has all four:

1. `-h` and `--version` (`-V`). shake answers `--help` and the word `help`, but `-h` is an unknown argument, and a spec's version shows only on the root page's first line; `tool --version` is an unknown argument.
2. A help page does not list the positionals. The usage line names them, but their help text, default, choices and env var appear nowhere. The env RFC left this open.
3. Errors name an argument by its binding name: `invalid value '8' for 'base'`, `required argument was not provided: b`. clap writes `'--base <BASE>'` and `<B>`, which is what the user typed or has to type.
4. `get(m, "nmae")` answers `None` for a misspelled name, the same as for an option the user did not give. A program cannot tell a typo in its own code from a missing value. bend-cli's readers check each read against the spec and call a mismatch a bug.

## Usage (caller's view)

```bend
def spec() -> Shake.Cli:
  Shake.app("demo", "A tiny command-line program.", Some{"0.1.0"},
    [Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
    [Shake.sub("add", "Add two numbers",
      [Shake.pos("a", "First addend", True{}, None{}, []),
       Shake.pos("b", "Second addend", True{}, None{}, []),
       Shake.opt("base", None{}, Some{"base"}, "Number base", False{}, Some{"10"}, ["10", "16"])],
      [])])

def reads() -> List<&2, Shake.Read>:
  [Shake.read_flag([], "verbose"),
   Shake.read_value(["add"], "a"), Shake.read_value(["add"], "b"),
   Shake.read_value(["add"], "base")]
```

`demo --version` and `demo -V` fail with `NeedVersion{}`, and `Shake.version_of(spec(), err)` is `Some{"demo 0.1.0"}`. `demo add -h` fails with `NeedHelp{["add"]}`. `demo help add` shows

```
add
Add two numbers

Usage: demo add [OPTIONS] <A> <B>

Commands:
  help  Print this message or the help of the given subcommand(s)

Arguments:
  <A>  First addend
  <B>  Second addend

Options:
      --base <BASE>  Number base [default: 10] [possible values: 10, 16]
  -h, --help         Print help
```

`demo add 2 3 --base 8` fails with

```
error: invalid value '8' for '--base <BASE>'
  [possible values: 10, 16]

Usage: demo add [OPTIONS] <A> <B>
...
```

and `Shake.check_reads(spec(), reads())` is `[]`; a misspelled `read_value(["add"], "bsae")` makes it `[NoArg{["add"], "bsae"}]`.

## Shape

```bend
# src/cli.bend
type ParseErr is Data:
  ...                                  # unchanged constructors
  NeedVersion{}

# src/check.bend
type Want is Data:  WantFlag{}  WantValue{}
type Read is Data:  Read{path: List<&2, String>, name: String, want: Want}
type ReadErr is Data:
  NoCommand{path: List<&2, String>}
  NoArg{path: List<&2, String>, name: String}
  NotFlag{path: List<&2, String>, name: String}
  IsFlag{path: List<&2, String>, name: String}

# main.bend, new
def version_of(+spec: S.Cli, err: S.ParseErr) -> Maybe<&2, String>
def Read() -> Data;  def ReadErr() -> Data
def read_flag(path: List<&2, String>, +name: String) -> K.Read
def read_value(path: List<&2, String>, +name: String) -> K.Read
def check_reads(spec: S.Cli, reads: List<&2, K.Read>) -> List<&2, K.ReadErr>
def read_err_text(err: K.ReadErr) -> String
```

**`-h` sits beside `--help` in the walker.** `parse.take_short` reads a body that is exactly `h` as `--help` is read when the current command spells neither `-h` nor `--help` and no positional is bound: the walker enters `Help{}` and the words after it are a help path (SHAKE-PARSE-8). Every other short word goes to `cluster` as today.

**`--version` is decided after the walk.** The walker does not know the spec's version, and its nine-field state is matched at several hundred proof sites, so the version is not threaded through it. `parse` turns a failure `UnknownFlag{[], "--version"}` into `NeedVersion{}` when the spec has a version (and `UnknownFlag{[], "-V"}` when the root also declares no long `version`), and leaves every other result alone. Since the first failure sticks (SHAKE-PARSE-9), this is exactly "the first word that fails the parse is `--version` read at the root". SHAKE-PARSE-9 itself is reworded to say that the words after a failure do not change what `parse` answers, rather than that its answer is the walk's own error, since a root `--version` failure is now answered as `NeedVersion`. Proving that a word `--=...` (SHAKE-TOK-1) is never `--version` needs string equality to be sound; `src/eq.bend` takes `string_eq_true` and the chain below it from ez's `check/str.bend`. `parse_env` runs `parse`, so it answers the version the same way. The rows that promise `UnknownFlag` (SHAKE-TOK-2, TOK-7) name the exception, and their laws gain a premise that the word is not a version request.

**Built-in rows are arguments the page adds.** A page renders its Options block, and its `[OPTIONS]` hint, from the command's arguments followed by synthetic flags for the spellings shake answers there (`help.builtins`). The existing renderers and their laws (`opts_listed`, `usage_listed`) are unchanged; what changes is the list a page gives them. The Arguments block is a new renderer over the positionals with the same line shape as an option line.

**The display form is derived from the spec.** `err_text` finds the argument named in the error on the command at `at`, or the deepest command above it on the path that has one (an env-filled `BadValue` of a root option is reported at the selected path), and renders it as the help page's label does. No walker or `ParseErr` change.

**`check_reads` is `check`'s twin.** It is a pure function of the spec and the list, so a program proves `check_reads(spec(), reads()) == []` once, and every reader in its code is then known to name a declared argument of the right kind. It does not wrap `get`: the reads list is a promise the program makes, as `check(spec)` is.

**What it deliberately does not do.** It does not take `-h` or `-V` inside a cluster. It does not propagate `--version` to subcommands (clap does not by default). It does not show a `help` row for a command that declares its own `--help` and `-h`. It does not add value types (`as_nat`) to arguments: that changes `Arg`, and is a separate RFC.

## Tradeoffs accepted

- We accept a post-walk rewrite for `--version`, and premises on two refusal laws, in exchange for leaving the walker's state alone.
- We accept that `-V` is answered at the root only and after a positional, as clap does, while `-h` follows `--help`'s rule (before any positional of the current command is bound).
- We accept a breaking change to `ParseErr` (a new constructor). Programs that match on it exhaustively must add a case; bolt reads errors through `help_path` and `err_text` and does not.
- We accept that `check_reads` checks only what a program lists. A read missing from the list is not checked.

## Rollout

| Step | What lands | Rows after |
| :---- | :---- | :---- |
| 1 | this RFC; the rows in SPEC.md as pending | SHAKE-HELP-2, HELP-3, HELP-4, ERR-5, PARSE-8, TOK-2, TOK-7, VER-1, VER-2, ERR-1, ERR-2, READ-1 pending |
| 2 | the Arguments block | SHAKE-HELP-3 proved |
| 3 | display forms in errors | SHAKE-ERR-5 proved |
| 4 | `-h`, the help and version rows | SHAKE-PARSE-8, HELP-2, HELP-4 proved |
| 5 | `--version`, `-V`, `version_of`; SHAKE-PARSE-9 reworded | SHAKE-VER-1, VER-2, ERR-1, ERR-2, TOK-2, TOK-7, PARSE-9 proved |
| 6 | `check_reads` | SHAKE-READ-1 proved; no pending rows |
