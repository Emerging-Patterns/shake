# shake: CLI argument parser for Bend 2. Describe a program with `app`, `sub`,
# `flag`, `opt`, `pos` and `rest`; `parse` binds argv against it, and `get`,
# `get_all`, `on` and `path_of` read the result. `help` writes the usage page
# for a command path, `err_text` the message for a failed parse, and
# `help_path` tells a request for help from an error. `check` reports a spec
# that contradicts itself. `argv` is the process's arguments. This file is
# the interface: everything under src/ is internal.
import Base
import ./src/cli.bend as S
import ./src/args.bend as Args
import ./src/check.bend as K

# a program spec
def Cli() -> Data:
  S.Cli

# a nested command
def Sub() -> Data:
  S.Sub

# one argument: a flag, an option, a positional or a rest positional
def Arg() -> Data:
  S.Arg

# a successful parse: the selected command path and the bindings
def Matched() -> Data:
  S.Matched

# a failed parse
def ParseErr() -> Data:
  S.ParseErr

# one way a spec contradicts itself
def SpecErr() -> Data:
  K.SpecErr

# a program: name, about, optional version, top-level args and commands
def app(
  +name: String,
  +about: String,
  version: Maybe<&2, String>,
  args: List<&2, S.Arg>,
  subs: List<&2, S.Sub>
) -> S.Cli:
  S.app(name, about, version, args, subs)

# a nested command
def sub(
  +name: String,
  +about: String,
  args: List<&2, S.Arg>,
  subs: List<&2, S.Sub>
) -> S.Sub:
  S.sub(name, about, args, subs)

# a boolean flag
def flag(
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String
) -> S.Arg:
  S.flag(name, short, long, help)

# a valued option
def opt(
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.opt(name, short, long, help, required, default, choices)

# a positional
def pos(
  +name: String,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.pos(name, help, required, default, choices)

# a rest positional: every leftover word, as one name
def rest(
  +name: String,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.rest(name, help, required, default, choices)

# every way a spec contradicts itself: a rest positional that is not the
# last, a repeated argument name or spelling, a repeated subcommand name, a
# subcommand named `help`, a default outside its choices, a required
# positional after an optional one. Empty for a well-formed spec, which is
# what SPEC.md's parse guarantees are about; `parse` does not call it
def check(spec: S.Cli) -> List<&2, K.SpecErr>:
  K.check(spec)

# a report of `check` as one line
def spec_err_text(err: K.SpecErr) -> String:
  K.text(err)

# argv against a program spec
def parse(spec: S.Cli, words: List<&2, String>) -> Result<&2, &2, S.ParseErr, S.Matched>:
  S.parse(spec, words)

# the value bound to `name` last, or "" when there is none
def get(found: S.Matched, +name: String) -> String:
  S.get(found, name)

# every value bound to `name`, in argv order
def get_all(found: S.Matched, +name: String) -> List<&2, String>:
  S.get_all(found, name)

# whether a flag named `name` was set
def on(found: S.Matched, +name: String) -> Bool:
  S.on(found, name)

# the selected command path
def path_of(found: S.Matched) -> List<&2, String>:
  S.path_of(found)

# the usage page for `path` under `spec`; an unknown name in the path is
# skipped
def help(+spec: S.Cli, path: List<&2, String>) -> String:
  S.help(spec, path)

# the message for a failed parse, ending with the root usage line; empty for
# a request for help, which the caller answers with `help`
def err_text(+spec: S.Cli, err: S.ParseErr) -> String:
  S.err_text(spec, err)

# the command path of a request for help (`help`, `help <path>`), or None
# when the parse failed for another reason
def help_path(err: S.ParseErr) -> Maybe<&2, List<&2, String>>:
  match err:
    case S.NeedHelp{path}:
      Some{path}
    case S.UnknownFlag{_flag}:
      None{}
    case S.Missing{_name}:
      None{}
    case S.NoValue{_name}:
      None{}
    case S.BadValue{_name, _value}:
      None{}
    case S.Unexpected{_arg}:
      None{}

# the process's arguments, each word reusable. A compiled program's runtime
# has already acted on `--help`, `--gpu-build`, `--threads N` and `--gpu X`
# and taken the first `--`, passing every word after it here unexamined; so
# the `--` that `parse` sees is the user's second one
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv
  Args.argv()
