# shake: CLI argument parser for Bend 2. Describe a program with `app`, `sub`,
# `flag`, `opt`, `many`, `pos` and `rest`; `parse` binds argv against it, and
# the result is read one command at a time, as clap's: `get`, `get_all` and
# `on` read a command's own bindings, and `sub_name`, `sub_of`, `at` and
# `path_of` reach the subcommands selected under it. `help` writes the usage
# page for a command path. For a failed parse, `help_path` tells a request for help
# from an error, `err_text` writes the message and `err_path` names the command
# it failed in. `check` reports a spec that contradicts itself. `argv` is the
# process's arguments. This file is the interface: everything under src/ is
# internal.
import Base
import ./src/cli.bend as S
import ./src/args.bend as Args
import ./src/check.bend as K

# a program spec
def Cli() -> Data:
  S.Cli

# a nested command
def Sub() -> Data:  # noqa: L001 a type alias of the interface
  S.Sub

# one argument: a flag, an option, a positional or a rest positional
def Arg() -> Data:  # noqa: L001 a type alias of the interface
  S.Arg

# a successful parse, one command at a time: the bindings the command made,
# and the subcommand selected under it with its own Matched
def Matched() -> Data:
  S.Matched

# a failed parse
def ParseErr() -> Data:
  S.ParseErr

# one way a spec contradicts itself
def SpecErr() -> Data:  # noqa: L001 a type alias of the interface
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
def sub(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
  +name: String,
  +about: String,
  args: List<&2, S.Arg>,
  subs: List<&2, S.Sub>
) -> S.Sub:
  S.sub(name, about, args, subs)

# a boolean flag
def flag(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String
) -> S.Arg:
  S.flag(name, short, long, help)

# a valued option
def opt(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.opt(name, short, long, help, required, default, choices)

# an option that may be given more than once; `get_all` reads every value, in
# order, and `get` the last
def many(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.many(name, short, long, help, required, default, choices)

# a positional
def pos(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
  +name: String,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> S.Arg:
  S.pos(name, help, required, default, choices)

# a rest positional: every leftover word, as one name
def rest(  # noqa: L001 a builder: its result is the Arg or Sub it names, nothing to state
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

# the value this command bound to `name` last, or None when it bound none
def get(found: S.Matched, +name: String) -> Maybe<&2, String>:
  S.get(found, name)

# every value this command bound to `name`, in argv order
def get_all(found: S.Matched, +name: String) -> List<&2, String>:
  S.get_all(found, name)

# whether this command's flag named `name` was set
def on(found: S.Matched, +name: String) -> Bool:
  S.on(found, name)

# the names of the subcommands selected below this command, in order: the
# whole selected path for the Matched `parse` answers
def path_of(found: S.Matched) -> List<&2, String>:
  S.path_of(found)

# the name of the subcommand selected under this command, or None
def sub_name(found: S.Matched) -> Maybe<&2, String>:
  S.sub_name(found)

# the Matched of subcommand `name` when it is the one selected, else None
def sub_of(found: S.Matched, +name: String) -> Maybe<&2, S.Matched>:
  S.sub_of(found, name)

# the Matched of the command `path` names below this one, following `sub_of`
# name by name, or None where a name is not the one selected
def at(found: S.Matched, path: List<&2, String>) -> Maybe<&2, S.Matched>:
  S.at(found, path)

# the usage page for `path` under `spec`; an unknown name in the path is
# skipped
def help(+spec: S.Cli, path: List<&2, String>) -> String:
  S.help(spec, path)

# the message for a failed parse, ending with the root usage line; empty for
# a request for help, which the caller answers with `help`
def err_text(+spec: S.Cli, err: S.ParseErr) -> String:
  S.err_text(spec, err)

# the command path where the parse failed: the path selected when it did, or
# for a request for help the path it asks about
def err_path(err: S.ParseErr) -> List<&2, String>:
  match err:
    case S.UnknownFlag{at, _flag}:
      at
    case S.Missing{at, _name}:
      at
    case S.NoValue{at, _name}:
      at
    case S.BadValue{at, _name, _value}:
      at
    case S.NeedHelp{path}:
      path
    case S.Unexpected{at, _arg}:
      at
    case S.Repeated{at, _name}:
      at

# the command path of a request for help (`help`, `help <path>`), or None
# when the parse failed for another reason
def help_path(err: S.ParseErr) -> Maybe<&2, List<&2, String>>:
  match err:
    case S.NeedHelp{path}:
      Some{path}
    case S.UnknownFlag{_at, _flag}:
      None{}
    case S.Missing{_at, _name}:
      None{}
    case S.NoValue{_at, _name}:
      None{}
    case S.BadValue{_at, _name, _value}:
      None{}
    case S.Unexpected{_at, _arg}:
      None{}
    case S.Repeated{_at, _name}:
      None{}

# the process's arguments, each word reusable. A compiled program's runtime
# has already acted on `--help`, `--gpu-build`, `--threads N` and `--gpu X`
# and taken the first `--`, passing every word after it here unexamined; so
# the `--` that `parse` sees is the user's second one
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv
  Args.argv()
