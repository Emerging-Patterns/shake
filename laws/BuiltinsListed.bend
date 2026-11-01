import Base
import ../src/cli.bend as S

# a built-in flag a page lists, spelled `--name` and maybe a short letter
def builtin(+name: String, short: Maybe<&2, String>, +help: String) -> S.Arg:
  S.Arg{name, short, Some{name}, S.Flag{}, help, False{}, S.Fallback{None{}, None{}}, []}

# the help row, given what the command spells as long `help` and short `h`
def help_rows.of(long: Maybe<&2, S.Arg>, short: Maybe<&2, S.Arg>) -> List<&2, S.Arg>:
  match long:
    case None{}:
      match short:
        case None{}:
          [builtin("help", Some{"h"}, "Print help")]
        case Some{_a}:
          [builtin("help", None{}, "Print help")]
    case Some{_a}:
      []

# the help row of a page: `-h, --help` when its command spells neither,
# `--help` when it spells `-h`, none when it spells `--help`
def help_rows(+args: List<&2, S.Arg>) -> List<&2, S.Arg>:
  help_rows.of(S.by_long(args, "help"), S.by_short(args, "h"))

# the version row, given what the command spells as long `version` and short
# `V`
def version_rows.of(long: Maybe<&2, S.Arg>, short: Maybe<&2, S.Arg>) -> List<&2, S.Arg>:
  match long:
    case None{}:
      match short:
        case None{}:
          [builtin("version", Some{"V"}, "Print version")]
        case Some{_a}:
          [builtin("version", None{}, "Print version")]
    case Some{_a}:
      []

# the version row of a page: none without a version; else `-V, --version`
# when its command spells neither, `--version` when it spells `-V`, none
# when it spells `--version`
def version_rows(+args: List<&2, S.Arg>, version: Maybe<&2, String>) -> List<&2, S.Arg>:
  match version:
    case None{}:
      []
    case Some{_v}:
      version_rows.of(S.by_long(args, "version"), S.by_short(args, "V"))

# LAW: the built-in flags a page lists after its command's own are its help
# row, then its version row
law builtins_listed:
  for +args: List<&2, S.Arg>
  for +version: Maybe<&2, String>
  {S.help.builtins(args, version) == List.append(&2, S.Arg, help_rows(args), version_rows(args, version))
    : List<&2, S.Arg>}
