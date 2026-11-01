# `check(spec)` reports exactly one error for each of: a rest positional that
# is not its command's last positional; an argument of a command with the
# name, short spelling or long spelling of an earlier argument of that
# command; a subcommand with the name of an earlier subcommand of the same
# command; a subcommand named `help`; a default outside its argument's
# nonempty choices; a required positional after an optional one. It reports
# nothing else.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/check.bend as K
import ./defs/ArgumentLists.bend as D1

# LAW: `check` reports, for the root and then for every subcommand depth
# first, each at its own path: each argument whose name, short spelling or
# long spelling an earlier argument of its command has, each default outside
# nonempty choices, each rest positional before the last positional, each
# required positional after an optional one, each subcommand with an earlier
# sibling's name, and each subcommand named `help`; one report each and
# nothing else
law check_listed:
  for +name: String
  for +about: String
  for +version: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  {Shake.check(S.Cli{name, about, version, args, subs}) == K.both(D1.cmd_reports([], args, subs), D1.below(subs, []))
    : List<&2, K.SpecErr>}
