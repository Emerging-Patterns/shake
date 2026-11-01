# Before `--` and before any positional of the current command is bound, a
# plain word `help`, a word `--help` when no argument of the current command
# has the long spelling `help`, or a word `-h` when no argument of the current
# command has the short spelling `h` or the long spelling `help`, makes the
# parse fail with `NeedHelp{path}`, where `path` is the selected path followed
# by the remaining words, as long as each names a subcommand under the one
# before; the first remaining word that does not makes the parse fail with
# `Unexpected{word}`. A command that declares its own long `help` gets
# `--help` as that argument (laws/LongOptionSplitsAtEquals.bend), and `-h` is
# read as any other short option word (laws/ShortClusterReadsLetters.bend);
# `help` still asks for help.
#
# also rests on: laws/HelpUnknown.bend, laws/HelpWalk.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/HelpPathNames.bend as D1

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `help` starts
# a help path at the selected path
law help_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  {S.parse.walk(List.append(&2, String, pre, ["help"]), S.parse.start(spec))
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `help`
# followed by words that each name a subcommand under the one before, until
# the words end, fails the parse with NeedHelp of the selected path followed
# by those words
law help_path:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +ns: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  for h_ns: {D1.help_names(ns, subs) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["help"]), ns))
    == Fail{S.NeedHelp{List.append(&2, String, path, ns)}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `--help`
# starts a help path at the selected path, as `help` does, when no argument of
# the current command spells long `help`
law dash_help_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  for h_none: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
  {S.parse.walk(List.append(&2, String, pre, ["--help"]), S.parse.start(spec))
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `--help`,
# when no argument of the current command spells long `help`, followed by
# words that each name a subcommand under the one before, until the words
# end, fails the parse with NeedHelp of the selected path followed by those
# words, as `help` does
law dash_help_path:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +ns: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  for h_none: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
  for h_ns: {D1.help_names(ns, subs) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--help"]), ns))
    == Fail{S.NeedHelp{List.append(&2, String, path, ns)}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `-h` starts a
# help path at the selected path, as `help` does, when no argument of the
# current command spells short `h` or long `help`
law short_help_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  for h_short: {S.by_short(args, "h") == None{} : Maybe<&2, S.Arg>}
  for h_long: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
  {S.parse.walk(List.append(&2, String, pre, ["-h"]), S.parse.start(spec))
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}

# LAW: wherever the words before it leave the walker free, before `--` and
# before any positional of the current command is bound, a word `-h`, when
# no argument of the current command spells short `h` or long `help`,
# followed by words that each name a subcommand under the one before, until
# the words end, fails the parse with NeedHelp of the selected path followed
# by those words, as `help` does
law short_help_path:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +ns: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  for h_short: {S.by_short(args, "h") == None{} : Maybe<&2, S.Arg>}
  for h_long: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
  for h_ns: {D1.help_names(ns, subs) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["-h"]), ns))
    == Fail{S.NeedHelp{List.append(&2, String, path, ns)}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
