# `help(spec, path)` renders the page of the command reached by following each
# name of `path` from the root through the subcommands, skipping a name that
# is not a subcommand where it stands.
#
# also rests on: laws/HelpPage.bend
import Base
import ../src/cli.bend as S

# LAW: a name that is a subcommand where the walk stands moves the page to
# that subcommand, its usage line gaining the name
law reach_child:
  for +bin: String
  for +about: String
  for +version: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +usage: String
  for +name: String
  for +sn: String
  for +sa: String
  for +sargs: List<&2, S.Arg>
  for +ssubs: List<&2, S.Sub>
  for h_sub: {S.find_sub(subs, name) == Some{S.Sub{sn, sa, sargs, ssubs}} : Maybe<&2, S.Sub>}
  {S.help.step(S.How{bin, about, version, args, subs, usage}, name)
    == S.How{sn, sa, None{}, sargs, ssubs, usage ++ " " ++ name} : S.How}

# LAW: a name that is no subcommand where the walk stands is skipped
law reach_skip:
  for +bin: String
  for +about: String
  for +version: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +usage: String
  for +name: String
  for h_sub: {S.find_sub(subs, name) == None{} : Maybe<&2, S.Sub>}
  {S.help.step(S.How{bin, about, version, args, subs, usage}, name)
    == S.How{bin, about, version, args, subs, usage} : S.How}
