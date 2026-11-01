import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/HelpPathNames.bend as D1

# LAW: wherever the words before them leave the walker reading a help path,
# words that each name a subcommand under the one before extend the path, in
# order
law help_walk:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +ns: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_ns: {D1.help_names(ns, subs) == True{} : Bool}
  exs kids: List<&2, S.Sub>
  {S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec))
    == S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen} : S.St}
