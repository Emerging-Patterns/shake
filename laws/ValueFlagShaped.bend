import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave an option waiting for its value, a
# word that starts with `-` and is not `-` fails the parse with Missing of the
# option, whatever follows
law value_flag_shaped:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_flag: {S.looks_flag(tok) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.NoValue{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
