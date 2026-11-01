import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave an option waiting for its value, a
# word that is not flag-shaped and that the option's choices do not allow
# fails the parse with BadValue of the option and the word, whatever follows
law value_refused:
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
  for h_flag: {S.looks_flag(tok) == False{} : Bool}
  for h_bad: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.BadValue{path, name, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
