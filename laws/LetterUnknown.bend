import Base
import ../src/cli.bend as S

# LAW: a letter no argument of the current command spells refuses the whole
# word as UnknownFlag, whatever letters came before it
law letter_unknown:
  for +cc: Char
  for +rest: String
  for +orig: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  {S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.St{S.Dead{S.UnknownFlag{path, orig}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
