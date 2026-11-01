import Base
import ../src/cli.bend as S

# LAW: in a free walker, a short option word whose first letter no argument
# of the current command has kills the walk with UnknownFlag of the whole
# word (a step lemma)
law unknown_short_step:
  for +cc: Char
  for +rest: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  for h_help: {S.short_help(SCon{cc, rest}, args, seen) == False{} : Bool}
  {S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
