import Base
import ../src/cli.bend as S

# LAW: in a free walker, a long option whose spelling no argument of the
# current command has kills the walk with UnknownFlag of the whole word (a
# step lemma)
law unknown_long_step:
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  for h_lh: {S.long_help(name, val, seen) == False{} : Bool}
  {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
