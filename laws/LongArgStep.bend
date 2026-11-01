import Base
import ../src/cli.bend as S

# LAW: a free walker hands a long option word to `take_long.found`, with the
# argument its name spells and the value after `=` (a step lemma)
law long_arg_step:
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
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
  {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos,
      False{}, seen) : S.St}
