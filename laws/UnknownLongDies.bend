import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: a walk that reaches an unknown long option dies there (a lemma)
law unknown_long_dies:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
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
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  for h_lh: {S.long_help(name, val, seen) == False{} : Bool}
  {D1.dead_of(S.parse.walk(List.append(&2, String, pre, ["--" ++ body]), S.parse.start(spec)))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
