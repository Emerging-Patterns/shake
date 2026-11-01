import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free, a short option
# word whose first letter no argument of that command has fails the parse
# with UnknownFlag of the word, whatever follows
law unknown_short:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +cc: Char
  for +rest: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  for h_help: {S.short_help(SCon{cc, rest}, args, seen) == False{} : Bool}
  for h_ver: {S.version.asks(spec, path, "-" ++ SCon{cc, rest}) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["-" ++ SCon{cc, rest}]), more))
    == Fail{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
