import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1
import ./defs/ValuesAtPath.bend as D2

# LAW: wherever the words before it leave the walker free, a long option
# `--name=vv` that spells an option built with `opt` not yet given, or one
# built with `many`, and whose choices allow `vv`, binds `vv`: when the parse
# succeeds, `get_all` of the option reads the values given it before, then
# `vv`, whatever follows
law long_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +vv: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>}
  for h_kind: {D1.takes(kind, S.bound(bs, nn)) == True{} : Bool}
  for h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D2.all_at(found, path, nn)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nn), vv <> after)}
    : Maybe<&2, List<&2, String>>}
