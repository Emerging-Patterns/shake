import Base
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1

# LAW: a letter that spells an option taking a value now, followed by `=`,
# takes everything after the `=` as its value, verbatim and possibly empty,
# when its choices allow it
law letter_value_eq:
  for +cc: Char
  for +vv: String
  for +orig: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_kind: {D1.takes(kind, S.bound(bs, nn)) == True{} : Bool}
  for h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
  {S.cluster(SCon{cc, "=" ++ vv}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
