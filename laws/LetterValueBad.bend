import Base
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1

# LAW: a letter that spells an option taking a value now, with a glued value
# its choices do not allow, refuses the whole word as BadValue
law letter_value_bad:
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
  for h_noeq: {String.starts_with(rest, "=") == False{} : Bool}
  for h_some: {String.is_empty(rest) == False{} : Bool}
  for h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), rest) == False{} : Bool}
  {S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.St{S.Dead{S.BadValue{path, nn, rest}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
