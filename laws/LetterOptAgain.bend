import Base
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: a letter that spells an option built with `opt` already given refuses
# the whole word as Repeated
law letter_opt_again:
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
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_again: {S.bound(bs, nn) == True{} : Bool}
  {D1.dead_of(S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{}))
    == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
