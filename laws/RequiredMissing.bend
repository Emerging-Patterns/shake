import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ./defs/FreeWalker.bend as D1

# LAW: when the words end with the walker free and a required argument of a
# command on the selected path unbound and without a default, the parse fails
# with Missing at the selected path
law required_missing:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for h_free: {D1.free(S.parse.walk(ws, S.parse.start(spec))) == True{} : Bool}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), bs} <> up), path}
    : Grow.Frame}
  for h_unbound: {S.bound(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa),
    bs), nn) == False{} : Bool}
  exs name: String
  {Shake.parse(spec, ws) == Fail{S.Missing{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
