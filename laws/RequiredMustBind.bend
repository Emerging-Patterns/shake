# A successful parse binds every required argument of every command on the
# selected path, in that command's Matched. Otherwise the parse fails with
# `Missing{name}`.
#
# also rests on: laws/RequiredMissing.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow

# whether a name has values in the command at `path` in a Matched, when the
# path reaches one
def present_at.go(mm: Maybe<&2, Shake.Matched>, +name: String) -> Maybe<&2, Bool>:
  match mm:
    case None{}:
      None{}
    case Some{found}:
      Some{Bool.not(List.is_empty(&2, String, Shake.get_all(found, name)))}

# whether a name has values in the command at `path` in a Matched
def present_at(found: Shake.Matched, path: List<&2, String>, +name: String) -> Maybe<&2, Bool>:
  present_at.go(Shake.at(found, path), name)

# LAW: when the parse succeeds, every required argument of every command on
# the selected path has a value in that command's Matched
law required_present:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
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
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  {present_at(found, path, nn) == Some{True{}} : Maybe<&2, Bool>}
