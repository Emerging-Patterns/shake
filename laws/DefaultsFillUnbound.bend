# After the last word, each argument of every command on the selected path
# that the words left unbound in that command and that has a default is bound
# to its default in that command's Matched. A bound argument's value is never
# replaced, and no argument without a default gains a binding.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ./defs/ValuesAtPath.bend as D1

# whether no argument of a list is named `name`
def none_named(args: List<&2, S.Arg>, +name: String) -> Bool:
  match args:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Arg{+nn, _s, _l, _k, _h, _r, _d, _c} = hh
      Bool.and(Bool.not(String.eq(nn, name)), none_named(tt, name))

# LAW: when the parse succeeds, an argument with a default that its command
# left unbound reads its default, once, in that command's Matched
law default_filled:
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
  for +req: Bool
  for +ev: Maybe<&2, String>
  for +dd: String
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{dd}}, cs} <> qa),
          bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  for h_free: {S.bound(bs, nn) == False{} : Bool}
  {D1.all_at(found, path, nn) == Some{[dd]} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, an argument its command bound reads exactly
# the values it was given, in order, in that command's Matched: a default
# never replaces them nor adds to them
law bound_kept:
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
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  for h_bound: {S.bound(bs, nn) == True{} : Bool}
  {D1.all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, an argument with no default reads only the
# values the words gave it in its command's Matched, none when they gave none
law no_default:
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
  for +req: Bool
  for +ev: Maybe<&2, String>
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, None{}}, cs} <> qa),
          bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  {D1.all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, a name no argument of a command has reads only
# what the words bound to it in that command's Matched
law no_argument:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +args: List<&2, S.Arg>
  for +nn: String
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_none: {none_named(args, nn) == True{} : Bool}
  {D1.all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}
