# the frame and Matched of a finished walker, defaults filled
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S
import ../../src/grow.bend as Grow

# Done{.} and Fail{.} told apart
def vr.done_ty(rr: Result<&2, &2, S.ParseErr, S.Matched>) -> Type:
  match rr:
    case Done{_m}:
      Unit
    case Fail{_e}:
      Empty

# a failure read for the version is still no success
def vr.clash(
  +spec: Shake.Cli,
  ee: S.ParseErr,
  found: S.Matched,
  h: {Fail{S.version.err(spec, ee)} == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}
) -> Empty:
  ef = Equal.sym(Result<&2, &2, S.ParseErr, S.Matched>, Fail{S.version.err(spec, ee)}, Done{found}, h)
  %ef : vr.done_ty(_)
  Unit{}

# a parse that succeeded did so before the version was read off it: the
# version only ever rewrites a failure
def vr.done(
  +spec: Shake.Cli,
  rr: Result<&2, &2, S.ParseErr, S.Matched>,
  +found: S.Matched,
  h: {S.version.res(spec, rr) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}
) -> {rr == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}:
  match rr:
    case Done{mm}:
      h
    case Fail{ee}:
      Empty.absurd({Fail{ee} == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}, vr.clash(spec, ee, found, h))

# the two orders a binding's value can be reversed onto a list in agree
def fin.hit_rev(
  hit: Bool,
  +vv: String,
  +xs: List<&2, String>,
  +acc: List<&2, String>
) -> {List.reverse.go(&2, String, xs, S.get_all.bind.hit(hit, vv, acc))
    == List.reverse.go(&2, String, S.get_all.bind.hit(hit, vv, xs), acc) : List<&2, String>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# `get_all` of bindings reversed onto a list is its values reversed onto that
# list's values
def fin.g_rev_go(
  xs: List<&2, S.Bind>,
  +acc: List<&2, S.Bind>,
  +nn: String
) -> {S.get_all.bind(List.reverse.go(&2, S.Bind, xs, acc), nn)
    == List.reverse.go(&2, String, S.get_all.bind(xs, nn), S.get_all.bind(acc, nn)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Bind{+mm, +vv}:
          Equal.trans(List<&2, String>,
            S.get_all.bind(List.reverse.go(&2, S.Bind, tt, S.Bind{mm, vv} <> acc), nn),
            List.reverse.go(&2, String, S.get_all.bind(tt, nn),
              S.get_all.bind.hit(String.eq(mm, nn), vv, S.get_all.bind(acc, nn))),
            List.reverse.go(&2, String, S.get_all.bind.hit(String.eq(mm, nn), vv, S.get_all.bind(tt, nn)),
              S.get_all.bind(acc, nn)),
            fin.g_rev_go(tt, S.Bind{mm, vv} <> acc, nn),
            fin.hit_rev(String.eq(mm, nn), vv, S.get_all.bind(tt, nn), S.get_all.bind(acc, nn)))

# `get_all` of reversed bindings is their values reversed
def fin.g_rev(
  +xs: List<&2, S.Bind>,
  +nn: String
) -> {S.get_all.bind(List.reverse(&2, S.Bind, xs), nn) == List.reverse(&2, String, S.get_all.bind(xs, nn))
    : List<&2, String>}:
  fin.g_rev_go(xs, [], nn)

# a bound name has values, and an unbound one none
def fin.bound_g.hit(
  hit: Bool,
  +vv: String,
  +rest: Bool,
  +vals: List<&2, String>,
  ih: {rest == Bool.not(List.is_empty(&2, String, vals)) : Bool}
) -> {S.bound.at(hit, rest) == Bool.not(List.is_empty(&2, String, S.get_all.bind.hit(hit, vv, vals))) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# whether a name is bound is whether it has values
def fin.bound_g(
  xs: List<&2, S.Bind>,
  +nn: String
) -> {S.bound(xs, nn) == Bool.not(List.is_empty(&2, String, S.get_all.bind(xs, nn))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Bind{+mm, +vv}:
          fin.bound_g.hit(String.eq(mm, nn), vv, S.bound(tt, nn), S.get_all.bind(tt, nn), fin.bound_g(tt, nn))

# the frame of the walker the words leave: levels `qs` in front of the level
# `args`, `bs`, above the levels `up`, and names `ms` after the path
def fin.Framed(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +ms: List<&2, String>
) -> Type:
  {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}

# the Matched of the command at `path`: its level, defaults filled, with the
# levels below it
def fin.at(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +found: Shake.Matched,
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +ms: List<&2, String>,
  h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>},
  h_fr: fin.Framed(spec, ws, qs, args, bs, up, path, ms),
  h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
) -> {S.at(found, path)
    == Some{S.matched.build(S.Level{args, S.fill.args(args, bs)} <> List.reverse(&2, S.Level, S.fill.levels(qs)), ms)}
    : Maybe<&2, S.Matched>}:
  +fs = S.parse.walk(ws, S.parse.start(spec))
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +fq = S.fill.levels(qs)
  +fu = S.fill.levels(up)
  +r0 = List.reverse(&2, S.Level, fu)
  +rq = List.reverse(&2, S.Level, fq)
  +pm = List.append(&2, String, path, ms)
  +lvs = List.append(&2, S.Level, qs, S.Level{args, bs} <> up)
  em = Equal.trans(S.Matched, found, Grow.gw.build_of(Grow.gw.frame(fs)),
    S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm),
    Grow.gw.finished(fs, found, vr.done(spec, S.parse.finish(fs), found, h_done)),
    Equal.trans(S.Matched, Grow.gw.build_of(Grow.gw.frame(fs)), Grow.gw.build_of(Grow.Frame{lvs, pm}),
      S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm),
      Equal.cong(Grow.Frame, S.Matched, fr => Grow.gw.build_of(fr), Grow.gw.frame(fs), Grow.Frame{lvs, pm}, h_fr),
      Equal.cong(List<&2, S.Level>, S.Matched, ls => S.matched.build(ls, pm),
        List.reverse(&2, S.Level, S.fill.levels(lvs)), List.append(&2, S.Level, r0, f0 <> rq),
        Equal.trans(List<&2, S.Level>, List.reverse(&2, S.Level, S.fill.levels(lvs)),
          List.reverse(&2, S.Level, List.append(&2, S.Level, fq, f0 <> fu)), List.append(&2, S.Level, r0, f0 <> rq),
          Equal.cong(List<&2, S.Level>, List<&2, S.Level>, ls => List.reverse(&2, S.Level, ls), S.fill.levels(lvs),
            List.append(&2, S.Level, fq, f0 <> fu), Grow.gw.fill_mid(qs, args, bs, up)),
          Grow.gw.lrev_mid(fq, f0, fu)))))
  hl = Equal.trans(Nat, List.length(&2, S.Level, r0), List.length(&2, S.Level, fu), List.length(&2, String, path),
    Grow.gw.len_rev(fu),
    Equal.trans(Nat, List.length(&2, S.Level, fu), List.length(&2, S.Level, up), List.length(&2, String, path),
      Grow.gw.len_fill(up), h_len))
  Equal.trans(Maybe<&2, S.Matched>, S.at(found, path),
    S.at(S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm), path), Some{S.matched.build(f0 <> rq, ms)},
    Equal.cong(S.Matched, Maybe<&2, S.Matched>, mm => S.at(mm, path), found,
      S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm), em),
    Grow.gw.at_build(r0, path, f0, rq, ms, hl))
