# the bindings a walk makes are kept and read back by get_all
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S
import ../../src/eq.bend as Eq
import ../../src/grow.bend as Grow
import ../../laws/BindValuesAppend.bend as L1
import ../../laws/Kept.bend as L2
import ../../laws/KeptAll.bend as L3
import ../../laws/WalkAppend.bend as L4
import ../../laws/defs/ValuesAtPath.bend as D1
import ./AppendedBindings.bend as M1
import ./FinishedWalker.bend as M2
import ./WalkSteps.bend as M3

# a binding's own name reads its value first
def kept.hit(
  +name: String,
  +vv: String,
  +rest: List<&2, String>
) -> {S.get_all.bind.hit(String.eq(name, name), vv, rest) == vv <> rest : List<&2, String>}:
  ee = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %ee : {S.get_all.bind.hit(_, vv, rest) == vv <> rest : List<&2, String>}
  {==}

# what `kept_all` claims
def kept_all.ty(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +name: String,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>
) -> Type:
  &after: List<&2, String> -> {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name),
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, xs), name), after))}
    : Maybe<&2, List<&2, String>>}

# the bindings of the level `mid` stayed in when the words end: those the words
# after it made, those `mid` made, and those it had
def kept_all.ys(+xx: List<&2, S.Bind>, +xs: List<&2, S.Bind>, +bs: List<&2, S.Bind>) -> List<&2, S.Bind>:
  List.append(&2, S.Bind, xx, List.append(&2, S.Bind, xs, bs))

# the level's values, defaults in front, read back
def kept_all.vals(+args: List<&2, S.Arg>, +ys: List<&2, S.Bind>, +name: String) -> List<&2, String>:
  S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, ys)), name)

# what `kept_all.fill` claims
def kept_all.fill.ty(
  +args: List<&2, S.Arg>,
  +xx: List<&2, S.Bind>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String
) -> Type:
  &after: List<&2, String> -> {kept_all.vals(args, kept_all.ys(xx, xs, bs), name)
    == List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name),
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, xs), name), after)) : List<&2, String>}

# what `kept_all.read` claims
def kept_all.read.ty(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +args: List<&2, S.Arg>,
  +ys: List<&2, S.Bind>,
  +name: String
) -> Type:
  {D1.all_at(found, path, name) == Some{kept_all.vals(args, ys, name)} : Maybe<&2, List<&2, String>>}

# a successful parse's Matched, read at the path where the words `mid` stayed:
# the level's bindings, all of them, with defaults in front, reversed
def kept_all.read(
  +found: Shake.Matched,
  +fs: S.St,
  +st1: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +yy: List<&2, S.Bind>,
  +xx: List<&2, S.Bind>,
  +qs: List<&2, S.Level>,
  +ms: List<&2, String>,
  +name: String,
  h_mid: {Grow.view(st1) == Grow.View{args, up, path, yy} : Grow.View},
  hd: {S.parse.finish(fs) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>},
  dep: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat},
  e2: {Grow.gw.frame(fs) == Grow.gw.grown(xx, qs, ms, Grow.view(st1)) : Grow.Frame}
) -> kept_all.read.ty(found, path, args, List.append(&2, S.Bind, xx, yy), name):
  +ys = List.append(&2, S.Bind, xx, yy)
  +f0 = {S.Level{args, S.fill.args(args, ys)} : S.Level}
  +fq = S.fill.levels(qs)
  +fu = S.fill.levels(up)
  +r0 = List.reverse(&2, S.Level, fu)
  +rq = List.reverse(&2, S.Level, fq)
  +pm = List.append(&2, String, path, ms)
  +lvs = List.append(&2, S.Level, qs, S.Level{args, ys} <> up)
  ef = Equal.trans(Grow.Frame, Grow.gw.frame(fs), Grow.gw.grown(xx, qs, ms, Grow.view(st1)), Grow.Frame{lvs, pm}, e2,
    Equal.cong(Grow.View, Grow.Frame, vv => Grow.gw.grown(xx, qs, ms, vv), Grow.view(st1), Grow.View{args, up,
        path, yy},
      h_mid))
  em = Equal.trans(S.Matched, found, Grow.gw.build_of(Grow.gw.frame(fs)),
    S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm),
    Grow.gw.finished(fs, found, hd),
    Equal.trans(S.Matched, Grow.gw.build_of(Grow.gw.frame(fs)), Grow.gw.build_of(Grow.Frame{lvs, pm}),
      S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm),
      Equal.cong(Grow.Frame, S.Matched, fr => Grow.gw.build_of(fr), Grow.gw.frame(fs), Grow.Frame{lvs, pm}, ef),
      Equal.cong(List<&2, S.Level>, S.Matched, ls => S.matched.build(ls, pm),
        List.reverse(&2, S.Level, S.fill.levels(lvs)), List.append(&2, S.Level, r0, f0 <> rq),
        Equal.trans(List<&2, S.Level>, List.reverse(&2, S.Level, S.fill.levels(lvs)),
          List.reverse(&2, S.Level, List.append(&2, S.Level, fq, f0 <> fu)), List.append(&2, S.Level, r0, f0 <> rq),
          Equal.cong(List<&2, S.Level>, List<&2, S.Level>, ls => List.reverse(&2, S.Level, ls), S.fill.levels(lvs),
            List.append(&2, S.Level, fq, f0 <> fu), Grow.gw.fill_mid(qs, args, ys, up)),
          Grow.gw.lrev_mid(fq, f0, fu)))))
  hl = Equal.trans(Nat, List.length(&2, S.Level, r0), List.length(&2, S.Level, fu), List.length(&2, String, path),
    Grow.gw.len_rev(fu),
    Equal.trans(Nat, List.length(&2, S.Level, fu), List.length(&2, S.Level, up), List.length(&2, String, path),
      Grow.gw.len_fill(up), dep))
  ea = Equal.trans(Maybe<&2, S.Matched>, S.at(found, path),
    S.at(S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm), path), Some{S.matched.build(f0 <> rq, ms)},
    Equal.cong(S.Matched, Maybe<&2, S.Matched>, mm => S.at(mm, path), found,
      S.matched.build(List.append(&2, S.Level, r0, f0 <> rq), pm), em),
    Grow.gw.at_build(r0, path, f0, rq, ms, hl))
  Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, name),
    Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), name)},
    Some{S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, ys)), name)},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, List<&2, String>>, mm => D1.all_at.go(mm, name), S.at(found, path),
      Some{S.matched.build(f0 <> rq, ms)}, ea),
    Equal.cong(List<&2, S.Bind>, Maybe<&2, List<&2, String>>, bs2 => Some{S.get_all.bind(bs2, name)},
      S.own(S.matched.build(f0 <> rq, ms)), List.reverse(&2, S.Bind, S.fill.args(args, ys)),
      Grow.gw.own_build(f0, rq, ms)))

# the level's bindings, defaults in front, read back: those made before
# `mid`, those `mid` made, then the rest
def kept_all.fill(
  +args: List<&2, S.Arg>,
  +xx: List<&2, S.Bind>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String,
  wf: Grow.gw.Ext(S.fill.args(args, kept_all.ys(xx, xs, bs)), kept_all.ys(xx, xs, bs))
) -> kept_all.fill.ty(args, xx, xs, bs, name):
  (dx, ee) = wf
  +defs = {dx : List<&2, S.Bind>}
  +ys = List.append(&2, S.Bind, xx, List.append(&2, S.Bind, xs, bs))
  +r1 = List.reverse.go(&2, S.Bind, xx, List.reverse(&2, S.Bind, defs))
  +gb = S.get_all.bind(List.reverse(&2, S.Bind, bs), name)
  +gx = S.get_all.bind(List.reverse(&2, S.Bind, xs), name)
  (S.get_all.bind(r1, name),
    Equal.trans(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, ys)), name),
      S.get_all.bind(List.reverse(&2, S.Bind, List.append(&2, S.Bind, defs, ys)), name),
      List.append(&2, String, gb, List.append(&2, String, gx, S.get_all.bind(r1, name))),
      Equal.cong(List<&2, S.Bind>, List<&2, String>, zs => S.get_all.bind(List.reverse(&2, S.Bind, zs), name),
        S.fill.args(args, ys), List.append(&2, S.Bind, defs, ys), ee),
      Equal.trans(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, List.append(&2, S.Bind, defs, ys)), name),
        S.get_all.bind(List.append(&2, S.Bind, List.reverse(&2, S.Bind, bs),
          List.append(&2, S.Bind, List.reverse(&2, S.Bind, xs), r1)), name),
        List.append(&2, String, gb, List.append(&2, String, gx, S.get_all.bind(r1, name))),
        Equal.cong(List<&2, S.Bind>, List<&2, String>, zs => S.get_all.bind(zs, name),
          List.reverse(&2, S.Bind, List.append(&2, S.Bind, defs, ys)),
          List.append(&2, S.Bind, List.reverse(&2, S.Bind, bs), List.append(&2, S.Bind, List.reverse(&2, S.Bind,
              xs), r1)),
          Grow.gw.rev_split(defs, xx, xs, bs)),
        Equal.trans(List<&2, String>,
          S.get_all.bind(List.append(&2, S.Bind, List.reverse(&2, S.Bind, bs),
            List.append(&2, S.Bind, List.reverse(&2, S.Bind, xs), r1)), name),
          List.append(&2, String, gb,
            S.get_all.bind(List.append(&2, S.Bind, List.reverse(&2, S.Bind, xs), r1), name)),
          List.append(&2, String, gb, List.append(&2, String, gx, S.get_all.bind(r1, name))),
          L1.bind_values_append(List.reverse(&2, S.Bind, bs), List.append(&2, S.Bind, List.reverse(&2, S.Bind,
              xs), r1),
            name),
          Equal.cong(List<&2, String>, List<&2, String>, zs => List.append(&2, String, gb, zs),
            S.get_all.bind(List.append(&2, S.Bind, List.reverse(&2, S.Bind, xs), r1), name),
            List.append(&2, String, gx, S.get_all.bind(r1, name)),
            L1.bind_values_append(List.reverse(&2, S.Bind, xs), r1, name))))))

# the read at the path, and the level's bindings read back
def kept_all.join(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +args: List<&2, S.Arg>,
  +xx: List<&2, S.Bind>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String,
  er: kept_all.read.ty(found, path, args, kept_all.ys(xx, xs, bs), name),
  wr: kept_all.fill.ty(args, xx, xs, bs, name)
) -> kept_all.ty(found, path, name, xs, bs):
  (ax, ee) = wr
  +after = {ax : List<&2, String>}
  +zz = S.get_all.bind(List.reverse(&2, S.Bind,
    S.fill.args(args, List.append(&2, S.Bind, xx, List.append(&2, S.Bind, xs, bs)))), name)
  +ww = List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name),
    List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, xs), name), after))
  (after, Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, name), Some{zz}, Some{ww}, er,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, zs => Some{zs}, zz, ww, ee)))

# a walker grown from where `mid` stayed
def kept_all.fin(
  +found: Shake.Matched,
  +fs: S.St,
  +st1: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String,
  h_mid: {Grow.view(st1) == Grow.View{args, up, path, List.append(&2, S.Bind, xs, bs)} : Grow.View},
  hd: {S.parse.finish(fs) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>},
  dep: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat},
  gg: Grow.gw.Grown(fs, Grow.view(st1))
) -> kept_all.ty(found, path, name, xs, bs):
  (x2, r2) = gg
  (q2, r3) = r2
  (m2, r4) = r3
  (_hl, e2) = r4
  +xx = {x2 : List<&2, S.Bind>}
  kept_all.join(found, path, args, xx, xs, bs, name,
    kept_all.read(found, fs, st1, args, up, path, List.append(&2, S.Bind, xs, bs), xx, q2, m2, name, h_mid, hd, dep,
      e2),
    kept_all.fill(args, xx, xs, bs, name,
      Grow.gw.fill(args, List.append(&2, S.Bind, xx, List.append(&2, S.Bind, xs, bs)))))

# the walk after `mid` grew the walker, or left it stuck, which no success
# follows
def kept_all.after(
  +found: Shake.Matched,
  +fs: S.St,
  +st1: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String,
  h_mid: {Grow.view(st1) == Grow.View{args, up, path, List.append(&2, S.Bind, xs, bs)} : Grow.View},
  hd: {S.parse.finish(fs) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>},
  dep: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat},
  rr: Grow.gw.Reach(fs, Grow.view(st1))
) -> kept_all.ty(found, path, name, xs, bs):
  match rr:
    case Grow.Grew{gg}:
      kept_all.fin(found, fs, st1, args, up, path, xs, bs, name, h_mid, hd, dep, gg)
    case Grow.Stopped{hs}:
      Empty.absurd(kept_all.ty(found, path, name, xs, bs), Grow.gw.live_done(fs, found, hd, hs))

# the walker `mid` left has one command above it per name of its path
def kept_all.dep(
  +w0: S.St,
  +st1: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +yy: List<&2, S.Bind>,
  e_st: {w0 == st1 : S.St},
  h_mid: {Grow.view(st1) == Grow.View{args, up, path, yy} : Grow.View},
  dd: Grow.gw.Deep(w0)
) -> {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}:
  +lit = {Grow.Frame{S.Level{args, yy} <> up, path} : Grow.Frame}
  +ef = {Equal.trans(Grow.Frame, Grow.gw.frame(w0), Grow.gw.frame(st1), lit,
    Equal.cong(S.St, Grow.Frame, xx => Grow.gw.frame(xx), w0, st1, e_st),
    Equal.trans(Grow.Frame, Grow.gw.frame(st1), Grow.gw.vframe(Grow.view(st1)), lit, Grow.gw.frame_view(st1),
      Equal.cong(Grow.View, Grow.Frame, vv => Grow.gw.vframe(vv), Grow.view(st1), Grow.View{args, up, path,
          yy}, h_mid)))
    : {Grow.gw.frame(w0) == lit : Grow.Frame}}
  Equal.cong(Nat, Nat, nn => Grow.gw.pred(nn), 1n+List.length(&2, S.Level, up), 1n+List.length(&2, String, path),
    Equal.trans(Nat, List.length(&2, S.Level, S.Level{args, yy} <> up),
      List.length(&2, S.Level, Grow.gw.flevels(Grow.gw.frame(w0))), 1n+List.length(&2, String, path),
      Equal.cong(Grow.Frame, Nat, fr => List.length(&2, S.Level, Grow.gw.flevels(fr)), lit, Grow.gw.frame(w0),
        Equal.sym(Grow.Frame, Grow.gw.frame(w0), lit, ef)),
      Equal.trans(Nat, List.length(&2, S.Level, Grow.gw.flevels(Grow.gw.frame(w0))),
        1n+List.length(&2, String, Grow.gw.fpath(Grow.gw.frame(w0))), 1n+List.length(&2, String, path), dd,
        Equal.cong(Grow.Frame, Nat, fr => 1n+List.length(&2, String, Grow.gw.fpath(fr)), Grow.gw.frame(w0), lit, ef))))

# the walk from the start to where `mid` stayed grew the walker, or left it
# stuck, which no success follows
def kept_all.start(
  spec: Shake.Cli,
  +w0: S.St,
  +found: Shake.Matched,
  +st1: S.St,
  +more: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +xs: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  +name: String,
  +e_st: {w0 == st1 : S.St},
  +h_mid: {Grow.view(st1) == Grow.View{args, up, path, List.append(&2, S.Bind, xs, bs)} : Grow.View},
  +hd: {S.parse.finish(S.parse.walk(more, st1)) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>},
  r0: Grow.gw.Reach(w0, Grow.view(S.parse.start(spec))),
  r1: Grow.gw.Reach(S.parse.walk(more, st1), Grow.view(st1))
) -> kept_all.ty(found, path, name, xs, bs):
  match spec:
    case S.Cli{_n, _a, _v, +sargs, _s}:
      match r0:
        case Grow.Grew{g0}:
          kept_all.after(found, S.parse.walk(more, st1), st1, args, up, path, xs, bs, name, h_mid, hd,
            kept_all.dep(w0, st1, args, up, path, List.append(&2, S.Bind, xs, bs), e_st, h_mid,
              Grow.gw.depth(w0, sargs, [], g0)),
            r1)
        case Grow.Stopped{hs}:
          Empty.absurd(kept_all.ty(found, path, name, xs, bs),
            Grow.gw.live_done(S.parse.walk(more, st1), found, hd,
              Grow.gw.stuck_walk(more, st1,
                Equal.trans(Bool, Grow.gw.live(st1), Grow.gw.live(w0), False{},
                  Equal.cong(S.St, Bool, xx => Grow.gw.live(xx), st1, w0, Equal.sym(S.St, w0, st1, e_st)), hs))))

def L3.kept_all(spec, pre, mid, more, st, args, up, path, xs, bs, name, found, h_at, h_mid, h_done):
  +st1 = S.parse.walk(mid, st)
  +ww = List.append(&2, String, pre, mid)
  +e_st = {Equal.trans(S.St, S.parse.walk(ww, S.parse.start(spec)),
    S.parse.walk(mid, S.parse.walk(pre, S.parse.start(spec))), st1, L4.walk_append(pre, mid, S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk(mid, xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))
    : {S.parse.walk(ww, S.parse.start(spec)) == st1 : S.St}}
  e1 = Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish(xx),
    S.parse.walk(List.append(&2, String, ww, more), S.parse.start(spec)),
    S.parse.walk(more, S.parse.walk(ww, S.parse.start(spec))), L4.walk_append(ww, more, S.parse.start(spec)))
  e2 = Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish(S.parse.walk(more, xx)),
    S.parse.walk(ww, S.parse.start(spec)), st1, e_st)
  +raw = S.parse.finish(S.parse.walk(List.append(&2, String, ww, more), S.parse.start(spec)))
  hd = Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, S.parse.finish(S.parse.walk(more, st1)),
    raw, Done{found},
    Equal.sym(Result<&2, &2, S.ParseErr, S.Matched>, raw,
      S.parse.finish(S.parse.walk(more, st1)),
      Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, raw,
        S.parse.finish(S.parse.walk(more, S.parse.walk(ww, S.parse.start(spec)))),
        S.parse.finish(S.parse.walk(more, st1)), e1, e2)),
    M2.vr.done(spec, raw, found, h_done))
  kept_all.start(spec, S.parse.walk(ww, S.parse.start(spec)), found, st1, more, args, up, path,
    xs, bs, name, e_st, h_mid, hd, Grow.gw.reach(ww, S.parse.start(spec)), Grow.gw.reach(more, st1))

# what `kept` claims
def kept.ty(+found: Shake.Matched, +path: List<&2, String>, +name: String, +vv: String, +bs: List<&2, S.Bind>) -> Type:
  &after: List<&2, String> -> {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), vv <> after)}
    : Maybe<&2, List<&2, String>>}

# one binding of the name, read back as its value
def kept.one(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +name: String,
  +vv: String,
  +bs: List<&2, S.Bind>,
  ww: kept_all.ty(found, path, name, [S.Bind{name, vv}], bs)
) -> kept.ty(found, path, name, vv, bs):
  (ax, ee) = ww
  +after = {ax : List<&2, String>}
  +gb = S.get_all.bind(List.reverse(&2, S.Bind, bs), name)
  (after, Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, name),
    Some{List.append(&2, String, gb, List.append(&2, String, S.get_all.bind.hit(String.eq(name, name), vv, []),
      after))},
    Some{List.append(&2, String, gb, vv <> after)}, ee,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>,
      ys => Some{List.append(&2, String, gb, List.append(&2, String, ys, after))},
      S.get_all.bind.hit(String.eq(name, name), vv, []), [vv], kept.hit(name, vv, []))))

def L2.kept(spec, pre, more, tok, st, args, up, path, name, vv, bs, found, h_at, h_step, h_done):
  kept.one(found, path, name, vv, bs,
    L3.kept_all(spec, pre, [tok], more, st, args, up, path, [S.Bind{name, vv}], bs, name, found, h_at, h_step,
      h_done))
