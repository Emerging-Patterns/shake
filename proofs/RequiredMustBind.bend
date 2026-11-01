# proofs of laws/RequiredMustBind.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ../laws/RequiredMustBind.bend as Laws
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/FinishedWalker.bend as M2

# anything and False is False
def fin.and_false(bb: Bool) -> {Bool.and(bb, False{}) == False{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# what `fin.empty_rev` says after one char
def fin.empty_rev.ih(+tt: List<&2, String>, +hh: String, +acc: List<&2, String>) -> Type:
  {List.is_empty(&2, String, List.reverse.go(&2, String, tt, hh <> acc))
    == Bool.and(List.is_empty(&2, String, tt), False{}) : Bool}

# a nonempty accumulator keeps the reversal nonempty
def fin.empty_rev.cons(
  +tt: List<&2, String>,
  +hh: String,
  +acc: List<&2, String>,
  ih: fin.empty_rev.ih(tt, hh, acc)
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, tt, hh <> acc)) == False{} : Bool}:
  Equal.trans(Bool, List.is_empty(&2, String, List.reverse.go(&2, String, tt, hh <> acc)),
    Bool.and(List.is_empty(&2, String, tt), False{}), False{}, ih, fin.and_false(List.is_empty(&2, String, tt)))

# anything and True is itself
def fin.and_true(bb: Bool) -> {Bool.and(bb, True{}) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a list reversed onto another is empty exactly when both are
def fin.empty_rev(
  xs: List<&2, String>,
  +acc: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, xs, acc))
    == Bool.and(List.is_empty(&2, String, xs), List.is_empty(&2, String, acc)) : Bool}:
  match xs:
    case Nil{}:
      match acc:
        case Nil{}:
          {==}
        case Con{_x, _t}:
          {==}
    case Con{+hh, +tt}:
      fin.empty_rev.cons(tt, hh, acc, fin.empty_rev(tt, hh <> acc))

# a reversed list is empty exactly when the list is
def fin.empty_rev0(
  +xs: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse(&2, String, xs))
    == List.is_empty(&2, String, xs) : Bool}:
  Equal.trans(Bool, List.is_empty(&2, String, List.reverse(&2, String, xs)),
    Bool.and(List.is_empty(&2, String, xs), True{}), List.is_empty(&2, String, xs), fin.empty_rev(xs, []),
    fin.and_true(List.is_empty(&2, String, xs)))

# Unit for None, Empty for Some: a motive that tells them apart
def fin.none_ty(mm: Maybe<&2, String>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_n}:
      Empty

# Some is never None
def fin.some_none(+nn: String, hh: {Some{nn} == None{} : Maybe<&2, String>}) -> Empty:
  ee = Equal.sym(Maybe<&2, String>, Some{nn}, None{}, hh)
  %ee : fin.none_ty(_)
  Unit{}

# a required check that found nothing here found nothing
def fin.miss_none(
  mm: Maybe<&2, String>,
  +path: List<&2, String>,
  +lvs: List<&2, S.Level>,
  +found: Shake.Matched,
  hh: {S.parse.finish.miss(mm, path, lvs) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}
) -> {mm == None{} : Maybe<&2, String>}:
  match mm:
    case None{}:
      {==}
    case Some{+nn}:
      Empty.absurd({Some{nn} == None{} : Maybe<&2, String>}, Grow.gw.fail_done(S.Missing{path, nn}, found, hh))

# a walker that finishes as a success found no required argument missing
def fin.finished_miss(
  fs: S.St,
  +found: Shake.Matched,
  hh: {S.parse.finish(fs) == Done{found} : Result<&2, &2, S.ParseErr, S.Matched>}
) -> {S.miss.levels(List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(Grow.gw.frame(fs))))) == None{}
    : Maybe<&2, String>}:
  match fs:
    case S.St{S.Free{}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      +lvs = List.reverse(&2, S.Level, S.fill.levels(S.Level{args, binds} <> up))
      fin.miss_none(S.miss.levels(lvs), path, lvs, found, hh)
    case S.St{S.Dead{+ee}, +args, +up, _s, _p, +binds, _o, _r, _n}:
      Empty.absurd({S.miss.levels(List.reverse(&2, S.Level, S.fill.levels(S.Level{args, binds} <> up))) == None{}
        : Maybe<&2, String>}, Grow.gw.fail_done(ee, found, hh))
    case S.St{S.Need{+nn}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd({S.miss.levels(List.reverse(&2, S.Level, S.fill.levels(S.Level{args, binds} <> up))) == None{}
        : Maybe<&2, String>}, Grow.gw.fail_done(S.NoValue{path, nn}, found, hh))
    case S.St{S.Help{}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd({S.miss.levels(List.reverse(&2, S.Level, S.fill.levels(S.Level{args, binds} <> up))) == None{}
        : Maybe<&2, String>}, Grow.gw.fail_done(S.NeedHelp{path}, found, hh))

# a first-required pick that found nothing found nothing in either part
def fin.first_none_l(
  here: Maybe<&2, String>,
  +rest: Maybe<&2, String>,
  hh: {S.parse.first_req.at(here, rest) == None{} : Maybe<&2, String>}
) -> {here == None{} : Maybe<&2, String>}:
  match here:
    case None{}:
      {==}
    case Some{+nn}:
      Empty.absurd({Some{nn} == None{} : Maybe<&2, String>}, fin.some_none(nn, hh))

# the same, for the rest
def fin.first_none_r(
  here: Maybe<&2, String>,
  +rest: Maybe<&2, String>,
  hh: {S.parse.first_req.at(here, rest) == None{} : Maybe<&2, String>}
) -> {rest == None{} : Maybe<&2, String>}:
  match here:
    case None{}:
      hh
    case Some{+nn}:
      Empty.absurd({rest == None{} : Maybe<&2, String>}, fin.some_none(nn, hh))

# a required check over the levels that found nothing found nothing in this one
def fin.miss_mid(
  r0: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +fb: List<&2, S.Bind>,
  +rq: List<&2, S.Level>,
  hh: {S.miss.levels(List.append(&2, S.Level, r0, S.Level{args, fb} <> rq)) == None{} : Maybe<&2, String>}
) -> {S.miss.args(args, fb) == None{} : Maybe<&2, String>}:
  match r0:
    case Nil{}:
      fin.first_none_l(S.miss.args(args, fb), S.miss.levels(rq), hh)
    case Con{ll, +tt}:
      match ll:
        case S.Level{+la, +lb}:
          fin.miss_mid(tt, args, fb, rq,
            fin.first_none_r(S.miss.args(la, lb), S.miss.levels(List.append(&2, S.Level, tt, S.Level{args, fb} <> rq)),
              hh))

# a required check that found nothing found nothing further on
def fin.one_none(
  need: Bool,
  +nm: String,
  +rest: Maybe<&2, String>,
  hh: {S.miss.one(need, nm, rest) == None{} : Maybe<&2, String>}
) -> {rest == None{} : Maybe<&2, String>}:
  match need:
    case True{}:
      Empty.absurd({rest == None{} : Maybe<&2, String>}, fin.some_none(nm, hh))
    case False{}:
      hh

# a required argument the check passed is bound
def fin.req_bound(
  bb: Bool,
  +nm: String,
  +rest: Maybe<&2, String>,
  hh: {S.miss.one(Bool.not(bb), nm, rest) == None{} : Maybe<&2, String>}
) -> {bb == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, fin.some_none(nm, hh))

# a command's arguments around a required one named `nn`
def fin.req_args(
  +pa: List<&2, S.Arg>,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +qa: List<&2, S.Arg>
) -> List<&2, S.Arg>:
  List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa)

# a required check that found nothing leaves every required argument bound
def fin.miss_req(
  pa: List<&2, S.Arg>,
  +qa: List<&2, S.Arg>,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +fb: List<&2, S.Bind>,
  hh: {S.miss.args(fin.req_args(pa, nn, sh, lo, kind, hp, dflt, cs, qa), fb) == None{} : Maybe<&2, String>}
) -> {S.bound(fb, nn) == True{} : Bool}:
  match pa:
    case Nil{}:
      fin.req_bound(S.bound(fb, nn), nn, S.miss.args(qa, fb), hh)
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+mm, _s, _l, _k, _h, +rq, _d, _c}:
          fin.miss_req(tt, qa, nn, sh, lo, kind, hp, dflt, cs, fb,
            fin.one_none(Bool.and(rq, Bool.not(S.bound(fb, mm))), mm,
              S.miss.args(List.append(&2, S.Arg, tt, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), fb), hh))

def Laws.required_present(
  spec,
  ws,
  found,
  qs,
  pa,
  qa,
  nn,
  sh,
  lo,
  kind,
  hp,
  dflt,
  cs,
  bs,
  up,
  path,
  ms,
  h_done,
  h_fr,
  h_len
):
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa)
  +fb = S.fill.args(args, bs)
  +fs = S.parse.walk(ws, S.parse.start(spec))
  +lvs = List.append(&2, S.Level, qs, S.Level{args, bs} <> up)
  +r0 = List.reverse(&2, S.Level, S.fill.levels(up))
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  +f0 = {S.Level{args, fb} : S.Level}
  +bm = S.matched.build(f0 <> rq, ms)
  +hd = {h_done : {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}}
  +h_fr2 = {h_fr : {Grow.gw.frame(fs) == Grow.Frame{lvs, List.append(&2, String, path, ms)} : Grow.Frame}}
  mn = Equal.trans(Maybe<&2, String>, S.miss.levels(List.append(&2, S.Level, r0, f0 <> rq)),
    S.miss.levels(List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(Grow.gw.frame(fs))))), None{},
    Equal.cong(List<&2, S.Level>, Maybe<&2, String>, ls => S.miss.levels(ls), List.append(&2, S.Level, r0, f0 <> rq),
      List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(Grow.gw.frame(fs)))),
      Equal.sym(List<&2, S.Level>, List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(Grow.gw.frame(fs)))),
        List.append(&2, S.Level, r0, f0 <> rq),
        Equal.trans(List<&2, S.Level>, List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(Grow.gw.frame(fs)))),
          List.reverse(&2, S.Level, S.fill.levels(lvs)), List.append(&2, S.Level, r0, f0 <> rq),
          Equal.cong(Grow.Frame, List<&2, S.Level>, fr => List.reverse(&2, S.Level, S.fill.levels(Grow.gw.flevels(fr))),
            Grow.gw.frame(fs), Grow.Frame{lvs, List.append(&2, String, path, ms)}, h_fr2),
          M1.fin.levels(qs, args, bs, up)))),
    fin.finished_miss(fs, found, M2.vr.done(spec, S.parse.finish(fs), found, hd)))
  hb = fin.miss_req(pa, qa, nn, sh, lo, kind, hp, dflt, cs, fb, fin.miss_mid(r0, args, fb, rq, mn))
  eb = Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(S.own(bm), nn))),
    Bool.not(List.is_empty(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, fb), nn))), True{},
    Equal.cong(List<&2, S.Bind>, Bool, xs => Bool.not(List.is_empty(&2, String, S.get_all.bind(xs, nn))), S.own(bm),
      List.reverse(&2, S.Bind, fb), Grow.gw.own_build(f0, rq, ms)),
    Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, fb), nn))),
      Bool.not(List.is_empty(&2, String, List.reverse(&2, String, S.get_all.bind(fb, nn)))), True{},
      Equal.cong(List<&2, String>, Bool, xs => Bool.not(List.is_empty(&2, String, xs)),
        S.get_all.bind(List.reverse(&2, S.Bind, fb), nn), List.reverse(&2, String, S.get_all.bind(fb, nn)),
        M2.fin.g_rev(fb, nn)),
      Equal.trans(Bool, Bool.not(List.is_empty(&2, String, List.reverse(&2, String, S.get_all.bind(fb, nn)))),
        Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))), True{},
        Equal.cong(Bool, Bool, xx => Bool.not(xx), List.is_empty(&2, String, List.reverse(&2, String,
            S.get_all.bind(fb, nn))),
          List.is_empty(&2, String, S.get_all.bind(fb, nn)), fin.empty_rev0(S.get_all.bind(fb, nn))),
        Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))), S.bound(fb, nn), True{},
          Equal.sym(Bool, S.bound(fb, nn), Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))),
            M2.fin.bound_g(fb, nn)), hb))))
  Equal.trans(Maybe<&2, Bool>, Laws.present_at(found, path, nn), Laws.present_at.go(Some{bm}, nn), Some{True{}},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, Bool>, mm => Laws.present_at.go(mm, nn), S.at(found, path), Some{bm},
      M2.fin.at(spec, ws, found, qs, args, bs, up, path, ms, hd, h_fr2, h_len)),
    Equal.cong(Bool, Maybe<&2, Bool>, xx => Some{xx}, Bool.not(List.is_empty(&2, String,
        S.get_all.bind(S.own(bm), nn))),
      True{}, eb))
