# proofs of laws/RequiredMissing.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
import ../laws/RequiredMissing.bend as Laws
import ../laws/defs/FreeWalker.bend as D1
import ./lemmas/ClusterEnd.bend as M1

# a walk that finishes missing a name, as a type
def vr.miss_ty(+spec: Shake.Cli, +ws: List<&2, String>, +path: List<&2, String>) -> Type:
  &nm: String -> {S.parse.finish(S.parse.walk(ws, S.parse.start(spec))) == Fail{S.Missing{path, nm}}
    : Result<&2, &2, S.ParseErr, S.Matched>}

# a walk that finishes missing a name parses missing it
def vr.miss(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +path: List<&2, String>,
  ww: vr.miss_ty(spec, ws, path)
) -> &nm: String -> {Shake.parse(spec, ws) == Fail{S.Missing{path, nm}} : Result<&2, &2, S.ParseErr, S.Matched>}:
  (n1, e1) = ww
  +nm = {n1 : String}
  (nm, Equal.cong(Result<&2, &2, S.ParseErr, S.Matched>, Result<&2, &2, S.ParseErr, S.Matched>,
    xx => S.version.res(spec, xx), S.parse.finish(S.parse.walk(ws, S.parse.start(spec))),
    Fail{S.Missing{path, nm}}, e1))

# a check that found something here finds something
def fin.one_some(
  need: Bool,
  +mm: String,
  +rest: Maybe<&2, String>,
  ww: &nm: String -> {rest == Some{nm} : Maybe<&2, String>}
) -> &nm: String -> {S.miss.one(need, mm, rest) == Some{nm} : Maybe<&2, String>}:
  match need:
    case True{}:
      (mm, {==})
    case False{}:
      ww

# the required, unbound argument itself is found missing
def fin.miss_here(
  +nn: String,
  +fb: List<&2, S.Bind>,
  +rest: Maybe<&2, String>,
  h_unbound: {S.bound(fb, nn) == False{} : Bool}
) -> {S.miss.one(Bool.and(True{}, Bool.not(S.bound(fb, nn))), nn, rest) == Some{nn} : Maybe<&2, String>}:
  ee = Equal.sym(Bool, S.bound(fb, nn), False{}, h_unbound)
  %ee : {S.miss.one(Bool.and(True{}, Bool.not(_)), nn, rest) == Some{nn} : Maybe<&2, String>}
  {==}

# a required argument its command left unbound is found missing
def fin.miss_args_some(
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
  +h_unbound: {S.bound(fb, nn) == False{} : Bool}
) -> &nm: String -> {S.miss.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), fb)
    == Some{nm} : Maybe<&2, String>}:
  match pa:
    case Nil{}:
      (nn, fin.miss_here(nn, fb, S.miss.args(qa, fb), h_unbound))
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+mm, _s, _l, _k, _h, +rq, _d, _c}:
          fin.one_some(Bool.and(rq, Bool.not(S.bound(fb, mm))), mm,
            S.miss.args(List.append(&2, S.Arg, tt, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), fb),
            fin.miss_args_some(tt, qa, nn, sh, lo, kind, hp, dflt, cs, fb, h_unbound))

# a first-required pick with something found here or further on finds it
def fin.first_some(
  here: Maybe<&2, String>,
  +rest: Maybe<&2, String>,
  ww: &nm: String -> {rest == Some{nm} : Maybe<&2, String>}
) -> &nm: String -> {S.parse.first_req.at(here, rest) == Some{nm} : Maybe<&2, String>}:
  match here:
    case Some{+nm}:
      (nm, {==})
    case None{}:
      ww

# a required check over the levels finds what one level's check finds, or an
# earlier one
def fin.miss_levels_some(
  r0: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +fb: List<&2, S.Bind>,
  +rq: List<&2, S.Level>,
  ww: &nm: String -> {S.miss.args(args, fb) == Some{nm} : Maybe<&2, String>}
) -> &nm: String -> {S.miss.levels(List.append(&2, S.Level, r0, S.Level{args, fb} <> rq)) == Some{nm}
    : Maybe<&2, String>}:
  match r0:
    case Nil{}:
      (n1, e1) = ww
      +nm = {n1 : String}
      (nm, Equal.cong(Maybe<&2, String>, Maybe<&2, String>, xx => S.parse.first_req.at(xx, S.miss.levels(rq)),
        S.miss.args(args, fb), Some{nm}, e1))
    case Con{ll, +tt}:
      match ll:
        case S.Level{+la, +lb}:
          fin.first_some(S.miss.args(la, lb), S.miss.levels(List.append(&2, S.Level, tt, S.Level{args, fb} <> rq)),
            fin.miss_levels_some(tt, args, fb, rq, ww))

# what `required_missing` claims of a finished walker
def fin.missing.ty(+fs: S.St, +path: List<&2, String>) -> Type:
  &nm: String -> {S.parse.finish(fs) == Fail{S.Missing{path, nm}} : Result<&2, &2, S.ParseErr, S.Matched>}

# a free walker whose levels' required check finds a name fails with it
def fin.missing(
  fs: S.St,
  +lvs: List<&2, S.Level>,
  +path: List<&2, String>,
  +ll: List<&2, S.Level>,
  h_free: {D1.free(fs) == True{} : Bool},
  h_fr: {Grow.gw.frame(fs) == Grow.Frame{lvs, path} : Grow.Frame},
  e_ll: {List.reverse(&2, S.Level, S.fill.levels(lvs)) == ll : List<&2, S.Level>},
  ww: &nm: String -> {S.miss.levels(ll) == Some{nm} : Maybe<&2, String>}
) -> fin.missing.ty(fs, path):
  match fs:
    case S.St{S.Free{}, +args, +up, +subs, +pp, +binds, +pos, +raw, +seen}:
      (n1, e1) = ww
      +nm = {n1 : String}
      +l0 = List.reverse(&2, S.Level, S.fill.levels(S.Level{args, binds} <> up))
      +h_fr2 = {h_fr : {Grow.Frame{S.Level{args, binds} <> up, pp} == Grow.Frame{lvs, path} : Grow.Frame}}
      em = Equal.trans(Maybe<&2, String>, S.miss.levels(l0), S.miss.levels(ll), Some{nm},
        Equal.cong(List<&2, S.Level>, Maybe<&2, String>, ls => S.miss.levels(ls), l0, ll,
          Equal.trans(List<&2, S.Level>, l0, List.reverse(&2, S.Level, S.fill.levels(lvs)), ll,
            Equal.cong(Grow.Frame, List<&2, S.Level>, fr => List.reverse(&2, S.Level,
                S.fill.levels(Grow.gw.flevels(fr))),
              Grow.Frame{S.Level{args, binds} <> up, pp}, Grow.Frame{lvs, path}, h_fr2), e_ll)), e1)
      ep = Equal.cong(Grow.Frame, List<&2, String>, fr => Grow.gw.fpath(fr), Grow.Frame{S.Level{args, binds} <> up, pp},
        Grow.Frame{lvs, path}, h_fr2)
      (nm, Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, S.parse.finish.miss(S.miss.levels(l0), pp, l0),
        Fail{S.Missing{pp, nm}}, Fail{S.Missing{path, nm}},
        Equal.cong(Maybe<&2, String>, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish.miss(xx, pp, l0),
          S.miss.levels(l0), Some{nm}, em),
        Equal.cong(List<&2, String>, Result<&2, &2, S.ParseErr, S.Matched>, qq => Fail{S.Missing{qq, nm}}, pp, path,
          ep)))
    case S.St{S.Dead{_e}, _a, _g, _s, _p, _b, _o, _r, _n}:
      Empty.absurd(fin.missing.ty(S.St{S.Dead{_e}, _a, _g, _s, _p, _b, _o, _r, _n}, path), Walk.wk.false_true(h_free))
    case S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}:
      Empty.absurd(fin.missing.ty(S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}, path), Walk.wk.false_true(h_free))
    case S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      Empty.absurd(fin.missing.ty(S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}, path), Walk.wk.false_true(h_free))

def Laws.required_missing(
  spec,
  ws,
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
  h_free,
  h_fr,
  h_unbound
):
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa)
  +fb = S.fill.args(args, bs)
  +r0 = List.reverse(&2, S.Level, S.fill.levels(up))
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  vr.miss(spec, ws, path, fin.missing(S.parse.walk(ws, S.parse.start(spec)),
    List.append(&2, S.Level, qs, S.Level{args, bs} <> up), path,
    List.append(&2, S.Level, r0, S.Level{args, fb} <> rq), h_free, h_fr, M1.fin.levels(qs, args, bs, up),
    fin.miss_levels_some(r0, args, fb, rq, fin.miss_args_some(pa, qa, nn, sh, lo, kind, hp, dflt, cs, fb, h_unbound))))
