# proofs of laws/DefaultsFillUnbound.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
import ../laws/DefaultsFillUnbound.bend as Laws
import ../laws/defs/ValuesAtPath.bend as D1
import ./lemmas/FinishedWalker.bend as M1

# a list that is not nonempty is empty
def fin.empty_of(
  xs: List<&2, String>,
  hh: {Bool.not(List.is_empty(&2, String, xs)) == False{} : Bool}
) -> {xs == [] : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({x <> t == [] : List<&2, String>}, Walk.wk.true_false(hh))

# an unbound name has no values
def fin.g_unbound(
  +xs: List<&2, S.Bind>,
  +nn: String,
  hh: {S.bound(xs, nn) == False{} : Bool}
) -> {S.get_all.bind(xs, nn) == [] : List<&2, String>}:
  fin.empty_of(S.get_all.bind(xs, nn),
    Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(xs, nn))), S.bound(xs, nn), False{},
      Equal.sym(Bool, S.bound(xs, nn), Bool.not(List.is_empty(&2, String, S.get_all.bind(xs, nn))),
        M1.fin.bound_g(xs, nn)), hh))

# a default of another name adds nothing to `nn`'s values, nor binds it
def fin.one_other(
  skip: Bool,
  +mm: String,
  +vv: String,
  +ff: List<&2, S.Bind>,
  +nn: String,
  h_ne: {String.eq(mm, nn) == False{} : Bool}
) -> {S.get_all.bind(S.fill.one(skip, mm, vv, ff), nn) == S.get_all.bind(ff, nn) : List<&2, String>}:
  match skip:
    case True{}:
      {==}
    case False{}:
      ee = Equal.sym(Bool, String.eq(mm, nn), False{}, h_ne)
      %ee : {S.get_all.bind.hit(_, vv, S.get_all.bind(ff, nn)) == S.get_all.bind(ff, nn) : List<&2, String>}
      {==}

# the same, for whether `nn` is bound
def fin.one_other_b(
  skip: Bool,
  +mm: String,
  +vv: String,
  +ff: List<&2, S.Bind>,
  +nn: String,
  h_ne: {String.eq(mm, nn) == False{} : Bool}
) -> {S.bound(S.fill.one(skip, mm, vv, ff), nn) == S.bound(ff, nn) : Bool}:
  match skip:
    case True{}:
      {==}
    case False{}:
      ee = Equal.sym(Bool, String.eq(mm, nn), False{}, h_ne)
      %ee : {S.bound.at(_, S.bound(ff, nn)) == S.bound(ff, nn) : Bool}
      {==}

# an argument of another name, with or without a default
def fin.go_other(
  dd: Maybe<&2, String>,
  +mm: String,
  +ff: List<&2, S.Bind>,
  +nn: String,
  +h_ne: {String.eq(mm, nn) == False{} : Bool}
) -> {S.get_all.bind(S.fill.arg.go(dd, mm, ff), nn) == S.get_all.bind(ff, nn) : List<&2, String>}:
  match dd:
    case None{}:
      {==}
    case Some{+vv}:
      fin.one_other(S.bound(ff, mm), mm, vv, ff, nn, h_ne)

# the same, for whether `nn` is bound
def fin.go_other_b(
  dd: Maybe<&2, String>,
  +mm: String,
  +ff: List<&2, S.Bind>,
  +nn: String,
  +h_ne: {String.eq(mm, nn) == False{} : Bool}
) -> {S.bound(S.fill.arg.go(dd, mm, ff), nn) == S.bound(ff, nn) : Bool}:
  match dd:
    case None{}:
      {==}
    case Some{+vv}:
      fin.one_other_b(S.bound(ff, mm), mm, vv, ff, nn, h_ne)

# the head of a list with no argument named `nn` is not named `nn`
def fin.named_head(
  +mm: String,
  +tt: List<&2, S.Arg>,
  +nn: String,
  +h_none: {Bool.and(Bool.not(String.eq(mm, nn)), Laws.none_named(tt, nn)) == True{} : Bool}
) -> {String.eq(mm, nn) == False{} : Bool}:
  Walk.wk.not_true(String.eq(mm, nn), Walk.wk.and_l(Bool.not(String.eq(mm, nn)), Laws.none_named(tt, nn), h_none))

# the rest of a list with no argument named `nn` has none
def fin.named_tail(
  +mm: String,
  +tt: List<&2, S.Arg>,
  +nn: String,
  +h_none: {Bool.and(Bool.not(String.eq(mm, nn)), Laws.none_named(tt, nn)) == True{} : Bool}
) -> {Laws.none_named(tt, nn) == True{} : Bool}:
  Walk.wk.and_r(Bool.not(String.eq(mm, nn)), Laws.none_named(tt, nn), h_none)

# filling the defaults of arguments none named `nn` changes none of its values
def fin.fill_other(
  args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +nn: String,
  +h_none: {Laws.none_named(args, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(args, bs), nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+mm, _s, _l, _k, _h, _r, S.Fallback{_e, dd}, _c}:
          Equal.trans(List<&2, String>, S.get_all.bind(S.fill.arg.go(dd, mm, S.fill.args(tt, bs)), nn),
            S.get_all.bind(S.fill.args(tt, bs), nn), S.get_all.bind(bs, nn),
            fin.go_other(dd, mm, S.fill.args(tt, bs), nn, fin.named_head(mm, tt, nn, h_none)),
            fin.fill_other(tt, bs, nn, fin.named_tail(mm, tt, nn, h_none)))

# the same, for whether `nn` is bound
def fin.fill_other_b(
  args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +nn: String,
  +h_none: {Laws.none_named(args, nn) == True{} : Bool}
) -> {S.bound(S.fill.args(args, bs), nn) == S.bound(bs, nn) : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+mm, _s, _l, _k, _h, _r, S.Fallback{_e, dd}, _c}:
          Equal.trans(Bool, S.bound(S.fill.arg.go(dd, mm, S.fill.args(tt, bs)), nn), S.bound(S.fill.args(tt, bs), nn),
            S.bound(bs, nn),
            fin.go_other_b(dd, mm, S.fill.args(tt, bs), nn, fin.named_head(mm, tt, nn, h_none)),
            fin.fill_other_b(tt, bs, nn, fin.named_tail(mm, tt, nn, h_none)))

# arguments before the one named `nn`, none named `nn`, change none of its
# values
def fin.fill_pre(
  pa: List<&2, S.Arg>,
  +rest: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +nn: String,
  +h_none: {Laws.none_named(pa, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, rest), bs), nn)
    == S.get_all.bind(S.fill.args(rest, bs), nn) : List<&2, String>}:
  match pa:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+mm, _s, _l, _k, _h, _r, S.Fallback{_e, dd}, _c}:
          +ff = S.fill.args(List.append(&2, S.Arg, tt, rest), bs)
          Equal.trans(List<&2, String>, S.get_all.bind(S.fill.arg.go(dd, mm, ff), nn), S.get_all.bind(ff, nn),
            S.get_all.bind(S.fill.args(rest, bs), nn),
            fin.go_other(dd, mm, ff, nn, fin.named_head(mm, tt, nn, h_none)),
            fin.fill_pre(tt, rest, bs, nn, fin.named_tail(mm, tt, nn, h_none)))

# the default goes in front, once, of values there were none of
def fin.fill_default.go(
  +nn: String,
  +dd: String,
  +ff: List<&2, S.Bind>,
  e1: {False{} == S.bound(ff, nn) : Bool},
  e2: {True{} == String.eq(nn, nn) : Bool},
  e3: {[] == S.get_all.bind(ff, nn) : List<&2, String>}
) -> {S.get_all.bind(S.fill.one(S.bound(ff, nn), nn, dd, ff), nn) == [dd] : List<&2, String>}:
  %e1 : {S.get_all.bind(S.fill.one(_, nn, dd, ff), nn) == [dd] : List<&2, String>}
  %e2 : {S.get_all.bind.hit(_, dd, S.get_all.bind(ff, nn)) == [dd] : List<&2, String>}
  %e3 : {dd <> _ == [dd] : List<&2, String>}
  {==}

# the default of the argument named `nn`, when its command left it unbound
def fin.fill_default(
  +pa: List<&2, S.Arg>,
  +qa: List<&2, S.Arg>,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +ev: Maybe<&2, String>,
  +dd: String,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  +h_qa: {Laws.none_named(qa, nn) == True{} : Bool},
  +h_free: {S.bound(bs, nn) == False{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev,
    Some{dd}}, cs} <> qa), bs),
    nn) == [dd] : List<&2, String>}:
  +ff = S.fill.args(qa, bs)
  e1 = Equal.sym(Bool, S.bound(ff, nn), False{},
    Equal.trans(Bool, S.bound(ff, nn), S.bound(bs, nn), False{}, fin.fill_other_b(qa, bs, nn, h_qa), h_free))
  e2 = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(ff, nn), [],
    Equal.trans(List<&2, String>, S.get_all.bind(ff, nn), S.get_all.bind(bs, nn), [], fin.fill_other(qa, bs, nn, h_qa),
      fin.g_unbound(bs, nn, h_free)))
  Equal.trans(List<&2, String>,
    S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{dd}},
        cs} <> qa),
        bs), nn),
    S.get_all.bind(S.fill.one(S.bound(ff, nn), nn, dd, ff), nn), [dd],
    fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{dd}}, cs} <> qa, bs, nn, h_pa),
    fin.fill_default.go(nn, dd, ff, e1, e2, e3))

# a bound argument's values, with or without a default
def fin.kept_go(
  dflt: Maybe<&2, String>,
  +nn: String,
  +ff: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>,
  eg: {S.get_all.bind(ff, nn) == S.get_all.bind(bs, nn) : List<&2, String>},
  eb: {S.bound(ff, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.arg.go(dflt, nn, ff), nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  match dflt:
    case None{}:
      eg
    case Some{+vv}:
      ee = Equal.sym(Bool, S.bound(ff, nn), True{}, eb)
      %ee : {S.get_all.bind(S.fill.one(_, nn, vv, ff), nn) == S.get_all.bind(bs, nn) : List<&2, String>}
      eg

# whatever the default, a bound argument keeps exactly its values
def fin.fill_kept(
  +pa: List<&2, S.Arg>,
  +qa: List<&2, S.Arg>,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  +h_qa: {Laws.none_named(qa, nn) == True{} : Bool},
  h_bound: {S.bound(bs, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa), bs),
    nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  match dflt:
    case S.Fallback{+ev, +dm}:
      +ff = S.fill.args(qa, bs)
      Equal.trans(List<&2, String>,
        S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dm},
            cs} <> qa),
          bs), nn),
        S.get_all.bind(S.fill.arg.go(dm, nn, ff), nn), S.get_all.bind(bs, nn),
        fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dm}, cs} <> qa, bs, nn, h_pa),
        fin.kept_go(dm, nn, ff, bs, fin.fill_other(qa, bs, nn, h_qa),
          Equal.trans(Bool, S.bound(ff, nn), S.bound(bs, nn), True{}, fin.fill_other_b(qa, bs, nn, h_qa), h_bound)))

# an argument with no default keeps exactly its values
def fin.fill_nodef(
  +pa: List<&2, S.Arg>,
  +qa: List<&2, S.Arg>,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +ev: Maybe<&2, String>,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  h_qa: {Laws.none_named(qa, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, None{}},
    cs} <> qa), bs),
    nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, None{}},
        cs} <> qa), bs), nn),
    S.get_all.bind(S.fill.args(qa, bs), nn), S.get_all.bind(bs, nn),
    fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, None{}}, cs} <> qa, bs, nn, h_pa),
        fin.fill_other(qa, bs,
        nn, h_qa))

# `get_all` in the Matched of the command at `path`: its bindings, defaults
# filled, read back
def fin.all(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +found: Shake.Matched,
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +ms: List<&2, String>,
  +nn: String,
  h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>},
  h_fr: M1.fin.Framed(spec, ws, qs, args, bs, up, path, ms),
  h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
) -> {D1.all_at(found, path, nn)
    == Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))} : Maybe<&2, List<&2, String>>}:
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, nn),
    Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), nn)},
    Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, List<&2, String>>, mm => D1.all_at.go(mm, nn), S.at(found, path),
      Some{S.matched.build(f0 <> rq, ms)}, M1.fin.at(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len)),
    Equal.trans(Maybe<&2, List<&2, String>>, Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), nn)},
      Some{S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, bs)), nn)},
      Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))},
      Equal.cong(List<&2, S.Bind>, Maybe<&2, List<&2, String>>, xs => Some{S.get_all.bind(xs, nn)},
        S.own(S.matched.build(f0 <> rq, ms)), List.reverse(&2, S.Bind, S.fill.args(args, bs)),
        Grow.gw.own_build(f0, rq, ms)),
      Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, xs => Some{xs},
        S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, bs)), nn),
        List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn)), M1.fin.g_rev(S.fill.args(args, bs), nn))))

# `get_all` of the command at `path` reads `xs`
def fin.All(+found: Shake.Matched, +path: List<&2, String>, +nn: String, +xs: List<&2, String>) -> Type:
  {D1.all_at(found, path, nn) == Some{xs} : Maybe<&2, List<&2, String>>}

# a level's values read back, from what filling it gives the name
def fin.back(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nn: String,
  +xs: List<&2, String>,
  +ys: List<&2, String>,
  ea: {D1.all_at(found, path, nn) == Some{List.reverse(&2, String, xs)} : Maybe<&2, List<&2, String>>},
  ex: {xs == ys : List<&2, String>}
) -> {D1.all_at(found, path, nn) == Some{List.reverse(&2, String, ys)} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, nn), Some{List.reverse(&2, String, xs)},
    Some{List.reverse(&2, String, ys)}, ea,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, zs => Some{List.reverse(&2, String, zs)}, xs, ys, ex))

# the values the words bound, read back in binding order
def fin.back_bs(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nn: String,
  +bs: List<&2, S.Bind>,
  ea: fin.All(found, path, nn, List.reverse(&2, String, S.get_all.bind(bs, nn)))
) -> {D1.all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)}
    : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, nn),
    Some{List.reverse(&2, String, S.get_all.bind(bs, nn))}, Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)}, ea,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, zs => Some{zs},
      List.reverse(&2, String, S.get_all.bind(bs, nn)), S.get_all.bind(List.reverse(&2, S.Bind, bs), nn),
      Equal.sym(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, bs), nn),
        List.reverse(&2, String, S.get_all.bind(bs, nn)), M1.fin.g_rev(bs, nn))))

def Laws.default_filled(
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
  req,
  ev,
  dd,
  cs,
  bs,
  up,
  path,
  ms,
  h_done,
  h_fr,
  h_len,
  h_pa,
  h_qa,
  h_free
):
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{dd}}, cs} <> qa)
  fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), [dd],
    fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
    fin.fill_default(pa, qa, nn, sh, lo, kind, hp, req, ev, dd, cs, bs, h_pa, h_qa, h_free))

def Laws.bound_kept(
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
  req,
  dflt,
  cs,
  bs,
  up,
  path,
  ms,
  h_done,
  h_fr,
  h_len,
  h_pa,
  h_qa,
  h_bound
):
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa)
  fin.back_bs(found, path, nn, bs,
    fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), S.get_all.bind(bs, nn),
      fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
      fin.fill_kept(pa, qa, nn, sh, lo, kind, hp, req, dflt, cs, bs, h_pa, h_qa, h_bound)))

def Laws.no_default(
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
  req,
  ev,
  cs,
  bs,
  up,
  path,
  ms,
  h_done,
  h_fr,
  h_len,
  h_pa,
  h_qa
):
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, None{}}, cs} <> qa)
  fin.back_bs(found, path, nn, bs,
    fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), S.get_all.bind(bs, nn),
      fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
      fin.fill_nodef(pa, qa, nn, sh, lo, kind, hp, req, ev, cs, bs, h_pa, h_qa)))

def Laws.no_argument(spec, ws, found, qs, args, nn, bs, up, path, ms, h_done, h_fr, h_len, h_none):
  fin.back_bs(found, path, nn, bs,
    fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), S.get_all.bind(bs, nn),
      fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
      fin.fill_other(args, bs, nn, h_none)))
