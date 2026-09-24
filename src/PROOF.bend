# shake: the proofs. `bend src/PROOF.bend` is the gate.
import Base
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/args.bend as Args
import ../src/walk.bend as Walk
import ./LAWS.bend as Laws

def Laws.looks_flag_long(_ss):
  {==}

def Laws.allowed_any(_vv):
  {==}

def Laws.get_nil(_name):
  {==}

def Laws.on_nil(_name):
  {==}

def Laws.err_text_help(_spec, _path):
  {==}

def Laws.err_text_iff(spec, err):
  match spec err:
    case S.Cli{_n, _a, _v, _g, _s} S.UnknownFlag{_flag}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Missing{_name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NoValue{_name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.BadValue{_name, _value}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedHelp{_path}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Unexpected{_arg}:
      {==}

def Laws.hit_append(bb, _vv, _xs, _ys):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bind_values_append(bs, cs, name):
  match bs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Bind{+nn, +vv}:
          ih = Equal.sym(List<&2, String>,
            S.get_all.bind(List.append(&2, S.Bind, tt, cs), name),
            List.append(&2, String, S.get_all.bind(tt, name), S.get_all.bind(cs, name)),
            Laws.bind_values_append(tt, cs, name))
          %ih : {S.get_all.bind.hit(String.eq(nn, name), vv, _)
            == List.append(&2, String,
              S.get_all.bind.hit(String.eq(nn, name), vv, S.get_all.bind(tt, name)),
              S.get_all.bind(cs, name)) : List<&2, String>}
          Laws.hit_append(String.eq(nn, name), vv, S.get_all.bind(tt, name),
            S.get_all.bind(cs, name))

def Laws.last_snoc(xs, vv, _dflt):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      Laws.last_snoc(tt, vv, hh)

def Laws.get_all_append(_path, bs, cs, name):
  Laws.bind_values_append(bs, cs, name)

def Laws.get_all_hit(_path, name, vv):
  ee = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %ee : {S.get_all.bind.hit(_, vv, []) == [vv] : List<&2, String>}
  {==}

def Laws.get_all_miss(_path, other, name, vv, differ):
  ee = Equal.sym(Bool, String.eq(other, name), False{}, differ)
  %ee : {S.get_all.bind.hit(_, vv, []) == [] : List<&2, String>}
  {==}

def Laws.get_last(_path, bs, cs, name, vv, after):
  e1 = Equal.sym(List<&2, String>,
    S.get_all.bind(List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs), name),
    List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(S.Bind{name, vv} <> cs, name)),
    Laws.bind_values_append(bs, S.Bind{name, vv} <> cs, name))
  %e1 : {S.get.last(_, "") == vv : String}
  e2 = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %e2 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name),
    S.get_all.bind.hit(_, vv, S.get_all.bind(cs, name))), "") == vv : String}
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(cs, name), [], after)
  %e3 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name), vv <> _), "")
    == vv : String}
  Laws.last_snoc(S.get_all.bind(bs, name), vv, "")

def Laws.get_none(_path, bs, name, none):
  ee = Equal.sym(List<&2, String>, S.get_all.bind(bs, name), [], none)
  %ee : {S.get.last(_, "") == "" : String}
  {==}

def Laws.on_get(_found, _name):
  {==}

def Laws.path_of_path(_path, _bs):
  {==}

def Laws.copy_keeps(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      ih = Equal.sym(List<&1, String>, Laws.down(Args.copy(tt)), tt, Laws.copy_keeps(tt))
      %ih : {hh <> _ == hh <> tt : List<&1, String>}
      {==}

def Laws.walk_append(xs, ys, st):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      Laws.walk_append(tt, ys, S.parse.step(hh, st))

def Laws.dead_walk(ys, err, args, specs, subs, path, binds, pos, raw, seen):
  match ys:
    case Nil{}:
      {==}
    case Con{_hh, tt}:
      Laws.dead_walk(tt, err, args, specs, subs, path, binds, pos, raw, seen)

# the type that is empty exactly where a Maybe is Some
def some.emp(mm: Maybe<&2, S.ParseErr>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_e}:
      Empty

# the clash itself: None is not Some
def none.clash(+err: S.ParseErr, eq: {None{} == Some{err} : Maybe<&2, S.ParseErr>}) -> Empty:
  %eq : some.emp(_)
  Unit{}

# nothing is in Empty, so it is any type
def gone(a, -A: Kind(a), never: Empty) -> A:
  match never:

# None is never Some, so such an equation proves anything
def none.absurd(
  a,
  -A: Kind(a),
  +err: S.ParseErr,
  eq: {None{} == Some{err} : Maybe<&2, S.ParseErr>}
) -> A:
  gone(a, A, none.clash(err, eq))

# a Some read back as a failed parse
def some.fail(mm: Maybe<&2, S.ParseErr>) -> Result<&2, &2, S.ParseErr, S.Matched>:
  match mm:
    case None{}:
      Fail{S.Missing{""}}
    case Some{ee}:
      Fail{ee}

def Laws.fail_from(st, more, err, died):
  match st:
    case S.St{S.Dead{+ee}, +aa, +gg, +ss, +pp, +bb, +oo, +rr, +nn}:
      e1 = Equal.sym(S.St,
        S.parse.walk(more, S.St{S.Dead{ee}, aa, gg, ss, pp, bb, oo, rr, nn}),
        S.St{S.Dead{ee}, aa, gg, ss, pp, bb, oo, rr, nn},
        Laws.dead_walk(more, ee, aa, gg, ss, pp, bb, oo, rr, nn))
      %e1 : {S.parse.finish(_) == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}
      Equal.cong(Maybe<&2, S.ParseErr>, Result<&2, &2, S.ParseErr, S.Matched>,
        mm => some.fail(mm), Some{ee}, Some{err}, died)
    case S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {S.parse.finish(S.parse.walk(more, S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n}))
        == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}, err, died)
    case S.St{S.Need{_name}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {S.parse.finish(S.parse.walk(more, S.St{S.Need{_name}, _a, _g, _s, _p, _b, _o, _r, _n}))
        == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}, err, died)
    case S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {S.parse.finish(S.parse.walk(more, S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}))
        == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}, err, died)

def Laws.fail_stays(spec, ws, more, err, died):
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec)),
    S.parse.walk(more, S.parse.walk(ws, S.parse.start(spec))),
    Laws.walk_append(ws, more, S.parse.start(spec)))
  %e1 : {S.parse.finish(_) == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}
  Laws.fail_from(S.parse.walk(ws, S.parse.start(spec)), more, err, died)

def Laws.prefix_empty(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def Laws.drop_zero(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def Laws.unknown_long_step(body, name, val, args, specs, subs, path, bs, pos, seen, h_dd, h_cut, h_name, h_none):
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "--" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, Laws.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(_, True{}, "--" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, Laws.drop_zero(body))
  %ed : {S.parse.take_long(_, "--" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {S.parse.take_long.cut(_, "--" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, String.is_empty(name), False{}, h_name)
  %e3 : {S.parse.take_long.named(_, name, val, "--" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e4 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), None{}, h_none)
  %e4 : {S.parse.take_arg(_, val, "--" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  {==}

def Laws.unknown_long_dies(
  spec,
  pre,
  body,
  name,
  val,
  args,
  specs,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_none
):
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, pre, ["--" ++ body]), S.parse.start(spec)),
    S.parse.walk(["--" ++ body], S.parse.walk(pre, S.parse.start(spec))),
    Laws.walk_append(pre, ["--" ++ body], S.parse.start(spec)))
  %e1 : {Laws.dead_of(_) == Some{S.UnknownFlag{"--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St,
    S.parse.walk(pre, S.parse.start(spec)),
    S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen},
    h_at)
  %e2 : {Laws.dead_of(S.parse.walk(["--" ++ body], _)) == Some{S.UnknownFlag{"--" ++ body}}
    : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen}),
    S.St{S.Dead{S.UnknownFlag{"--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen},
    Laws.unknown_long_step(body, name, val, args, specs, subs, path, bs, pos, seen,
      h_dd, h_cut, h_name, h_none))
  %e3 : {Laws.dead_of(_) == Some{S.UnknownFlag{"--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.unknown_long(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  specs,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_none
):
  Laws.fail_stays(spec, List.append(&2, String, pre, ["--" ++ body]), more, S.UnknownFlag{"--" ++ body},
    Laws.unknown_long_dies(spec, pre, body, name, val, args, specs, subs, path, bs, pos, seen,
      h_at, h_dd, h_cut, h_name, h_none))

def Laws.unknown_short_step(
  body,
  name,
  val,
  args,
  specs,
  subs,
  path,
  bs,
  pos,
  seen,
  h_dd,
  h_alone,
  h_dash,
  h_cut,
  h_none
):
  e1 = Equal.sym(Bool, String.eq("-" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "-" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, Laws.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(String.starts_with(body, "-"), _, "-" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(Bool, String.starts_with(body, "-"), False{}, h_dash)
  %e2 : {S.parse.step.kind.go(_, True{}, "-" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, String.eq("-" ++ body, "-"), False{}, h_alone)
  %e3 : {S.parse.step.short.go(_, "-" ++ body, args, specs, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, Laws.drop_zero(body))
  %ed : {S.parse.take_short(_, "-" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e4 = Equal.sym(String & Maybe<&2, String>, S.short_of(body), (name, val), h_cut)
  %e4 : {S.parse.take_short.cut(_, "-" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  e5 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, name), None{}, h_none)
  %e5 : {S.parse.take_arg(_, val, "-" ++ body, args, specs, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  {==}

def Laws.unknown_short_dies(
  spec,
  pre,
  body,
  name,
  val,
  args,
  specs,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_alone,
  h_dash,
  h_cut,
  h_none
):
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, pre, ["-" ++ body]), S.parse.start(spec)),
    S.parse.walk(["-" ++ body], S.parse.walk(pre, S.parse.start(spec))),
    Laws.walk_append(pre, ["-" ++ body], S.parse.start(spec)))
  %e1 : {Laws.dead_of(_) == Some{S.UnknownFlag{"-" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St,
    S.parse.walk(pre, S.parse.start(spec)),
    S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen},
    h_at)
  %e2 : {Laws.dead_of(S.parse.walk(["-" ++ body], _)) == Some{S.UnknownFlag{"-" ++ body}}
    : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(S.St,
    S.parse.step("-" ++ body, S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen}),
    S.St{S.Dead{S.UnknownFlag{"-" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen},
    Laws.unknown_short_step(body, name, val, args, specs, subs, path, bs, pos, seen,
      h_dd, h_alone, h_dash, h_cut, h_none))
  %e3 : {Laws.dead_of(_) == Some{S.UnknownFlag{"-" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.unknown_short(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  specs,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_alone,
  h_dash,
  h_cut,
  h_none
):
  Laws.fail_stays(spec, List.append(&2, String, pre, ["-" ++ body]), more, S.UnknownFlag{"-" ++ body},
    Laws.unknown_short_dies(spec, pre, body, name, val, args, specs, subs, path, bs, pos, seen,
      h_at, h_dd, h_alone, h_dash, h_cut, h_none))
