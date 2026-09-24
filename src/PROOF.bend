# shake: the proofs. `bend src/PROOF.bend` is the gate.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/args.bend as Args
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
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
    case S.Cli{_n, _a, _v, _g, _s} S.UnknownFlag{_at, _flag}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Missing{_at, _name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NoValue{_at, _name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.BadValue{_at, _name, _value}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedHelp{_path}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Unexpected{_at, _arg}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Repeated{_at, _name}:
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
      Laws.last_snoc(tt, vv, Some{hh})

def Laws.get_all_append(bs, cs, name):
  Laws.bind_values_append(bs, cs, name)

def Laws.get_all_hit(name, vv):
  ee = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %ee : {S.get_all.bind.hit(_, vv, []) == [vv] : List<&2, String>}
  {==}

def Laws.get_all_miss(other, name, vv, differ):
  ee = Equal.sym(Bool, String.eq(other, name), False{}, differ)
  %ee : {S.get_all.bind.hit(_, vv, []) == [] : List<&2, String>}
  {==}

def Laws.get_last(bs, cs, name, vv, after):
  e1 = Equal.sym(List<&2, String>,
    S.get_all.bind(List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs), name),
    List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(S.Bind{name, vv} <> cs, name)),
    Laws.bind_values_append(bs, S.Bind{name, vv} <> cs, name))
  %e1 : {S.get.last(_, None{}) == Some{vv} : Maybe<&2, String>}
  e2 = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %e2 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name),
    S.get_all.bind.hit(_, vv, S.get_all.bind(cs, name))), None{}) == Some{vv}
    : Maybe<&2, String>}
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(cs, name), [], after)
  %e3 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name), vv <> _), None{})
    == Some{vv} : Maybe<&2, String>}
  Laws.last_snoc(S.get_all.bind(bs, name), vv, None{})

def Laws.get_none(bs, name, none):
  ee = Equal.sym(List<&2, String>, S.get_all.bind(bs, name), [], none)
  %ee : {S.get.last(_, None{}) == None{} : Maybe<&2, String>}
  {==}

def Laws.on_some(found, name, vv, h_get):
  ee = Equal.sym(Maybe<&2, String>, Shake.get(found, name), Some{vv}, h_get)
  %ee : {S.on.of(_) == String.eq(vv, "true") : Bool}
  {==}

def Laws.on_none(found, name, h_get):
  ee = Equal.sym(Maybe<&2, String>, Shake.get(found, name), None{}, h_get)
  %ee : {S.on.of(_) == False{} : Bool}
  {==}

def Laws.get_all_node(_bs, _nn, _below, _name):
  {==}

def Laws.get_node(_bs, _nn, _below, _name):
  {==}

def Laws.sub_name_leaf(_bs):
  {==}

def Laws.sub_name_node(_bs, _nn, _below):
  {==}

def Laws.sub_of_hit(_bs, nn, below):
  ee = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  %ee : {S.sub_of.pick(_, below) == Some{below} : Maybe<&2, S.Matched>}
  {==}

def Laws.sub_of_miss(_bs, nn, below, name, differ):
  ee = Equal.sym(Bool, String.eq(nn, name), False{}, differ)
  %ee : {S.sub_of.pick(_, below) == None{} : Maybe<&2, S.Matched>}
  {==}

def Laws.sub_of_leaf(_bs, _name):
  {==}

def Laws.path_of_leaf(_bs):
  {==}

def Laws.path_of_node(_bs, _nn, _below):
  {==}

def Laws.at_nil(found):
  match found:
    case S.Leaf{_b}:
      {==}
    case S.Node{_b, _n, _s}:
      {==}

# a walk down that found nothing finds nothing further down
def at_cons.none(rest: List<&2, String>) -> {S.at.go(rest, None{}) == None{} : Maybe<&2, S.Matched>}:
  match rest:
    case Nil{}:
      {==}
    case Con{_h, tt}:
      at_cons.none(tt)

# the rest of a walk down, from what the first name found
def at_cons.via(
  mm: Maybe<&2, S.Matched>,
  +rest: List<&2, String>
) -> {S.at.go(rest, mm) == Laws.at.via(mm, rest) : Maybe<&2, S.Matched>}:
  match mm:
    case None{}:
      at_cons.none(rest)
    case Some{_m}:
      {==}

def Laws.at_cons(found, name, rest):
  at_cons.via(S.sub_of(found, name), rest)

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

def Laws.dead_walk(ys, err, args, up, subs, path, binds, pos, raw, seen):
  match ys:
    case Nil{}:
      {==}
    case Con{_hh, tt}:
      Laws.dead_walk(tt, err, args, up, subs, path, binds, pos, raw, seen)

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
      Fail{S.Missing{[], ""}}
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

def Laws.unknown_long_step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name, h_none):
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, Laws.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, Laws.drop_zero(body))
  %ed : {S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, String.is_empty(name), False{}, h_name)
  %e3 : {S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e4 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), None{}, h_none)
  %e4 : {S.parse.take_arg(_, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  {==}

def Laws.unknown_long_dies(
  spec,
  pre,
  body,
  name,
  val,
  args,
  up,
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
  %e1 : {Laws.dead_of(_) == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St,
    S.parse.walk(pre, S.parse.start(spec)),
    S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
    h_at)
  %e2 : {Laws.dead_of(S.parse.walk(["--" ++ body], _)) == Some{S.UnknownFlag{path, "--" ++ body}}
    : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen},
    Laws.unknown_long_step(body, name, val, args, up, subs, path, bs, pos, seen,
      h_dd, h_cut, h_name, h_none))
  %e3 : {Laws.dead_of(_) == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.unknown_long(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
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
  Laws.fail_stays(spec, List.append(&2, String, pre, ["--" ++ body]), more, S.UnknownFlag{path, "--" ++ body},
    Laws.unknown_long_dies(spec, pre, body, name, val, args, up, subs, path, bs, pos, seen,
      h_at, h_dd, h_cut, h_name, h_none))

def Laws.step_dies(
  spec,
  pre,
  tok,
  st,
  err,
  h_at,
  h_step
):
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)),
    S.parse.walk([tok], S.parse.walk(pre, S.parse.start(spec))),
    Laws.walk_append(pre, [tok], S.parse.start(spec)))
  %e1 : {Laws.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St, S.parse.walk(pre, S.parse.start(spec)), st, h_at)
  %e2 : {Laws.dead_of(S.parse.walk([tok], _)) == Some{err} : Maybe<&2, S.ParseErr>}
  h_step

def Laws.refused(
  spec,
  pre,
  more,
  tok,
  st,
  err,
  h_at,
  h_step
):
  Laws.fail_stays(spec, List.append(&2, String, pre, [tok]), more, err,
    Laws.step_dies(spec, pre, tok, st, err, h_at, h_step))

def Laws.cluster_done(body, orig, st):
  match body:
    case SNil{}:
      {==}
    case SCon{_cc, rest}:
      Laws.cluster_done(rest, orig, st)

def Laws.unknown_short_step(
  cc,
  rest,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_dd,
  h_dash,
  h_none
):
  e1 = Equal.sym(Bool, String.eq("-" ++ SCon{cc, rest}, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "-" ++ SCon{cc, rest}, args, up, subs, path, bs, pos,
      seen) == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, h_dash)
  %e3 : {S.parse.step.kind.go(String.starts_with.if(rest, "", _), True{}, "-" ++ SCon{cc, rest}, args, up,
      subs, path, bs, pos,
      seen) == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), None{}, h_none)
  %e2 : {S.cluster(rest, "-" ++ SCon{cc, rest},
      S.parse.take_arg(_, S.cluster.val(_, rest), "-" ++ SCon{cc, rest}, args, up, subs, path, bs, pos,
          False{}, seen),
      S.cluster.ends(_, rest))
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  Laws.cluster_done(rest, "-" ++ SCon{cc, rest}, S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args,
      up, subs, path, bs, pos, False{}, seen})

# the first letter of a short cluster that no argument has fails the step
def unknown_short.step(
  +cc: Char,
  +rest: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool},
  h_dash: {Char.is_eq(cc, '-') == False{} : Bool},
  h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
) -> {Laws.dead_of(S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
    seen})) == Some{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}
    : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(S.St, S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos,
      False{}, seen}), S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen},
    Laws.unknown_short_step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_none))
  %ee : {Laws.dead_of(_) == Some{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.unknown_short(
  spec,
  pre,
  more,
  cc,
  rest,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_dash,
  h_none
):
  Laws.refused(spec, pre, more, "-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
      seen}, S.UnknownFlag{path, "-" ++ SCon{cc, rest}}, h_at,
    unknown_short.step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_none))

# a plain word with no positional left fails the step with Unexpected
def no_pos_left.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{},
    seen})) == Some{S.Unexpected{path, tok}}
    : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(S.St, S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, [], False{}),
    Walk.wk.word_step(tok, args, up, subs, path, bs, [], seen, h_dd, h_help, h_dash, h_sub))
  %ee : {Laws.dead_of(_) == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.no_pos_left(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub
):
  Laws.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{}, seen},
      S.Unexpected{path, tok}, h_at,
    no_pos_left.step(tok, args, up, subs, path, bs, seen, h_dd, h_help, h_dash, h_sub))

# a plain word outside the next positional's choices fails the step with
# BadValue
def choice_refused.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>},
  h_bad: {S.allowed(cs, tok) == False{} : Bool}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
    req, dflt, cs} <> rest, False{}, seen})) == Some{S.BadValue{path, name, tok}}
    : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind,
      hp, req, dflt, cs} <> rest, False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}),
    Walk.wk.word_step(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
        seen, h_dd, h_help, h_dash,
      h_sub))
  %e1 : {Laws.dead_of(_) == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.allowed(cs, tok), False{}, h_bad)
  %e2 : {Laws.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.choice_refused(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_bad
):
  Laws.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
      req, dflt, cs} <> rest, False{}, seen}, S.BadValue{path, name, tok}, h_at,
    choice_refused.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs,
      rest, h_dd, h_help, h_dash, h_sub, h_bad))

def Laws.long_arg_step(
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_dd,
  h_cut,
  h_name
):
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, Laws.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, Laws.drop_zero(body))
  %ed : {S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e3 = Equal.sym(Bool, String.is_empty(name), False{}, h_name)
  %e3 : {S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  {==}

# a long option that gives a flag a value fails the step
def flag_long_valued.step(
  +body: String,
  +name: String,
  +vv: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_once: {S.bound(bs, nn) == False{} : Bool}
) -> {Laws.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_arg(S.by_long(args, name), Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen),
    Laws.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {Laws.dead_of(_) == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}, h_found)
  %e2 : {Laws.dead_of(S.parse.take_arg(_, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, h_once)
  %e3 : {Laws.dead_of(S.parse.once(_, S.St{S.Dead{S.Unexpected{path, "--" ++ body}}, args, up, subs, path, bs, pos,
      False{}, seen}, nn, path)) == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.flag_long_valued(
  spec,
  pre,
  more,
  body,
  name,
  vv,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_once
):
  Laws.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.Unexpected{path, "--" ++ body}, h_at,
    flag_long_valued.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_once))

# a flag-shaped word where a value is wanted fails the step
def value_flag_shaped.step(
  +tok: String,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_flag: {S.looks_flag(tok) == True{} : Bool}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.NoValue{path, name}} : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(Bool, S.looks_flag(tok), True{}, h_flag)
  %ee : {Laws.dead_of(S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.NoValue{path, name}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.value_flag_shaped(
  spec,
  pre,
  more,
  tok,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at,
  h_flag
):
  Laws.refused(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen},
    S.NoValue{path, name}, h_at, value_flag_shaped.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag))

def Laws.value_absent(
  spec,
  ws,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at
):
  ee = Equal.sym(S.St, S.parse.walk(ws, S.parse.start(spec)),
    S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}, h_at)
  %ee : {S.parse.finish(_) == Fail{S.NoValue{path, name}} : Result<&2, &2, S.ParseErr, S.Matched>}
  {==}

# a word after `help` that names no subcommand where the path stands fails
# the step
def help_unknown.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, tok), None{}, h_sub)
  %ee : {Laws.dead_of(S.parse.step.help_path(_, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.help_unknown(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at,
  h_sub
):
  Laws.refused(spec, pre, more, tok, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen},
    S.Unexpected{path, tok}, h_at, help_unknown.step(tok, args, up, subs, path, bs, pos, raw, seen, h_sub))

# `--=...` fails the step
def long_no_name.step(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_empty: {String.is_empty(name) == True{} : Bool}
) -> {Laws.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {Laws.dead_of(S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, Laws.prefix_empty(body))
  %e0 : {Laws.dead_of(S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  ed = Equal.sym(String, String.drop(body, 0n), body, Laws.drop_zero(body))
  %ed : {Laws.dead_of(S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {Laws.dead_of(S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, String.is_empty(name), True{}, h_empty)
  %e3 : {Laws.dead_of(S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos,
      False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.long_no_name(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_empty
):
  Laws.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.UnknownFlag{path, "--" ++ body}, h_at,
    long_no_name.step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_empty))

def Laws.once_dead(st, _nn, _path):
  match st:
    case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      {==}

# a long option given again fails the step
def repeated_long_flag.step(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_again: {S.bound(bs, nn) == True{} : Bool}
) -> {Laws.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
    seen})) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen),
    Laws.long_arg_step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {Laws.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}, h_found)
  %e2 : {Laws.dead_of(S.parse.take_arg(_, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e3 : {Laws.dead_of(S.parse.once(_, S.parse.take_flag(val, nn, "--" ++ body, args, up, subs, path, bs, pos,
      False{}, seen), nn, path)) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  Laws.once_dead(S.parse.take_flag(val, nn, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen), nn, path)

def Laws.repeated_long_flag(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_again
):
  Laws.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.Repeated{path, nn}, h_at,
    repeated_long_flag.step(body, name, val, args, up, subs, path, bs, pos, seen, nn, sh, lo, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_again))

# a long option given again fails the step
def repeated_long_opt.step(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_again: {S.bound(bs, nn) == True{} : Bool}
) -> {Laws.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
    seen})) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen),
    Laws.long_arg_step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {Laws.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}}, h_found)
  %e2 : {Laws.dead_of(S.parse.take_arg(_, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e3 : {Laws.dead_of(S.parse.once(_, S.parse.take_opt(val, nn, args, up, subs, path, bs, pos, False{},
      seen), nn, path)) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  Laws.once_dead(S.parse.take_opt(val, nn, args, up, subs, path, bs, pos, False{}, seen), nn, path)

def Laws.repeated_long_opt(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_again
):
  Laws.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.Repeated{path, nn}, h_at,
    repeated_long_opt.step(body, name, val, args, up, subs, path, bs, pos, seen, nn, sh, lo, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_again))

# the walk through `tok` is one step from where the words before it stood
def kept.stepped(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +tok: String,
  +st: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)) == S.parse.step(tok, st) : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)),
    S.parse.walk([tok], S.parse.walk(pre, S.parse.start(spec))), S.parse.step(tok, st),
    Laws.walk_append(pre, [tok], S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk([tok], xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))

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
  &after: List<&2, String> -> {Laws.all_at(found, path, name)
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
  {Laws.all_at(found, path, name) == Some{kept_all.vals(args, ys, name)} : Maybe<&2, List<&2, String>>}

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
  Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, name),
    Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), name)},
    Some{S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, ys)), name)},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, List<&2, String>>, mm => Laws.all_at.go(mm, name), S.at(found, path),
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
          Laws.bind_values_append(List.reverse(&2, S.Bind, bs), List.append(&2, S.Bind, List.reverse(&2, S.Bind,
              xs), r1),
            name),
          Equal.cong(List<&2, String>, List<&2, String>, zs => List.append(&2, String, gb, zs),
            S.get_all.bind(List.append(&2, S.Bind, List.reverse(&2, S.Bind, xs), r1), name),
            List.append(&2, String, gx, S.get_all.bind(r1, name)),
            Laws.bind_values_append(List.reverse(&2, S.Bind, xs), r1, name))))))

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
  (after, Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, name), Some{zz}, Some{ww}, er,
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

def Laws.kept_all(spec, pre, mid, more, st, args, up, path, xs, bs, name, found, h_at, h_mid, h_done):
  +st1 = S.parse.walk(mid, st)
  +ww = List.append(&2, String, pre, mid)
  +e_st = {Equal.trans(S.St, S.parse.walk(ww, S.parse.start(spec)),
    S.parse.walk(mid, S.parse.walk(pre, S.parse.start(spec))), st1, Laws.walk_append(pre, mid, S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk(mid, xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))
    : {S.parse.walk(ww, S.parse.start(spec)) == st1 : S.St}}
  e1 = Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish(xx),
    S.parse.walk(List.append(&2, String, ww, more), S.parse.start(spec)),
    S.parse.walk(more, S.parse.walk(ww, S.parse.start(spec))), Laws.walk_append(ww, more, S.parse.start(spec)))
  e2 = Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish(S.parse.walk(more, xx)),
    S.parse.walk(ww, S.parse.start(spec)), st1, e_st)
  hd = Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, S.parse.finish(S.parse.walk(more, st1)),
    Shake.parse(spec, List.append(&2, String, ww, more)), Done{found},
    Equal.sym(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, List.append(&2, String, ww, more)),
      S.parse.finish(S.parse.walk(more, st1)),
      Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, List.append(&2, String, ww, more)),
        S.parse.finish(S.parse.walk(more, S.parse.walk(ww, S.parse.start(spec)))),
        S.parse.finish(S.parse.walk(more, st1)), e1, e2)),
    h_done)
  kept_all.start(spec, S.parse.walk(ww, S.parse.start(spec)), found, st1, more, args, up, path,
    xs, bs, name, e_st, h_mid, hd, Grow.gw.reach(ww, S.parse.start(spec)), Grow.gw.reach(more, st1))

# what `kept` claims
def kept.ty(+found: Shake.Matched, +path: List<&2, String>, +name: String, +vv: String, +bs: List<&2, S.Bind>) -> Type:
  &after: List<&2, String> -> {Laws.all_at(found, path, name)
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
  (after, Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, name),
    Some{List.append(&2, String, gb, List.append(&2, String, S.get_all.bind.hit(String.eq(name, name), vv, []),
      after))},
    Some{List.append(&2, String, gb, vv <> after)}, ee,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>,
      ys => Some{List.append(&2, String, gb, List.append(&2, String, ys, after))},
      S.get_all.bind.hit(String.eq(name, name), vv, []), [vv], kept.hit(name, vv, []))))

def Laws.kept(spec, pre, more, tok, st, args, up, path, name, vv, bs, found, h_at, h_step, h_done):
  kept.one(found, path, name, vv, bs,
    Laws.kept_all(spec, pre, [tok], more, st, args, up, path, [S.Bind{name, vv}], bs, name, found, h_at, h_step,
      h_done))

# an option's value that is not flag-shaped and is allowed binds
def value.step(
  +tok: String,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_flag: {S.looks_flag(tok) == False{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == True{} : Bool}
) -> {S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}:
  e1 = Equal.sym(Bool, S.looks_flag(tok), False{}, h_flag)
  %e1 : {S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}
  e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, name)), tok), True{}, h_ok)
  %e2 : {S.parse.take_choice(_, name, tok, args, up, subs, path, bs, pos, raw, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}
  {==}

def Laws.value_binds(
  spec,
  pre,
  more,
  tok,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  found,
  h_at,
  h_flag,
  h_ok,
  h_done
):
  Laws.kept(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}, args, up, path,
      name, tok, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx),
      S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen},
      value.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag, h_ok)),
    h_done)

# an allowed value taken by the next positional, through `take_choice`
def pos.take(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +raw: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_ok: {S.allowed(cs, tok) == True{} : Bool}
) -> {S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, raw)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{}} : S.St}:
  e2 = Equal.sym(Bool, S.allowed(cs, tok), True{}, h_ok)
  %e2 : {S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{}} : S.St}
  {==}

# a plain word taken by the next positional
def pos.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>},
  h_ok: {S.allowed(cs, tok) == True{} : Bool}
) -> {S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs,
      S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}:
  Equal.trans(S.St,
    S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    Walk.wk.word_step(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, seen,
      h_dd, h_help, h_dash, h_sub),
    pos.take(tok, args, up, subs, path, bs, False{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))

def Laws.pos_next(
  spec,
  pre,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{},
    seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)), S.parse.step(tok, st),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    kept.stepped(spec, pre, tok, st, h_at),
    pos.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs, rest, h_dd, h_help, h_dash,
      h_sub, h_ok))

def Laws.pos_binds(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  found,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{},
    seen} : S.St}
  Laws.kept(spec, pre, more, tok, st, args, up, path, name, tok, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step(tok, st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
        S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
          S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
      pos.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs, rest, h_dd, h_help,
        h_dash, h_sub, h_ok)),
    h_done)

def Laws.dd_step(spec, pre, args, up, subs, path, bs, pos, seen, h_at):
  kept.stepped(spec, pre, "--", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}, h_at)

def Laws.raw_next(
  spec,
  pre,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  h_at,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, True{},
    seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)), S.parse.step(tok, st),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}},
    kept.stepped(spec, pre, tok, st, h_at),
    pos.take(tok, args, up, subs, path, bs, True{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))

def Laws.raw_binds(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  found,
  h_at,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, True{},
    seen} : S.St}
  Laws.kept(spec, pre, more, tok, st, args, up, path, name, tok, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step(tok, st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
        S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
          S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}},
      pos.take(tok, args, up, subs, path, bs, True{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok)),
    h_done)

def Laws.raw_no_pos(spec, pre, more, tok, args, up, subs, path, bs, seen, h_at):
  Laws.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, [], True{}, seen},
    S.Unexpected{path, tok}, h_at, {==})

# after `--`, a word the next positional's choices refuse fails the step
def raw_refused.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_bad: {S.allowed(cs, tok) == False{} : Bool}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
    req, dflt, cs} <> rest, True{}, seen})) == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}:
  e2 = Equal.sym(Bool, S.allowed(cs, tok), False{}, h_bad)
  %e2 : {Laws.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.raw_refused(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  h_at,
  h_bad
):
  Laws.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req,
      dflt, cs} <> rest, True{}, seen}, S.BadValue{path, name, tok}, h_at,
    raw_refused.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs, rest, h_bad))

# what `long.kind` claims of an argument kind
def long.kind.ty(
  kk: S.ArgKind,
  +nn: String,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> Type:
  {S.parse.take_arg.kind(kk, nn, Some{vv}, orig, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}

# an option that takes a value now binds an allowed one
def long.kind(
  kk: S.ArgKind,
  +nn: String,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
) -> long.kind.ty(kk, nn, vv, orig, args, up, subs, path, bs, pos, seen):
  match kk:
    case S.Opt{}:
      e1 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e1 : {S.parse.once(_, S.parse.take_opt(Some{vv}, nn, args, up, subs, path, bs, pos, False{}, seen), nn, path)
        == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), True{}, h_ok)
      %e2 : {S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen)
        == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
      {==}
    case S.Many{}:
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), True{}, h_ok)
      %e2 : {S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen)
        == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
      {==}
    case S.Flag{}:
      Empty.absurd(long.kind.ty(S.Flag{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(long.kind.ty(S.Pos{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(long.kind.ty(S.Rest{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))

# a long option `--name=vv` that takes a value binds an allowed one
def long.step(
  +body: String,
  +name: String,
  +vv: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_kind: {Laws.takes(kind, S.bound(bs, nn)) == True{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
) -> {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_arg(S.by_long(args, name), Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen),
    Laws.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {_ == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}, h_found)
  %e2 : {S.parse.take_arg(_, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
  long.kind(kind, nn, vv, "--" ++ body, args, up, subs, path, bs, pos, seen, h_kind, h_ok)

def Laws.long_binds(
  spec,
  pre,
  more,
  body,
  name,
  vv,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  found,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_kind,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  Laws.kept(spec, pre, more, "--" ++ body, st, args, up, path, nn, vv, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step("--" ++ body, st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen},
      long.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, kind, hp, req, dflt, cs, h_dd,
        h_cut, h_name, h_found, h_kind, h_ok)),
    h_done)

# an option's value that is not flag-shaped and is not allowed fails the step
def value_refused.step(
  +tok: String,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_flag: {S.looks_flag(tok) == False{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == False{} : Bool}
) -> {Laws.dead_of(S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(Bool, S.looks_flag(tok), False{}, h_flag)
  %e1 : {Laws.dead_of(S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, name)), tok), False{}, h_bad)
  %e2 : {Laws.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.value_refused(spec, pre, more, tok, name, args, up, subs, path, bs, pos, raw, seen, h_at, h_flag, h_bad):
  Laws.refused(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen},
    S.BadValue{path, name, tok}, h_at,
    value_refused.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag, h_bad))

# what `long_refused.kind` claims of an argument kind
def long_refused.kind.ty(
  kk: S.ArgKind,
  +nn: String,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> Type:
  {Laws.dead_of(S.parse.take_arg.kind(kk, nn, Some{vv}, orig, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}

# an option that takes a value now refuses one outside its choices
def long_refused.kind(
  kk: S.ArgKind,
  +nn: String,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == False{} : Bool}
) -> long_refused.kind.ty(kk, nn, vv, orig, args, up, subs, path, bs, pos, seen):
  match kk:
    case S.Opt{}:
      e1 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e1 : {Laws.dead_of(S.parse.once(_, S.parse.take_opt(Some{vv}, nn, args, up, subs, path, bs, pos, False{},
          seen), nn, path)) == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), False{}, h_bad)
      %e2 : {Laws.dead_of(S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen))
        == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
      {==}
    case S.Many{}:
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), False{}, h_bad)
      %e2 : {Laws.dead_of(S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen))
        == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
      {==}
    case S.Flag{}:
      Empty.absurd(long_refused.kind.ty(S.Flag{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(long_refused.kind.ty(S.Pos{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(long_refused.kind.ty(S.Rest{}, nn, vv, orig, args, up, subs, path, bs, pos, seen),
        Walk.wk.false_true(h_kind))

# a long option `--name=vv` that takes a value refuses one outside its choices
def long_refused.step(
  +body: String,
  +name: String,
  +vv: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_kind: {Laws.takes(kind, S.bound(bs, nn)) == True{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == False{} : Bool}
) -> {Laws.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_arg(S.by_long(args, name), Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen),
    Laws.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {Laws.dead_of(_) == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}, h_found)
  %e2 : {Laws.dead_of(S.parse.take_arg(_, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
  long_refused.kind(kind, nn, vv, "--" ++ body, args, up, subs, path, bs, pos, seen, h_kind, h_bad)

def Laws.long_refused(
  spec,
  pre,
  more,
  body,
  name,
  vv,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_kind,
  h_bad
):
  Laws.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
    S.BadValue{path, nn, vv}, h_at,
    long_refused.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, kind, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_kind, h_bad))

# a string read back from its chars is itself
def cut.from_to(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, xx => SCon{hh, xx}, String.from_list(String.to_list(tt)), tt, cut.from_to(tt))

# reversing chars onto a list, then reversing that, puts the list back in
# front of the chars
def cut.rev_rev(
  xs: List<&2, Char>,
  +acc: List<&2, Char>
) -> {List.reverse.go(&2, Char, List.reverse.go(&2, Char, xs, acc), []) == List.reverse.go(&2, Char, acc, xs)
    : List<&2, Char>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      cut.rev_rev(tt, hh <> acc)

# a char a string with no `=` starts with is not `=`
def cut.head(
  +cc: Char,
  +tt: String,
  h_name: {Laws.no_eq(SCon{cc, tt}) == True{} : Bool}
) -> {Char.is_eq(cc, '=') == False{} : Bool}:
  Walk.wk.not_true(Char.is_eq(cc, '='), Walk.wk.and_l(Bool.not(Char.is_eq(cc, '=')), Laws.no_eq(tt), h_name))

# the rest of a string with no `=` has none either
def cut.tail(
  +cc: Char,
  +tt: String,
  h_name: {Laws.no_eq(SCon{cc, tt}) == True{} : Bool}
) -> {Laws.no_eq(tt) == True{} : Bool}:
  Walk.wk.and_r(Bool.not(Char.is_eq(cc, '=')), Laws.no_eq(tt), h_name)

# the cut, char by char: every char before the first `=` goes onto the
# accumulator, and the `=` ends the name
def cut.go_eq(
  name: String,
  +vv: String,
  +acc: List<&2, Char>,
  +h_name: {Laws.no_eq(name) == True{} : Bool}
) -> {S.cut_eq.go(String.to_list(name ++ ("=" ++ vv)), acc)
    == (S.from.rev(List.reverse.go(&2, Char, String.to_list(name), acc)), Some{String.from_list(String.to_list(vv))})
    : String & Maybe<&2, String>}:
  match name:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      +rest = String.to_list(tt ++ ("=" ++ vv))
      ee = Equal.sym(Bool, Char.is_eq(cc, '='), False{}, cut.head(cc, tt, h_name))
      %ee : {S.cut_eq.pick(_, acc, rest, S.cut_eq.go(rest, cc <> acc))
        == (S.from.rev(List.reverse.go(&2, Char, String.to_list(tt), cc <> acc)),
          Some{String.from_list(String.to_list(vv))}) : String & Maybe<&2, String>}
      cut.go_eq(tt, vv, cc <> acc, cut.tail(cc, tt, h_name))

# the cut, char by char, of a string with no `=`
def cut.go_none(
  name: String,
  +acc: List<&2, Char>,
  +h_name: {Laws.no_eq(name) == True{} : Bool}
) -> {S.cut_eq.go(String.to_list(name), acc)
    == (S.from.rev(List.reverse.go(&2, Char, String.to_list(name), acc)), None{}) : String & Maybe<&2, String>}:
  match name:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      +rest = String.to_list(tt)
      ee = Equal.sym(Bool, Char.is_eq(cc, '='), False{}, cut.head(cc, tt, h_name))
      %ee : {S.cut_eq.pick(_, acc, rest, S.cut_eq.go(rest, cc <> acc))
        == (S.from.rev(List.reverse.go(&2, Char, String.to_list(tt), cc <> acc)), None{})
        : String & Maybe<&2, String>}
      cut.go_none(tt, cc <> acc, cut.tail(cc, tt, h_name))

# the name the cut reads back, reversed twice, is the name
def cut.name(+name: String) -> {S.from.rev(List.reverse.go(&2, Char, String.to_list(name), [])) == name : String}:
  Equal.trans(String, S.from.rev(List.reverse.go(&2, Char, String.to_list(name), [])),
    String.from_list(String.to_list(name)), name,
    Equal.cong(List<&2, Char>, String, cs => String.from_list(cs),
      List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(name), []), []), String.to_list(name),
      cut.rev_rev(String.to_list(name), [])),
    cut.from_to(name))

def Laws.cut_first_eq(name, vv, h_name):
  +nm = S.from.rev(List.reverse.go(&2, Char, String.to_list(name), []))
  +vl = String.from_list(String.to_list(vv))
  Equal.trans(String & Maybe<&2, String>, S.cut_eq(name ++ ("=" ++ vv)), (nm, Some{vl}), (name, Some{vv}),
    cut.go_eq(name, vv, [], h_name),
    Equal.trans(String & Maybe<&2, String>, (nm, Some{vl}), (name, Some{vl}), (name, Some{vv}),
      Equal.cong(String, String & Maybe<&2, String>, xx => (xx, Some{vl}), nm, name, cut.name(name)),
      Equal.cong(String, String & Maybe<&2, String>, xx => (name, Some{xx}), vl, vv, cut.from_to(vv))))

def Laws.cut_no_eq(name, h_name):
  +nm = S.from.rev(List.reverse.go(&2, Char, String.to_list(name), []))
  Equal.trans(String & Maybe<&2, String>, S.cut_eq(name), (nm, None{}), (name, None{}),
    cut.go_none(name, [], h_name),
    Equal.cong(String, String & Maybe<&2, String>, xx => (xx, None{}), nm, name, cut.name(name)))

# a rest positional, as the walker holds it
def rest.arg(
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>
) -> S.Arg:
  S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}

# before `--`, plain words bind the rest one by one
def rest.walk(
  fs: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +h_plain: {Walk.all_plain(fs) == True{} : Bool},
  +h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool},
  +h_ok: {Laws.all_allowed(cs, fs) == True{} : Bool}
) -> {S.parse.walk(fs, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
      seen})
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)],
      False{}, Walk.wk.seen(fs, seen)} : S.St}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = Walk.wk.and_l(Walk.plain_word(ww), Walk.all_plain(tl), h_plain)
      su = Walk.wk.and_l(Maybe.is_none(&2, S.Sub, S.find_sub(subs, ww)), Walk.wk.unfound(subs, tl), h_sub)
      ok = Walk.wk.and_l(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok)
      ee = Equal.sym(S.St,
        S.parse.step(ww, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
          seen}),
        S.St{S.Free{}, args, up, subs, path, S.Bind{nm, ww} <> bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
          True{}},
        pos.step(ww, args, up, subs, path, bs, seen, nm, sh, lo, S.Rest{}, hp, req, dflt, cs, [],
          Walk.wk.plain_dd(ww, pl), Walk.wk.plain_help(ww, pl), Walk.wk.plain_dash(ww, pl),
          Walk.wk.none_of(S.find_sub(subs, ww), su), ok))
      %ee : {S.parse.walk(tl, _)
        == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(tl, nm, S.Bind{nm, ww} <> bs),
          [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, Walk.wk.seen(tl, True{})} : S.St}
      rest.walk(tl, args, up, subs, path, S.Bind{nm, ww} <> bs, True{}, nm, sh, lo, hp, req, dflt, cs,
        Walk.wk.and_r(Walk.plain_word(ww), Walk.all_plain(tl), h_plain),
        Walk.wk.and_r(Maybe.is_none(&2, S.Sub, S.find_sub(subs, ww)), Walk.wk.unfound(subs, tl), h_sub),
        Walk.wk.and_r(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok))

# after `--`, every word binds the rest one by one
def rest.raw(
  fs: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +h_ok: {Laws.all_allowed(cs, fs) == True{} : Bool}
) -> {S.parse.walk(fs, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
      seen})
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)],
      True{}, Walk.wk.seen(fs, seen)} : S.St}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      ee = Equal.sym(S.St,
        S.parse.take_pos(ww, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}),
        S.St{S.Free{}, args, up, subs, path, S.Bind{nm, ww} <> bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
          True{}},
        pos.take(ww, args, up, subs, path, bs, True{}, nm, sh, lo, S.Rest{}, hp, req, dflt, cs, [],
          Walk.wk.and_l(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok)))
      %ee : {S.parse.walk(tl, _)
        == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(tl, nm, S.Bind{nm, ww} <> bs),
          [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, Walk.wk.seen(tl, True{})} : S.St}
      rest.raw(tl, args, up, subs, path, S.Bind{nm, ww} <> bs, True{}, nm, sh, lo, hp, req, dflt, cs,
        Walk.wk.and_r(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok))

# the words before `fs`, then `fs`, from where the words before left the walker
def rest.after(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +fs: List<&2, String>,
  +st: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)) == S.parse.walk(fs, st) : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)),
    S.parse.walk(fs, S.parse.walk(pre, S.parse.start(spec))), S.parse.walk(fs, st),
    Laws.walk_append(pre, fs, S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk(fs, xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))

def Laws.rest_next(
  spec,
  pre,
  fs,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_plain,
  h_sub,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)), S.parse.walk(fs, st),
    S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
      Walk.wk.seen(fs, seen)},
    rest.after(spec, pre, fs, st, h_at),
    rest.walk(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_plain, h_sub, h_ok))

def Laws.rest_raw_next(spec, pre, fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_at, h_ok):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)), S.parse.walk(fs, st),
    S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
      Walk.wk.seen(fs, seen)},
    rest.after(spec, pre, fs, st, h_at),
    rest.raw(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_ok))

# the bindings a walk pushes onto some it had are those it pushes onto none,
# then those
def rest.pushed(
  fs: List<&2, String>,
  +nm: String,
  +acc: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>
) -> {Walk.wk.pushed(fs, nm, List.append(&2, S.Bind, acc, bs))
    == List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, acc), bs) : List<&2, S.Bind>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, tl}:
      rest.pushed(tl, nm, S.Bind{nm, ww} <> acc, bs)

# one binding of `nm` per word, in order
def rest.bs(fs: List<&2, String>, +nm: String) -> List<&2, S.Bind>:
  match fs:
    case Nil{}:
      []
    case Con{+ww, tl}:
      S.Bind{nm, ww} <> rest.bs(tl, nm)

# the pushed bindings, reversed onto a list, are one per word in order
def rest.rev(
  fs: List<&2, String>,
  +nm: String,
  +acc: List<&2, S.Bind>,
  +out: List<&2, S.Bind>
) -> {List.reverse.go(&2, S.Bind, Walk.wk.pushed(fs, nm, acc), out)
    == List.reverse.go(&2, S.Bind, acc, List.append(&2, S.Bind, rest.bs(fs, nm), out)) : List<&2, S.Bind>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, tl}:
      rest.rev(tl, nm, S.Bind{nm, ww} <> acc, out)

# bindings with nothing after them
def rest.nil_b(bs: List<&2, S.Bind>) -> {List.append(&2, S.Bind, bs, []) == bs : List<&2, S.Bind>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      Equal.cong(List<&2, S.Bind>, List<&2, S.Bind>, xs => hh <> xs, List.append(&2, S.Bind, tt,
          []), tt, rest.nil_b(tt))

# one binding of `nm` per word reads back the words
def rest.vals(fs: List<&2, String>, +nm: String) -> {S.get_all.bind(rest.bs(fs, nm), nm) == fs : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      ee = Equal.sym(Bool, String.eq(nm, nm), True{}, Eq.string_eq_self(nm))
      %ee : {S.get_all.bind.hit(_, ww, S.get_all.bind(rest.bs(tl, nm), nm)) == ww <> tl : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, xs => ww <> xs, S.get_all.bind(rest.bs(tl, nm), nm), tl,
        rest.vals(tl, nm))

# the rest's values the words pushed, read back in order, are the words
def rest.read(
  +fs: List<&2, String>,
  +nm: String
) -> {S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm) == fs : List<&2, String>}:
  Equal.trans(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm),
    S.get_all.bind(rest.bs(fs, nm), nm), fs,
    Equal.cong(List<&2, S.Bind>, List<&2, String>, xs => S.get_all.bind(xs, nm),
      List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), rest.bs(fs, nm),
      Equal.trans(List<&2, S.Bind>, List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])),
        List.append(&2, S.Bind, rest.bs(fs, nm), []), rest.bs(fs, nm), rest.rev(fs, nm, [], []),
        rest.nil_b(rest.bs(fs, nm)))),
    rest.vals(fs, nm))

# what `rest_binds` claims
def rest.ty(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nm: String,
  +fs: List<&2, String>,
  +bs: List<&2, S.Bind>
) -> Type:
  &after: List<&2, String> -> {Laws.all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}

# the pushed bindings read back as the words
def rest.back(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nm: String,
  +fs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  ww: kept_all.ty(found, path, nm, Walk.wk.pushed(fs, nm, []), bs)
) -> rest.ty(found, path, nm, fs, bs):
  (ax, ee) = ww
  +after = {ax : List<&2, String>}
  +gb = S.get_all.bind(List.reverse(&2, S.Bind, bs), nm)
  (after, Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, nm),
    Some{List.append(&2, String, gb,
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm), after))},
    Some{List.append(&2, String, gb, List.append(&2, String, fs, after))}, ee,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>,
      xs => Some{List.append(&2, String, gb, List.append(&2, String, xs, after))},
      S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm), fs, rest.read(fs, nm))))

# the view after the words, from the walker's state after them
def rest.view(
  +fs: List<&2, String>,
  +st: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +nm: String,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  ew: {S.parse.walk(fs, st) == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), pos, raw, seen} : S.St}
) -> {Grow.view(S.parse.walk(fs, st))
    == Grow.View{args, up, path, List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs)} : Grow.View}:
  Equal.trans(Grow.View, Grow.view(S.parse.walk(fs, st)), Grow.View{args, up, path, Walk.wk.pushed(fs, nm, bs)},
    Grow.View{args, up, path, List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs)},
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.walk(fs, st),
      S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), pos, raw, seen}, ew),
    Equal.cong(List<&2, S.Bind>, Grow.View, xs => Grow.View{args, up, path, xs}, Walk.wk.pushed(fs, nm, bs),
      List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs), rest.pushed(fs, nm, [], bs)))

def Laws.rest_binds(
  spec,
  pre,
  fs,
  more,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  found,
  h_at,
  h_plain,
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, seen} : S.St}
  rest.back(found, path, nm, fs, bs,
    Laws.kept_all(spec, pre, fs, more, st, args, up, path, Walk.wk.pushed(fs, nm, []), bs, nm, found, h_at,
      rest.view(fs, st, args, up, subs, path, bs, nm, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
        Walk.wk.seen(fs, seen),
        rest.walk(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_plain, h_sub, h_ok)),
      h_done))

def Laws.rest_raw_binds(
  spec,
  pre,
  fs,
  more,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  found,
  h_at,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, seen} : S.St}
  rest.back(found, path, nm, fs, bs,
    Laws.kept_all(spec, pre, fs, more, st, args, up, path, Walk.wk.pushed(fs, nm, []), bs, nm, found, h_at,
      rest.view(fs, st, args, up, subs, path, bs, nm, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
        Walk.wk.seen(fs, seen), rest.raw(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_ok)),
      h_done))
