# shake: the proofs. `bend src/PROOF.bend` is the gate.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/check.bend as K
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
        fin.bound_g(xs, nn)), hh))

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
        case S.Arg{+mm, _s, _l, _k, _h, _r, dd, _c}:
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
        case S.Arg{+mm, _s, _l, _k, _h, _r, dd, _c}:
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
        case S.Arg{+mm, _s, _l, _k, _h, _r, dd, _c}:
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
  +dd: String,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  +h_qa: {Laws.none_named(qa, nn) == True{} : Bool},
  +h_free: {S.bound(bs, nn) == False{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, Some{dd}, cs} <> qa), bs),
    nn) == [dd] : List<&2, String>}:
  +ff = S.fill.args(qa, bs)
  e1 = Equal.sym(Bool, S.bound(ff, nn), False{},
    Equal.trans(Bool, S.bound(ff, nn), S.bound(bs, nn), False{}, fin.fill_other_b(qa, bs, nn, h_qa), h_free))
  e2 = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(ff, nn), [],
    Equal.trans(List<&2, String>, S.get_all.bind(ff, nn), S.get_all.bind(bs, nn), [], fin.fill_other(qa, bs, nn, h_qa),
      fin.g_unbound(bs, nn, h_free)))
  Equal.trans(List<&2, String>,
    S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, Some{dd}, cs} <> qa),
        bs), nn),
    S.get_all.bind(S.fill.one(S.bound(ff, nn), nn, dd, ff), nn), [dd],
    fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, Some{dd}, cs} <> qa, bs, nn, h_pa),
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
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  +h_qa: {Laws.none_named(qa, nn) == True{} : Bool},
  h_bound: {S.bound(bs, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa), bs),
    nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  +ff = S.fill.args(qa, bs)
  Equal.trans(List<&2, String>,
    S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa), bs), nn),
    S.get_all.bind(S.fill.arg.go(dflt, nn, ff), nn), S.get_all.bind(bs, nn),
    fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa, bs, nn, h_pa),
    fin.kept_go(dflt, nn, ff, bs, fin.fill_other(qa, bs, nn, h_qa),
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
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  h_pa: {Laws.none_named(pa, nn) == True{} : Bool},
  h_qa: {Laws.none_named(qa, nn) == True{} : Bool}
) -> {S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, None{}, cs} <> qa), bs),
    nn) == S.get_all.bind(bs, nn) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    S.get_all.bind(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, None{}, cs} <> qa), bs), nn),
    S.get_all.bind(S.fill.args(qa, bs), nn), S.get_all.bind(bs, nn),
    fin.fill_pre(pa, S.Arg{nn, sh, lo, kind, hp, req, None{}, cs} <> qa, bs, nn, h_pa), fin.fill_other(qa, bs,
        nn, h_qa))

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
    Grow.gw.finished(fs, found, h_done),
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
  h_fr: fin.Framed(spec, ws, qs, args, bs, up, path, ms),
  h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
) -> {Laws.all_at(found, path, nn)
    == Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))} : Maybe<&2, List<&2, String>>}:
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, nn),
    Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), nn)},
    Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, List<&2, String>>, mm => Laws.all_at.go(mm, nn), S.at(found, path),
      Some{S.matched.build(f0 <> rq, ms)}, fin.at(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len)),
    Equal.trans(Maybe<&2, List<&2, String>>, Some{S.get_all.bind(S.own(S.matched.build(f0 <> rq, ms)), nn)},
      Some{S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, bs)), nn)},
      Some{List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn))},
      Equal.cong(List<&2, S.Bind>, Maybe<&2, List<&2, String>>, xs => Some{S.get_all.bind(xs, nn)},
        S.own(S.matched.build(f0 <> rq, ms)), List.reverse(&2, S.Bind, S.fill.args(args, bs)),
        Grow.gw.own_build(f0, rq, ms)),
      Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, xs => Some{xs},
        S.get_all.bind(List.reverse(&2, S.Bind, S.fill.args(args, bs)), nn),
        List.reverse(&2, String, S.get_all.bind(S.fill.args(args, bs), nn)), fin.g_rev(S.fill.args(args, bs), nn))))

# `get_all` of the command at `path` reads `xs`
def fin.All(+found: Shake.Matched, +path: List<&2, String>, +nn: String, +xs: List<&2, String>) -> Type:
  {Laws.all_at(found, path, nn) == Some{xs} : Maybe<&2, List<&2, String>>}

# a level's values read back, from what filling it gives the name
def fin.back(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nn: String,
  +xs: List<&2, String>,
  +ys: List<&2, String>,
  ea: {Laws.all_at(found, path, nn) == Some{List.reverse(&2, String, xs)} : Maybe<&2, List<&2, String>>},
  ex: {xs == ys : List<&2, String>}
) -> {Laws.all_at(found, path, nn) == Some{List.reverse(&2, String, ys)} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, nn), Some{List.reverse(&2, String, xs)},
    Some{List.reverse(&2, String, ys)}, ea,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, zs => Some{List.reverse(&2, String, zs)}, xs, ys, ex))

# the values the words bound, read back in binding order
def fin.back_bs(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nn: String,
  +bs: List<&2, S.Bind>,
  ea: fin.All(found, path, nn, List.reverse(&2, String, S.get_all.bind(bs, nn)))
) -> {Laws.all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)}
    : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Laws.all_at(found, path, nn),
    Some{List.reverse(&2, String, S.get_all.bind(bs, nn))}, Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)}, ea,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>, zs => Some{zs},
      List.reverse(&2, String, S.get_all.bind(bs, nn)), S.get_all.bind(List.reverse(&2, S.Bind, bs), nn),
      Equal.sym(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, bs), nn),
        List.reverse(&2, String, S.get_all.bind(bs, nn)), fin.g_rev(bs, nn))))

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
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, Some{dd}, cs} <> qa)
  fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), [dd],
    fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
    fin.fill_default(pa, qa, nn, sh, lo, kind, hp, req, dd, cs, bs, h_pa, h_qa, h_free))

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
  +args = List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, None{}, cs} <> qa)
  fin.back_bs(found, path, nn, bs,
    fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), S.get_all.bind(bs, nn),
      fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
      fin.fill_nodef(pa, qa, nn, sh, lo, kind, hp, req, cs, bs, h_pa, h_qa)))

def Laws.no_argument(spec, ws, found, qs, args, nn, bs, up, path, ms, h_done, h_fr, h_len, h_none):
  fin.back_bs(found, path, nn, bs,
    fin.back(found, path, nn, S.get_all.bind(S.fill.args(args, bs), nn), S.get_all.bind(bs, nn),
      fin.all(spec, ws, found, qs, args, bs, up, path, ms, nn, h_done, h_fr, h_len),
      fin.fill_other(args, bs, nn, h_none)))

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
  +dflt: Maybe<&2, String>,
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
  +dflt: Maybe<&2, String>,
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

# the filled levels of a finished walker whose frame is known, root first
def fin.levels(
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>
) -> {List.reverse(&2, S.Level, S.fill.levels(List.append(&2, S.Level, qs, S.Level{args, bs} <> up)))
    == List.append(&2, S.Level, List.reverse(&2, S.Level, S.fill.levels(up)),
      S.Level{args, S.fill.args(args, bs)} <> List.reverse(&2, S.Level, S.fill.levels(qs))) : List<&2, S.Level>}:
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  Equal.trans(List<&2, S.Level>,
    List.reverse(&2, S.Level, S.fill.levels(List.append(&2, S.Level, qs, S.Level{args, bs} <> up))),
    List.reverse(&2, S.Level, List.append(&2, S.Level, S.fill.levels(qs), f0 <> S.fill.levels(up))),
    List.append(&2, S.Level, List.reverse(&2, S.Level, S.fill.levels(up)),
      f0 <> List.reverse(&2, S.Level, S.fill.levels(qs))),
    Equal.cong(List<&2, S.Level>, List<&2, S.Level>, ls => List.reverse(&2, S.Level, ls),
      S.fill.levels(List.append(&2, S.Level, qs, S.Level{args, bs} <> up)),
      List.append(&2, S.Level, S.fill.levels(qs), f0 <> S.fill.levels(up)), Grow.gw.fill_mid(qs, args, bs, up)),
    Grow.gw.lrev_mid(S.fill.levels(qs), f0, S.fill.levels(up)))

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
          fin.levels(qs, args, bs, up)))),
    fin.finished_miss(fs, found, hd))
  hb = fin.miss_req(pa, qa, nn, sh, lo, kind, hp, dflt, cs, fb, fin.miss_mid(r0, args, fb, rq, mn))
  eb = Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(S.own(bm), nn))),
    Bool.not(List.is_empty(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, fb), nn))), True{},
    Equal.cong(List<&2, S.Bind>, Bool, xs => Bool.not(List.is_empty(&2, String, S.get_all.bind(xs, nn))), S.own(bm),
      List.reverse(&2, S.Bind, fb), Grow.gw.own_build(f0, rq, ms)),
    Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, fb), nn))),
      Bool.not(List.is_empty(&2, String, List.reverse(&2, String, S.get_all.bind(fb, nn)))), True{},
      Equal.cong(List<&2, String>, Bool, xs => Bool.not(List.is_empty(&2, String, xs)),
        S.get_all.bind(List.reverse(&2, S.Bind, fb), nn), List.reverse(&2, String, S.get_all.bind(fb, nn)),
        fin.g_rev(fb, nn)),
      Equal.trans(Bool, Bool.not(List.is_empty(&2, String, List.reverse(&2, String, S.get_all.bind(fb, nn)))),
        Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))), True{},
        Equal.cong(Bool, Bool, xx => Bool.not(xx), List.is_empty(&2, String, List.reverse(&2, String,
            S.get_all.bind(fb, nn))),
          List.is_empty(&2, String, S.get_all.bind(fb, nn)), fin.empty_rev0(S.get_all.bind(fb, nn))),
        Equal.trans(Bool, Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))), S.bound(fb, nn), True{},
          Equal.sym(Bool, S.bound(fb, nn), Bool.not(List.is_empty(&2, String, S.get_all.bind(fb, nn))),
            fin.bound_g(fb, nn)), hb))))
  Equal.trans(Maybe<&2, Bool>, Laws.present_at(found, path, nn), Laws.present_at.go(Some{bm}, nn), Some{True{}},
    Equal.cong(Maybe<&2, S.Matched>, Maybe<&2, Bool>, mm => Laws.present_at.go(mm, nn), S.at(found, path), Some{bm},
      fin.at(spec, ws, found, qs, args, bs, up, path, ms, hd, h_fr2, h_len)),
    Equal.cong(Bool, Maybe<&2, Bool>, xx => Some{xx}, Bool.not(List.is_empty(&2, String,
        S.get_all.bind(S.own(bm), nn))),
      True{}, eb))

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
  +dflt: Maybe<&2, String>,
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
  h_free: {Laws.free(fs) == True{} : Bool},
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
  fin.missing(S.parse.walk(ws, S.parse.start(spec)), List.append(&2, S.Level, qs, S.Level{args, bs} <> up), path,
    List.append(&2, S.Level, r0, S.Level{args, fb} <> rq), h_free, h_fr, fin.levels(qs, args, bs, up),
    fin.miss_levels_some(r0, args, fb, rq, fin.miss_args_some(pa, qa, nn, sh, lo, kind, hp, dflt, cs, fb, h_unbound)))

# a plain word before `--` is read as a word: a subcommand or a positional
def enter.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
) -> {S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen) : S.St}:
  +rhs = S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e2 = Equal.sym(Bool, String.eq(tok, "help"), False{}, h_help)
  %e2 : {S.parse.step.help(Bool.and(_, Bool.not(seen)), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, Walk.wk.dash(tok, h_dash))
  %e3 : {S.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {S.parse.step.kind.go(False{}, _, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  {==}

# a found subcommand, entered or refused, as the first blocking positional says
def enter.go(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +sub: S.Sub,
  h_sub: {S.find_sub(subs, tok) == Some{sub} : Maybe<&2, S.Sub>}
) -> {S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, tok), Some{sub}, h_sub)
  %ee : {S.parse.word.go(_, tok, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen) : S.St}
  {==}

# nothing blocking: the subcommand is entered
def enter.none(
  +pos: List<&2, S.Arg>,
  +name: String,
  +about: String,
  +next: List<&2, S.Arg>,
  +kids: List<&2, S.Sub>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_req: {S.parse.first_req(pos) == None{} : Maybe<&2, String>}
) -> {S.parse.enter_or(S.parse.first_req(pos), S.Sub{name, about, next, kids}, args, up, subs, path, bs, pos, False{},
      seen)
    == S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
      False{}, False{}} : S.St}:
  er = Equal.sym(Maybe<&2, String>, S.parse.first_req(pos), None{}, h_req)
  %er : {S.parse.enter_or(_, S.Sub{name, about, next, kids}, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
      False{}, False{}} : S.St}
  {==}

# a blocking positional: the word fails the step with Missing of it
def enter.miss(
  +pos: List<&2, S.Arg>,
  +sub: S.Sub,
  +nm: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_req: {S.parse.first_req(pos) == Some{nm} : Maybe<&2, String>}
) -> {Laws.dead_of(S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Missing{path, nm}} : Maybe<&2, S.ParseErr>}:
  er = Equal.sym(Maybe<&2, String>, S.parse.first_req(pos), Some{nm}, h_req)
  %er : {Laws.dead_of(S.parse.enter_or(_, sub, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Missing{path, nm}} : Maybe<&2, S.ParseErr>}
  {==}

# a step equal to a failed walker fails the same way
def enter.dead(
  +tok: String,
  +st: S.St,
  +st2: S.St,
  +err: S.ParseErr,
  ee: {st2 == S.parse.step(tok, st) : S.St},
  hd: {Laws.dead_of(st2) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {Laws.dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}:
  %ee : {Laws.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
  hd

def Laws.enter_step(
  spec,
  pre,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  name,
  about,
  next,
  kids,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_req
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  +sub = {S.Sub{name, about, next, kids} : S.Sub}
  +rhs = {S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
    False{}, False{}} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)), S.parse.step(tok, st), rhs,
    kept.stepped(spec, pre, tok, st, h_at),
    Equal.trans(S.St, S.parse.step(tok, st),
      S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen), rhs,
      enter.word(tok, args, up, subs, path, bs, pos, seen, h_dd, h_help, h_dash),
      Equal.trans(S.St, S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen),
        S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen), rhs,
        enter.go(tok, args, up, subs, path, bs, pos, seen, sub, h_sub),
        enter.none(pos, name, about, next, kids, args, up, subs, path, bs, seen, h_req))))

def Laws.enter_missing(
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
  seen,
  sub,
  nm,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_req
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e1 = Equal.sym(S.St, S.parse.step(tok, st),
    S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
    Equal.trans(S.St, S.parse.step(tok, st),
      S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen),
      S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
      enter.word(tok, args, up, subs, path, bs, pos, seen, h_dd, h_help, h_dash),
      enter.go(tok, args, up, subs, path, bs, pos, seen, sub, h_sub)))
  Laws.refused(spec, pre, more, tok, st, S.Missing{path, nm}, h_at,
    enter.dead(tok, st, S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
      S.Missing{path, nm}, e1, enter.miss(pos, sub, nm, args, up, subs, path, bs, seen, h_req)))

# a positional that does not block a subcommand is skipped: a rest, one not
# required, or one with a default
def blk.req(
  rk: Bool,
  req: Bool,
  dflt: Maybe<&2, String>,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +cs: List<&2, String>,
  hh: {Bool.not(Bool.and(Bool.not(rk), Bool.and(req, Maybe.is_none(&2, String, dflt)))) == True{} : Bool}
) -> {S.parse.first_req.skip(rk, S.Arg{nm, sh, lo, kind, hp, req, dflt, cs}) == None{} : Maybe<&2, String>}:
  match rk:
    case True{}:
      {==}
    case False{}:
      match req:
        case False{}:
          {==}
        case True{}:
          match dflt:
            case Some{_d}:
              {==}
            case None{}:
              Empty.absurd({S.parse.first_req.skip(False{}, S.Arg{nm, sh, lo, kind, hp, True{}, None{}, cs}) == None{}
                : Maybe<&2, String>}, Walk.wk.false_true(hh))

# the same, from the argument's kind
def blk.skip(
  +kind: S.ArgKind,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +cs: List<&2, String>,
  hh: {Bool.not(Laws.blocks(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs})) == True{} : Bool}
) -> {S.parse.first_req.skip(S.rest.is.kind(kind), S.Arg{nm, sh, lo, kind, hp, req, dflt, cs}) == None{}
    : Maybe<&2, String>}:
  blk.req(S.rest.is.kind(kind), req, dflt, nm, sh, lo, kind, hp, cs, hh)

# past a positional that does not block, the first blocking one is the rest's
def blk.past(
  +kind: S.ArgKind,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +cs: List<&2, String>,
  +tt: List<&2, S.Arg>,
  hh: {Bool.not(Laws.blocks(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs})) == True{} : Bool}
) -> {S.parse.first_req(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs} <> tt) == S.parse.first_req(tt) : Maybe<&2, String>}:
  ee = Equal.sym(Maybe<&2, String>,
    S.parse.first_req.skip(S.rest.is.kind(kind), S.Arg{nm, sh, lo, kind, hp, req, dflt, cs}), None{},
    blk.skip(kind, req, dflt, nm, sh, lo, hp, cs, hh))
  %ee : {S.parse.first_req.at(_, S.parse.first_req(tt)) == S.parse.first_req(tt) : Maybe<&2, String>}
  {==}

def Laws.none_blocking(pos, h_none):
  match pos:
    case Nil{}:
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+nm, +sh, +lo, +kind, +hp, +req, +dflt, +cs}:
          +ab = {S.Arg{nm, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
          Equal.trans(Maybe<&2, String>, S.parse.first_req(ab <> tt), S.parse.first_req(tt), None{},
            blk.past(kind, req, dflt, nm, sh, lo, hp, cs, tt,
              Walk.wk.and_l(Bool.not(Laws.blocks(ab)), Laws.none_block(tt), h_none)),
            Laws.none_blocking(tt, Walk.wk.and_r(Bool.not(Laws.blocks(ab)), Laws.none_block(tt), h_none)))

def Laws.first_blocking(pa, nm, sh, lo, kind, hp, cs, qa, h_pa, h_kind):
  match pa:
    case Nil{}:
      ee = Equal.sym(Bool, S.rest.is.kind(kind), False{}, h_kind)
      %ee : {S.parse.first_req.at(S.parse.first_req.skip(_, S.Arg{nm, sh, lo, kind, hp, True{}, None{}, cs}),
          S.parse.first_req(qa)) == Some{nm} : Maybe<&2, String>}
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+n2, +s2, +l2, +k2, +h2, +r2, +d2, +c2}:
          +ab = {S.Arg{n2, s2, l2, k2, h2, r2, d2, c2} : S.Arg}
          +rest = List.append(&2, S.Arg, tt, S.Arg{nm, sh, lo, kind, hp, True{}, None{}, cs} <> qa)
          Equal.trans(Maybe<&2, String>, S.parse.first_req(ab <> rest), S.parse.first_req(rest), Some{nm},
            blk.past(k2, r2, d2, n2, s2, l2, h2, c2, rest, Walk.wk.and_l(Bool.not(Laws.blocks(ab)),
                Laws.none_block(tt), h_pa)),
            Laws.first_blocking(tt, nm, sh, lo, kind, hp, cs, qa,
              Walk.wk.and_r(Bool.not(Laws.blocks(ab)), Laws.none_block(tt), h_pa), h_kind))


def Laws.help_step(spec, pre, args, up, subs, path, bs, pos, h_at):
  kept.stepped(spec, pre, "help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}, h_at)

# the first word of a list, or none
def hp.head(ns: List<&2, String>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{hh, _t}:
      hh

# what `hp.walk` claims
def hp.ty(
  +ns: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> Type:
  &kids: List<&2, S.Sub> -> {S.parse.walk(ns, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen})
    == S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen} : S.St}

# the names under a found subcommand, carried to its own subcommands
def hp.names_tr(
  +tt: List<&2, String>,
  +aa: List<&2, S.Sub>,
  +bb: List<&2, S.Sub>,
  ee: {aa == bb : List<&2, S.Sub>},
  hh: {Laws.help_names(tt, aa) == True{} : Bool}
) -> {Laws.help_names(tt, bb) == True{} : Bool}:
  Equal.trans(Bool, Laws.help_names(tt, bb), Laws.help_names(tt, aa), True{},
    Equal.cong(List<&2, S.Sub>, Bool, kk => Laws.help_names(tt, kk), bb, aa, Equal.sym(List<&2, S.Sub>, aa, bb,
        ee)), hh)

# one name further down the help path, then the rest
def hp.cons(
  +nn: String,
  +tt: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +sn: String,
  +sa: String,
  +sg: List<&2, S.Arg>,
  +kids: List<&2, S.Sub>,
  e_fm: {S.find_sub(subs, nn) == Some{S.Sub{sn, sa, sg, kids}} : Maybe<&2, S.Sub>},
  ih: hp.ty(tt, args, up, kids, List.append(&2, String, path, [nn]), bs, pos, raw, seen)
) -> hp.ty(nn <> tt, args, up, subs, path, bs, pos, raw, seen):
  (k2, e2) = ih
  +k3 = {k2 : List<&2, S.Sub>}
  +mid = {S.St{S.Help{}, args, up, kids, List.append(&2, String, path, [nn]), bs, pos, raw, seen} : S.St}
  +fin_st = {S.St{S.Help{}, args, up, k3, List.append(&2, String, path, nn <> tt), bs, pos, raw, seen} : S.St}
  es = Equal.cong(Maybe<&2, S.Sub>, S.St, mm => S.parse.walk(tt, S.parse.step.help_path(mm, nn, args, up, subs,
      path, bs,
      pos, raw, seen)), S.find_sub(subs, nn), Some{S.Sub{sn, sa, sg, kids}}, e_fm)
  (k3, Equal.trans(S.St, S.parse.walk(nn <> tt, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen}),
    S.parse.walk(tt, mid), fin_st, es,
    Equal.trans(S.St, S.parse.walk(tt, mid),
      S.St{S.Help{}, args, up, k3, List.append(&2, String, List.append(&2, String, path, [nn]), tt), bs, pos,
          raw, seen},
      fin_st, e2,
      Equal.cong(List<&2, String>, S.St, pp => S.St{S.Help{}, args, up, k3, pp, bs, pos, raw, seen},
        List.append(&2, String, List.append(&2, String, path, [nn]), tt), List.append(&2, String, path, nn <> tt),
        Grow.gw.sapp(path, [nn], tt)))))

# words that each name a subcommand under the one before extend a help path
def hp.walk(
  ns: List<&2, String>,
  +subs: List<&2, S.Sub>,
  fm: Maybe<&2, S.Sub>,
  +e_fm: {S.find_sub(subs, hp.head(ns)) == fm : Maybe<&2, S.Sub>},
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +h_ns: {Laws.help_names(ns, subs) == True{} : Bool}
) -> hp.ty(ns, args, up, subs, path, bs, pos, raw, seen):
  match ns:
    case Nil{}:
      (subs, Equal.cong(List<&2, String>, S.St, pp => S.St{S.Help{}, args, up, subs, pp, bs, pos, raw, seen}, path,
        List.append(&2, String, path, []), Equal.sym(List<&2, String>, List.append(&2, String, path, []), path,
          Grow.gw.nil_s(path))))
    case Con{+nn, +tt}:
      match fm:
        case None{}:
          Empty.absurd(hp.ty(nn <> tt, args, up, subs, path, bs, pos, raw, seen),
            Walk.wk.false_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)), True{},
              Equal.cong(Maybe<&2, S.Sub>, Bool, mm => Maybe.is_some(&2, S.Sub, mm), None{}, S.find_sub(subs, nn),
                Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, nn), None{}, e_fm)),
              Walk.wk.and_l(Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)),
                Laws.help_names(tt, Laws.kids_of(S.find_sub(subs, nn))), h_ns))))
        case Some{ss}:
          match ss:
            case S.Sub{+sn, +sa, +sg, +kids}:
              hp.cons(nn, tt, args, up, subs, path, bs, pos, raw, seen, sn, sa, sg, kids, e_fm,
                hp.walk(tt, kids, S.find_sub(kids, hp.head(tt)), {==}, args, up, List.append(&2, String, path,
                    [nn]), bs,
                  pos, raw, seen,
                  hp.names_tr(tt, Laws.kids_of(S.find_sub(subs, nn)), kids,
                    Equal.cong(Maybe<&2, S.Sub>, List<&2, S.Sub>, mm => Laws.kids_of(mm), S.find_sub(subs, nn),
                      Some{S.Sub{sn, sa, sg, kids}}, e_fm),
                    Walk.wk.and_r(Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)),
                      Laws.help_names(tt, Laws.kids_of(S.find_sub(subs, nn))), h_ns))))

# the walk after the words before, read from where they left the walker
def hp.from(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +ns: List<&2, String>,
  +st: S.St,
  +big: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St},
  ew: {S.parse.walk(ns, st) == big : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec)) == big : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec)), S.parse.walk(ns, st), big,
    rest.after(spec, pre, ns, st, h_at), ew)

# the help walk, read from the start
def hp.at(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +ns: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen} : S.St},
  ww: hp.ty(ns, args, up, subs, path, bs, pos, raw, seen)
) -> &kids: List<&2, S.Sub> -> {S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec))
    == S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen} : S.St}:
  (k1, e1) = ww
  +kids = {k1 : List<&2, S.Sub>}
  (kids, hp.from(spec, pre, ns, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen},
    S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen}, h_at, e1))

def Laws.help_walk(spec, pre, ns, args, up, subs, path, bs, pos, raw, seen, h_at, h_ns):
  hp.at(spec, pre, ns, args, up, subs, path, bs, pos, raw, seen, h_at,
    hp.walk(ns, subs, S.find_sub(subs, hp.head(ns)), {==}, args, up, path, bs, pos, raw, seen, h_ns))

# the words leave the walker reading the help path `path`
def hp.ended(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>
) -> Type:
  &kids: List<&2, S.Sub> -> {S.parse.walk(ws, S.parse.start(spec))
    == S.St{S.Help{}, args, up, kids, path, bs, pos, False{}, False{}} : S.St}

# a help walk that ends reading its path fails with NeedHelp of it
def hp.need(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  ww: hp.ended(spec, ws, args, up, path, bs, pos)
) -> {Shake.parse(spec, ws) == Fail{S.NeedHelp{path}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}:
  (k1, e1) = ww
  Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.parse.finish(xx), S.parse.walk(ws,
      S.parse.start(spec)),
    S.St{S.Help{}, args, up, k1, path, bs, pos, False{}, False{}}, e1)

def Laws.help_path(spec, pre, ns, args, up, subs, path, bs, pos, h_at, h_ns):
  +ph = List.append(&2, String, pre, ["help"])
  hp.need(spec, List.append(&2, String, ph, ns), args, up, List.append(&2, String, path, ns), bs, pos,
    Laws.help_walk(spec, ph, ns, args, up, subs, path, bs, pos, False{}, False{},
      Laws.help_step(spec, pre, args, up, subs, path, bs, pos, h_at), h_ns))

def Laws.start_state(_name, _about, _version, _args, _subs):
  {==}

# keeping an argument in front of two lists is keeping it in front of the first
def pof.put_app(
  keep: Bool,
  +hh: S.Arg,
  +aa: List<&2, S.Arg>,
  +bb: List<&2, S.Arg>
) -> {S.pos_of.put(keep, hh, List.append(&2, S.Arg, aa, bb))
    == List.append(&2, S.Arg, S.pos_of.put(keep, hh, aa), bb) : List<&2, S.Arg>}:
  match keep:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.pos_of_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, S.Arg>, S.pos_of.put(S.pos.is(hh), hh, S.pos_of(List.append(&2, S.Arg, tt, ys))),
        S.pos_of.put(S.pos.is(hh), hh, List.append(&2, S.Arg, S.pos_of(tt), S.pos_of(ys))),
        List.append(&2, S.Arg, S.pos_of.put(S.pos.is(hh), hh, S.pos_of(tt)), S.pos_of(ys)),
        Equal.cong(List<&2, S.Arg>, List<&2, S.Arg>, zs => S.pos_of.put(S.pos.is(hh), hh, zs),
          S.pos_of(List.append(&2, S.Arg, tt, ys)), List.append(&2, S.Arg, S.pos_of(tt), S.pos_of(ys)),
          Laws.pos_of_app(tt, ys)),
        pof.put_app(S.pos.is(hh), hh, S.pos_of(tt), S.pos_of(ys)))

def Laws.pos_of_pos(aa, h_pos):
  ee = Equal.sym(Bool, S.pos.is(aa), True{}, h_pos)
  %ee : {S.pos_of.put(_, aa, []) == [aa] : List<&2, S.Arg>}
  {==}

def Laws.pos_of_opt(aa, h_opt):
  ee = Equal.sym(Bool, S.pos.is(aa), False{}, h_opt)
  %ee : {S.pos_of.put(_, aa, []) == [] : List<&2, S.Arg>}
  {==}

# after a positional is bound, `help` reaches the positional it binds
def hw.step(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>}
) -> {S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, True{}})
    == S.parse.take_pos("help", args, up, subs, path, bs, pos, False{}) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, "help"), None{}, h_sub)
  %ee : {S.parse.word.go(_, "help", args, up, subs, path, bs, pos, False{}, True{})
    == S.parse.take_pos("help", args, up, subs, path, bs, pos, False{}) : S.St}
  {==}

# `help` taken by the next positional
def hw.full(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>},
  h_ok: {S.allowed(cs, "help") == True{} : Bool}
) -> {S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt,
    cs} <> rest,
      False{}, True{}})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}:
  +pp = {S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest : List<&2, S.Arg>}
  Equal.trans(S.St, S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, pp, False{}, True{}}),
    S.parse.take_pos("help", args, up, subs, path, bs, pp, False{}),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    hw.step(args, up, subs, path, bs, pp, h_sub),
    pos.take("help", args, up, subs, path, bs, False{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))

def Laws.help_word_next(
  spec,
  pre,
  args,
  up,
  subs,
  path,
  bs,
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
  h_sub,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, True{}}
    : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ["help"]), S.parse.start(spec)), S.parse.step("help", st),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    kept.stepped(spec, pre, "help", st, h_at),
    hw.full(args, up, subs, path, bs, name, sh, lo, kind, hp, req, dflt, cs, rest, h_sub, h_ok))

def Laws.help_word_binds(
  spec,
  pre,
  more,
  args,
  up,
  subs,
  path,
  bs,
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
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, True{}}
    : S.St}
  Laws.kept(spec, pre, more, "help", st, args, up, path, name, "help", bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step("help", st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
        S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
          S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
      hw.full(args, up, subs, path, bs, name, sh, lo, kind, hp, req, dflt, cs, rest, h_sub, h_ok)),
    h_done)

# one letter against a failed walker keeps it failed, read or skipped
def cd.letter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  +err: S.ParseErr,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> {S.cluster.letter(done, cc, rest, orig, S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen})
    == S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen} : S.St}:
  match done:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.cluster_dead(body, orig, err, args, up, subs, path, bs, pos, raw, seen, done):
  match body:
    case SNil{}:
      {==}
    case SCon{+cc, +rest}:
      +dd = {S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen} : S.St}
      ee = Equal.sym(S.St, S.cluster.letter(done, cc, rest, orig, dd), dd,
        cd.letter(done, cc, rest, orig, err, args, up, subs, path, bs, pos, raw, seen))
      %ee : {S.cluster(rest, orig, _, S.cluster.done(done, cc, rest, dd)) == dd : S.St}
      Laws.cluster_dead(rest, orig, err, args, up, subs, path, bs, pos, raw, seen, S.cluster.done(done, cc, rest, dd))

# one letter of a cluster in a free walker, once the argument it spells is
# known: `take_arg` with the value the letter's kind gives, then the rest,
# ended or not as the kind says
def cl.step(
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +aa: S.Arg,
  h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{aa} : Maybe<&2, S.Arg>}
) -> {S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs,
        path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest)) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), Some{aa}, h_found)
  %ee : {S.cluster(rest, orig, S.parse.take_arg(_, S.cluster.val(_, rest), orig, args, up, subs, path, bs, pos, raw,
      seen), S.cluster.ends(_, rest))
    == S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs, path, bs,
      pos, raw, seen), S.cluster.ends(Some{aa}, rest)) : S.St}
  {==}

# the same, the other way round, for rewriting a goal about the cluster
def cl.back(
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +aa: S.Arg,
  h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{aa} : Maybe<&2, S.Arg>}
) -> {S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs,
    path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest))
    == S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{}) : S.St}:
  Equal.sym(S.St, S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{}),
    S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs, path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest)),
    cl.step(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found))

def Laws.short_step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash):
  +tok = "-" ++ SCon{cc, rest}
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == S.cluster(SCon{cc, rest}, tok, st,
      False{}) : S.St}
  e3 = Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, h_dash)
  %e3 : {S.parse.step.kind.go(String.starts_with.if(rest, "", _), True{}, tok, args, up, subs, path, bs, pos, seen)
    == S.cluster(SCon{cc, rest}, tok, st, False{}) : S.St}
  {==}

# a cluster whose walker has failed stays failed, whatever letters are left
def cl.dead(
  +rest: String,
  +orig: String,
  xx: S.St,
  +done: Bool,
  +err: S.ParseErr,
  hh: {Laws.dead_of(xx) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {Laws.dead_of(S.cluster(rest, orig, xx, done)) == Some{err} : Maybe<&2, S.ParseErr>}:
  match xx:
    case S.St{S.Dead{+ee}, +a, +g, +s, +p, +b, +o, +r, +n}:
      ec = Equal.sym(S.St, S.cluster(rest, orig, S.St{S.Dead{ee}, a, g, s, p, b, o, r, n}, done),
        S.St{S.Dead{ee}, a, g, s, p, b, o, r, n}, Laws.cluster_dead(rest, orig, ee, a, g, s, p, b, o, r, n, done))
      %ec : {Laws.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
      hh
    case S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {Laws.dead_of(S.cluster(rest, orig, S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n},
          done)) == Some{err}
        : Maybe<&2, S.ParseErr>}, err, hh)
    case S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {Laws.dead_of(S.cluster(rest, orig, S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}, done))
        == Some{err} : Maybe<&2, S.ParseErr>}, err, hh)
    case S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {Laws.dead_of(S.cluster(rest, orig, S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n},
          done)) == Some{err}
        : Maybe<&2, S.ParseErr>}, err, hh)

def Laws.letter_flag(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_once,
  h_noeq
):
  +aa = {S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs} : S.Arg}
  +rhs = {S.cluster(rest, orig, S.St{S.Free{}, args, up, subs, path, S.Bind{nn, "true"} <> bs, pos, raw, seen}, False{})
    : S.St}
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == rhs : S.St}
  e1 = Equal.sym(Bool, String.starts_with(rest, "="), False{}, h_noeq)
  %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Flag{}, nn, S.cluster.val.flag(_, rest), orig, args, up,
      subs, path,
      bs, pos, raw, seen), _) == rhs : S.St}
  e2 = Equal.sym(Bool, S.bound(bs, nn), False{}, h_once)
  %e2 : {S.cluster(rest, orig, S.parse.once(_, S.parse.take_flag(None{}, nn, orig, args, up, subs, path, bs,
      pos, raw, seen),
      nn, path), False{}) == rhs : S.St}
  {==}

def Laws.letter_flag_eq(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_once,
  h_eq
):
  +aa = {S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs} : S.Arg}
  +dd = {S.St{S.Dead{S.Unexpected{path, orig}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == dd : S.St}
  e1 = Equal.sym(Bool, String.starts_with(rest, "="), True{}, h_eq)
  %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Flag{}, nn, S.cluster.val.flag(_, rest), orig, args, up,
      subs, path,
      bs, pos, raw, seen), _) == dd : S.St}
  e2 = Equal.sym(Bool, S.bound(bs, nn), False{}, h_once)
  %e2 : {S.cluster(rest, orig, S.parse.once(_, dd, nn, path), True{}) == dd : S.St}
  Laws.cluster_done(rest, orig, dd)

def Laws.letter_unknown(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, h_none):
  +dd = {S.St{S.Dead{S.UnknownFlag{path, orig}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), None{}, h_none)
  %e2 : {S.cluster(rest, orig,
      S.parse.take_arg(_, S.cluster.val(_, rest), orig, args, up, subs, path, bs, pos, raw, seen),
      S.cluster.ends(_, rest)) == dd : S.St}
  Laws.cluster_done(rest, orig, dd)

def Laws.letter_flag_again(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_again
):
  +aa = {S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs} : S.Arg}
  +vv = S.cluster.val.flag(String.starts_with(rest, "="), rest)
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {Laws.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e2 : {Laws.dead_of(S.cluster(rest, orig, S.parse.once(_, S.parse.take_flag(vv, nn, orig, args, up, subs,
      path, bs, pos,
      raw, seen), nn, path), String.starts_with(rest, "="))) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  cl.dead(rest, orig, S.parse.once(True{}, S.parse.take_flag(vv, nn, orig, args, up, subs, path, bs, pos, raw,
      seen), nn,
      path), String.starts_with(rest, "="), S.Repeated{path, nn},
    Laws.once_dead(S.parse.take_flag(vv, nn, orig, args, up, subs, path, bs, pos, raw, seen), nn, path))

def Laws.letter_opt_again(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_again
):
  +aa = {S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs} : S.Arg}
  +vv = S.short_of.val(String.starts_with(rest, "="), rest)
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {Laws.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e2 : {Laws.dead_of(S.cluster(rest, orig, S.parse.once(_, S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw,
      seen), nn, path), True{})) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  cl.dead(rest, orig, S.parse.once(True{}, S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw, seen),
      nn, path),
    True{}, S.Repeated{path, nn}, Laws.once_dead(S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw,
        seen), nn, path))

# what `lv` claims of an argument kind
def lv.ty(
  kk: S.ArgKind,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String
) -> Type:
  {S.cluster(rest, orig, S.parse.take_arg.kind(kk, nn, S.cluster.val.kind(kk, rest), orig, args, up, subs, path,
      bs, pos, raw, seen),
    S.cluster.ends.kind(kk, rest)) == S.St{S.Free{}, args, up, subs, path, S.Bind{nn,
        rest} <> bs, pos, raw, seen} : S.St}

# a letter spelling an option that takes a value now, with a glued value its
# choices allow, by the option's kind
def lv(
  kk: S.ArgKind,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_noeq: {String.starts_with(rest, "=") == False{} : Bool},
  h_some: {String.is_empty(rest) == False{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), rest) == True{} : Bool}
) -> lv.ty(kk, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn):
  match kk:
    case S.Opt{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, rest} <> bs, pos, raw, seen} : S.St}
      e1 = Equal.sym(Bool, String.starts_with(rest, "="), False{}, h_noeq)
      %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Opt{}, nn, S.short_of.val(_, rest), orig, args, up,
          subs, path, bs, pos, raw, seen), True{})
        == T : S.St}
      e2 = Equal.sym(Bool, String.is_empty(rest), False{}, h_some)
      %e2 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Opt{}, nn,
          Bool.pick(Maybe<&2, String>, _, None{},
              Some{rest}), orig, args, up, subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e3 : {S.cluster(rest, orig, S.parse.once(_, S.parse.take_opt(Some{rest}, nn, args, up, subs, path, bs,
          pos, raw, seen), nn, path), True{}) == T
        : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), rest), True{}, h_ok)
      %e4 : {S.cluster(rest, orig, S.parse.take_choice(_, nn, rest, args, up, subs, path, bs, pos, raw, seen),
          True{}) == T : S.St}
      Laws.cluster_done(rest, orig, T)
    case S.Many{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, rest} <> bs, pos, raw, seen} : S.St}
      e1 = Equal.sym(Bool, String.starts_with(rest, "="), False{}, h_noeq)
      %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Many{}, nn, S.short_of.val(_, rest), orig, args, up,
          subs, path, bs, pos, raw, seen), True{})
        == T : S.St}
      e2 = Equal.sym(Bool, String.is_empty(rest), False{}, h_some)
      %e2 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Many{}, nn,
          Bool.pick(Maybe<&2, String>, _, None{},
              Some{rest}), orig, args, up, subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), rest), True{}, h_ok)
      %e4 : {S.cluster(rest, orig, S.parse.take_choice(_, nn, rest, args, up, subs, path, bs, pos, raw, seen),
          True{}) == T : S.St}
      Laws.cluster_done(rest, orig, T)
    case S.Flag{}:
      Empty.absurd(lv.ty(S.Flag{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(lv.ty(S.Pos{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(lv.ty(S.Rest{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))

# what `lb` claims of an argument kind
def lb.ty(
  kk: S.ArgKind,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String
) -> Type:
  {S.cluster(rest, orig, S.parse.take_arg.kind(kk, nn, S.cluster.val.kind(kk, rest), orig, args, up, subs, path,
      bs, pos, raw, seen),
    S.cluster.ends.kind(kk, rest)) == S.St{S.Dead{S.BadValue{path, nn,
        rest}}, args, up, subs, path, bs, pos, raw, seen} : S.St}

# the same, with a glued value its choices refuse
def lb(
  kk: S.ArgKind,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_noeq: {String.starts_with(rest, "=") == False{} : Bool},
  h_some: {String.is_empty(rest) == False{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), rest) == False{} : Bool}
) -> lb.ty(kk, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn):
  match kk:
    case S.Opt{}:
      +T = {S.St{S.Dead{S.BadValue{path, nn, rest}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
      e1 = Equal.sym(Bool, String.starts_with(rest, "="), False{}, h_noeq)
      %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Opt{}, nn, S.short_of.val(_, rest), orig, args, up,
          subs, path, bs, pos, raw, seen), True{})
        == T : S.St}
      e2 = Equal.sym(Bool, String.is_empty(rest), False{}, h_some)
      %e2 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Opt{}, nn,
          Bool.pick(Maybe<&2, String>, _, None{},
              Some{rest}), orig, args, up, subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e3 : {S.cluster(rest, orig, S.parse.once(_, S.parse.take_opt(Some{rest}, nn, args, up, subs, path, bs,
          pos, raw, seen), nn, path), True{}) == T
        : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), rest), False{}, h_ok)
      %e4 : {S.cluster(rest, orig, S.parse.take_choice(_, nn, rest, args, up, subs, path, bs, pos, raw, seen),
          True{}) == T : S.St}
      Laws.cluster_done(rest, orig, T)
    case S.Many{}:
      +T = {S.St{S.Dead{S.BadValue{path, nn, rest}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
      e1 = Equal.sym(Bool, String.starts_with(rest, "="), False{}, h_noeq)
      %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Many{}, nn, S.short_of.val(_, rest), orig, args, up,
          subs, path, bs, pos, raw, seen), True{})
        == T : S.St}
      e2 = Equal.sym(Bool, String.is_empty(rest), False{}, h_some)
      %e2 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Many{}, nn,
          Bool.pick(Maybe<&2, String>, _, None{},
              Some{rest}), orig, args, up, subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), rest), False{}, h_ok)
      %e4 : {S.cluster(rest, orig, S.parse.take_choice(_, nn, rest, args, up, subs, path, bs, pos, raw, seen),
          True{}) == T : S.St}
      Laws.cluster_done(rest, orig, T)
    case S.Flag{}:
      Empty.absurd(lb.ty(S.Flag{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(lb.ty(S.Pos{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(lb.ty(S.Rest{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))

# what `ln` claims of an argument kind
def ln.ty(
  kk: S.ArgKind,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String
) -> Type:
  {S.cluster(SNil{}, orig, S.parse.take_arg.kind(kk, nn, S.cluster.val.kind(kk, SNil{}), orig, args, up, subs,
      path, bs, pos, raw, seen),
    S.cluster.ends.kind(kk, SNil{})) == S.St{S.Need{nn}, args, up, subs, path, bs, pos, raw, seen} : S.St}

# a letter spelling an option that takes a value now, last in its word
def ln(
  kk: S.ArgKind,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool}
) -> ln.ty(kk, orig, args, up, subs, path, bs, pos, raw, seen, nn):
  match kk:
    case S.Opt{}:
      e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e3 : {S.parse.once(_, S.St{S.Need{nn}, args, up, subs, path, bs, pos, raw, seen}, nn,
          path) == S.St{S.Need{nn}, args, up, subs, path, bs, pos, raw, seen} : S.St}
      {==}
    case S.Many{}:
      {==}
    case S.Flag{}:
      Empty.absurd(ln.ty(S.Flag{}, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(ln.ty(S.Pos{}, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(ln.ty(S.Rest{}, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))

# what `le` claims of an argument kind
def le.ty(
  kk: S.ArgKind,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String
) -> Type:
  {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(kk, nn, S.cluster.val.kind(kk, "=" ++ vv), orig, args, up,
      subs, path, bs, pos, raw, seen),
    S.cluster.ends.kind(kk, "=" ++ vv)) == S.St{S.Free{}, args, up, subs, path, S.Bind{nn,
        vv} <> bs, pos, raw, seen} : S.St}

# a letter spelling an option that takes a value now, then `=` and a value
def le(
  kk: S.ArgKind,
  +vv: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +nn: String,
  h_kind: {Laws.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
) -> le.ty(kk, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn):
  match kk:
    case S.Opt{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
      ep = Equal.sym(Bool, String.starts_with(vv, ""), True{}, Laws.prefix_empty(vv))
      %ep : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Opt{}, nn, S.short_of.val(_, "=" ++ vv), orig, args, up,
          subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      ed = Equal.sym(String, String.drop(vv, 0n), vv, Laws.drop_zero(vv))
      %ed : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Opt{}, nn, Some{_}, orig, args, up, subs, path,
          bs, pos, raw, seen), True{}) == T
        : S.St}
      e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e3 : {S.cluster("=" ++ vv, orig, S.parse.once(_, S.parse.take_opt(Some{vv}, nn, args, up, subs, path, bs,
          pos, raw, seen), nn, path), True{}) == T
        : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), True{}, h_ok)
      %e4 : {S.cluster("=" ++ vv, orig, S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, raw,
          seen), True{}) == T : S.St}
      Laws.cluster_done("=" ++ vv, orig, T)
    case S.Many{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
      ep = Equal.sym(Bool, String.starts_with(vv, ""), True{}, Laws.prefix_empty(vv))
      %ep : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Many{}, nn, S.short_of.val(_, "=" ++ vv), orig,
          args, up,
          subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      ed = Equal.sym(String, String.drop(vv, 0n), vv, Laws.drop_zero(vv))
      %ed : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Many{}, nn, Some{_}, orig, args, up, subs, path,
          bs, pos, raw, seen), True{}) == T
        : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), True{}, h_ok)
      %e4 : {S.cluster("=" ++ vv, orig, S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, raw,
          seen), True{}) == T : S.St}
      Laws.cluster_done("=" ++ vv, orig, T)
    case S.Flag{}:
      Empty.absurd(le.ty(S.Flag{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(le.ty(S.Pos{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(le.ty(S.Rest{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))

def Laws.letter_value(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_kind,
  h_noeq,
  h_some,
  h_ok
):
  +aa = {S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
  +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, rest} <> bs, pos, raw, seen} : S.St}
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  lv(kind, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_noeq, h_some, h_ok)

def Laws.letter_value_bad(
  cc,
  rest,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_kind,
  h_noeq,
  h_some,
  h_bad
):
  +aa = {S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
  +T = {S.St{S.Dead{S.BadValue{path, nn, rest}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  e0 = cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  lb(kind, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_noeq, h_some, h_bad)

def Laws.letter_value_next(
  cc,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_kind
):
  +aa = {S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
  +T = {S.St{S.Need{nn}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  e0 = cl.back(cc, SNil{}, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  ln(kind, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind)

def Laws.letter_value_eq(
  cc,
  vv,
  orig,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  nn,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  h_found,
  h_kind,
  h_ok
):
  +aa = {S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
  +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
  e0 = cl.back(cc, "=" ++ vv, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  le(kind, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_ok)

def Laws.plain_word_step(tok, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_help):
  +rhs = S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e2 = Equal.sym(Bool, Bool.and(String.eq(tok, "help"), Bool.not(seen)), False{}, h_help)
  %e2 : {S.parse.step.help(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, Walk.wk.dash(tok, h_dash))
  %e3 : {S.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {S.parse.step.kind.go(False{}, _, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  {==}

def Laws.dash_word_step(_args, _up, _subs, _path, _bs, _pos, _seen):
  {==}

# the help walk renders the page it reaches
def hl.go(
  path: List<&2, String>,
  how: S.How
) -> {S.help.go(path, how) == Laws.page(Laws.reach(path, how)) : String}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, _g, _s, _u}:
          {==}
    case Con{+hh, tt}:
      hl.go(tt, S.help.step(how, hh))

# the usage walk reads the usage line of the page it reaches
def hl.usage(
  path: List<&2, String>,
  how: S.How
) -> {S.usage.go(path, how) == Laws.usage_line(Laws.reach(path, how)) : String}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, _g, _s, _u}:
          {==}
    case Con{+hh, tt}:
      hl.usage(tt, S.help.step(how, hh))

def Laws.help_page(spec, path):
  match spec:
    case S.Cli{+name, +about, +version, +args, +subs}:
      hl.go(path, S.How{name, about, version, args, subs, name})

def Laws.reach_child(bin, about, version, args, subs, usage, name, sn, sa, sargs, ssubs, h_sub):
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, name), Some{S.Sub{sn, sa, sargs, ssubs}}, h_sub)
  %ee : {S.help.step.go(_, bin, about, version, args, subs, name, usage)
    == S.How{sn, sa, None{}, sargs, ssubs, usage ++ " " ++ name} : S.How}
  {==}

def Laws.reach_skip(bin, about, version, args, subs, usage, name, h_sub):
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, name), None{}, h_sub)
  %ee : {S.help.step.go(_, bin, about, version, args, subs, name, usage) == S.How{bin, about, version, args,
      subs, usage}
    : S.How}
  {==}

def Laws.err_path_at(_at, _word, _name, _value):
  {==}

# the usage line an error's text shows is the one its command's page shows
def et.usage(
  spec: Shake.Cli,
  +path: List<&2, String>
) -> {S.usage.at(spec, path) == Laws.usage_line(Laws.reach(path, Laws.root(spec))) : String}:
  match spec:
    case S.Cli{+name, +about, +version, +args, +subs}:
      hl.usage(path, S.How{name, about, version, args, subs, name})

# an error's text, with its usage line read as its page's
def et.wrap(
  +spec: Shake.Cli,
  +at: List<&2, String>,
  +msg: String
) -> {S.err.wrap(spec, at, msg)
    == msg ++ "\n\n" ++ Laws.usage_line(Laws.reach(at, Laws.root(spec))) ++ "\n\n" ++ S.err.hint(at) : String}:
  Equal.cong(String, String, uu => msg ++ "\n\n" ++ uu ++ "\n\n" ++ S.err.hint(at), S.usage.at(spec, at),
    Laws.usage_line(Laws.reach(at, Laws.root(spec))), et.usage(spec, at))

# what `err_text_usage` claims of an error
def et.ty(+spec: Shake.Cli, +err: Shake.ParseErr) -> Type:
  &msg: String -> {Shake.err_text(spec, err)
    == msg ++ "\n\n" ++ Laws.usage_line(Laws.reach(Shake.err_path(err), Laws.root(spec))) ++ "\n\n" ++
      S.err.hint(Shake.err_path(err)) : String}

# Unit for None, Empty for Some: a motive that tells them apart
def et.none_ty(mm: Maybe<&2, List<&2, String>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_p}:
      Empty

# a request for help has a help path
def et.some_none(+path: List<&2, String>, hh: {Some{path} == None{} : Maybe<&2, List<&2, String>>}) -> Empty:
  ee = Equal.sym(Maybe<&2, List<&2, String>>, Some{path}, None{}, hh)
  %ee : et.none_ty(_)
  Unit{}

def Laws.err_text_usage(spec, err, h_err):
  match err:
    case S.UnknownFlag{+at, +word}:
      ("error: unexpected argument '" ++ word ++ "' found",
        et.wrap(spec, at, "error: unexpected argument '" ++ word ++ "' found"))
    case S.Missing{+at, +name}:
      ("error: the following required argument was not provided:\n  " ++ name,
        et.wrap(spec, at, "error: the following required argument was not provided:\n  " ++ name))
    case S.NoValue{+at, +name}:
      ("error: a value is required for '" ++ name ++ "' but none was supplied",
        et.wrap(spec, at, "error: a value is required for '" ++ name ++ "' but none was supplied"))
    case S.BadValue{+at, +name, +value}:
      ("error: invalid value '" ++ value ++ "' for '" ++ name ++ "'",
        et.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ name ++ "'"))
    case S.NeedHelp{+path}:
      Empty.absurd(et.ty(spec, S.NeedHelp{path}), et.some_none(path, h_err))
    case S.Unexpected{+at, +arg}:
      ("error: unexpected argument '" ++ arg ++ "' found",
        et.wrap(spec, at, "error: unexpected argument '" ++ arg ++ "' found"))
    case S.Repeated{+at, +name}:
      ("error: the argument '" ++ name ++ "' cannot be used multiple times",
        et.wrap(spec, at, "error: the argument '" ++ name ++ "' cannot be used multiple times"))

# a string with nothing after it is itself
def hs.nil(xs: String) -> {xs ++ "" == xs : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(String, String, ys => SCon{hh, ys}, tt ++ "", tt, hs.nil(tt))

# the Commands lines are the subcommands' lines, then `help`'s
def hs.cmds(
  +subs: List<&2, S.Sub>,
  +ww: Nat
) -> {S.help.cmd_lines(subs, ww) == Laws.sub_lines(List.append(&2, S.Sub, subs, [Laws.help_sub()]), ww) : String}:
  match subs:
    case Nil{}:
      Equal.sym(String, S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww) ++ "",
        S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww),
        hs.nil(S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww)))
    case Con{+hh, +tt}:
      Equal.cong(String, String, xs => S.help.cmd_line(S.help.sub_name(hh), S.help.sub_about(hh), ww) ++ xs,
        S.help.cmd_lines(tt, ww), Laws.sub_lines(List.append(&2, S.Sub, tt, [Laws.help_sub()]), ww), hs.cmds(tt, ww))

def Laws.cmds_listed(subs):
  Equal.cong(String, String, xs => "Commands:\n" ++ xs ++ "\n", S.help.cmd_lines(subs, S.help.cmd_width(subs, 0n)),
    Laws.sub_lines(List.append(&2, S.Sub, subs, [Laws.help_sub()]), S.help.cmd_width(subs, 0n)),
    hs.cmds(subs, S.help.cmd_width(subs, 0n)))

# an option's line, then the lines after it
def hs.opt_next(
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +ww: Nat,
  ee: {S.help.opt_lines(tt, ww) == Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww) : String}
) -> {S.help.opt_line(aa, ww) ++ "\n" ++ S.help.opt_lines(tt, ww)
    == S.help.opt_line(aa, ww) ++ "\n" ++ Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww) : String}:
  Equal.cong(String, String, xs => S.help.opt_line(aa, ww) ++ "\n" ++ xs, S.help.opt_lines(tt, ww),
    Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww), ee)

# the Options lines are the lines of the flags and options, in order
def hs.opts(
  +args: List<&2, S.Arg>,
  +ww: Nat
) -> {S.help.opt_lines(args, ww) == Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, args), ww) : String}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, kind, +h, +r, +d, +c}:
          match kind:
            case S.Flag{}:
              hs.opt_next(S.Arg{n, s, l, S.Flag{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Opt{}:
              hs.opt_next(S.Arg{n, s, l, S.Opt{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Many{}:
              hs.opt_next(S.Arg{n, s, l, S.Many{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Pos{}:
              hs.opts(tt, ww)
            case S.Rest{}:
              hs.opts(tt, ww)

def Laws.opts_listed(args):
  Equal.cong(String, String, xs => S.help.opts.go(xs), S.help.opt_lines(args, S.help.opt_width(args, 0n)),
    Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, args), S.help.opt_width(args, 0n)),
    hs.opts(args, S.help.opt_width(args, 0n)))

# a positional's hint, then the hints after it
def hs.pos_next(
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  ee: {S.help.pos(tt) == Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt)) : String}
) -> {S.help.pos.one(aa) ++ S.help.pos(tt) == S.help.pos.one(aa) ++ Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt))
    : String}:
  Equal.cong(String, String, xs => S.help.pos.one(aa) ++ xs, S.help.pos(tt),
    Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt)), ee)

# the usage hints are the marks of the positionals, in order
def hs.pos(+args: List<&2, S.Arg>) -> {S.help.pos(args) == Laws.marks(List.filter(~S.Arg, ~S.pos.is, args)) : String}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, kind, +h, r, +d, +c}:
          match kind:
            case S.Flag{}:
              hs.pos(tt)
            case S.Opt{}:
              hs.pos(tt)
            case S.Many{}:
              hs.pos(tt)
            case S.Pos{}:
              match r:
                case True{}:
                  hs.pos_next(S.Arg{n, s, l, S.Pos{}, h, True{}, d, c}, tt, hs.pos(tt))
                case False{}:
                  hs.pos_next(S.Arg{n, s, l, S.Pos{}, h, False{}, d, c}, tt, hs.pos(tt))
            case S.Rest{}:
              match r:
                case True{}:
                  hs.pos_next(S.Arg{n, s, l, S.Rest{}, h, True{}, d, c}, tt, hs.pos(tt))
                case False{}:
                  hs.pos_next(S.Arg{n, s, l, S.Rest{}, h, False{}, d, c}, tt, hs.pos(tt))

def Laws.usage_listed(name, args, subs):
  Equal.cong(String, String, xs => "Usage: " ++ name ++ S.help.opts_hint(args) ++ xs ++ S.help.cmd_hint(subs),
    S.help.pos(args), Laws.marks(List.filter(~S.Arg, ~S.pos.is, args)), hs.pos(args))

# two report lists, each equal to another, one after the other
def sc.both(
  +x1: List<&2, K.SpecErr>,
  +y1: List<&2, K.SpecErr>,
  +x2: List<&2, K.SpecErr>,
  +y2: List<&2, K.SpecErr>,
  e1: {x1 == y1 : List<&2, K.SpecErr>},
  e2: {x2 == y2 : List<&2, K.SpecErr>}
) -> {K.both(x1, x2) == K.both(y1, y2) : List<&2, K.SpecErr>}:
  Equal.trans(List<&2, K.SpecErr>, K.both(x1, x2), K.both(y1, x2), K.both(y1, y2),
    Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>, zz => K.both(zz, x2), x1, y1, e1),
    Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>, zz => K.both(y1, zz), x2, y2, e2))

# a listed-or-not answer, then the rest's
def sc.ok.at(
  bb: Bool,
  +r1: Bool,
  +r2: Bool,
  ee: {r1 == r2 : Bool}
) -> {S.allowed.ok.at(bb, r1) == Bool.or(bb, r2) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ee

# a value is listed among choices when the choices contain it
def sc.ok(
  cs: List<&2, String>,
  +vv: String
) -> {S.allowed.ok(cs, vv) == List.contains(~String, ~String.eq, cs, vv) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      sc.ok.at(String.eq(hh, vv), S.allowed.ok(tt, vv), List.contains(~String, ~String.eq, tt, vv), sc.ok(tt, vv))

# the default's report is the one the law names
def sc.dflt(
  +path: List<&2, String>,
  +name: String,
  +cs: List<&2, String>,
  dflt: Maybe<&2, String>
) -> {K.args.default(dflt, cs, path, name) == Laws.off_choice(path, name, cs, dflt) : List<&2, K.SpecErr>}:
  match dflt:
    case None{}:
      {==}
    case Some{+vv}:
      Equal.cong(Bool, List<&2, K.SpecErr>,
        bb => K.one(Bool.and(Bool.not(List.is_empty(&2, String, cs)), Bool.not(bb)),
          K.DefaultNotChoice{path, name, vv}),
        S.allowed.ok(cs, vv), List.contains(~String, ~String.eq, cs, vv), sc.ok(cs, vv))

# the argument reports, from the arguments before
def sc.args(
  args: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> {K.args.dups(args, path, Laws.arg_names(before), Laws.arg_shorts(before), Laws.arg_longs(before))
    == Laws.args_reports(args, path, before) : List<&2, K.SpecErr>}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+name, +short, +long, +kind, +help, +req, +dflt, +cs}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(
              K.one(List.contains(~String, ~String.eq, Laws.arg_names(before), name), K.SameName{path, name}),
              K.both(K.one(K.spelled.seen(short, Laws.arg_shorts(before)), K.SameShort{path, S.text.of(short, "")}),
                K.both(K.one(K.spelled.seen(long, Laws.arg_longs(before)), K.SameLong{path, S.text.of(long, "")}),
                  zz))),
            K.both(K.args.default(dflt, cs, path, name),
              K.args.dups(tt, path, name <> Laws.arg_names(before), K.spelled.add(short, Laws.arg_shorts(before)),
                K.spelled.add(long, Laws.arg_longs(before)))),
            K.both(Laws.off_choice(path, name, cs, dflt),
              Laws.args_reports(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before)),
            sc.both(K.args.default(dflt, cs, path, name), Laws.off_choice(path, name, cs, dflt),
              K.args.dups(tt, path, name <> Laws.arg_names(before), K.spelled.add(short, Laws.arg_shorts(before)),
                K.spelled.add(long, Laws.arg_longs(before))),
              Laws.args_reports(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before),
              sc.dflt(path, name, cs, dflt),
              sc.args(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before)))

# the positional reports, from the positionals before
def sc.pos(
  pos: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> {K.pos.order(pos, path, Laws.any_optional(before)) == Laws.pos_reports(pos, path, before)
    : List<&2, K.SpecErr>}:
  match pos:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+name, +short, +long, +kind, +help, +req, +dflt, +cs}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(
              K.one(Bool.and(S.rest.is.kind(kind), Bool.not(List.is_empty(&2, S.Arg, tt))), K.RestNotLast{path, name}),
              K.both(K.one(Bool.and(req, Laws.any_optional(before)), K.RequiredAfterOptional{path, name}), zz)),
            K.pos.order(tt, path, Bool.or(Laws.any_optional(before), Bool.not(req))),
            Laws.pos_reports(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before),
            sc.pos(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before))

# the subcommand reports, from the subcommands before
def sc.subs(
  subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +before: List<&2, S.Sub>
) -> {K.subs.dups(subs, path, Laws.sub_names(before)) == Laws.sub_reports(subs, path, before) : List<&2, K.SpecErr>}:
  match subs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Sub{+name, +about, +args, +kids}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(K.one(List.contains(~String, ~String.eq, Laws.sub_names(before), name), K.SameSub{path, name}),
              K.both(K.one(String.eq(name, "help"), K.HelpSub{path}), zz)),
            K.subs.dups(tt, path, name <> Laws.sub_names(before)),
            Laws.sub_reports(tt, path, S.Sub{name, about, args, kids} <> before),
            sc.subs(tt, path, S.Sub{name, about, args, kids} <> before))

# one command's reports
def sc.cmd(
  +path: List<&2, String>,
  +args: List<&2, S.Arg>,
  +subs: List<&2, S.Sub>
) -> {K.cmd(path, args, subs) == Laws.cmd_reports(path, args, subs) : List<&2, K.SpecErr>}:
  sc.both(K.args.dups(args, path, [], [], []), Laws.args_reports(args, path, []),
    K.both(K.pos.order(S.pos_of(args), path, False{}), K.subs.dups(subs, path, [])),
    K.both(Laws.pos_reports(S.pos_of(args), path, []), Laws.sub_reports(subs, path, [])),
    sc.args(args, path, []),
    sc.both(K.pos.order(S.pos_of(args), path, False{}), Laws.pos_reports(S.pos_of(args), path, []),
      K.subs.dups(subs, path, []), Laws.sub_reports(subs, path, []),
      sc.pos(S.pos_of(args), path, []), sc.subs(subs, path, [])))

# appending names is associative
def sc.app(
  aa: List<&2, String>,
  +bb: List<&2, String>,
  +cc: List<&2, String>
) -> {List.append(&2, String, List.append(&2, String, aa, bb), cc)
    == List.append(&2, String, aa, List.append(&2, String, bb, cc)) : List<&2, String>}:
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => hh <> xs,
        List.append(&2, String, List.append(&2, String, tt, bb), cc),
        List.append(&2, String, tt, List.append(&2, String, bb, cc)), sc.app(tt, bb, cc))

# reversing names onto a list is reversing them, then appending it
def sc.rev_go(
  xs: List<&2, String>,
  +acc: List<&2, String>
) -> {List.reverse.go(&2, String, xs, acc) == List.append(&2, String, List.reverse.go(&2, String, xs, []), acc)
    : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, tt, hh <> acc),
        List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
        List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
        sc.rev_go(tt, hh <> acc),
        Equal.sym(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
          List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
          Equal.trans(List<&2, String>,
            List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
            List.append(&2, String, List.append(&2, String, List.reverse.go(&2, String, tt, []), [hh]), acc),
            List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
            Equal.cong(List<&2, String>, List<&2, String>, ys => List.append(&2, String, ys, acc),
              List.reverse.go(&2, String, tt, [hh]),
              List.append(&2, String, List.reverse.go(&2, String, tt, []), [hh]), sc.rev_go(tt, [hh])),
            sc.app(List.reverse.go(&2, String, tt, []), [hh], acc))))

# a reversed path with a name in front is the path, then the name
def sc.rev(
  +name: String,
  back: List<&2, String>
) -> {List.reverse(&2, String, name <> back) == List.append(&2, String, List.reverse(&2, String, back), [name])
    : List<&2, String>}:
  sc.rev_go(back, [name])

# every subcommand's reports, under a reversed path
def sc.forest(
  subs: List<&2, S.Sub>,
  +back: List<&2, String>
) -> {K.forest(subs, back) == Laws.below(subs, List.reverse(&2, String, back)) : List<&2, K.SpecErr>}:
  match subs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Sub{+name, _a, +args, +kids}:
          +rn = List.reverse(&2, String, name <> back)
          +rp = List.append(&2, String, List.reverse(&2, String, back), [name])
          sc.both(K.cmd(rn, args, kids), Laws.cmd_reports(rp, args, kids),
            K.both(K.forest(kids, name <> back), K.forest(tt, back)),
            K.both(Laws.below(kids, rp), Laws.below(tt, List.reverse(&2, String, back))),
            Equal.trans(List<&2, K.SpecErr>, K.cmd(rn, args, kids), Laws.cmd_reports(rn, args, kids),
              Laws.cmd_reports(rp, args, kids), sc.cmd(rn, args, kids),
              Equal.cong(List<&2, String>, List<&2, K.SpecErr>, pp => Laws.cmd_reports(pp, args, kids), rn, rp,
                sc.rev(name, back))),
            sc.both(K.forest(kids, name <> back), Laws.below(kids, rp), K.forest(tt, back),
              Laws.below(tt, List.reverse(&2, String, back)),
              Equal.trans(List<&2, K.SpecErr>, K.forest(kids, name <> back), Laws.below(kids, rn),
                Laws.below(kids, rp), sc.forest(kids, name <> back),
                Equal.cong(List<&2, String>, List<&2, K.SpecErr>, pp => Laws.below(kids, pp), rn, rp,
                  sc.rev(name, back))),
              sc.forest(tt, back)))

def Laws.check_listed(_name, _about, _version, args, subs):
  sc.both(K.cmd([], args, subs), Laws.cmd_reports([], args, subs), K.forest(subs, []), Laws.below(subs, []),
    sc.cmd([], args, subs), sc.forest(subs, []))

# ---- SHAKE-PARSE-1: every value bound is a piece of a word, `true` or a default

# anything or true is true
def gv.or_t(bb: Bool) -> {Bool.or(bb, True{}) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# both halves of a true `and` are true
def gv.and_tt(
  aa: Bool,
  +bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, bb) == True{} : Bool}, Walk.wk.false_true(ha))

# the left half of a true `and`
def gv.and_l(aa: Bool, bb: Bool, +hh: {Bool.and(aa, bb) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Walk.wk.false_true(hh))

# the right half of a true `and`
def gv.and_r(aa: Bool, +bb: Bool, +hh: {Bool.and(aa, bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      Empty.absurd({bb == True{} : Bool}, Walk.wk.false_true(hh))

# a word is what is left of itself
def gv.ends_self(ww: String) -> {Laws.ends(ww, ww) == True{} : Bool}:
  match ww:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      ee = Equal.sym(Bool, String.eq(SCon{hh, tt}, SCon{hh, tt}), True{}, Eq.string_eq_self(SCon{hh, tt}))
      %ee : {Bool.or(_, Laws.ends(tt, SCon{hh, tt})) == True{} : Bool}
      {==}

# what is left of a word's tail is left of the word
def gv.ends_tail(
  +cc: Char,
  +tt: String,
  +vv: String,
  +hh: {Laws.ends(tt, vv) == True{} : Bool}
) -> {Laws.ends(SCon{cc, tt}, vv) == True{} : Bool}:
  ee = Equal.sym(Bool, Laws.ends(tt, vv), True{}, hh)
  %ee : {Bool.or(String.eq(vv, SCon{cc, tt}), _) == True{} : Bool}
  gv.or_t(String.eq(vv, SCon{cc, tt}))

# dropping nothing leaves the string
def gv.drop0(ss: String) -> {String.drop(ss, 0n) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_c, _t}:
      {==}

# whether every piece of `ww` is a piece of one of the words
def gv.sufs(ww: String, +ws: List<&2, String>) -> Bool:
  match ww:
    case SNil{}:
      Laws.piece(ws, "")
    case SCon{+cc, +tt}:
      Bool.and(Laws.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws))

# every piece of `ww` is a piece of one of the words
def gv.In(+ww: String, +ws: List<&2, String>) -> Type:
  {gv.sufs(ww, ws) == True{} : Bool}

# a word's tail is within the words when the word is
def gv.in_tail(+cc: Char, +tt: String, +ws: List<&2, String>, hh: gv.In(SCon{cc, tt}, ws)) -> gv.In(tt, ws):
  gv.and_r(Laws.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws), hh)

# a word with chars dropped from its front is within the words when it is
def gv.in_drop(ww: String, kk: Nat, +ws: List<&2, String>, hh: gv.In(ww, ws)) -> gv.In(String.drop(ww, kk), ws):
  match ww kk:
    case SNil{} _:
      hh
    case SCon{+cc, +tt} 0n:
      hh
    case SCon{+cc, +tt} 1n+pp:
      gv.in_drop(tt, pp, ws, gv.in_tail(cc, tt, ws, hh))

# a word within the words is a piece of them
def gv.in_piece(ww: String, +ws: List<&2, String>, hh: gv.In(ww, ws)) -> {Laws.piece(ws, ww) == True{} : Bool}:
  match ww:
    case SNil{}:
      hh
    case SCon{+cc, +tt}:
      gv.and_l(Laws.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws), hh)

# what is left of a word once some chars are dropped is left of it
def gv.ends_drop(ww: String, kk: Nat) -> {Laws.ends(ww, String.drop(ww, kk)) == True{} : Bool}:
  match ww kk:
    case SNil{} _:
      {==}
    case SCon{+cc, +tt} 0n:
      gv.ends_self(SCon{cc, tt})
    case SCon{+cc, +tt} 1n+(+pp):
      gv.ends_tail(cc, tt, String.drop(tt, pp), gv.ends_drop(tt, pp))

# what is left of a word of a list is a piece of the list
def gv.mid_piece(
  pre: List<&2, String>,
  +tok: String,
  +rest: List<&2, String>,
  +vv: String,
  +hv: {Laws.ends(tok, vv) == True{} : Bool}
) -> {Laws.piece(List.append(&2, String, pre, tok <> rest), vv) == True{} : Bool}:
  match pre:
    case Nil{}:
      ee = Equal.sym(Bool, Laws.ends(tok, vv), True{}, hv)
      %ee : {Bool.or(_, Laws.piece(rest, vv)) == True{} : Bool}
      {==}
    case Con{+pp, +pt}:
      ih = gv.mid_piece(pt, tok, rest, vv, hv)
      ee = Equal.sym(Bool, Laws.piece(List.append(&2, String, pt, tok <> rest), vv), True{}, ih)
      %ee : {Bool.or(Laws.ends(pp, vv), _) == True{} : Bool}
      gv.or_t(Laws.ends(pp, vv))

# the tail of a string, empty for the empty one
def gv.tail(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{_c, tt}:
      tt

# whether a string is empty, as a type: the empty one is not a char in front
def gv.snil_ty(ss: String) -> Type:
  match ss:
    case SNil{}:
      Unit
    case SCon{_c, _t}:
      Empty

# the empty string is never a char in front of one
def gv.snil_scon(+cc: Char, +tt: String, ee: {SNil{} == SCon{cc, tt} : String}) -> Empty:
  %ee : gv.snil_ty(_)
  Unit{}

# dropping one more char leaves the tail of what was left
def gv.drop_succ(
  ww: String,
  kk: Nat,
  +cc: Char,
  +tt: String,
  +ee: {String.drop(ww, kk) == SCon{cc, tt} : String}
) -> {String.drop(ww, 1n+kk) == tt : String}:
  match ww kk:
    case SNil{} _:
      Empty.absurd({SNil{} == tt : String}, gv.snil_scon(cc, tt, ee))
    case SCon{+dd, +uu} 0n:
      Equal.trans(String, String.drop(uu, 0n), uu, tt, gv.drop0(uu),
        Equal.cong(String, String, ss => gv.tail(ss), SCon{dd, uu}, SCon{cc, tt}, ee))
    case SCon{+dd, +uu} 1n+pp:
      gv.drop_succ(uu, pp, cc, tt, ee)

# what is left of a word once some chars are dropped, named
def gv.ends_at(
  +tok: String,
  +kk: Nat,
  +xx: String,
  +ee: {String.drop(tok, kk) == xx : String}
) -> {Laws.ends(tok, xx) == True{} : Bool}:
  %ee : {Laws.ends(tok, _) == True{} : Bool}
  gv.ends_drop(tok, kk)

# every suffix of a word of a list is within the list
def gv.sufs_in(
  xx: String,
  +tok: String,
  +kk: Nat,
  +pre: List<&2, String>,
  +rest: List<&2, String>,
  +ee: {String.drop(tok, kk) == xx : String}
) -> gv.In(xx, List.append(&2, String, pre, tok <> rest)):
  match xx:
    case SNil{}:
      gv.mid_piece(pre, tok, rest, SNil{}, gv.ends_at(tok, kk, SNil{}, ee))
    case SCon{+cc, +tt}:
      gv.and_tt(Laws.piece(List.append(&2, String, pre, tok <> rest), SCon{cc, tt}),
        gv.sufs(tt, List.append(&2, String, pre, tok <> rest)),
        gv.mid_piece(pre, tok, rest, SCon{cc, tt}, gv.ends_at(tok, kk, SCon{cc, tt}, ee)),
        gv.sufs_in(tt, tok, 1n+kk, pre, rest, gv.drop_succ(tok, kk, cc, tt, ee)))

# a word of a list is within it
def gv.in_mid(
  +pre: List<&2, String>,
  +tok: String,
  +rest: List<&2, String>
) -> gv.In(tok, List.append(&2, String, pre, tok <> rest)):
  gv.sufs_in(tok, tok, 0n, pre, rest, gv.drop0(tok))

# a value is `true` or a piece of one of the words
def gv.ok(+ws: List<&2, String>, +vv: String) -> Bool:
  Bool.or(String.eq(vv, "true"), Laws.piece(ws, vv))

# a value within the words is one
def gv.ok_in(+ws: List<&2, String>, +vv: String, hh: gv.In(vv, ws)) -> {gv.ok(ws, vv) == True{} : Bool}:
  ee = Equal.sym(Bool, Laws.piece(ws, vv), True{}, gv.in_piece(vv, ws, hh))
  %ee : {Bool.or(String.eq(vv, "true"), _) == True{} : Bool}
  gv.or_t(String.eq(vv, "true"))

# every binding's value is one
def gv.all(bs: List<&2, S.Bind>, +ws: List<&2, String>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Bind{_n, vv} = hh
      Bool.and(gv.ok(ws, vv), gv.all(tt, ws))

# every level's bindings' values are
def gv.ups(lvs: List<&2, S.Level>, +ws: List<&2, String>) -> Bool:
  match lvs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Level{_a, bs} = hh
      Bool.and(gv.all(bs, ws), gv.ups(tt, ws))

# every value a walker holds, at every level, is one
def gv.good(st: S.St, +ws: List<&2, String>) -> Bool:
  S.St{_m, _a, up, _s, _p, binds, _o, _r, _n} = st
  Bool.and(gv.all(binds, ws), gv.ups(up, ws))

# a walker whose values all are
def gv.G(st: S.St, +ws: List<&2, String>) -> Type:
  {gv.good(st, ws) == True{} : Bool}

# a value, when there is one, is
def gv.mok(mv: Maybe<&2, String>, +ws: List<&2, String>) -> Bool:
  match mv:
    case None{}:
      True{}
    case Some{vv}:
      gv.ok(ws, vv)

# the value of a name and value cut, when there is one, is
def gv.pok(nv: String & Maybe<&2, String>, +ws: List<&2, String>) -> Bool:
  (_n, mv) = nv
  gv.mok(mv, ws)

# a walker that keeps its bindings and the levels above
def gv.keep(
  +binds: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +ws: List<&2, String>,
  +hb: {gv.all(binds, ws) == True{} : Bool},
  +hu: {gv.ups(up, ws) == True{} : Bool}
) -> {Bool.and(gv.all(binds, ws), gv.ups(up, ws)) == True{} : Bool}:
  gv.and_tt(gv.all(binds, ws), gv.ups(up, ws), hb, hu)

# the values a walker holds, as a type
def gv.B(+binds: List<&2, S.Bind>, +ws: List<&2, String>) -> Type:
  {gv.all(binds, ws) == True{} : Bool}

# the values of the levels above, as a type
def gv.U(+up: List<&2, S.Level>, +ws: List<&2, String>) -> Type:
  {gv.ups(up, ws) == True{} : Bool}

# a binding of a value that is one
def gv.put(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.and_tt(Bool.and(gv.ok(ws, val), gv.all(binds, ws)), gv.ups(up, ws),
    gv.and_tt(gv.ok(ws, val), gv.all(binds, ws), hv, hb), hu)

# a value bound when allowed
def gv.choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  match ok:
    case True{}:
      gv.put(name, val, args, up, subs, path, binds, pos, raw, seen, ws, hv, hb, hu)
    case False{}:
      gv.keep(binds, up, ws, hb, hu)

# an option's value
def gv.opt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.choice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos,
    raw, seen, ws, hv, hb, hu)

# a flag binds `true`
def gv.flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gv.put(name, "true", args, up, subs, path, binds, pos, raw, seen, ws, {==}, hb, hu)
    case Some{_v}:
      gv.keep(binds, up, ws, hb, hu)

# an option: its value now, or it waits
def gv.opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{vv}:
      gv.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# the once-check keeps the walker's values
def gv.once(
  again: Bool,
  st: S.St,
  +name: String,
  +path: List<&2, String>,
  +ws: List<&2, String>,
  hg: gv.G(st, ws)
) -> gv.G(S.parse.once(again, st, name, path), ws):
  match again:
    case True{}:
      match st:
        case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
          hg
    case False{}:
      hg

# a found argument, by its kind
def gv.akind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match kk:
    case S.Flag{}:
      gv.once(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gv.flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen, ws, hb, hu))
    case S.Opt{}:
      gv.once(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gv.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu))
    case S.Many{}:
      gv.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)
    case S.Pos{}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Rest{}:
      gv.keep(binds, up, ws, hb, hu)

# a found argument, or an unknown flag
def gv.arg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          gv.akind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# a long option with a name
def gv.named(
  empty: Bool,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match empty:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.arg(S.by_long(args, name), val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# a long option after the `=` cut
def gv.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hp: {gv.pok(nv, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match nv:
    case (+name, +val):
      gv.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hp, hb, hu)

# the `=` cut's value, when the `=` is here
def gv.cut_pick(
  eq: Bool,
  +acc: List<&2, Char>,
  +tt: List<&2, Char>,
  rest: String & Maybe<&2, String>,
  +ws: List<&2, String>,
  +hr: {gv.pok(rest, ws) == True{} : Bool},
  +ht: {gv.ok(ws, String.from_list(tt)) == True{} : Bool}
) -> {gv.pok(S.cut_eq.pick(eq, acc, tt, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      ht
    case False{}:
      hr

# the `=` cut's value is within the words when the body is
def gv.cut_go(
  cs: List<&2, Char>,
  +acc: List<&2, Char>,
  +ws: List<&2, String>,
  hh: gv.In(String.from_list(cs), ws)
) -> {gv.pok(S.cut_eq.go(cs, acc), ws) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+cc, +tt}:
      +hi = {gv.in_tail(cc, String.from_list(tt), ws, hh) : {gv.sufs(String.from_list(tt), ws) == True{} : Bool}}
      gv.cut_pick(Char.is_eq(cc, '='), acc, tt, S.cut_eq.go(tt, cc <> acc), ws, gv.cut_go(tt, cc <> acc, ws, hi),
        gv.ok_in(ws, String.from_list(tt), hi))

# a string read as chars and back is itself
def gv.round(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(String, String, xs => SCon{hh, xs}, String.from_list(String.to_list(tt)), tt, gv.round(tt))

# a long option body within the words
def gv.long(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hh: gv.In(body, ws),
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  ee = Equal.sym(String, String.from_list(String.to_list(body)), body, gv.round(body))
  hr = {%ee : gv.In(_, ws)
    hh : gv.In(String.from_list(String.to_list(body)), ws)}
  gv.cut(S.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen, ws,
    gv.cut_go(String.to_list(body), [], ws, hr), hb, hu)

# a flag letter's value: the rest after `=`
def gv.cflag(
  eq: Bool,
  +rest: String,
  +ws: List<&2, String>,
  hh: gv.In(rest, ws)
) -> {gv.mok(S.cluster.val.flag(eq, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      gv.ok_in(ws, rest, hh)
    case False{}:
      {==}

# the rest of the cluster, when there is any
def gv.crest(
  rest: String,
  +ws: List<&2, String>,
  hh: gv.In(rest, ws)
) -> {gv.mok(Bool.pick(Maybe<&2, String>, String.is_empty(rest), None{}, Some{rest}), ws) == True{} : Bool}:
  match rest:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      gv.ok_in(ws, SCon{cc, tt}, hh)

# an option letter's value: after one `=`, or the rest
def gv.sval(
  eq: Bool,
  +rest: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool}
) -> {gv.mok(S.short_of.val(eq, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      gv.ok_in(ws, String.drop(rest, 1n), gv.in_drop(rest, 1n, ws, hh))
    case False{}:
      gv.crest(rest, ws, hh)

# a letter's value is within the words when the rest of the cluster is
def gv.cval(
  found: Maybe<&2, S.Arg>,
  +rest: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool}
) -> {gv.mok(S.cluster.val(found, rest), ws) == True{} : Bool}:
  match found:
    case None{}:
      {==}
    case Some{aa}:
      match aa:
        case S.Arg{_n, _s, _l, kind, _h, _r, _d, _c}:
          match kind:
            case S.Flag{}:
              gv.cflag(String.starts_with(rest, "="), rest, ws, hh)
            case S.Opt{}:
              gv.sval(String.starts_with(rest, "="), rest, ws, hh)
            case S.Many{}:
              gv.sval(String.starts_with(rest, "="), rest, ws, hh)
            case S.Pos{}:
              {==}
            case S.Rest{}:
              {==}

# one letter, by the walker's mode
def gv.capply_mode(
  mode: S.Mode,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.cluster.apply.mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Free{}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)
    case S.Need{_n}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)
    case S.Help{}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)

# one letter against the walker
def gv.capply(
  st: S.St,
  +cc: Char,
  +rest: String,
  +orig: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster.apply(st, cc, rest, orig), ws):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gv.capply_mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_l(gv.all(binds, ws), gv.ups(up, ws), hg), gv.and_r(gv.all(binds, ws), gv.ups(up, ws), hg))

# one letter, unless the cluster has ended
def gv.letter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster.letter(done, cc, rest, orig, st), ws):
  match done:
    case True{}:
      hg
    case False{}:
      gv.capply(st, cc, rest, orig, ws, hh, hg)

# every letter of a cluster within the words
def gv.cluster(
  body: String,
  +orig: String,
  +st: S.St,
  +done: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster(body, orig, st, done), ws):
  match body:
    case SNil{}:
      hg
    case SCon{+cc, +rest}:
      +hr = {gv.in_tail(cc, rest, ws, hh) : {gv.sufs(rest, ws) == True{} : Bool}}
      gv.cluster(rest, orig, S.cluster.letter(done, cc, rest, orig, st), S.cluster.done(done, cc, rest, st), ws, hr,
        gv.letter(done, cc, rest, orig, st, ws, hr, hg))

# a short option body within the words
def gv.short(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_short(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.cluster(body, orig, S.St{S.Free{}, args, up, subs, path, binds, pos, raw, seen}, False{}, ws, hh,
    gv.keep(binds, up, ws, hb, hu))

# a positional binds the word
def gv.take_pos(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  pos: List<&2, S.Arg>,
  +raw: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), ws):
  match pos:
    case Nil{}:
      gv.keep(binds, up, ws, hb, hu)
    case Con{hp, +tt}:
      match hp:
        case S.Arg{+name, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          gv.choice(S.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt), raw, True{}, ws, gv.ok_in(ws, tok, hh), hb, hu)

# entering a subcommand moves the bindings up a level
def gv.enter(
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.enter(ss, args, up, path, binds), ws):
  match ss:
    case S.Sub{_n, _a, _g, _c}:
      gv.keep(binds, up, ws, hb, hu)

# a subcommand entered, or a missing positional
def gv.enter_or(
  miss: Maybe<&2, String>,
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), ws):
  match miss:
    case None{}:
      gv.enter(ss, args, up, path, binds, ws, hb, hu)
    case Some{_n}:
      gv.keep(binds, up, ws, hb, hu)

# a word: a subcommand, or a positional
def gv.word_go(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.take_pos(tok, args, up, subs, path, binds, pos, raw, ws, hh, hb, hu)
    case Some{ss}:
      gv.enter_or(S.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen, ws, hb, hu)

# a word
def gv.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.word_go(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)

# `-` alone is a word; otherwise a cluster
def gv.short_go(
  alone: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), ws):
  match alone:
    case True{}:
      gv.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hu)
    case False{}:
      gv.short(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 1n, ws, hh), hb, hu)

# a short option or a word
def gv.step_short(
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match dash:
    case True{}:
      gv.short_go(String.eq(tok, "-"), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)
    case False{}:
      gv.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hu)

# a long option, a short one, or a word
def gv.kind_go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match long:
    case True{}:
      gv.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 2n, ws, hh), hb, hu)
    case False{}:
      gv.step_short(dash, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# a word by its shape
def gv.skind(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.kind(tok, args, up, subs, path, binds, pos, seen), ws):
  gv.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds, pos, seen, ws,
    hh, hb, hu)

# `help` starts a help path, keeping the bindings
def gv.help(
  hit: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), ws):
  match hit:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.skind(tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# `--` switches to positionals, keeping the bindings
def gv.end(
  end: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), ws):
  match end:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen, ws, hh,
        hb, hu)

# after `--` a word is a positional
def gv.raw(
  raw: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), ws):
  match raw:
    case True{}:
      gv.take_pos(tok, args, up, subs, path, binds, pos, True{}, ws, hh, hb, hu)
    case False{}:
      gv.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# a pending option binds the word
def gv.need(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match flag:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen, ws, gv.ok_in(ws, tok, hh), hb, hu)

# a word of a help path keeps the bindings
def gv.help_path(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  _hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.help_path(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{ss}:
      match ss:
        case S.Sub{_n, _a, _g, _c}:
          gv.keep(binds, up, ws, hb, hu)

# one word, by the walker's mode
def gv.mode(
  mode: S.Mode,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Need{name}:
      gv.need(S.looks_flag(tok), name, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)
    case S.Help{}:
      gv.help_path(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)
    case S.Free{}:
      gv.raw(raw, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# one word within the words keeps every value a walker holds one
def gv.step(
  +tok: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.parse.step(tok, st), ws):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gv.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_l(gv.all(binds, ws), gv.ups(up, ws), hg), gv.and_r(gv.all(binds, ws), gv.ups(up, ws), hg))

# a walker's values, from one list of words to an equal one
def gv.tr(
  st: S.St,
  +aa: List<&2, String>,
  +bb: List<&2, String>,
  +ee: {aa == bb : List<&2, String>},
  +hg: {gv.good(st, bb) == True{} : Bool}
) -> {gv.good(st, aa) == True{} : Bool}:
  e2 = Equal.sym(List<&2, String>, aa, bb, ee)
  %e2 : {gv.good(st, _) == True{} : Bool}
  hg

# walking the words after `pre` keeps every value one of the words' pieces
def gv.walk(
  tt: List<&2, String>,
  +pre: List<&2, String>,
  +st: S.St,
  +hg: {gv.good(st, List.append(&2, String, pre, tt)) == True{} : Bool}
) -> {gv.good(S.parse.walk(tt, st), List.append(&2, String, pre, tt)) == True{} : Bool}:
  match tt:
    case Nil{}:
      hg
    case Con{+tok, +rest}:
      +ll = List.append(&2, String, pre, tok <> rest)
      +mm = List.append(&2, String, List.append(&2, String, pre, [tok]), rest)
      +ee = {sc.app(pre, [tok], rest) : {mm == ll : List<&2, String>}}
      g1 = gv.step(tok, st, ll, gv.in_mid(pre, tok, rest), hg)
      gw = gv.walk(rest, List.append(&2, String, pre, [tok]), S.parse.step(tok, st),
        gv.tr(S.parse.step(tok, st), mm, ll, ee, g1))
      gv.tr(S.parse.walk(rest, S.parse.step(tok, st)), ll, mm, Equal.sym(List<&2, String>, mm, ll, ee), gw)

# a fresh walker holds no values
def gv.start(spec: Shake.Cli, +ws: List<&2, String>) -> {gv.good(S.parse.start(spec), ws) == True{} : Bool}:
  match spec:
    case S.Cli{_n, _a, _v, _g, _s}:
      {==}

# the values of a frame's levels
def gv.fups(fr: Grow.Frame, +ws: List<&2, String>) -> Bool:
  Grow.Frame{lvs, _p} = fr
  gv.ups(lvs, ws)

# a walker's frame holds its values
def gv.frame(
  st: S.St,
  +ws: List<&2, String>,
  hg: {gv.good(st, ws) == True{} : Bool}
) -> {gv.fups(Grow.gw.frame(st), ws) == True{} : Bool}:
  match st:
    case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      hg

# a level in the middle of a list of levels whose values all are
def gv.ups_mid(
  qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +ws: List<&2, String>,
  +hh: {gv.ups(List.append(&2, S.Level, qs, S.Level{args, bs} <> up), ws) == True{} : Bool}
) -> {gv.all(bs, ws) == True{} : Bool}:
  match qs:
    case Nil{}:
      gv.and_l(gv.all(bs, ws), gv.ups(up, ws), hh)
    case Con{qq, +qt}:
      match qq:
        case S.Level{_a, +qb}:
          gv.ups_mid(qt, args, bs, up, ws,
            gv.and_r(gv.all(qb, ws), gv.ups(List.append(&2, S.Level, qt, S.Level{args, bs} <> up), ws), hh))

# `true` or a piece is given
def gv.or3(
  ee: Bool,
  pp: Bool,
  +dd: Bool,
  +hh: {Bool.or(ee, pp) == True{} : Bool}
) -> {Bool.or(ee, Bool.or(pp, dd)) == True{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      match pp:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({Bool.or(False{}, Bool.or(False{}, dd)) == True{} : Bool}, Walk.wk.false_true(hh))

# a list of values that all are one is given
def gv.all_given(
  bs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hh: {gv.all(bs, ws) == True{} : Bool}
) -> {Laws.all_given(bs, ws, args) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Bind{+nn, +vv}:
          gv.and_tt(Laws.given(ws, args, S.Bind{nn, vv}), Laws.all_given(tt, ws, args),
            gv.or3(String.eq(vv, "true"), Laws.piece(ws, vv), Laws.is_default(args, nn, vv),
              gv.and_l(gv.ok(ws, vv), gv.all(tt, ws), hh)),
            gv.all_given(tt, ws, args, gv.and_r(gv.ok(ws, vv), gv.all(tt, ws), hh)))

# a default of more arguments is still one
def gv.dmono(
  ee: Bool,
  pp: Bool,
  +xx: Bool,
  dd: Bool,
  +hh: {Bool.or(ee, Bool.or(pp, dd)) == True{} : Bool}
) -> {Bool.or(ee, Bool.or(pp, Bool.or(xx, dd))) == True{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      match pp:
        case True{}:
          {==}
        case False{}:
          e2 = Equal.sym(Bool, dd, True{}, hh)
          %e2 : {Bool.or(xx, _) == True{} : Bool}
          gv.or_t(xx)

# bindings given against some arguments are given against more
def gv.given_mono(
  xs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {Laws.all_given(xs, ws, tt) == True{} : Bool}
) -> {Laws.all_given(xs, ws, aa <> tt) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +xt}:
      match hd:
        case S.Bind{+nn, +vv}:
          match aa:
            case S.Arg{+an, +sh, +lo, +kind, +hp, +req, +ad, +cs}:
              gv.and_tt(Laws.given(ws, S.Arg{an, sh, lo, kind, hp, req, ad, cs} <> tt, S.Bind{nn, vv}),
                Laws.all_given(xt, ws, S.Arg{an, sh, lo, kind, hp, req, ad, cs} <> tt),
                gv.dmono(String.eq(vv, "true"), Laws.piece(ws, vv),
                  Bool.and(String.eq(an, nn), Laws.default_is(ad, vv)), Laws.is_default(tt, nn, vv),
                  gv.and_l(Laws.given(ws, tt, S.Bind{nn, vv}), Laws.all_given(xt, ws, tt), hh)),
                gv.given_mono(xt, ws, S.Arg{an, sh, lo, kind, hp, req, ad, cs}, tt,
                  gv.and_r(Laws.given(ws, tt, S.Bind{nn, vv}), Laws.all_given(xt, ws, tt), hh)))

# an argument's own default is given
def gv.dself(
  +ee: Bool,
  +pp: Bool,
  +nn: String,
  +vv: String,
  dd: Bool
) -> {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(String.eq(nn, nn), String.eq(vv, vv)), dd))) == True{} : Bool}:
  e1 = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  e2 = Equal.sym(Bool, String.eq(vv, vv), True{}, Eq.string_eq_self(vv))
  e3 = Equal.sym(Bool, Bool.or(pp, True{}), True{}, gv.or_t(pp))
  %e1 : {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(_, String.eq(vv, vv)), dd))) == True{} : Bool}
  %e2 : {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(True{}, _), dd))) == True{} : Bool}
  %e3 : {Bool.or(ee, _) == True{} : Bool}
  gv.or_t(ee)

# a default goes in front when its name is unbound
def gv.fone(
  skip: Bool,
  +nn: String,
  +vv: String,
  +rr: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hr: {Laws.all_given(rr, ws, args) == True{} : Bool},
  +hd: {Laws.given(ws, args, S.Bind{nn, vv}) == True{} : Bool}
) -> {Laws.all_given(S.fill.one(skip, nn, vv, rr), ws, args) == True{} : Bool}:
  match skip:
    case True{}:
      hr
    case False{}:
      gv.and_tt(Laws.given(ws, args, S.Bind{nn, vv}), Laws.all_given(rr, ws, args), hd, hr)

# the defaults filled in are the arguments' own
def gv.fill(
  args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +hh: {gv.all(bs, ws) == True{} : Bool}
) -> {Laws.all_given(S.fill.args(args, bs), ws, args) == True{} : Bool}:
  match args:
    case Nil{}:
      gv.all_given(bs, ws, [], hh)
    case Con{aa, +tt}:
      match aa:
        case S.Arg{+an, +sh, +lo, +kind, +hp, +req, ad, +cs}:
          match ad:
            case None{}:
              gv.given_mono(S.fill.args(tt, bs), ws, S.Arg{an, sh, lo, kind, hp, req, None{}, cs}, tt,
                gv.fill(tt, bs, ws, hh))
            case Some{+dv}:
              gv.fone(S.bound(S.fill.args(tt, bs), an), an, dv, S.fill.args(tt, bs), ws,
                S.Arg{an, sh, lo, kind, hp, req, Some{dv}, cs} <> tt,
                gv.given_mono(S.fill.args(tt, bs), ws, S.Arg{an, sh, lo, kind, hp, req, Some{dv}, cs}, tt,
                  gv.fill(tt, bs, ws, hh)),
                gv.dself(String.eq(dv, "true"), Laws.piece(ws, dv), an, dv, Laws.is_default(tt, an, dv)))

# reversed bindings are given when they are
def gv.rev_given(
  xs: List<&2, S.Bind>,
  +acc: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hx: {Laws.all_given(xs, ws, args) == True{} : Bool},
  +ha: {Laws.all_given(acc, ws, args) == True{} : Bool}
) -> {Laws.all_given(List.reverse.go(&2, S.Bind, xs, acc), ws, args) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+hd, +tt}:
      gv.rev_given(tt, hd <> acc, ws, args,
        gv.and_r(Laws.given(ws, args, hd), Laws.all_given(tt, ws, args), hx),
        gv.and_tt(Laws.given(ws, args, hd), Laws.all_given(acc, ws, args),
          gv.and_l(Laws.given(ws, args, hd), Laws.all_given(tt, ws, args), hx), ha))

# the bindings of a finished walker's level at `path` all are one
def gv.level(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +ms: List<&2, String>,
  h_fr: fin.Framed(spec, ws, qs, args, bs, up, path, ms)
) -> {gv.all(bs, ws) == True{} : Bool}:
  +fs = S.parse.walk(ws, S.parse.start(spec))
  +fr = {Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  fg = gv.frame(fs, ws, gv.walk(ws, [], S.parse.start(spec), gv.start(spec, ws)))
  gv.ups_mid(qs, args, bs, up, ws,
    Equal.trans(Bool, gv.fups(fr, ws), gv.fups(Grow.gw.frame(fs), ws), True{},
      Equal.cong(Grow.Frame, Bool, ff => gv.fups(ff, ws), fr, Grow.gw.frame(fs),
        Equal.sym(Grow.Frame, Grow.gw.frame(fs), fr, h_fr)),
      fg))

def Laws.values_given(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len):
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  ea = Equal.sym(Maybe<&2, S.Matched>, S.at(found, path), Some{S.matched.build(f0 <> rq, ms)},
    fin.at(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len))
  eo = Equal.sym(List<&2, S.Bind>, S.own(S.matched.build(f0 <> rq, ms)),
    List.reverse(&2, S.Bind, S.fill.args(args, bs)), Grow.gw.own_build(f0, rq, ms))
  %ea : {Laws.given_at.go(_, ws, args) == Some{True{}} : Maybe<&2, Bool>}
  %eo : {Some{Laws.all_given(_, ws, args)} == Some{True{}} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, bb => Some{bb},
    Laws.all_given(List.reverse(&2, S.Bind, S.fill.args(args, bs)), ws, args), True{},
    gv.rev_given(S.fill.args(args, bs), [], ws, args,
      gv.fill(args, bs, ws, gv.level(spec, ws, qs, args, bs, up, path, ms, h_fr)), {==}))
