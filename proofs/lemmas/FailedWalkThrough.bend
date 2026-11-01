# a failed walker stays failed through letters, clusters and later words
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S
import ../../laws/ClusterDead.bend as L1
import ../../laws/DeadWalk.bend as L2
import ../../laws/FailFrom.bend as L3
import ../../laws/Refused.bend as L4
import ../../laws/StepDies.bend as L5
import ../../laws/WalkAppend.bend as L6
import ../../laws/defs/WalkerFailure.bend as D1
import ./WalkSteps.bend as M1

def L2.dead_walk(ys, err, args, up, subs, path, binds, pos, raw, seen):
  match ys:
    case Nil{}:
      {==}
    case Con{_hh, tt}:
      L2.dead_walk(tt, err, args, up, subs, path, binds, pos, raw, seen)

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

def L3.fail_from(st, more, err, died):
  match st:
    case S.St{S.Dead{+ee}, +aa, +gg, +ss, +pp, +bb, +oo, +rr, +nn}:
      e1 = Equal.sym(S.St,
        S.parse.walk(more, S.St{S.Dead{ee}, aa, gg, ss, pp, bb, oo, rr, nn}),
        S.St{S.Dead{ee}, aa, gg, ss, pp, bb, oo, rr, nn},
        L2.dead_walk(more, ee, aa, gg, ss, pp, bb, oo, rr, nn))
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

# a failed walk finishes as its failure, whatever words follow
def fs.raw(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +more: List<&2, String>,
  +err: Shake.ParseErr,
  died: {D1.dead_of(S.parse.walk(ws, S.parse.start(spec))) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {S.parse.finish(S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec))) == Fail{err}
    : Result<&2, &2, S.ParseErr, S.Matched>}:
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec)),
    S.parse.walk(more, S.parse.walk(ws, S.parse.start(spec))),
    L6.walk_append(ws, more, S.parse.start(spec)))
  %e1 : {S.parse.finish(_) == Fail{err} : Result<&2, &2, S.ParseErr, S.Matched>}
  L3.fail_from(S.parse.walk(ws, S.parse.start(spec)), more, err, died)

# a failed walk's parse is its failure, read as a request for the version
# when it is one, whatever words follow
def fs.fail(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +more: List<&2, String>,
  +err: Shake.ParseErr,
  died: {D1.dead_of(S.parse.walk(ws, S.parse.start(spec))) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {Shake.parse(spec, List.append(&2, String, ws, more)) == Fail{S.version.err(spec, err)}
    : Result<&2, &2, S.ParseErr, S.Matched>}:
  Equal.cong(Result<&2, &2, S.ParseErr, S.Matched>, Result<&2, &2, S.ParseErr, S.Matched>,
    xx => S.version.res(spec, xx), S.parse.finish(S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec))),
    Fail{err}, fs.raw(spec, ws, more, err, died))

# an unknown option that is no request for the version stays as it is
def fs.keep(
  +spec: Shake.Cli,
  +at: List<&2, String>,
  +word: String,
  h_ver: {S.version.asks(spec, at, word) == False{} : Bool}
) -> {Fail{S.version.err(spec, S.UnknownFlag{at, word})} == Fail{S.UnknownFlag{at, word}}
    : Result<&2, &2, S.ParseErr, S.Matched>}:
  ee = Equal.sym(Bool, S.version.asks(spec, at, word), False{}, h_ver)
  %ee : {Fail{Bool.pick(S.ParseErr, _, S.NeedVersion{}, S.UnknownFlag{at, word})} == Fail{S.UnknownFlag{at, word}}
    : Result<&2, &2, S.ParseErr, S.Matched>}
  {==}

def L5.step_dies(
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
    L6.walk_append(pre, [tok], S.parse.start(spec)))
  %e1 : {D1.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St, S.parse.walk(pre, S.parse.start(spec)), st, h_at)
  %e2 : {D1.dead_of(S.parse.walk([tok], _)) == Some{err} : Maybe<&2, S.ParseErr>}
  h_step

def L4.refused(
  spec,
  pre,
  more,
  tok,
  st,
  err,
  h_at,
  h_step
):
  fs.fail(spec, List.append(&2, String, pre, [tok]), more, err,
    L5.step_dies(spec, pre, tok, st, err, h_at, h_step))

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

def L1.cluster_dead(body, orig, err, args, up, subs, path, bs, pos, raw, seen, done):
  match body:
    case SNil{}:
      {==}
    case SCon{+cc, +rest}:
      +dd = {S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen} : S.St}
      ee = Equal.sym(S.St, S.cluster.letter(done, cc, rest, orig, dd), dd,
        cd.letter(done, cc, rest, orig, err, args, up, subs, path, bs, pos, raw, seen))
      %ee : {S.cluster(rest, orig, _, S.cluster.done(done, cc, rest, dd)) == dd : S.St}
      L1.cluster_dead(rest, orig, err, args, up, subs, path, bs, pos, raw, seen, S.cluster.done(done, cc, rest, dd))

# a cluster whose walker has failed stays failed, whatever letters are left
def cl.dead(
  +rest: String,
  +orig: String,
  xx: S.St,
  +done: Bool,
  +err: S.ParseErr,
  hh: {D1.dead_of(xx) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {D1.dead_of(S.cluster(rest, orig, xx, done)) == Some{err} : Maybe<&2, S.ParseErr>}:
  match xx:
    case S.St{S.Dead{+ee}, +a, +g, +s, +p, +b, +o, +r, +n}:
      ec = Equal.sym(S.St, S.cluster(rest, orig, S.St{S.Dead{ee}, a, g, s, p, b, o, r, n}, done),
        S.St{S.Dead{ee}, a, g, s, p, b, o, r, n}, L1.cluster_dead(rest, orig, ee, a, g, s, p, b, o, r, n, done))
      %ec : {D1.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
      hh
    case S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {D1.dead_of(S.cluster(rest, orig, S.St{S.Free{}, _a, _g, _s, _p, _b, _o, _r, _n},
          done)) == Some{err}
        : Maybe<&2, S.ParseErr>}, err, hh)
    case S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {D1.dead_of(S.cluster(rest, orig, S.St{S.Need{_m}, _a, _g, _s, _p, _b, _o, _r, _n}, done))
        == Some{err} : Maybe<&2, S.ParseErr>}, err, hh)
    case S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      none.absurd(&1, {D1.dead_of(S.cluster(rest, orig, S.St{S.Help{}, _a, _g, _s, _p, _b, _o, _r, _n},
          done)) == Some{err}
        : Maybe<&2, S.ParseErr>}, err, hh)
