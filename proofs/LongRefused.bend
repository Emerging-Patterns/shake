# proofs of laws/LongRefused.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/LongArgStep.bend as L1
import ../laws/LongRefused.bend as Laws
import ../laws/Refused.bend as L2
import ../laws/defs/ArgumentLists.bend as D1
import ../laws/defs/WalkerFailure.bend as D2
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/WalkSteps.bend as M2

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
  {D2.dead_of(S.parse.take_arg.kind(kk, nn, Some{vv}, orig, args, up, subs, path, bs, pos, False{}, seen))
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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == False{} : Bool}
) -> long_refused.kind.ty(kk, nn, vv, orig, args, up, subs, path, bs, pos, seen):
  match kk:
    case S.Opt{}:
      e1 = Equal.sym(Bool, S.bound(bs, nn), False{}, Walk.wk.not_true(S.bound(bs, nn), h_kind))
      %e1 : {D2.dead_of(S.parse.once(_, S.parse.take_opt(Some{vv}, nn, args, up, subs, path, bs, pos, False{},
          seen), nn, path)) == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), False{}, h_bad)
      %e2 : {D2.dead_of(S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen))
        == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
      {==}
    case S.Many{}:
      e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), False{}, h_bad)
      %e2 : {D2.dead_of(S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, False{}, seen))
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
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_kind: {D1.takes(kind, S.bound(bs, nn)) == True{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == False{} : Bool}
) -> {D2.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_long.found(S.by_long(args, name), name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen),
    L1.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {D2.dead_of(_) == Some{S.BadValue{path, nn, vv}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}, h_found)
  %e2 : {D2.dead_of(S.parse.take_long.found(_, name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen))
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
  L2.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
    S.BadValue{path, nn, vv}, h_at,
    long_refused.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, kind, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_kind, h_bad))
