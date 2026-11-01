# proofs of laws/LongBinds.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
import ../laws/Kept.bend as L1
import ../laws/LongArgStep.bend as L2
import ../laws/LongBinds.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/BindingsKept.bend as M1
import ./lemmas/WalkSteps.bend as M2

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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool},
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
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_kind: {D1.takes(kind, S.bound(bs, nn)) == True{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
) -> {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_long.found(S.by_long(args, name), name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen),
    L2.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {_ == S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}, h_found)
  %e2 : {S.parse.take_long.found(_, name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
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
  L1.kept(spec, pre, more, "--" ++ body, st, args, up, path, nn, vv, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step("--" ++ body, st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, False{}, seen},
      long.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, kind, hp, req, dflt, cs, h_dd,
        h_cut, h_name, h_found, h_kind, h_ok)),
    h_done)
