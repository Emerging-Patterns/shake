# proofs of laws/LetterValueEq.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/ClusterDone.bend as L1
import ../laws/DropZero.bend as L2
import ../laws/LetterValueEq.bend as Laws
import ../laws/PrefixEmpty.bend as L3
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/ClusterSteps.bend as M2
import ./lemmas/WalkSteps.bend as M3

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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
) -> le.ty(kk, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn):
  match kk:
    case S.Opt{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
      ep = Equal.sym(Bool, String.starts_with(vv, ""), True{}, L3.prefix_empty(vv))
      %ep : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Opt{}, nn, S.short_of.val(_, "=" ++ vv), orig, args, up,
          subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      ed = Equal.sym(String, String.drop(vv, 0n), vv, L2.drop_zero(vv))
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
      L1.cluster_done("=" ++ vv, orig, T)
    case S.Many{}:
      +T = {S.St{S.Free{}, args, up, subs, path, S.Bind{nn, vv} <> bs, pos, raw, seen} : S.St}
      ep = Equal.sym(Bool, String.starts_with(vv, ""), True{}, L3.prefix_empty(vv))
      %ep : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Many{}, nn, S.short_of.val(_, "=" ++ vv), orig,
          args, up,
          subs, path, bs, pos, raw, seen), True{}) == T : S.St}
      ed = Equal.sym(String, String.drop(vv, 0n), vv, L2.drop_zero(vv))
      %ed : {S.cluster("=" ++ vv, orig, S.parse.take_arg.kind(S.Many{}, nn, Some{_}, orig, args, up, subs, path,
          bs, pos, raw, seen), True{}) == T
        : S.St}
      e4 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, nn)), vv), True{}, h_ok)
      %e4 : {S.cluster("=" ++ vv, orig, S.parse.take_choice(_, nn, vv, args, up, subs, path, bs, pos, raw,
          seen), True{}) == T : S.St}
      L1.cluster_done("=" ++ vv, orig, T)
    case S.Flag{}:
      Empty.absurd(le.ty(S.Flag{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(le.ty(S.Pos{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(le.ty(S.Rest{}, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))

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
  e0 = M2.cl.back(cc, "=" ++ vv, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  le(kind, vv, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_ok)
