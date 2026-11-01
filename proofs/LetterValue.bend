# proofs of laws/LetterValue.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/ClusterDone.bend as L1
import ../laws/LetterValue.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/ClusterSteps.bend as M2

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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool},
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
      L1.cluster_done(rest, orig, T)
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
      L1.cluster_done(rest, orig, T)
    case S.Flag{}:
      Empty.absurd(lv.ty(S.Flag{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(lv.ty(S.Pos{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(lv.ty(S.Rest{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))

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
  e0 = M2.cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  lv(kind, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_noeq, h_some, h_ok)
