# a finished cluster, the filled levels of a finished walker, refused glued
# values
import Base
import ../../src/cli.bend as S
import ../../src/eq.bend as Eq
import ../../src/walk.bend as Walk
import ../../src/grow.bend as Grow
import ../../laws/ClusterDone.bend as L1
import ../../laws/UnknownShortStep.bend as L2
import ../../laws/defs/ArgumentLists.bend as D1

def L1.cluster_done(body, orig, st):
  match body:
    case SNil{}:
      {==}
    case SCon{_cc, rest}:
      L1.cluster_done(rest, orig, st)

def L2.unknown_short_step(
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
  h_none,
  h_help
):
  e1 = Equal.sym(Bool, String.eq("-" ++ SCon{cc, rest}, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "-" ++ SCon{cc, rest}, args, up, subs, path, bs, pos,
      seen) == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e4 = Equal.sym(Cmp, String.order.go(SCon{cc, rest}, "elp", LT{}), LT{}, Eq.string_order_lt(SCon{cc, rest}, "elp"))
  %e4 : {S.parse.step.help(Bool.and(Cmp.is_eq(_), Bool.not(seen)), "-" ++ SCon{cc, rest}, args, up, subs, path, bs,
      pos, seen) == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, h_dash)
  %e3 : {S.parse.step.kind.go(String.starts_with.go.if("", rest, _), True{}, "-" ++ SCon{cc, rest}, args, up,
      subs, path, bs, pos,
      seen) == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e5 = Equal.sym(Bool, S.short_help(SCon{cc, rest}, args, seen), False{}, h_help)
  %e5 : {S.parse.take_short.go(_, SCon{cc, rest}, "-" ++ SCon{cc, rest}, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), None{}, h_none)
  %e2 : {S.cluster(rest, "-" ++ SCon{cc, rest},
      S.parse.take_arg(_, S.cluster.val(_, rest), "-" ++ SCon{cc, rest}, args, up, subs, path, bs, pos,
          False{}, seen),
      S.cluster.ends(_, rest))
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  L1.cluster_done(rest, "-" ++ SCon{cc, rest}, S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args,
      up, subs, path, bs, pos, False{}, seen})

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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool},
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
      L1.cluster_done(rest, orig, T)
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
      L1.cluster_done(rest, orig, T)
    case S.Flag{}:
      Empty.absurd(lb.ty(S.Flag{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))
    case S.Pos{}:
      Empty.absurd(lb.ty(S.Pos{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn), Walk.wk.false_true(h_kind))
    case S.Rest{}:
      Empty.absurd(lb.ty(S.Rest{}, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn),
          Walk.wk.false_true(h_kind))
