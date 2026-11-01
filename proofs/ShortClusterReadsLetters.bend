# proofs of laws/ShortClusterReadsLetters.bend
import Base
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/walk.bend as Walk
import ../laws/ShortClusterReadsLetters.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/ClusterSteps.bend as M1

def Laws.short_step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_help):
  +tok = "-" ++ SCon{cc, rest}
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == S.cluster(SCon{cc, rest}, tok, st,
      False{}) : S.St}
  e4 = Equal.sym(Cmp, String.order.go(SCon{cc, rest}, "elp", LT{}), LT{}, Eq.string_order_lt(SCon{cc, rest}, "elp"))
  %e4 : {S.parse.step.help(Bool.and(Cmp.is_eq(_), Bool.not(seen)), tok, args, up, subs, path, bs, pos, seen)
    == S.cluster(SCon{cc, rest}, tok, st, False{}) : S.St}
  e3 = Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, h_dash)
  %e3 : {S.parse.step.kind.go(String.starts_with.go.if("", rest, _), True{}, tok, args, up, subs, path, bs, pos, seen)
    == S.cluster(SCon{cc, rest}, tok, st, False{}) : S.St}
  e5 = Equal.sym(Bool, S.short_help(SCon{cc, rest}, args, seen), False{}, h_help)
  %e5 : {S.parse.take_short.go(_, SCon{cc, rest}, tok, args, up, subs, path, bs, pos, False{}, seen)
    == S.cluster(SCon{cc, rest}, tok, st, False{}) : S.St}
  {==}

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
  e0 = M1.cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
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
  h_kind: {D1.takes(kk, S.bound(bs, nn)) == True{} : Bool}
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
  e0 = M1.cl.back(cc, SNil{}, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  ln(kind, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind)
