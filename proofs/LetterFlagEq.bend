# proofs of laws/LetterFlagEq.bend
import Base
import ../src/cli.bend as S
import ../laws/ClusterDone.bend as L1
import ../laws/LetterFlagEq.bend as Laws
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/ClusterSteps.bend as M2

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
  e0 = M2.cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == dd : S.St}
  e1 = Equal.sym(Bool, String.starts_with(rest, "="), True{}, h_eq)
  %e1 : {S.cluster(rest, orig, S.parse.take_arg.kind(S.Flag{}, nn, S.cluster.val.flag(_, rest), orig, args, up,
      subs, path,
      bs, pos, raw, seen), _) == dd : S.St}
  e2 = Equal.sym(Bool, S.bound(bs, nn), False{}, h_once)
  %e2 : {S.cluster(rest, orig, S.parse.once(_, dd, nn, path), True{}) == dd : S.St}
  L1.cluster_done(rest, orig, dd)
