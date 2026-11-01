# proofs of laws/LetterValueBad.bend
import Base
import ../src/cli.bend as S
import ../laws/LetterValueBad.bend as Laws
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/ClusterSteps.bend as M2

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
  e0 = M2.cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {_ == T : S.St}
  M1.lb(kind, rest, orig, args, up, subs, path, bs, pos, raw, seen, nn, h_kind, h_noeq, h_some, h_bad)
