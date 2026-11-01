# proofs of laws/LetterOptAgain.bend
import Base
import ../src/cli.bend as S
import ../laws/LetterOptAgain.bend as Laws
import ../laws/OnceDead.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/ClusterSteps.bend as M1
import ./lemmas/FailedWalkThrough.bend as M2
import ./lemmas/FailedWalkerStays.bend as M3

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
  e0 = M1.cl.back(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found)
  %e0 : {D1.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e2 : {D1.dead_of(S.cluster(rest, orig, S.parse.once(_, S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw,
      seen), nn, path), True{})) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  M2.cl.dead(rest, orig, S.parse.once(True{}, S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw, seen),
      nn, path),
    True{}, S.Repeated{path, nn}, L1.once_dead(S.parse.take_opt(vv, nn, args, up, subs, path, bs, pos, raw,
        seen), nn, path))
