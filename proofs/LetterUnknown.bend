# proofs of laws/LetterUnknown.bend
import Base
import ../src/cli.bend as S
import ../laws/ClusterDone.bend as L1
import ../laws/LetterUnknown.bend as Laws
import ./lemmas/ClusterEnd.bend as M1

def Laws.letter_unknown(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, h_none):
  +dd = {S.St{S.Dead{S.UnknownFlag{path, orig}}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), None{}, h_none)
  %e2 : {S.cluster(rest, orig,
      S.parse.take_arg(_, S.cluster.val(_, rest), orig, args, up, subs, path, bs, pos, raw, seen),
      S.cluster.ends(_, rest)) == dd : S.St}
  L1.cluster_done(rest, orig, dd)
