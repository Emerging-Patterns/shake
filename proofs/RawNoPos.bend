# proofs of laws/RawNoPos.bend
import Base
import ../src/cli.bend as S
import ../laws/RawNoPos.bend as Laws
import ../laws/Refused.bend as L1
import ./lemmas/FailedWalkThrough.bend as M1

def Laws.raw_no_pos(spec, pre, more, tok, args, up, subs, path, bs, seen, h_at):
  L1.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, [], True{}, seen},
    S.Unexpected{path, tok}, h_at, {==})
