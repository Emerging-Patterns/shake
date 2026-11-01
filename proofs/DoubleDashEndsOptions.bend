# proofs of laws/DoubleDashEndsOptions.bend
import Base
import ../src/cli.bend as S
import ../laws/DoubleDashEndsOptions.bend as Laws
import ./lemmas/WalkSteps.bend as M1

def Laws.dd_step(spec, pre, args, up, subs, path, bs, pos, seen, h_at):
  M1.kept.stepped(spec, pre, "--", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}, h_at)
