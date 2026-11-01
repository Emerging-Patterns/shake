# proofs of laws/UnknownLong.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../laws/UnknownLong.bend as Laws
import ../laws/UnknownLongDies.bend as L1
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/WalkSteps.bend as M2

def Laws.unknown_long(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_none,
  h_lh,
  h_ver
):
  +ww = List.append(&2, String, pre, ["--" ++ body])
  +er = {S.UnknownFlag{path, "--" ++ body} : S.ParseErr}
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, List.append(&2, String, ww, more)),
    Fail{S.version.err(spec, er)}, Fail{er},
    M1.fs.fail(spec, ww, more, er,
      L1.unknown_long_dies(spec, pre, body, name, val, args, up, subs, path, bs, pos, seen,
        h_at, h_dd, h_cut, h_name, h_none, h_lh)),
    M1.fs.keep(spec, path, "--" ++ body, h_ver))
