# proofs of laws/ValueAbsent.bend
import Base
import ../src/cli.bend as S
import ../laws/ValueAbsent.bend as Laws

def Laws.value_absent(
  spec,
  ws,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at
):
  ee = Equal.sym(S.St, S.parse.walk(ws, S.parse.start(spec)),
    S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}, h_at)
  %ee : {S.version.res(spec, S.parse.finish(_)) == Fail{S.NoValue{path, name}} : Result<&2, &2, S.ParseErr, S.Matched>}
  {==}
