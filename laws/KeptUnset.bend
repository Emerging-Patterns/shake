import Base
import ../main.bend as Shake
import ../src/args.bend as Args

# LAW: a name `IO.get_env` failed for gives no pair (a lemma for
# ../laws/.bend's reading)
law kept_unset:
  for nn: String
  for ee: U32 & String
  for rest: List<&2, Shake.Var>
  {Args.kept(nn, Fail{ee}, rest) == rest : List<&2, Shake.Var>}
