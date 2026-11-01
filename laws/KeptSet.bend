import Base
import ../main.bend as Shake
import ../src/args.bend as Args

# LAW: a name `IO.get_env` found a value for is kept with that value, in front
# of the rest (a lemma for ../laws/.bend's reading)
law kept_set:
  for +nn: String
  for vv: String
  for rest: List<&2, Shake.Var>
  {Args.kept(nn, Done{vv}, rest) == (nn, vv) <> rest : List<&2, Shake.Var>}
