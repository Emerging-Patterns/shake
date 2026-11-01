import Base
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: the once-check, told the name was given before, fails with Repeated
# whatever the step it guards would have done (a lemma)
law once_dead:
  for st: S.St
  for +nn: String
  for +path: List<&2, String>
  {D1.dead_of(S.parse.once(True{}, st, nn, path)) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
