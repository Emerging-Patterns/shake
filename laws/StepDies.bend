import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: when the words before `tok` reach a state where `tok` fails the walk,
# the walk through `tok` has failed with that error (a lemma)
law step_dies:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +tok: String
  for +st: S.St
  for +err: S.ParseErr
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {D1.dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}
  {D1.dead_of(S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)))
    == Some{err} : Maybe<&2, S.ParseErr>}
