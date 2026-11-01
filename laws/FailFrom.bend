import Base
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: a walker that has failed finishes as that failure, whatever words
# follow (a lemma)
law fail_from:
  for st: S.St
  for +more: List<&2, String>
  for +err: S.ParseErr
  for died: {D1.dead_of(st) == Some{err} : Maybe<&2, S.ParseErr>}
  {S.parse.finish(S.parse.walk(more, st)) == Fail{err}
    : Result<&2, &2, S.ParseErr, S.Matched>}
