# Once a word makes the parse fail, the words after it do not change what
# `parse` answers.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: once a word makes the parse fail, the words after it do not change
# what the parse answers
law fail_stays:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +more: List<&2, String>
  for +err: Shake.ParseErr
  for +died: {D1.dead_of(S.parse.walk(ws, S.parse.start(spec))) == Some{err} : Maybe<&2, S.ParseErr>}
  {Shake.parse(spec, List.append(&2, String, ws, more)) == Shake.parse(spec, ws)
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
