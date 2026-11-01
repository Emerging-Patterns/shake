import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/WalkerFailure.bend as D1

# LAW: when the words before `tok` reach a state where `tok` fails the walk,
# the parse fails with that error, read as a request for the version when it
# is one, whatever follows (a lemma: every refusal row is its step fact
# through this)
law refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +st: S.St
  for +err: S.ParseErr
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {D1.dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.version.err(spec, err)} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
