import Base
import ../src/cli.bend as S

# LAW: once a letter of a short cluster fails the walker, the letters after it
# change nothing: the word fails with the first letter's error
law cluster_dead:
  for body: String
  for +orig: String
  for +err: S.ParseErr
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +done: Bool
  {S.cluster(body, orig, S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen}, done)
    == S.St{S.Dead{err}, args, up, subs, path, bs, pos, raw, seen} : S.St}
