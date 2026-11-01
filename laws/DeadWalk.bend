import Base
import ../src/cli.bend as S

# LAW: a failed walker stays as it is, whatever words follow (a lemma)
law dead_walk:
  for ys: List<&2, String>
  for +err: S.ParseErr
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  {S.parse.walk(ys, S.St{S.Dead{err}, args, up, subs, path, binds, pos, raw, seen})
    == S.St{S.Dead{err}, args, up, subs, path, binds, pos, raw, seen} : S.St}
