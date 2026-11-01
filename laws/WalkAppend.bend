import Base
import ../src/cli.bend as S

# LAW: walking two word lists is walking the first, then the second (a lemma)
law walk_append:
  for xs: List<&2, String>
  for ys: List<&2, String>
  for st: S.St
  {S.parse.walk(List.append(&2, String, xs, ys), st)
    == S.parse.walk(ys, S.parse.walk(xs, st)) : S.St}
