import Base
import ../src/cli.bend as S

# LAW: once a short cluster has ended, the letters left change nothing (a
# lemma)
law cluster_done:
  for body: String
  for +orig: String
  for +st: S.St
  {S.cluster(body, orig, st, True{}) == st : S.St}
