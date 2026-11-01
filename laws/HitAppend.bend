import Base
import ../src/cli.bend as S

# LAW: a flag binding's hit keeps whatever list follows it (a lemma)
law hit_append:
  for bb: Bool
  for +vv: String
  for xs: List<&2, String>
  for ys: List<&2, String>
  {S.get_all.bind.hit(bb, vv, List.append(&2, String, xs, ys))
    == List.append(&2, String, S.get_all.bind.hit(bb, vv, xs), ys) : List<&2, String>}
