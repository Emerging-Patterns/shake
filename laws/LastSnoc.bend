import Base
import ../src/cli.bend as S

# LAW: the last of a list that ends in `vv` is `vv`, whatever the default
law last_snoc:
  for xs: List<&2, String>
  for +vv: String
  for dflt: Maybe<&2, String>
  {S.get.last(List.append(&2, String, xs, [vv]), dflt) == Some{vv} : Maybe<&2, String>}
