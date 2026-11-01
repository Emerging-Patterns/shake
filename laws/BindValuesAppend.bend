import Base
import ../src/cli.bend as S

# LAW: the values bound to a name in two lists of bindings are the first's
# then the second's (a lemma over the bindings alone)
law bind_values_append:
  for bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  {S.get_all.bind(List.append(&2, S.Bind, bs, cs), name)
    == List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(cs, name))
    : List<&2, String>}
