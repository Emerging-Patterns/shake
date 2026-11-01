import Base
import ../src/cli.bend as S

# LAW: `get` on a Matched with no bindings is None
law get_nil:
  for name: String
  {S.get(S.Leaf{[]}, name) == None{} : Maybe<&2, String>}
