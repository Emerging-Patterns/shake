import Base
import ../src/cli.bend as S

# LAW: no flag is on in a Matched with no bindings
law on_nil:
  for name: String
  {S.on(S.Leaf{[]}, name) == False{} : Bool}
