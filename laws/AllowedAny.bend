import Base
import ../src/cli.bend as S

# LAW: empty choices accept every value
law allowed_any:
  for vv: String
  {S.allowed([], vv) == True{} : Bool}
