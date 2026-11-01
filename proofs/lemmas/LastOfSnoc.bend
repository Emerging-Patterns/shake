# the last element of a list grown at its end is what was added
import Base
import ../../laws/LastSnoc.bend as L1

def L1.last_snoc(xs, vv, _dflt):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      L1.last_snoc(tt, vv, Some{hh})
