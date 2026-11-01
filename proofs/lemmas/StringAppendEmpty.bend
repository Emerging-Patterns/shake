# a string with nothing appended is itself
import Base

# a string with nothing after it is itself
def hs.nil(xs: String) -> {xs ++ "" == xs : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(String, String, ys => SCon{hh, ys}, tt ++ "", tt, hs.nil(tt))
