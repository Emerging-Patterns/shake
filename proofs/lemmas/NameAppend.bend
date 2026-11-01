# appending lists of names is associative
import Base

# appending names is associative
def sc.app(
  aa: List<&2, String>,
  +bb: List<&2, String>,
  +cc: List<&2, String>
) -> {List.append(&2, String, List.append(&2, String, aa, bb), cc)
    == List.append(&2, String, aa, List.append(&2, String, bb, cc)) : List<&2, String>}:
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => hh <> xs,
        List.append(&2, String, List.append(&2, String, tt, bb), cc),
        List.append(&2, String, tt, List.append(&2, String, bb, cc)), sc.app(tt, bb, cc))
