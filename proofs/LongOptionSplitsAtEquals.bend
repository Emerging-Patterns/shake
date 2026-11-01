# proofs of laws/LongOptionSplitsAtEquals.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/LongOptionSplitsAtEquals.bend as Laws

# a string read back from its chars is itself
def cut.from_to(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, xx => SCon{hh, xx}, String.from_list(String.to_list(tt)), tt, cut.from_to(tt))

# appending two lists, then a third, is appending the first to the rest
def cut.app(
  +aa: List<&2, Char>,
  +bb: List<&2, Char>,
  +cc: List<&2, Char>
) -> {List.append(&2, Char, List.append(&2, Char, aa, bb), cc)
    == List.append(&2, Char, aa, List.append(&2, Char, bb, cc)) : List<&2, Char>}:
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, Char>, List<&2, Char>, xs => hh <> xs,
        List.append(&2, Char, List.append(&2, Char, tt, bb), cc),
        List.append(&2, Char, tt, List.append(&2, Char, bb, cc)), cut.app(tt, bb, cc))

# reversing onto a list is reversing, then appending it
def cut.rev_acc(
  xs: List<&2, Char>,
  +acc: List<&2, Char>
) -> {List.reverse.go(&2, Char, xs, acc)
    == List.append(&2, Char, List.reverse.go(&2, Char, xs, []), acc) : List<&2, Char>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, tt, hh <> acc),
        List.append(&2, Char, List.reverse.go(&2, Char, tt, []), hh <> acc),
        List.append(&2, Char, List.reverse.go(&2, Char, tt, [hh]), acc),
        cut.rev_acc(tt, hh <> acc),
        Equal.sym(List<&2, Char>, List.append(&2, Char, List.reverse.go(&2, Char, tt, [hh]), acc),
          List.append(&2, Char, List.reverse.go(&2, Char, tt, []), hh <> acc),
          Equal.trans(List<&2, Char>,
            List.append(&2, Char, List.reverse.go(&2, Char, tt, [hh]), acc),
            List.append(&2, Char, List.append(&2, Char, List.reverse.go(&2, Char, tt, []), [hh]),
              acc),
            List.append(&2, Char, List.reverse.go(&2, Char, tt, []), hh <> acc),
            Equal.cong(List<&2, Char>, List<&2, Char>, ys => List.append(&2, Char, ys, acc),
              List.reverse.go(&2, Char, tt, [hh]),
              List.append(&2, Char, List.reverse.go(&2, Char, tt, []), [hh]), cut.rev_acc(tt, [hh])),
            cut.app(List.reverse.go(&2, Char, tt, []), [hh], acc))))

# a char after a buffer is that char in front of the buffer folded onto acc
def cut.snoc(
  xs: List<&2, Char>,
  +hh: Char,
  +acc: String
) -> {S.from.rev.go(List.append(&2, Char, xs, [hh]), acc) == SCon{hh, S.from.rev.go(xs, acc)} : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+xx, tt}:
      cut.snoc(tt, hh, SCon{xx, acc})

# folding a string's chars, reversed, onto acc is the string in front of acc
def cut.fold(
  ss: String,
  +acc: String
) -> {S.from.rev.go(List.reverse.go(&2, Char, String.to_list(ss), []), acc) == String.append(ss, acc) : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      +rev = List.reverse.go(&2, Char, String.to_list(tt), [])
      Equal.trans(String,
        S.from.rev.go(List.reverse.go(&2, Char, String.to_list(tt), [hh]), acc),
        S.from.rev.go(List.append(&2, Char, rev, [hh]), acc),
        String.append(SCon{hh, tt}, acc),
        Equal.cong(List<&2, Char>, String, xs => S.from.rev.go(xs, acc),
          List.reverse.go(&2, Char, String.to_list(tt), [hh]),
          List.append(&2, Char, rev, [hh]),
          cut.rev_acc(String.to_list(tt), [hh])),
        Equal.trans(String,
          S.from.rev.go(List.append(&2, Char, rev, [hh]), acc),
          SCon{hh, S.from.rev.go(rev, acc)},
          SCon{hh, String.append(tt, acc)},
          cut.snoc(rev, hh, acc),
          Equal.cong(String, String, xx => SCon{hh, xx},
            S.from.rev.go(rev, acc), String.append(tt, acc), cut.fold(tt, acc))))

# a string in front of nothing is the string
def cut.app_nil(ss: String) -> {String.append(ss, SNil{}) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, xx => SCon{hh, xx}, String.append(tt, SNil{}), tt, cut.app_nil(tt))

# a char a string with no `=` starts with is not `=`
def cut.head(
  +cc: Char,
  +tt: String,
  h_name: {Laws.no_eq(SCon{cc, tt}) == True{} : Bool}
) -> {Char.is_eq(cc, '=') == False{} : Bool}:
  Walk.wk.not_true(Char.is_eq(cc, '='), Walk.wk.and_l(Bool.not(Char.is_eq(cc, '=')), Laws.no_eq(tt), h_name))

# the rest of a string with no `=` has none either
def cut.tail(
  +cc: Char,
  +tt: String,
  h_name: {Laws.no_eq(SCon{cc, tt}) == True{} : Bool}
) -> {Laws.no_eq(tt) == True{} : Bool}:
  Walk.wk.and_r(Bool.not(Char.is_eq(cc, '=')), Laws.no_eq(tt), h_name)

# the cut, char by char: every char before the first `=` goes onto the
# accumulator, and the `=` ends the name
def cut.go_eq(
  name: String,
  +vv: String,
  +acc: List<&2, Char>,
  +h_name: {Laws.no_eq(name) == True{} : Bool}
) -> {S.cut_eq.go(String.to_list(name ++ ("=" ++ vv)), acc)
    == (S.from.rev(List.reverse.go(&2, Char, String.to_list(name), acc)), Some{String.from_list(String.to_list(vv))})
    : String & Maybe<&2, String>}:
  match name:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      +rest = String.to_list(tt ++ ("=" ++ vv))
      ee = Equal.sym(Bool, Char.is_eq(cc, '='), False{}, cut.head(cc, tt, h_name))
      %ee : {S.cut_eq.pick(_, acc, rest, S.cut_eq.go(rest, cc <> acc))
        == (S.from.rev(List.reverse.go(&2, Char, String.to_list(tt), cc <> acc)),
          Some{String.from_list(String.to_list(vv))}) : String & Maybe<&2, String>}
      cut.go_eq(tt, vv, cc <> acc, cut.tail(cc, tt, h_name))

# the cut, char by char, of a string with no `=`
def cut.go_none(
  name: String,
  +acc: List<&2, Char>,
  +h_name: {Laws.no_eq(name) == True{} : Bool}
) -> {S.cut_eq.go(String.to_list(name), acc)
    == (S.from.rev(List.reverse.go(&2, Char, String.to_list(name), acc)), None{}) : String & Maybe<&2, String>}:
  match name:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      +rest = String.to_list(tt)
      ee = Equal.sym(Bool, Char.is_eq(cc, '='), False{}, cut.head(cc, tt, h_name))
      %ee : {S.cut_eq.pick(_, acc, rest, S.cut_eq.go(rest, cc <> acc))
        == (S.from.rev(List.reverse.go(&2, Char, String.to_list(tt), cc <> acc)), None{})
        : String & Maybe<&2, String>}
      cut.go_none(tt, cc <> acc, cut.tail(cc, tt, h_name))

# the name the cut reads back is the name
def cut.name(+name: String) -> {S.from.rev(List.reverse.go(&2, Char, String.to_list(name), [])) == name : String}:
  Equal.trans(String, S.from.rev(List.reverse.go(&2, Char, String.to_list(name), [])),
    String.append(name, SNil{}), name, cut.fold(name, SNil{}), cut.app_nil(name))

def Laws.cut_first_eq(name, vv, h_name):
  +nm = S.from.rev(List.reverse.go(&2, Char, String.to_list(name), []))
  +vl = String.from_list(String.to_list(vv))
  Equal.trans(String & Maybe<&2, String>, S.cut_eq(name ++ ("=" ++ vv)), (nm, Some{vl}), (name, Some{vv}),
    cut.go_eq(name, vv, [], h_name),
    Equal.trans(String & Maybe<&2, String>, (nm, Some{vl}), (name, Some{vl}), (name, Some{vv}),
      Equal.cong(String, String & Maybe<&2, String>, xx => (xx, Some{vl}), nm, name, cut.name(name)),
      Equal.cong(String, String & Maybe<&2, String>, xx => (name, Some{xx}), vl, vv, cut.from_to(vv))))

def Laws.cut_no_eq(name, h_name):
  +nm = S.from.rev(List.reverse.go(&2, Char, String.to_list(name), []))
  Equal.trans(String & Maybe<&2, String>, S.cut_eq(name), (nm, None{}), (name, None{}),
    cut.go_none(name, [], h_name),
    Equal.cong(String, String & Maybe<&2, String>, xx => (xx, None{}), nm, name, cut.name(name)))
