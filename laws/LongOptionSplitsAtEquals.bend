# A word that starts with `--`, is not exactly `--`, and has at least one char
# before its first `=` is a long option: the chars between `--` and the first
# `=` (or the end) are its spelling, and when there is an `=` everything after
# it, verbatim and possibly empty, is its value. A word `--=...` is refused as
# `UnknownFlag{word}`.
#
# also rests on: laws/LongBinds.bend, laws/LongNoName.bend
import Base
import ../src/cli.bend as S

# whether a string has no `=`
def no_eq(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+cc, tt}:
      Bool.and(Bool.not(Char.is_eq(cc, '=')), no_eq(tt))

# LAW: the `=` cut of a long option's body splits it at its first `=`: the
# chars before it are the spelling, and everything after it, verbatim and
# possibly empty, is the value
law cut_first_eq:
  for +name: String
  for +vv: String
  for h_name: {no_eq(name) == True{} : Bool}
  {S.cut_eq(name ++ ("=" ++ vv)) == (name, Some{vv}) : String & Maybe<&2, String>}

# LAW: a long option's body with no `=` is all spelling, with no value
law cut_no_eq:
  for +name: String
  for h_name: {no_eq(name) == True{} : Bool}
  {S.cut_eq(name) == (name, None{}) : String & Maybe<&2, String>}
