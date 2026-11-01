# The copy `argv` makes of the words `IO.args` gives drops the first, the
# program as invoked, and keeps all the others, in order and unchanged: for
# every list, reading the copy back gives the list after its first word, and
# nothing for an empty list.
import Base
import ../src/args.bend as Args

# a `&2` word list read back as the `&1` list IO.args answers
def down(ys: List<&2, String>) -> List<&1, String>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+hh, tt}:
      hh <> down(tt)

# the words of an IO.args line after its first, the program name
def after_head(xs: List<&1, String>) -> List<&1, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_hh, tt}:
      tt

# LAW: `copy` keeps every word IO.args gives, all of them, in order and
# unchanged: read back, the copy is the list it was made from
law copy_keeps:
  for xs: List<&1, String>
  {down(Args.copy(xs)) == xs : List<&1, String>}

# LAW: `words` drops the program name IO.args starts with and keeps every
# word after it, in order and unchanged; a line with no program name gives
# no arguments
law words_keeps:
  for xs: List<&1, String>
  {down(Args.words(xs)) == after_head(xs) : List<&1, String>}
