# whether each word of a help path names a subcommand under the one before
import Base
import ../../src/cli.bend as S

# the subcommands under a found one, or none
def kids_of(mm: Maybe<&2, S.Sub>) -> List<&2, S.Sub>:
  match mm:
    case None{}:
      []
    case Some{ss}:
      S.Sub{_n, _a, _g, kids} = ss
      kids

# whether each word names a subcommand under the one before, starting from
# `subs`
def help_names(ns: List<&2, String>, +subs: List<&2, S.Sub>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+nn, tt}:
      Bool.and(Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)), help_names(tt, kids_of(S.find_sub(subs, nn))))
