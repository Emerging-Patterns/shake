# A flag or an option built with `opt` that is given a second time while the
# same command is current, under any of its spellings, fails the parse with
# `Repeated{at, name}`; an argument of a parent command with the same name is
# a different argument (laws/UnknownSpellingRefused.bend). An option built with `many` binds every
# value given, in the order given, and `get_all` of its command's Matched
# reads them all.
#
# also rests on: laws/LetterFlagAgain.bend, laws/LetterOptAgain.bend,
# laws/LetterValue.bend, laws/LetterValueEq.bend, laws/LongBinds.bend,
# laws/RepeatedLongFlag.bend, laws/RepeatedLongOpt.bend
import Base


