# A value given to an argument with a nonempty choices list binds only when it
# is in the list, and otherwise fails with `BadValue{name, value}`. An
# argument with no choices accepts every value.
#
# also rests on: laws/ChoiceRefused.bend, laws/LetterValue.bend,
# laws/LetterValueBad.bend, laws/LetterValueEq.bend, laws/LongBinds.bend,
# laws/LongRefused.bend, laws/PosBinds.bend, laws/PosNext.bend,
# laws/RawBinds.bend, laws/RawRefused.bend, laws/ValueBinds.bend,
# laws/ValueRefused.bend
import Base


