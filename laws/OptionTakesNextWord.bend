# An option given no value in its own word takes the next word as its value,
# unless that word starts with `-` and is not `-`, or there is none; then the
# parse fails with `NoValue{name}`.
#
# also rests on: laws/ValueAbsent.bend, laws/ValueBinds.bend,
# laws/ValueFlagShaped.bend
import Base


