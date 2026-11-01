# the error a walker has failed with, if any
import Base
import ../../src/cli.bend as S

# the error a walker has failed with, or None while it is still going
def dead_of(st: S.St) -> Maybe<&2, S.ParseErr>:
  match st:
    case S.St{S.Dead{err}, _a, _g, _s, _p, _b, _o, _r, _n}:
      Some{err}
    case S.St{_mode, _a, _g, _s, _p, _b, _o, _r, _n}:
      None{}
