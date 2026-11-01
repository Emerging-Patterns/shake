# a failed walker stays failed
import Base
import ../../src/cli.bend as S
import ../../laws/OnceDead.bend as L1

def L1.once_dead(st, _nn, _path):
  match st:
    case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      {==}
